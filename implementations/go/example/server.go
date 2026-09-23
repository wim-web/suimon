package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"net/http"
	"os"
	"strconv"
	"sync"
	"time"
)

// The JSON API of the playground:
//
//	GET  /api/scenarios            the scenarios with their programs and default inputs
//	POST /api/runs                 {"scenario": id, "input": value?} starts a run; returns {"id": ...}
//	GET  /api/runs/{id}?after=n    the progress, with the record lines from n on
//	GET  /api/runs/{id}/events     the same progress as server-sent events, until the run is done
//	GET  /api/runs/{id}/report     the report of a finished run (409 while it runs)
//	POST /api/runs/{id}/cancel     cancels the run
//
// Runs are kept in memory; the oldest finished runs are dropped beyond maxRuns.

const maxRuns = 50

type server struct {
	ctx       context.Context
	scenarios []*scenario
	unit      time.Duration

	mu    sync.Mutex
	next  int
	runs  map[string]*run
	order []string
}

func newServer(ctx context.Context, scenarios []*scenario, unit time.Duration) *server {
	return &server{ctx: ctx, scenarios: scenarios, unit: unit, runs: map[string]*run{}}
}

func (s *server) handler(assets fs.FS) http.Handler {
	mux := http.NewServeMux()
	if assets != nil {
		mux.Handle("GET /", http.FileServer(http.FS(assets)))
	}
	mux.HandleFunc("GET /api/scenarios", func(w http.ResponseWriter, r *http.Request) { writeJSON(w, http.StatusOK, s.scenarios) })
	mux.HandleFunc("POST /api/runs", s.start)
	mux.HandleFunc("GET /api/runs/{id}", s.withRun(s.poll))
	mux.HandleFunc("GET /api/runs/{id}/events", s.withRun(s.events))
	mux.HandleFunc("GET /api/runs/{id}/report", s.withRun(s.report))
	mux.HandleFunc("POST /api/runs/{id}/cancel", s.withRun(func(w http.ResponseWriter, r *http.Request, run *run) {
		run.exec.Cancel()
		w.WriteHeader(http.StatusNoContent)
	}))
	return mux
}

func (s *server) scenario(id string) *scenario {
	for _, sc := range s.scenarios {
		if sc.ID == id {
			return sc
		}
	}
	return nil
}

func (s *server) start(w http.ResponseWriter, r *http.Request) {
	var req struct {
		Scenario string          `json:"scenario"`
		Input    json.RawMessage `json:"input"`
	}
	dec := json.NewDecoder(http.MaxBytesReader(w, r.Body, 64<<10))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&req); err != nil || dec.Decode(new(any)) != io.EOF {
		http.Error(w, "expected one JSON object {scenario, input?}", http.StatusBadRequest)
		return
	}
	sc := s.scenario(req.Scenario)
	if sc == nil {
		http.Error(w, fmt.Sprintf("unknown scenario %q", req.Scenario), http.StatusNotFound)
		return
	}
	input := req.Input
	if input == nil || string(input) == "null" {
		input = sc.Input
	}
	if sc.Input == nil {
		input = nil
	}
	s.mu.Lock()
	s.next++
	id := "r" + strconv.Itoa(s.next)
	s.mu.Unlock()
	run, err := startRun(s.ctx, id, sc, input, s.unit)
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	s.mu.Lock()
	s.runs[id] = run
	s.order = append(s.order, id)
	s.evict()
	s.mu.Unlock()
	writeJSON(w, http.StatusCreated, map[string]string{"id": id})
}

// evict drops the oldest finished runs beyond maxRuns.
func (s *server) evict() {
	for i := 0; len(s.order) > maxRuns && i < len(s.order); {
		id := s.order[i]
		if _, _, done := s.runs[id].result(); done {
			delete(s.runs, id)
			s.order = append(s.order[:i], s.order[i+1:]...)
			continue
		}
		i++
	}
}

func (s *server) withRun(h func(http.ResponseWriter, *http.Request, *run)) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		s.mu.Lock()
		run := s.runs[r.PathValue("id")]
		s.mu.Unlock()
		if run == nil {
			http.Error(w, "unknown run", http.StatusNotFound)
			return
		}
		h(w, r, run)
	}
}

func (s *server) poll(w http.ResponseWriter, r *http.Request, run *run) {
	after := 0
	if v := r.URL.Query().Get("after"); v != "" {
		n, err := strconv.Atoi(v)
		if err != nil || n < 0 {
			http.Error(w, "after must be a natural number", http.StatusBadRequest)
			return
		}
		after = n
	}
	p, _, err := run.progress(after)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	writeJSON(w, http.StatusOK, p)
}

// events sends the progress as server-sent events: each event carries the record lines since the
// previous one. Changes are coalesced for a short while, and a running run sends an event at least
// every tick so that the elapsed time advances.
func (s *server) events(w http.ResponseWriter, r *http.Request, run *run) {
	flusher, ok := w.(http.Flusher)
	if !ok {
		http.Error(w, "streaming unsupported", http.StatusInternalServerError)
		return
	}
	w.Header().Set("Content-Type", "text/event-stream")
	w.Header().Set("Cache-Control", "no-store")
	offset := 0
	const coalesce, tick = 40 * time.Millisecond, 250 * time.Millisecond
	for {
		p, changed, err := run.progress(offset)
		if err != nil {
			fmt.Fprintf(w, "event: failure\ndata: %s\n\n", mustJSON(err.Error()))
			flusher.Flush()
			return
		}
		if _, err := fmt.Fprintf(w, "data: %s\n\n", mustJSON(p)); err != nil {
			return
		}
		flusher.Flush()
		if p.Done {
			return
		}
		offset = p.Offset + len(p.Records)
		select {
		case <-r.Context().Done():
			return
		case <-changed:
		case <-time.After(tick):
		}
		select {
		case <-r.Context().Done():
			return
		case <-time.After(coalesce):
		}
	}
}

func (s *server) report(w http.ResponseWriter, r *http.Request, run *run) {
	report, runErr, done := run.result()
	switch {
	case !done:
		http.Error(w, "the run has not finished", http.StatusConflict)
	case report == nil:
		http.Error(w, runErr, http.StatusInternalServerError)
	default:
		writeJSON(w, http.StatusOK, report)
	}
}

func writeJSON(w http.ResponseWriter, status int, v any) {
	data, err := json.Marshal(v)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(status)
	_, _ = w.Write(data)
}

func mustJSON(v any) []byte {
	data, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	return data
}

// uiAssets checks that the UI was built.
func uiAssets(dir string) (fs.FS, error) {
	assets := os.DirFS(dir)
	if _, err := fs.Stat(assets, "index.html"); err != nil {
		return nil, errors.Join(err, errors.New("build the UI first: pnpm --filter @suimon/go-example-ui build (from the repository root)"))
	}
	return assets, nil
}
