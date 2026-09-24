package main

import (
	"context"
	"encoding/json"
	"fmt"
	"strings"
	"sync"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// A run is one execution of a scenario. It is its own journal: the engine appends the record
// lines to it, the header with the definition first, and progress replays them with Check into the
// current state, as a reader of a journal file would.
type run struct {
	id       string
	scenario *scenario
	env      *env
	exec     *suimon.WorkflowExecution
	// finished is closed once the report or the error is set.
	finished chan struct{}

	mu      sync.Mutex
	lines   []string
	changed chan struct{} // closed and replaced on every change
	done    bool
	endMs   float64 // when the run finished, from its start
	report  *reportJSON
	raw     *suimon.Report
	err     string
}

func startRun(ctx context.Context, id string, s *scenario, input json.RawMessage, unit time.Duration) (*run, error) {
	r := &run{id: id, scenario: s, changed: make(chan struct{}), finished: make(chan struct{})}
	r.env = newEnv(unit, r.signal)
	var in any // an untyped nil for a workflow without input
	if input != nil {
		in = input
	}
	exec, err := s.engine.Start(withEnv(ctx, r.env), in, suimon.WithJournal(r))
	if err != nil {
		return nil, err
	}
	r.exec = exec
	go func() {
		report, err := exec.Wait()
		r.mu.Lock()
		r.done, r.endMs = true, r.env.now()
		if err != nil {
			r.err = err.Error()
		} else {
			r.report, r.raw = newReportJSON(report), report
		}
		r.mu.Unlock()
		close(r.finished)
		r.signal()
	}()
	return r, nil
}

// Append receives complete record lines from the engine.
func (r *run) Append(lines []byte) error {
	text := strings.TrimSuffix(string(lines), "\n")
	r.mu.Lock()
	r.lines = append(r.lines, strings.Split(text, "\n")...)
	r.mu.Unlock()
	r.signal()
	return nil
}

// Sync does nothing: the record is kept in memory only, so the run cannot be resumed.
func (r *run) Sync() error { return nil }

func (r *run) signal() {
	r.mu.Lock()
	close(r.changed)
	r.changed = make(chan struct{})
	r.mu.Unlock()
}

// progress is what a client sees of a run: the record lines from offset on, the state they
// establish, the spans of user code, and the time since the start of the run, which stops at its end.
type progress struct {
	ID         string          `json:"id"`
	Scenario   string          `json:"scenario"`
	Definition json.RawMessage `json:"definition"`
	State      json.RawMessage `json:"state"`
	Offset     int             `json:"offset"`
	Records    []string        `json:"records"`
	Spans      []span          `json:"spans"`
	ElapsedMs  float64         `json:"elapsedMs"`
	Done       bool            `json:"done"`
	Error      string          `json:"error,omitempty"`
}

// progress returns the progress from record offset on, and a channel closed on the next change.
func (r *run) progress(offset int) (progress, <-chan struct{}, error) {
	r.mu.Lock()
	lines := r.lines
	done, endMs, runErr, changed := r.done, r.endMs, r.err, r.changed
	r.mu.Unlock()
	elapsed := r.env.now()
	if done {
		elapsed = endMs
	}
	offset = min(max(offset, 0), len(lines))
	checked, err := suimon.Check(strings.Join(lines, "\n")+"\n", suimon.LoadHeader)
	if err != nil {
		return progress{}, nil, fmt.Errorf("replaying the record: %w", err)
	}
	state, err := json.Marshal(checked.State)
	if err != nil {
		return progress{}, nil, err
	}
	return progress{ID: r.id, Scenario: r.scenario.ID, Definition: r.scenario.Definition, State: state, Offset: offset,
		Records: append([]string{}, lines[offset:]...), Spans: r.env.snapshot(), ElapsedMs: elapsed, Done: done,
		Error: runErr}, changed, nil
}

// wait waits for the run to finish.
func (r *run) wait() { <-r.finished }

func (r *run) result() (*reportJSON, string, bool) {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.report, r.err, r.done
}

// reportJSON is suimon.Report without the state, which progress already carries. Outputs hold the
// JSON text of each value, so that the UI shows it as written: parsing it in JavaScript would round
// large integers.
type reportJSON struct {
	Status    string            `json:"status"`
	Outputs   map[string]string `json:"outputs"`
	Endpoints map[string]string `json:"endpoints"`
	Failures  []failureJSON     `json:"failures"`
}

type failureJSON struct {
	Run       []string `json:"run"`
	Placement string   `json:"placement"`
	Task      *string  `json:"task,omitempty"`
	Cause     string   `json:"cause"`
	Error     string   `json:"error,omitempty"`
}

func newReportJSON(r *suimon.Report) *reportJSON {
	out := &reportJSON{Status: r.Status.String(), Outputs: map[string]string{}, Endpoints: map[string]string{}, Failures: []failureJSON{}}
	for name, value := range r.Outputs {
		out.Outputs[name] = string(value)
	}
	for name, outcome := range r.Endpoints {
		out.Endpoints[name] = outcome.String()
	}
	for _, f := range r.Failures {
		fj := failureJSON{Run: append([]string{}, f.Run...), Placement: f.Placement, Task: f.Task, Cause: f.Cause.String()}
		if f.Err != nil {
			fj.Error = f.Err.Error()
		}
		out.Failures = append(out.Failures, fj)
	}
	return out
}
