package main

import (
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"mime"
	"net"
	"net/http"
	"os"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

func serveUI(address, directory string) error {
	assets := os.DirFS(directory)
	for _, name := range []string{"index.html", "assets"} {
		if _, err := fs.Stat(assets, name); err != nil {
			return fmt.Errorf("example UI: %w (run pnpm build from the repository root; -ui-dir points to example/ui/dist)", err)
		}
	}
	listener, err := net.Listen("tcp", address)
	if err != nil {
		return err
	}
	fmt.Printf("suimon example UI: http://%s\n", listener.Addr())
	server := &http.Server{Handler: uiHandler(assets), ReadHeaderTimeout: 5 * time.Second}
	return server.Serve(listener)
}

func uiHandler(assets fs.FS) http.Handler {
	return uiHandlerWithConfig(assets, demoConfig{})
}

func uiHandlerWithConfig(assets fs.FS, config demoConfig) http.Handler {
	mux := http.NewServeMux()
	mux.Handle("GET /", http.FileServer(http.FS(assets)))
	mux.HandleFunc("GET /api/run", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Allow", "POST")
		http.Error(w, "use POST to execute a workflow", http.StatusMethodNotAllowed)
	})
	mux.HandleFunc("GET /api/graph", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(createGraph().Graph)
	})
	mux.HandleFunc("GET /api/samples", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(samples())
	})
	mux.HandleFunc("POST /api/run", func(w http.ResponseWriter, r *http.Request) {
		mediaType, _, err := mime.ParseMediaType(r.Header.Get("Content-Type"))
		if err != nil || mediaType != "application/json" {
			http.Error(w, "expected application/json", http.StatusUnsupportedMediaType)
			return
		}
		var request struct {
			Input    *string `json:"input"`
			Scenario string  `json:"scenario"`
			DelayMS  *int    `json:"delay_ms"`
		}
		decoder := json.NewDecoder(http.MaxBytesReader(w, r.Body, 64<<10))
		decoder.DisallowUnknownFields()
		if err := decoder.Decode(&request); err != nil || request.Input == nil {
			http.Error(w, "expected an object with a string input", http.StatusBadRequest)
			return
		}
		if err := decoder.Decode(new(any)); err != io.EOF {
			http.Error(w, "expected one JSON object", http.StatusBadRequest)
			return
		}
		if request.Scenario == "" {
			request.Scenario = "basic"
		}
		runConfig := config
		if request.DelayMS != nil {
			if *request.DelayMS < 10 || *request.DelayMS > 2000 {
				http.Error(w, "delay_ms must be between 10 and 2000", http.StatusBadRequest)
				return
			}
			runConfig.delay = time.Duration(*request.DelayMS) * time.Millisecond
		}
		workflow, err := scenario(request.Scenario, *request.Input, runConfig)
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if r.Header.Get("Accept") == "application/x-ndjson" {
			streamRun(w, r, workflow)
			return
		}
		result, err := workflow.Run(r.Context())
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		w.Header().Set("Cache-Control", "no-store")
		_ = json.NewEncoder(w).Encode(result.Snapshot)
	})
	return mux
}

type runFrame struct {
	Graph     *suimon.Graph                   `json:"graph,omitempty"`
	Offset    int                             `json:"event_offset"`
	Events    suimon.List[suimon.Event]       `json:"events"`
	Values    map[string]json.RawMessage      `json:"values"`
	Outputs   *suimon.List[suimon.ResultPort] `json:"outputs,omitempty"`
	ElapsedMS int64                           `json:"elapsed_ms"`
	Done      bool                            `json:"done"`
	Error     string                          `json:"error,omitempty"`
}

// The cursor belongs to one HTTP response. Graphs and item values are immutable
// during a run, so only the first frame needs the graph and each value is sent
// once. The offset lets the receiver reject missing or repeated event batches.
type runStreamCursor struct {
	started bool
	events  int
	values  map[string]struct{}
}

func (cursor *runStreamCursor) next(result suimon.RunResult, elapsedMS int64, done bool, runErr error) *runFrame {
	if cursor.started && len(result.Snapshot.Events) == cursor.events && !done {
		return nil
	}
	frame := &runFrame{Offset: cursor.events, Events: result.Snapshot.Events[cursor.events:], Values: map[string]json.RawMessage{}, ElapsedMS: elapsedMS, Done: done}
	if !cursor.started {
		frame.Graph = &result.Snapshot.Graph
		cursor.values = map[string]struct{}{}
	}
	for id, value := range result.Snapshot.Values {
		if _, sent := cursor.values[id]; !sent {
			frame.Values[id] = value
			cursor.values[id] = struct{}{}
		}
	}
	if done {
		frame.Outputs = &result.Outputs
	}
	if runErr != nil {
		frame.Error = runErr.Error()
	}
	cursor.started = true
	cursor.events = len(result.Snapshot.Events)
	return frame
}

func streamRun(w http.ResponseWriter, r *http.Request, workflow suimon.Workflow) {
	flusher, ok := w.(http.Flusher)
	if !ok {
		http.Error(w, "streaming unavailable", http.StatusInternalServerError)
		return
	}
	started := time.Now()
	execution, err := workflow.Start(r.Context())
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	defer execution.Stop()
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-store")
	w.Header().Set("X-Accel-Buffering", "no")
	encoder := json.NewEncoder(w)
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()
	cursor := runStreamCursor{}
	for {
		// WaitForChange signals settled-state changes, not every model commit.
		// A small example can poll the committed view to show in-flight values.
		update := execution.Observe()
		result := update.Result()
		done := update.Settled || update.Stopped
		if frame := cursor.next(result, time.Since(started).Milliseconds(), done, update.Err); frame != nil {
			if err := encoder.Encode(frame); err != nil {
				return
			}
			flusher.Flush()
		}
		if done {
			return
		}
		select {
		case <-r.Context().Done():
			return
		case <-ticker.C:
		}
	}
}
