package main

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"testing/fstest"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// Server routing can be tested without requiring a frontend build for Go users.
var testUI = fstest.MapFS{
	"index.html":     {Data: []byte("<!doctype html><div id=\"root\"></div>")},
	"assets/app.js":  {Data: []byte("export {}")},
	"assets/app.css": {Data: []byte("body { margin: 0; }")},
}

func TestUIRun(t *testing.T) {
	handler := uiHandler(testUI)
	for _, input := range []string{"  hello UI  ", "", "  日本語 <script>  "} {
		t.Run(input, func(t *testing.T) {
			body, _ := json.Marshal(map[string]string{"input": input})
			request := httptest.NewRequest(http.MethodPost, "/api/run", strings.NewReader(string(body)))
			request.Header.Set("Content-Type", "application/json")
			response := httptest.NewRecorder()
			handler.ServeHTTP(response, request)
			if response.Code != http.StatusOK {
				t.Fatalf("status %d: %s", response.Code, response.Body)
			}
			var snapshot suimon.Snapshot
			if err := json.Unmarshal(response.Body.Bytes(), &snapshot); err != nil {
				t.Fatal(err)
			}
			state, diagnostic := suimon.Check(snapshot.Graph, snapshot.Events)
			if diagnostic != nil || state.Status != "succeeded" {
				t.Fatalf("invalid run: %v, status %s", diagnostic, state.Status)
			}
			for _, event := range snapshot.Events {
				if event.Op != nil && event.Op.Kind == "complete" {
					instance := state.Instance(event.Op.Auth.Instance)
					if instance.Node != "uppercase" {
						continue
					}
					var got string
					if err := json.Unmarshal(snapshot.Values[event.Op.Outputs[0].Items[0]], &got); err != nil {
						t.Fatal(err)
					}
					if want := strings.ToUpper(strings.TrimSpace(input)); got != want {
						t.Fatalf("got %q, want %q", got, want)
					}
					return
				}
			}
			t.Fatal("missing uppercase completion")
		})
	}
}

func TestUIRejectsInvalidInput(t *testing.T) {
	handler := uiHandler(testUI)
	for _, body := range []string{`{}`, `null`, `{"input":null}`, `{"input":3}`, `{"input":"x","unknown":true}`, `{"input":"x"}{}`, `{"input":"` + strings.Repeat("a", 64<<10) + `"}`} {
		request := httptest.NewRequest(http.MethodPost, "/api/run", strings.NewReader(body))
		request.Header.Set("Content-Type", "application/json")
		response := httptest.NewRecorder()
		handler.ServeHTTP(response, request)
		if response.Code != http.StatusBadRequest {
			t.Fatalf("got %d for invalid input", response.Code)
		}
	}
	request := httptest.NewRequest(http.MethodPost, "/api/run", strings.NewReader(`{"input":"x"}`))
	response := httptest.NewRecorder()
	handler.ServeHTTP(response, request)
	if response.Code != http.StatusUnsupportedMediaType {
		t.Fatalf("missing JSON content type: got %d", response.Code)
	}
}

func TestUIAssets(t *testing.T) {
	handler := uiHandler(testUI)
	for _, path := range []string{"/", "/api/graph", "/api/samples", "/assets/app.js", "/assets/app.css"} {
		response := httptest.NewRecorder()
		handler.ServeHTTP(response, httptest.NewRequest(http.MethodGet, path, nil))
		if response.Code != http.StatusOK || response.Body.Len() == 0 {
			t.Errorf("%s: status %d, length %d", path, response.Code, response.Body.Len())
		}
	}
	response := httptest.NewRecorder()
	handler.ServeHTTP(response, httptest.NewRequest(http.MethodGet, "/api/run", nil))
	if response.Code != http.StatusMethodNotAllowed {
		t.Errorf("GET must not execute workflow: status %d", response.Code)
	}
}

func TestUILiveRunFlushesBeforeCompletionAndCancels(t *testing.T) {
	started := make(chan struct{})
	cancelled := make(chan struct{}, 1)
	server := httptest.NewServer(uiHandlerWithConfig(testUI, demoConfig{sleep: func(ctx context.Context, _ time.Duration) error {
		close(started)
		<-ctx.Done()
		cancelled <- struct{}{}
		return ctx.Err()
	}}))
	defer server.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	request, _ := http.NewRequestWithContext(ctx, http.MethodPost, server.URL+"/api/run", strings.NewReader(`{"scenario":"streaming","input":"alpha"}`))
	request.Header.Set("Content-Type", "application/json")
	request.Header.Set("Accept", "application/x-ndjson")
	response, err := server.Client().Do(request)
	if err != nil {
		t.Fatal(err)
	}
	defer response.Body.Close()
	var frame runFrame
	if err := json.NewDecoder(response.Body).Decode(&frame); err != nil {
		t.Fatal(err)
	}
	if frame.Done || response.Header.Get("Content-Type") != "application/x-ndjson" {
		t.Fatal("did not receive an in-flight frame")
	}
	// Wait until the handler enters its simulated I/O, then disconnect.
	select {
	case <-started:
	case <-ctx.Done():
		t.Fatal(ctx.Err())
	}
	cancel()
	_ = response.Body.Close()
	select {
	case <-cancelled:
	case <-time.After(2 * time.Second):
		t.Fatal("disconnect did not cancel the sleeping handler")
	}
}

func TestUILiveRunFinalFrame(t *testing.T) {
	handler := uiHandlerWithConfig(testUI, demoConfig{sleep: func(context.Context, time.Duration) error { return nil }})
	request := httptest.NewRequest(http.MethodPost, "/api/run", strings.NewReader(`{"scenario":"streaming","input":"alpha bravo #skip charlie delta echo"}`))
	request.Header.Set("Content-Type", "application/json")
	request.Header.Set("Accept", "application/x-ndjson")
	response := httptest.NewRecorder()
	handler.ServeHTTP(response, request)
	if response.Code != http.StatusOK || !response.Flushed {
		t.Fatalf("response was not streamed: %d", response.Code)
	}
	decoder := json.NewDecoder(response.Body)
	var last runFrame
	var snapshot suimon.Snapshot
	snapshot.Values = map[string]json.RawMessage{}
	count := 0
	for {
		var frame runFrame
		if err := decoder.Decode(&frame); err == io.EOF {
			break
		} else if err != nil {
			t.Fatal(err)
		}
		if frame.ElapsedMS < last.ElapsedMS || last.Done {
			t.Fatal("invalid progress order")
		}
		if frame.Offset != len(snapshot.Events) {
			t.Fatalf("event gap or duplicate: offset %d, received %d", frame.Offset, len(snapshot.Events))
		}
		if count == 0 {
			if frame.Graph == nil {
				t.Fatal("first frame has no graph")
			}
			snapshot.Graph = *frame.Graph
		} else if frame.Graph != nil {
			t.Fatal("graph was retransmitted")
		}
		if !frame.Done && frame.Outputs != nil {
			t.Fatal("outputs must only be sent at completion")
		}
		snapshot.Events = append(snapshot.Events, frame.Events...)
		for id, value := range frame.Values {
			if _, exists := snapshot.Values[id]; exists {
				t.Fatalf("value %s was retransmitted", id)
			}
			snapshot.Values[id] = value
		}
		if _, diagnostic := suimon.Check(snapshot.Graph, snapshot.Events); diagnostic != nil {
			t.Fatalf("frame contains an uncommitted or invalid history: %v", diagnostic)
		}
		last = frame
		count++
	}
	if count < 2 || !last.Done || last.Error != "" || last.Outputs == nil {
		t.Fatalf("missing final frame: %#v", last)
	}
	state, diagnostic := suimon.Check(snapshot.Graph, snapshot.Events)
	if diagnostic != nil {
		t.Fatal(diagnostic)
	}
	assertStreamOutput(t, suimon.RunResult{State: state, Snapshot: snapshot, Outputs: *last.Outputs})
}

func TestRunStreamCursorSendsEachEventAndValueOnce(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	node := leaf("source")
	node.Outputs = suimon.List[suimon.Port]{{Name: "items", Kind: "stream"}}
	ready, finish := make(chan *suimon.Task, 1), make(chan struct{})
	workflow := suimon.Workflow{
		Graph:  suimon.Graph{Nodes: suimon.List[suimon.Node]{node}, Entries: suimon.List[suimon.PortRef]{{Node: "source", Port: "in"}}, Exits: suimon.List[suimon.PortRef]{{Node: "source", Port: "items"}}},
		Inputs: []suimon.ValueInput{{Entry: suimon.PortRef{Node: "source", Port: "in"}, Items: []suimon.InputItem{{ID: "input", Value: "seed"}}}},
		Bindings: []suimon.Binding{{Path: suimon.Path{"source"}, Leaf: func(ctx context.Context, task *suimon.Task) (suimon.Values, error) {
			ready <- task
			select {
			case <-finish:
				return suimon.Values{}, nil
			case <-ctx.Done():
				return nil, ctx.Err()
			}
		}}},
		Options: suimon.RunOptions{Now: func() suimon.Nat { return suimon.N(1000) }},
	}
	execution, err := workflow.Start(ctx)
	if err != nil {
		t.Fatal(err)
	}
	defer execution.Stop()
	var task *suimon.Task
	select {
	case task = <-ready:
	case <-ctx.Done():
		t.Fatal(ctx.Err())
	}
	cursor := runStreamCursor{}
	initial := execution.Observe()
	first, err := cursor.next(initial, 0)
	if err != nil || first == nil || first.Graph == nil || first.Offset != 0 || first.Done {
		t.Fatalf("invalid initial frame: %#v %v", first, err)
	}
	const count, valueSize = 80, 1024
	encodedBytes := 0
	received := first.Offset + len(first.Events)
	for i := range count {
		key := fmt.Sprint(i)
		if err := task.Emit("items", key, strings.Repeat("x", valueSize)); err != nil {
			t.Fatal(err)
		}
		update := execution.Observe()
		frame, err := cursor.next(update, int64(i+1))
		id := suimon.StreamItemID(nil, "source", "items", key)
		if err != nil || frame == nil || frame.Offset != received || len(frame.Events) == 0 || len(frame.Values) != 1 || frame.Values[id] == nil || frame.Outputs != nil || frame.Graph != nil {
			t.Fatalf("frame %d retransmits history or misses new data: %#v %v", i, frame, err)
		}
		received += len(frame.Events)
		encoded, err := json.Marshal(frame)
		if err != nil {
			t.Fatal(err)
		}
		encodedBytes += len(encoded)
		if duplicate, err := cursor.next(update, int64(i+1)); err != nil || duplicate != nil {
			t.Fatal("unchanged snapshot produced another frame", err)
		}
	}
	if encodedBytes > count*(valueSize+2048) {
		t.Fatalf("transport grew beyond one copy of each payload plus metadata: %d bytes", encodedBytes)
	}
	close(finish)
	if _, err := execution.Wait(ctx); err != nil {
		t.Fatal(err)
	}
	completed := execution.Observe()
	// A status change can follow the last data commit without new events.
	pending := completed
	pending.Settled, pending.Stopped = false, false
	if _, err := cursor.next(pending, count+1); err != nil {
		t.Fatal(err)
	}
	final, err := cursor.next(completed, count+2)
	if err != nil || final == nil || !final.Done || final.Offset != completed.EventCount() || len(final.Events) != 0 || len(final.Values) != 0 || final.Graph != nil || final.Outputs == nil || len((*final.Outputs)[0].Items) != count {
		t.Fatalf("invalid completion frame: %#v %v", final, err)
	}
	// A new HTTP response starts a fresh cursor.
	restarted, err := (&runStreamCursor{}).next(completed, 0)
	if err != nil || restarted.Graph == nil || restarted.Offset != 0 || len(restarted.Events) != completed.EventCount() || len(restarted.Values) != count+1 {
		t.Fatal("new stream inherited the previous stream cursor", err)
	}
}
