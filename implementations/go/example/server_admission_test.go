package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

func admissionScenario(t *testing.T, id string, fn func(context.Context) (int, error)) *scenario {
	t.Helper()
	definition := json.RawMessage(`{"main":"main","functions":[{"id":"work","output":{"single":"Int"}}],"workflows":[{"id":"main","placements":[{"name":"work","node":{"type":"function","function":"work"},"policy":"stop"}]}]}`)
	p, err := suimon.ParseDefinition(definition)
	if err != nil {
		t.Fatal(err)
	}
	registry, err := suimon.NewRegistry(suimon.FuncNoInput("work", fn))
	if err != nil {
		t.Fatal(err)
	}
	engine, err := suimon.NewEngine(p, registry)
	if err != nil {
		t.Fatal(err)
	}
	return &scenario{ID: id, Definition: definition, engine: engine}
}

func admissionRequest(h http.Handler, method, path, body, remote string) *httptest.ResponseRecorder {
	r := httptest.NewRequest(method, path, strings.NewReader(body))
	r.RemoteAddr = remote
	// Vary these with the source port: neither may create a new client bucket.
	r.Header.Set("X-Forwarded-For", remote)
	r.Header.Set("Forwarded", "for="+remote)
	w := httptest.NewRecorder()
	h.ServeHTTP(w, r)
	return w
}

func awaitAdmission(t *testing.T, ch <-chan struct{}) {
	t.Helper()
	select {
	case <-ch:
	case <-time.After(5 * time.Second):
		t.Fatal("timed out waiting for a run")
	}
}

func awaitCapacity(t *testing.T, s *server, want int) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(deadline) {
		s.mu.Lock()
		active, clients := s.active, len(s.clients)
		s.mu.Unlock()
		if active == want {
			if want == 0 && clients != 0 {
				t.Fatalf("idle server retains %d client buckets", clients)
			}
			return
		}
		time.Sleep(time.Millisecond)
	}
	t.Fatalf("capacity did not return to %d active runs", want)
}

func TestServerAdmissionConcurrent(t *testing.T) {
	for _, tc := range []struct {
		name   string
		remote func(int) string
		limit  int
	}{
		{"global", func(i int) string { return fmt.Sprintf("192.0.2.%d:1234", i+1) }, maxActiveRuns},
		{"client", func(i int) string { return fmt.Sprintf("192.0.2.1:%d", 1000+i) }, maxClientRuns},
		{"wasm", func(int) string { return "" }, maxClientRuns},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, cancel := context.WithCancel(context.Background())
			sc := admissionScenario(t, "hold", func(ctx context.Context) (int, error) {
				<-ctx.Done()
				return 0, ctx.Err()
			})
			s := newServer(ctx, []*scenario{sc})
			t.Cleanup(func() { cancel(); awaitCapacity(t, s, 0) })
			h := s.handler(nil)
			const callers = 128
			ready := make(chan struct{})
			responses := make(chan *httptest.ResponseRecorder, callers)
			for i := 0; i < callers; i++ {
				go func(i int) {
					<-ready
					responses <- admissionRequest(h, "POST", "/api/runs", `{"scenario":"hold","unitMs":10}`, tc.remote(i))
				}(i)
			}
			close(ready)
			accepted := 0
			for i := 0; i < callers; i++ {
				var w *httptest.ResponseRecorder
				select {
				case w = <-responses:
				case <-time.After(5 * time.Second):
					t.Fatal("overloaded start request did not return")
				}
				switch w.Code {
				case http.StatusCreated:
					accepted++
				case http.StatusTooManyRequests:
					if w.Header().Get("Retry-After") != "1" {
						t.Error("missing retry hint")
					}
				default:
					t.Errorf("unexpected start response: %d %s", w.Code, w.Body)
				}
			}
			if accepted != tc.limit {
				t.Fatalf("accepted %d concurrent starts, want %d", accepted, tc.limit)
			}
			s.mu.Lock()
			defer s.mu.Unlock()
			if s.next != accepted || s.active != accepted || len(s.runs) != accepted || len(s.order) != accepted {
				t.Errorf("rejected starts allocated runs: next=%d active=%d runs=%d order=%d", s.next, s.active, len(s.runs), len(s.order))
			}
		})
	}
}

func TestServerAdmissionRelease(t *testing.T) {
	for _, ending := range []string{"success", "failure", "cancel", "timeout", "shutdown"} {
		t.Run(ending, func(t *testing.T) {
			ctx, cancel := context.WithCancel(context.Background())
			complete, canReturn := make(chan struct{}), make(chan struct{})
			started, cancelled := make(chan struct{}, maxClientRuns), make(chan struct{}, maxClientRuns)
			var once sync.Once
			unblock := func() { once.Do(func() { close(canReturn) }) }
			sc := admissionScenario(t, "hold", func(ctx context.Context) (int, error) {
				started <- struct{}{}
				select {
				case <-complete:
					if ending == "failure" {
						return 0, errors.New("callback failed")
					}
					return 1, nil
				case <-ctx.Done():
					cancelled <- struct{}{}
					<-canReturn
					return 0, ctx.Err()
				}
			})
			s := newServer(ctx, []*scenario{sc})
			if ending == "timeout" {
				s.runTime = time.Second
			}
			t.Cleanup(func() { unblock(); cancel(); awaitCapacity(t, s, 0) })
			h := s.handler(nil)
			start := func() *httptest.ResponseRecorder {
				return admissionRequest(h, "POST", "/api/runs", `{"scenario":"hold","unitMs":10}`, "192.0.2.1:1234")
			}
			var runs []*run
			for i := 0; i < maxClientRuns; i++ {
				w := start()
				if w.Code != http.StatusCreated {
					t.Fatalf("start: %d %s", w.Code, w.Body)
				}
				id := decode[map[string]string](t, w.Body.Bytes())["id"]
				runs = append(runs, s.runs[id])
				awaitAdmission(t, started)
			}
			switch ending {
			case "success", "failure":
				close(complete)
			case "cancel":
				for _, r := range runs {
					w := admissionRequest(h, "POST", "/api/runs/"+r.id+"/cancel", "", "192.0.2.1:1234")
					if w.Code != http.StatusNoContent {
						t.Fatalf("cancel: %d %s", w.Code, w.Body)
					}
				}
			case "shutdown":
				cancel()
			}
			if ending == "cancel" || ending == "timeout" || ending == "shutdown" {
				for range runs {
					awaitAdmission(t, cancelled)
				}
				want := http.StatusTooManyRequests
				if ending == "shutdown" {
					want = http.StatusServiceUnavailable
				}
				if w := start(); w.Code != want {
					t.Fatalf("start while callbacks are still exiting: %d, want %d", w.Code, want)
				}
				unblock()
			}
			for _, r := range runs {
				awaitAdmission(t, r.finished)
				want := map[string]string{"success": "succeeded", "failure": "failed"}[ending]
				if want == "" {
					want = "cancelled"
				}
				if report, err, _ := r.result(); report == nil || report.Status != want {
					t.Fatalf("run ended with report %+v, error %q; want %s", report, err, want)
				}
			}
			awaitCapacity(t, s, 0)
			if ending != "shutdown" {
				if w := start(); w.Code != http.StatusCreated {
					t.Fatalf("capacity was not reusable: %d %s", w.Code, w.Body)
				}
			}
		})
	}
}

func TestServerAdmissionStartError(t *testing.T) {
	sc := admissionScenario(t, "bad", func(context.Context) (int, error) { return 1, nil })
	// Force Engine.Start to fail: this engine's workflow does not accept an input.
	sc.Input = json.RawMessage(`true`)
	s := newServer(context.Background(), []*scenario{sc})
	h := s.handler(nil)
	for i := 0; i < 2*maxActiveRuns; i++ {
		w := admissionRequest(h, "POST", "/api/runs", `{"scenario":"bad","unitMs":10}`, "192.0.2.1:1234")
		if w.Code != http.StatusBadRequest {
			t.Fatalf("start error: %d %s", w.Code, w.Body)
		}
	}
	awaitCapacity(t, s, 0)
	if len(s.runs) != 0 || len(s.order) != 0 {
		t.Fatal("failed starts retained runs")
	}
}

func TestServerAdmissionRetention(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	hold := admissionScenario(t, "hold", func(ctx context.Context) (int, error) {
		<-ctx.Done()
		return 0, ctx.Err()
	})
	quick := admissionScenario(t, "quick", func(context.Context) (int, error) { return 1, nil })
	s := newServer(ctx, []*scenario{hold, quick})
	t.Cleanup(func() { cancel(); awaitCapacity(t, s, 0) })
	h := s.handler(nil)
	for i := 0; i < maxRuns+10; i++ {
		name := "quick"
		if i == 0 {
			name = "hold"
		}
		w := admissionRequest(h, "POST", "/api/runs", fmt.Sprintf(`{"scenario":%q,"unitMs":10}`, name), fmt.Sprintf("192.0.2.%d:1234", i+1))
		if w.Code != http.StatusCreated {
			t.Fatalf("start: %d %s", w.Code, w.Body)
		}
		id := decode[map[string]string](t, w.Body.Bytes())["id"]
		if i > 0 {
			awaitAdmission(t, s.runs[id].finished)
			awaitCapacity(t, s, 1)
		}
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if len(s.runs) != maxRuns || len(s.order) != maxRuns || s.runs["r1"] == nil || s.runs["r2"] != nil || len(s.clients) != 1 {
		t.Fatalf("retention: %d runs, %d ordered, %d clients; active retained=%v, oldest finished evicted=%v",
			len(s.runs), len(s.order), len(s.clients), s.runs["r1"] != nil, s.runs["r2"] == nil)
	}
}

func TestClientIP(t *testing.T) {
	for remote, want := range map[string]string{
		"192.0.2.1:1234": "192.0.2.1", "192.0.2.1:5678": "192.0.2.1",
		"[::ffff:192.0.2.1]:1234": "192.0.2.1", "[2001:0db8::1]:1234": "2001:db8::1",
		"[2001:db8::1]:5678": "2001:db8::1", "": "", "invalid": "",
	} {
		if got := clientIP(remote); got != want {
			t.Errorf("clientIP(%q) = %q, want %q", remote, got, want)
		}
	}
}
