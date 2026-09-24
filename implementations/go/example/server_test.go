package main

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"testing"
	"testing/fstest"
	"time"
)

func newTestServer(t *testing.T) *httptest.Server {
	t.Helper()
	scenarios, err := loadScenarios()
	if err != nil {
		t.Fatal(err)
	}
	assets := fstest.MapFS{"index.html": {Data: []byte("<!doctype html><title>ui</title>")}}
	srv := httptest.NewServer(newServer(context.Background(), scenarios).handler(assets))
	t.Cleanup(srv.Close)
	return srv
}

func call(t *testing.T, method, url, body string) (int, []byte) {
	t.Helper()
	req, err := http.NewRequest(method, url, strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	if body != "" {
		req.Header.Set("Content-Type", "application/json")
	}
	res, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	defer res.Body.Close()
	data, err := io.ReadAll(res.Body)
	if err != nil {
		t.Fatal(err)
	}
	return res.StatusCode, data
}

func decode[T any](t *testing.T, data []byte) T {
	t.Helper()
	var v T
	if err := json.Unmarshal(data, &v); err != nil {
		t.Fatalf("%v: %s", err, data)
	}
	return v
}

func startTestRun(t *testing.T, srv *httptest.Server, body string) string {
	t.Helper()
	status, data := call(t, "POST", srv.URL+"/api/runs", body)
	if status != http.StatusCreated {
		t.Fatalf("start: %d %s", status, data)
	}
	return decode[map[string]string](t, data)["id"]
}

func pollUntilDone(t *testing.T, srv *httptest.Server, id string) progress {
	t.Helper()
	deadline := time.Now().Add(10 * time.Second)
	for time.Now().Before(deadline) {
		status, data := call(t, "GET", srv.URL+"/api/runs/"+id, "")
		if status != http.StatusOK {
			t.Fatalf("poll: %d %s", status, data)
		}
		if p := decode[progress](t, data); p.Done {
			return p
		}
		time.Sleep(10 * time.Millisecond)
	}
	t.Fatal("the run did not finish")
	return progress{}
}

func TestServerScenarios(t *testing.T) {
	srv := newTestServer(t)
	status, data := call(t, "GET", srv.URL+"/api/scenarios", "")
	if status != http.StatusOK {
		t.Fatalf("%d %s", status, data)
	}
	list := decode[[]struct {
		ID         string         `json:"id"`
		Definition map[string]any `json:"definition"`
		Input      any            `json:"input"`
	}](t, data)
	if len(list) != 7 || list[0].ID != "stream" || list[0].Definition["main"] != "stream" || list[0].Input == nil {
		t.Errorf("unexpected scenarios: %s", data)
	}
	if status, data := call(t, "GET", srv.URL+"/", ""); status != http.StatusOK || !strings.Contains(string(data), "<title>ui</title>") {
		t.Errorf("index: %d %s", status, data)
	}
}

// The runs of the tests have the unit testUnit, "unitMs":10, unless a test says otherwise.

func TestServerRun(t *testing.T) {
	srv := newTestServer(t)
	id := startTestRun(t, srv, `{"scenario":"branch","input":{"id":"B-9","amount":2000},"unitMs":10}`)
	p := pollUntilDone(t, srv, id)
	if p.Scenario != "branch" || p.UnitMs != 10 || p.Offset != 0 || len(p.Records) == 0 || len(p.Spans) != 2 {
		t.Errorf("unexpected progress: %+v", p)
	}
	// The record starts with the header, which holds the definition of the scenario, validated by
	// NewEngine.
	if !strings.HasPrefix(p.Records[0], `{"definition":{"main":"branch",`) || !strings.HasSuffix(p.Records[0], `,"validated":true}`) ||
		!strings.HasPrefix(p.Records[1], `{"seq":1,"op":{"type":"start"`) {
		t.Errorf("first records %s %s", p.Records[0], p.Records[1])
	}
	if state := decode[map[string]any](t, p.State); state["status"] != "succeeded" {
		t.Errorf("state status %v", state["status"])
	}
	for _, s := range p.Spans {
		if *s.EndMs > p.ElapsedMs {
			t.Errorf("%s ended at %.1fms, after the run at %.1fms", s.Function, *s.EndMs, p.ElapsedMs)
		}
	}
	// A finished run keeps its duration as the elapsed time.
	time.Sleep(30 * time.Millisecond)
	status, data := call(t, "GET", srv.URL+"/api/runs/"+id+"?after=2", "")
	tail := decode[progress](t, data)
	if status != http.StatusOK || tail.Offset != 2 || !slices.Equal(tail.Records, p.Records[2:]) {
		t.Errorf("after=2: %d offset %d, %d records of %d", status, tail.Offset, len(tail.Records), len(p.Records))
	}
	if tail.ElapsedMs != p.ElapsedMs {
		t.Errorf("elapsed %.3fms, then %.3fms after the end", p.ElapsedMs, tail.ElapsedMs)
	}
	status, data = call(t, "GET", srv.URL+"/api/runs/"+id+"/report", "")
	if status != http.StatusOK {
		t.Fatalf("report: %d %s", status, data)
	}
	report := decode[reportJSON](t, data)
	var decisions []decision
	if err := json.Unmarshal([]byte(report.Outputs["decide"]), &decisions); err != nil {
		t.Fatal(err)
	}
	if report.Status != "succeeded" || len(decisions) != 1 || decisions[0].By != "review" {
		t.Errorf("report %s", data)
	}
}

func TestServerEvents(t *testing.T) {
	srv := newTestServer(t)
	id := startTestRun(t, srv, `{"scenario":"stream","unitMs":10}`)
	res, err := http.Get(srv.URL + "/api/runs/" + id + "/events")
	if err != nil {
		t.Fatal(err)
	}
	defer res.Body.Close()
	if ct := res.Header.Get("Content-Type"); ct != "text/event-stream" {
		t.Fatalf("content type %s", ct)
	}
	var records []string
	var last progress
	scanner := bufio.NewScanner(res.Body)
	scanner.Buffer(nil, 1<<20)
	events := 0
	for scanner.Scan() {
		data, ok := strings.CutPrefix(scanner.Text(), "data: ")
		if !ok {
			continue
		}
		p := decode[progress](t, []byte(data))
		if p.Offset != len(records) {
			t.Fatalf("event at offset %d after %d records", p.Offset, len(records))
		}
		records = append(records, p.Records...)
		last = p
		events++
	}
	if !last.Done || events < 2 {
		t.Fatalf("%d events, done %v", events, last.Done)
	}
	full := pollUntilDone(t, srv, id)
	if !slices.Equal(records, full.Records) {
		t.Errorf("events carried %d records, the run has %d", len(records), len(full.Records))
	}
}

func TestServerCancelAndErrors(t *testing.T) {
	srv := newTestServer(t)
	id := startTestRun(t, srv, `{"scenario":"timeout","unitMs":10}`)
	if status, _ := call(t, "GET", srv.URL+"/api/runs/"+id+"/report", ""); status != http.StatusConflict {
		t.Errorf("report of a running run: %d", status)
	}
	if status, _ := call(t, "POST", srv.URL+"/api/runs/"+id+"/cancel", ""); status != http.StatusNoContent {
		t.Errorf("cancel: %d", status)
	}
	if p := pollUntilDone(t, srv, id); decode[map[string]any](t, p.State)["status"] != "cancelled" {
		t.Errorf("state after cancel: %s", p.State)
	}
	for _, c := range []struct {
		method, path, body string
		status             int
	}{
		{"POST", "/api/runs", `{"scenario":"nope","unitMs":10}`, http.StatusNotFound},
		{"POST", "/api/runs", `{"scenario":"stream","unitMs":10,"extra":1}`, http.StatusBadRequest},
		{"POST", "/api/runs", `{"scenario":"stream","unitMs":10} {}`, http.StatusBadRequest},
		{"GET", "/api/runs/r999", "", http.StatusNotFound},
		{"GET", "/api/runs/" + id + "?after=x", "", http.StatusBadRequest},
	} {
		if status, data := call(t, c.method, srv.URL+c.path, c.body); status != c.status {
			t.Errorf("%s %s %s: %d %s, want %d", c.method, c.path, c.body, status, data, c.status)
		}
	}
}

func TestServerUnit(t *testing.T) {
	srv := newTestServer(t)
	// The run takes the unit of the request: orderSize waits half a unit, approve one.
	id := startTestRun(t, srv, `{"scenario":"branch","unitMs":60}`)
	p := pollUntilDone(t, srv, id)
	if p.UnitMs != 60 || len(p.Spans) != 2 {
		t.Errorf("unit %dms, %d spans; want 60ms, orderSize and approve", p.UnitMs, len(p.Spans))
	}
	for _, s := range p.Spans {
		if d, want := *s.EndMs-s.StartMs, map[string]float64{"orderSize": 30, "approve": 60}[s.Function]; d < want-0.01 {
			t.Errorf("%s took %.1fms, want at least %.0fms", s.Function, d, want)
		}
	}
	// The bounds are accepted.
	for _, unit := range []int64{10, 1000} {
		id := startTestRun(t, srv, fmt.Sprintf(`{"scenario":"stop","unitMs":%d}`, unit))
		if status, _ := call(t, "POST", srv.URL+"/api/runs/"+id+"/cancel", ""); status != http.StatusNoContent {
			t.Errorf("cancel: %d", status)
		}
		if p := pollUntilDone(t, srv, id); p.UnitMs != unit {
			t.Errorf("unit %dms, want %dms", p.UnitMs, unit)
		}
	}
	// The unit is required: an integer number of milliseconds within the bounds.
	for _, unit := range []string{``, `,"unitMs":null`, `,"unitMs":9`, `,"unitMs":1001`, `,"unitMs":-600`, `,"unitMs":600.5`, `,"unitMs":"600"`} {
		body := `{"scenario":"stream"` + unit + `}`
		if status, data := call(t, "POST", srv.URL+"/api/runs", body); status != http.StatusBadRequest {
			t.Errorf("%s: %d %s, want %d", body, status, data, http.StatusBadRequest)
		}
	}
}
