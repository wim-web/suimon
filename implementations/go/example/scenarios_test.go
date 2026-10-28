package main

import (
	"context"
	"encoding/json"
	"math"
	"slices"
	"sort"
	"testing"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// The deterministic parts of each scenario: status, failures, outputs, settled outcomes, and the
// orderings of user code that follow from the definition (not from how fast the machine is).

// testUnit is the unit of the runs of the tests, unless a case says otherwise.
const testUnit = 10 * time.Millisecond

func scenarioByID(t *testing.T, id string) *scenario {
	t.Helper()
	scenarios, err := loadScenarios()
	if err != nil {
		t.Fatal(err)
	}
	for _, s := range scenarios {
		if s.ID == id {
			return s
		}
	}
	t.Fatalf("no scenario %s", id)
	return nil
}

// startScenario starts a run of the scenario with the input, or with its default input when input is
// empty.
func startScenario(t *testing.T, id string, input string, unit time.Duration) *run {
	t.Helper()
	s := scenarioByID(t, id)
	in := s.Input
	if input != "" {
		in = json.RawMessage(input)
	}
	r, err := startRun(context.Background(), "test", s, in, unit)
	if err != nil {
		t.Fatal(err)
	}
	return r
}

// finish waits for the run to end with a report.
func finish(t *testing.T, r *run) *run {
	t.Helper()
	select {
	case <-r.finished:
	case <-time.After(20 * time.Second):
		t.Fatal("the run did not finish")
	}
	if r.raw == nil {
		t.Fatalf("no report: %s", r.err)
	}
	return r
}

func runScenario(t *testing.T, id string, input string, unit time.Duration) *run {
	t.Helper()
	return finish(t, startScenario(t, id, input, unit))
}

func failureNames(r *suimon.Report) []string {
	names := []string{}
	for _, f := range r.Failures {
		names = append(names, f.Placement+":"+f.Cause.String())
	}
	sort.Strings(names)
	return names
}

// sortedValues ignores completion order while retaining every payload field and duplicate.
func sortedValues(t *testing.T, data []byte) []string {
	t.Helper()
	var list []any
	if err := json.Unmarshal(data, &list); err != nil {
		t.Fatal(err)
	}
	values := make([]string, len(list))
	for i, value := range list {
		encoded, err := json.Marshal(value)
		if err != nil {
			t.Fatal(err)
		}
		values[i] = string(encoded)
	}
	slices.Sort(values)
	return values
}

func settled(r *suimon.Report, placement string) string {
	for _, x := range r.State.Settled {
		if len(x.Run) == 0 && x.Placement == placement {
			return x.Outcome.String()
		}
	}
	return "unsettled"
}

// hasTimeout reports whether a placement or a task of the definition has a timeout.
func hasTimeout(p *suimon.Definition) bool {
	for _, w := range p.Workflows {
		for _, pl := range w.Placements {
			if !pl.Timeout.IsEmpty() {
				return true
			}
			if c, ok := pl.Control.(suimon.ConcurrencyControl); ok {
				for _, task := range c.Spec.Tasks {
					if !task.Timeout.IsEmpty() {
						return true
					}
				}
			}
		}
	}
	return false
}

func spansOf(r *run, function string) []span {
	var out []span
	for _, s := range r.env.snapshot() {
		if s.Function == function {
			out = append(out, s)
		}
	}
	return out
}

func TestScenariosLoad(t *testing.T) {
	scenarios, err := loadScenarios()
	if err != nil {
		t.Fatal(err)
	}
	var ids []string
	for _, s := range scenarios {
		ids = append(ids, s.ID)
		if s.Compare != "" && !slices.ContainsFunc(scenarios, func(o *scenario) bool { return o.ID == s.Compare }) {
			t.Errorf("%s compares with unknown %s", s.ID, s.Compare)
		}
		// The delays scale with the unit, and timeouts do not: TestScenarios runs the scenario with a
		// timeout at the largest unit too.
		p, err := suimon.ParseDefinition(s.Definition)
		if err != nil {
			t.Fatal(err)
		}
		if timed := hasTimeout(p); timed != (s.ID == "timeout") {
			t.Errorf("%s has a timeout: %v", s.ID, timed)
		}
	}
	want := []string{"stream", "batch", "branch", "merge", "limit", "timeout", "stop"}
	if !slices.Equal(ids, want) {
		t.Errorf("scenarios %v, want %v", ids, want)
	}
}

func TestScenarios(t *testing.T) {
	t.Parallel()
	const processed = `[{"index":0,"result":"BRAVO"},{"index":1,"result":"CHARLIE"},{"index":2,"result":"ECHO"},{"index":3,"result":"HOTEL"},{"index":4,"result":"LIMA"}]`
	const found = `[{"index":0,"result":"found alpha"},{"index":2,"result":"found charlie"}]`
	// Each lookup but the stuck one ends in time, after one unit.
	timeout := func(t *testing.T, r *run) {
		for _, s := range spansOf(r, "lookup") {
			if want := map[bool]string{true: "cancelled", false: "ok"}[s.Detail == "stuck"]; s.Outcome != want {
				t.Errorf("lookup %s ended %s, want %s", s.Detail, s.Outcome, want)
			}
			if d, unit := *s.EndMs-s.StartMs, float64(r.env.unit.Milliseconds()); s.Detail != "stuck" && d < unit-0.01 {
				t.Errorf("lookup %s took %.1fms, less than one unit of %.0fms", s.Detail, d, unit)
			}
		}
	}
	cases := []struct {
		id, input string
		// unit is testUnit when zero.
		unit     time.Duration
		status   suimon.Status
		failures []string
		outputs  map[string]string
		settled  map[string]string
		check    func(t *testing.T, r *run)
	}{
		{id: "stream", status: suimon.StatusSucceeded, outputs: map[string]string{"collect": processed}},
		{id: "batch", status: suimon.StatusSucceeded, outputs: map[string]string{"collect": processed}},
		{id: "branch", status: suimon.StatusSucceeded, outputs: map[string]string{"decide": `[{"order":"A-100","by":"approve"}]`},
			settled: map[string]string{"review": "skipped", "approve": "normal", "decide": "normal"}},
		{id: "branch", input: `{"id":"B-1","amount":5000}`, status: suimon.StatusSucceeded, outputs: map[string]string{"decide": `[{"order":"B-1","by":"review"}]`},
			settled: map[string]string{"review": "normal", "approve": "skipped"}},
		{id: "merge", status: suimon.StatusSucceeded, outputs: map[string]string{"summary": `[{"source":"profile","value":"profile of User u-1"},{"source":"orders","value":"orders of User u-1"},{"source":"points","value":"points of User u-1"}]`}},
		{id: "limit", status: suimon.StatusSucceeded, outputs: map[string]string{"lookups": `[{"source":"profile","value":"profile of User u-1"},{"source":"orders","value":"orders of User u-1"},{"source":"points","value":"points of User u-1"},{"source":"coupons","value":"coupons of User u-1"}]`},
			check: func(t *testing.T, r *run) {
				var fetches []span
				for _, s := range r.env.snapshot() {
					if s.Function != "loadUser" {
						fetches = append(fetches, s)
					}
				}
				if len(fetches) != 4 {
					t.Fatalf("%d fetches, want 4", len(fetches))
				}
				for _, a := range fetches {
					running := 0
					for _, b := range fetches {
						if b.StartMs <= a.StartMs && a.StartMs < *b.EndMs {
							running++
						}
					}
					if running > 2 {
						t.Errorf("%d tasks running when %s started, limit 2", running, a.Function)
					}
				}
			}},
		{id: "timeout", status: suimon.StatusFailed, failures: []string{"lookup:timeout"}, outputs: map[string]string{"collect": found},
			check: timeout},
		// Its timeout does not scale with the unit, and holds at the largest unit.
		{id: "timeout", unit: maxUnit, status: suimon.StatusFailed, failures: []string{"lookup:timeout"},
			outputs: map[string]string{"collect": found}, check: timeout},
		{id: "stop", status: suimon.StatusFailed, failures: []string{"charge:error"}, outputs: map[string]string{},
			check: func(t *testing.T, r *run) {
				if s := spansOf(r, "ship")[0]; s.Outcome != "cancelled" {
					t.Errorf("ship ended %s, want cancelled", s.Outcome)
				}
			}},
	}
	for _, c := range cases {
		name, unit := c.id, c.unit
		if unit == 0 {
			unit = testUnit
		} else {
			name += " at " + unit.String()
		}
		t.Run(name, func(t *testing.T) {
			t.Parallel()
			r := runScenario(t, c.id, c.input, unit)
			report := r.raw
			if report.Status != c.status {
				t.Errorf("status %v, want %v", report.Status, c.status)
			}
			if got := failureNames(report); !slices.Equal(got, c.failures) {
				t.Errorf("failures %v, want %v", got, c.failures)
			}
			if len(report.Outputs) != len(c.outputs) {
				t.Errorf("outputs %v, want %v", report.Outputs, c.outputs)
			}
			for endpoint, expected := range c.outputs {
				got, want := sortedValues(t, report.Outputs[endpoint]), sortedValues(t, []byte(expected))
				if !slices.Equal(got, want) {
					t.Errorf("%s values %v, want %v", endpoint, got, want)
				}
			}
			for placement, want := range c.settled {
				if got := settled(report, placement); got != want {
					t.Errorf("%s settled %s, want %s", placement, got, want)
				}
			}
			for _, s := range r.env.snapshot() {
				if s.EndMs == nil {
					t.Errorf("%s %s still running after the report", s.Function, s.Detail)
				}
			}
			// The record the run kept replays to the final state.
			p, _, err := r.progress(0)
			if err != nil {
				t.Fatal(err)
			}
			if want, _ := json.Marshal(report.State); string(p.State) != string(want) {
				t.Errorf("replayed state differs from the report:\n%s\n%s", p.State, want)
			}
			if c.check != nil {
				c.check(t, r)
			}
		})
	}
}

func TestProcessUnits(t *testing.T) {
	// process takes 0.5 to 3 units in steps of 0.1, drawn from the name of the item and nothing else.
	for _, name := range []string{"", "alpha", "bravo", "lima", "stuck", "an item", "名前"} {
		u := processUnits(name)
		if tenths := u * 10; u < 0.5 || u > 3 || math.Abs(tenths-math.Round(tenths)) > 1e-9 {
			t.Errorf("process of %q takes %v units", name, u)
		}
		if again := processUnits(name); again != u {
			t.Errorf("process of %q takes %v units, then %v", name, u, again)
		}
	}
}

func TestProcessUsesRunUnit(t *testing.T) {
	// A unit above the fallback's 250ms detects a process that loses the run
	// context. One short item retains this guarantee without rerunning both flows.
	const unit = 600 * time.Millisecond
	it := item{Index: 7, Name: "lima"}
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()
	ctx = withEnv(ctx, newEnv(unit, nil))
	started := time.Now()
	got, err := process(ctx, it)
	elapsed := time.Since(started)
	if err != nil {
		t.Fatal(err)
	}
	if got != (done{Index: 7, Result: "LIMA"}) {
		t.Fatalf("process returned %+v", got)
	}
	if want := time.Duration(processUnits(it.Name) * float64(unit)); elapsed < want {
		t.Errorf("process took %v with run unit %v, want at least %v", elapsed, unit, want)
	}
}

// The journal establishes the stream/batch ordering without comparing wall-clock
// completion times. TestProcessUsesRunUnit checks process unit propagation;
// TestServerUnit checks the HTTP unit boundary.
func TestStreamAndBatchInvocationOrder(t *testing.T) {
	t.Parallel()
	stream, batch := startScenario(t, "stream", "", testUnit), startScenario(t, "batch", "", testUnit)
	finish(t, stream)
	finish(t, batch)
	ps, pb := processTimes(stream), processTimes(batch)
	if len(ps) != 5 || len(pb) != len(ps) {
		t.Fatalf("process ran for %v in stream and %v in batch", ps, pb)
	}
	for name, duration := range ps {
		want := processUnits(name) * float64(testUnit.Milliseconds())
		if other, ok := pb[name]; !ok || duration < want-0.01 || other < want-0.01 {
			t.Errorf("process %s took %.1fms in stream and %.1fms in batch, want at least %.0fms in both", name, duration, other, want)
		}
	}
	// The engine records this order in one goroutine, independent of when a
	// callback goroutine receives CPU time to record its span.
	yields, returns := 0, 0
	for _, op := range recordedOps(t, stream) {
		if op, ok := op.(suimon.OpInvoke); ok && op.Placement == "process" {
			break
		}
		if _, ok := op.(suimon.OpYielded); ok {
			yields++
		}
	}
	if yields == 0 || yields >= len(ps) {
		t.Errorf("stream invoked process after %d of %d yields, want while produce was still yielding", yields, len(ps))
	}
	for _, op := range recordedOps(t, batch) {
		if op, ok := op.(suimon.OpInvoke); ok && op.Placement == "process" {
			break
		}
		if _, ok := op.(suimon.OpReturned); ok {
			returns++
		}
	}
	if returns == 0 {
		t.Error("batch invoked process before produceAll returned")
	}
}

func TestDefaultInputFavoursStream(t *testing.T) {
	// The schedule the drawn times give, in units: Stream fetches item i at i+1 and processes it right
	// away; Batch fetches all n items, then processes them in parallel.
	var r request
	for _, s := range scenarioList {
		if s.id == "stream" {
			if err := json.Unmarshal([]byte(s.input), &r); err != nil {
				t.Fatal(err)
			}
		}
	}
	if len(r.Names) == 0 {
		t.Fatal("the stream scenario has no default names")
	}
	streamFirst, streamTotal, quickest, slowest := math.Inf(1), 0.0, math.Inf(1), 0.0
	for i, name := range r.Names {
		d := processUnits(name)
		streamFirst, streamTotal = min(streamFirst, float64(i+1)+d), max(streamTotal, float64(i+1)+d)
		quickest, slowest = min(quickest, d), max(slowest, d)
	}
	n := float64(len(r.Names))
	batchFirst, batchTotal := n+quickest, n+slowest
	if streamFirst >= batchFirst || streamTotal+1 > batchTotal {
		t.Errorf("stream: first result at %.1f units, total %.1f; batch: %.1f and %.1f; want stream earlier, by at least a unit in total",
			streamFirst, streamTotal, batchFirst, batchTotal)
	}
}

// recordedOps decodes the operations of r's record, in record order, after the header.
func recordedOps(t *testing.T, r *run) []suimon.Op {
	t.Helper()
	r.mu.Lock()
	lines := append([]string(nil), r.lines...)
	r.mu.Unlock()
	var ops []suimon.Op
	for _, line := range lines[1:] {
		record, err := suimon.DecodeRecord(line)
		if err != nil {
			t.Fatalf("record %q: %v", line, err)
		}
		if !record.Commit {
			ops = append(ops, record.Op)
		}
	}
	return ops
}

// processTimes returns how long process took for each item, by name.
func processTimes(r *run) map[string]float64 {
	out := map[string]float64{}
	for _, s := range spansOf(r, "process") {
		out[s.Detail] = *s.EndMs - s.StartMs
	}
	return out
}
