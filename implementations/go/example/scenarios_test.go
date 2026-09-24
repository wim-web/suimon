package main

import (
	"context"
	"encoding/json"
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

func runScenario(t *testing.T, id string, input string, unit time.Duration) *run {
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
	select {
	case <-r.finished:
	case <-time.After(10 * time.Second):
		t.Fatal("the run did not finish")
	}
	if r.raw == nil {
		t.Fatalf("no report: %s", r.err)
	}
	return r
}

func failureNames(r *suimon.Report) []string {
	names := []string{}
	for _, f := range r.Failures {
		names = append(names, f.Placement+":"+f.Cause.String())
	}
	sort.Strings(names)
	return names
}

func outputLen(t *testing.T, r *suimon.Report, endpoint string) int {
	t.Helper()
	var list []json.RawMessage
	if err := r.Output(endpoint, &list); err != nil {
		t.Fatal(err)
	}
	return len(list)
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
		outputs  map[string]int
		settled  map[string]string
		check    func(t *testing.T, r *run)
	}{
		{id: "stream", status: suimon.StatusSucceeded, outputs: map[string]int{"collect": 5},
			check: func(t *testing.T, r *run) {
				// Downstream work starts while the generator is still running.
				produce := spansOf(r, "produce")[0]
				if first := spansOf(r, "process")[0]; first.StartMs >= *produce.EndMs {
					t.Errorf("first process started at %.1fms, after produce ended at %.1fms", first.StartMs, *produce.EndMs)
				}
			}},
		{id: "batch", status: suimon.StatusSucceeded, outputs: map[string]int{"collect": 5},
			check: func(t *testing.T, r *run) {
				// Downstream work cannot start before the whole list has been returned.
				all := spansOf(r, "produceAll")[0]
				for _, p := range spansOf(r, "process") {
					if p.StartMs < *all.EndMs {
						t.Errorf("process %s started at %.1fms, before produceAll ended at %.1fms", p.Detail, p.StartMs, *all.EndMs)
					}
				}
			}},
		{id: "branch", status: suimon.StatusSucceeded, outputs: map[string]int{"decide": 1},
			settled: map[string]string{"review": "skipped", "approve": "normal", "decide": "normal"}},
		{id: "branch", input: `{"id":"B-1","amount":5000}`, status: suimon.StatusSucceeded, outputs: map[string]int{"decide": 1},
			settled: map[string]string{"review": "normal", "approve": "skipped"}},
		{id: "merge", status: suimon.StatusSucceeded, outputs: map[string]int{"summary": 3}},
		{id: "limit", status: suimon.StatusSucceeded, outputs: map[string]int{"lookups": 4},
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
		{id: "timeout", status: suimon.StatusFailed, failures: []string{"lookup:timeout"}, outputs: map[string]int{"collect": 2},
			check: timeout},
		// Its timeout does not scale with the unit, and holds at the largest unit.
		{id: "timeout", unit: maxUnit, status: suimon.StatusFailed, failures: []string{"lookup:timeout"},
			outputs: map[string]int{"collect": 2}, check: timeout},
		{id: "stop", status: suimon.StatusFailed, failures: []string{"charge:error"}, outputs: map[string]int{},
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
			for endpoint, n := range c.outputs {
				if got := outputLen(t, report, endpoint); got != n {
					t.Errorf("%s has %d values, want %d", endpoint, got, n)
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
