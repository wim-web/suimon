package suimon

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"iter"
	"runtime"
	"slices"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// Runtime scenarios: the definitions of Test/definitions and testdata run with the Go functions of
// fixtures_test.go. Every run writes a journal, which Check must replay to the final state of the
// report; TestConformanceRuntime also has Lean check it.

// run is one run of a scenario: its bindings, what to do while it runs, and how to check it.
type run struct {
	bindings []Binding
	// during runs after the start; cancel cancels the context of the execution.
	during func(t *testing.T, x *WorkflowExecution, cancel context.CancelFunc)
	check  func(t *testing.T, r *Report, journal string)
}

type scenario struct {
	name       string
	definition string
	// adjust changes the loaded definition, for example its runtime settings.
	adjust  func(p *Definition)
	input   any
	prepare func(t *testing.T, j *memJournal) run
	// deterministic scenarios give the same report in every run and after every recovery in which
	// no call was lost; recovery tests use them.
	deterministic bool
}

// scaleTimeouts sets every timeout of p to ms, so that fast functions never time out on a busy
// machine while the timers still run.
func scaleTimeouts(ms uint64) func(p *Definition) {
	scale := func(t *Timeout) {
		if t.CallMs != nil {
			t.CallMs = ptr(ms)
		}
		if t.ElementMs != nil {
			t.ElementMs = ptr(ms)
		}
	}
	return func(p *Definition) {
		for i := range p.Workflows {
			for j := range p.Workflows[i].Placements {
				pl := &p.Workflows[i].Placements[j]
				scale(&pl.Timeout)
				if c, ok := pl.Control.(ConcurrencyControl); ok {
					c.Spec.Tasks = slices.Clone(c.Spec.Tasks)
					for k := range c.Spec.Tasks {
						scale(&c.Spec.Tasks[k].Timeout)
					}
					pl.Control = c
				}
			}
		}
	}
}

func adjustAll(fs ...func(p *Definition)) func(p *Definition) {
	return func(p *Definition) {
		for _, f := range fs {
			f(p)
		}
	}
}

func setPolicy(workflow, placement string, policy Policy) func(p *Definition) {
	return func(p *Definition) {
		mapWorkflow(p, workflow, mapPlacement(placement, func(pl *Placement) { pl.Policy = policy }))
	}
}

func setTimeout(workflow, placement string, timeout Timeout) func(p *Definition) {
	return func(p *Definition) {
		mapWorkflow(p, workflow, mapPlacement(placement, func(pl *Placement) { pl.Timeout = timeout }))
	}
}

// Checks of reports.

func expectStatusOf(t *testing.T, r *Report, want Status) {
	t.Helper()
	if r.Status != want {
		t.Errorf("status %v, want %v; failures %v", r.Status, want, failureNames(r))
	}
}

// failureNames are the failures as placement[/task]:cause, sorted.
func failureNames(r *Report) []string {
	var names []string
	for _, f := range r.Failures {
		name := f.Placement
		if f.Task != nil {
			name += "/" + *f.Task
		}
		names = append(names, name+":"+f.Cause.String())
	}
	sort.Strings(names)
	return names
}

func expectFailures(t *testing.T, r *Report, want ...string) {
	t.Helper()
	sort.Strings(want)
	if got := failureNames(r); !slices.Equal(got, want) {
		t.Errorf("failures %q, want %q", got, want)
	}
}

func expectOutput(t *testing.T, r *Report, name string, want any) {
	t.Helper()
	var got any
	if err := r.Output(name, &got); err != nil {
		t.Errorf("output %s: %v", name, err)
		return
	}
	wantJSON, _ := json.Marshal(want)
	gotJSON, _ := json.Marshal(got)
	if string(gotJSON) != string(wantJSON) {
		t.Errorf("output %s = %s, want %s", name, gotJSON, wantJSON)
	}
}

// expectOutputSet compares a list output with want regardless of order: lists have no order
// (§5.4). Elements are compared as JSON.
func expectOutputSet(t *testing.T, r *Report, name string, want ...any) {
	t.Helper()
	got, err := outputSet(r, name)
	if err != nil {
		t.Errorf("output %s: %v", name, err)
		return
	}
	wantSet := []string{}
	for _, w := range want {
		data, _ := json.Marshal(w)
		var v any
		json.Unmarshal(data, &v)
		data, _ = json.Marshal(normalizeLists(v))
		wantSet = append(wantSet, string(data))
	}
	sort.Strings(wantSet)
	if !slices.Equal(got, wantSet) {
		t.Errorf("output %s = %q, want %q", name, got, wantSet)
	}
}

func outputSet(r *Report, name string) ([]string, error) {
	var items []json.RawMessage
	if err := r.Output(name, &items); err != nil {
		return nil, err
	}
	set := []string{}
	for _, item := range items {
		var v any
		if err := json.Unmarshal(item, &v); err != nil {
			return nil, err
		}
		data, _ := json.Marshal(normalizeLists(v))
		set = append(set, string(data))
	}
	sort.Strings(set)
	return set, nil
}

// normalizeLists sorts nested lists by their JSON, so that lists of lists compare as sets.
func normalizeLists(v any) any {
	list, ok := v.([]any)
	if !ok {
		return v
	}
	out := make([]any, len(list))
	for i, item := range list {
		out[i] = normalizeLists(item)
	}
	sort.Slice(out, func(i, j int) bool {
		a, _ := json.Marshal(out[i])
		b, _ := json.Marshal(out[j])
		return string(a) < string(b)
	})
	return out
}

func expectEndpoint(t *testing.T, r *Report, name string, want Outcome) {
	t.Helper()
	if got, ok := r.Endpoints[name]; !ok || got != want {
		t.Errorf("endpoint %s: %v (settled %v), want %v", name, got, ok, want)
	}
}

func expectNoOutput(t *testing.T, r *Report, name string) {
	t.Helper()
	if data, ok := r.Outputs[name]; ok {
		t.Errorf("output %s = %s, want none", name, data)
	}
}

// resultPayloads are the payloads of the results of a placement in the root run of a journal, which
// replays against the definition of its header.
func resultPayloads(t *testing.T, journal, placement string) []string {
	t.Helper()
	c, err := Check(journal, loadHeader)
	if err != nil {
		t.Fatal(err)
	}
	var payloads []string
	for _, r := range c.State.resultsOf(nil, placement) {
		for _, v := range c.Values {
			if v.Value == r.Value {
				payloads = append(payloads, v.Payload)
			}
		}
	}
	sort.Strings(payloads)
	return payloads
}

// callsWith are the calls of the final state whose target is fn.
func callsWith(r *Report, fn string) []Call {
	var calls []Call
	for _, c := range r.State.Calls {
		if c.Target.ID == fn {
			calls = append(calls, c)
		}
	}
	return calls
}

func opIndex(journal, fragment string) int { return strings.Index(journal, fragment) }

// recordLines are the lines of the records of a journal, after its header, or of a part of a journal
// after the header.
func recordLines(journal string) []string {
	lines := strings.Split(strings.TrimSuffix(journal, "\n"), "\n")
	if strings.HasPrefix(journal, `{"definition":`) {
		lines = lines[1:]
	}
	return lines
}

// opsOf are the operations of a journal, in order.
func opsOf(t *testing.T, journal string) []Op {
	t.Helper()
	var ops []Op
	for _, line := range recordLines(journal) {
		r, err := DecodeRecord(line)
		if err != nil {
			t.Fatal(err)
		}
		if !r.Commit {
			ops = append(ops, r.Op)
		}
	}
	return ops
}

// firstOp is the index of the first operation that matches, or -1.
func firstOp(ops []Op, match func(Op) bool) int { return slices.IndexFunc(ops, match) }

// verifyJournal checks a journal against the report of its run: it records p, it replays completely
// to the final state, and it is what the engine would write for its operations.
func verifyJournal(t *testing.T, p *Definition, journal string, r *Report) {
	t.Helper()
	if !strings.HasPrefix(journal, EncodeHeader(p)+"\n") {
		t.Errorf("the journal does not start with the header of its definition")
	}
	c, err := Check(journal, sameDefinition(p))
	if err != nil {
		t.Fatalf("the journal does not replay: %v", err)
	}
	if c.Uncommitted || c.Length != len(journal) {
		t.Errorf("the journal has an uncommitted tail")
	}
	if !c.State.Equal(r.State) {
		t.Errorf("the journal replays to another state than the report's")
	}
	if !r.State.Status.Terminal() {
		t.Errorf("the final state is %v", r.State.Status)
	}
	for _, v := range c.State.Values() {
		if !hasPayload(c.Values, v) {
			t.Errorf("value %s has no payload", v)
		}
	}
	for _, v := range c.Values {
		if !json.Valid([]byte(v.Payload)) {
			t.Errorf("payload of %s is not JSON: %q", v.Value, v.Payload)
		}
	}
}

// wait waits for an execution, and fails the test instead of hanging.
func wait(t *testing.T, x *WorkflowExecution) (*Report, error) {
	t.Helper()
	select {
	case <-x.Done():
	case <-time.After(60 * time.Second):
		t.Fatal("the execution did not end")
	}
	return x.Wait()
}

// runOnce runs a scenario and returns its definition, journal and report after the checks.
func runOnce(t *testing.T, sc scenario) (*Definition, string, *Report) {
	t.Helper()
	p := load(t, sc.definition)
	if sc.adjust != nil {
		sc.adjust(p)
	}
	j := &memJournal{}
	rn := sc.prepare(t, j)
	e, err := NewEngine(p, mustRegistry(t, rn.bindings...))
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	x, err := e.Start(ctx, sc.input, WithJournal(j))
	if err != nil {
		t.Fatal(err)
	}
	if rn.during != nil {
		rn.during(t, x, cancel)
	}
	r, err := wait(t, x)
	if err != nil {
		t.Fatalf("Wait: %v", err)
	}
	verifyJournal(t, p, j.text(), r)
	if rn.check != nil {
		rn.check(t, r, j.text())
	}
	return p, j.text(), r
}

func scenarios() []scenario {
	return []scenario{
		{
			name: "merge", definition: "merge", deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: mergeBindings(mergeKnobs{journal: j}), check: func(t *testing.T, r *Report, _ string) {
					expectStatusOf(t, r, StatusSucceeded)
					expectFailures(t, r)
					// The list's elements are in the order of their identities, which the origin of
					// each value decides, so the page is the same in every run.
					expectOutput(t, r, "page", "sales=120,stock=7")
					expectOutput(t, r, "archive", "archived 120")
					expectOutput(t, r, "notify", "ack")
					for _, name := range []string{"page", "archive", "notify"} {
						expectEndpoint(t, r, name, OutcomeNormal)
					}
				}}
			},
		},
		{
			name: "merge continue failure", definition: "merge", deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: mergeBindings(mergeKnobs{failSales: true}), check: func(t *testing.T, r *Report, _ string) {
					expectStatusOf(t, r, StatusFailed)
					expectFailures(t, r, "sales:error")
					if !errors.Is(r.Failures[0].Err, errBoom) {
						t.Errorf("the failure keeps the error of the function: %v", r.Failures[0].Err)
					}
					// Merge takes the inputs that came; the other targets of sales are not run (§9.2).
					expectOutput(t, r, "page", "stock=7")
					expectEndpoint(t, r, "archive", OutcomeUpstreamFailed)
					expectEndpoint(t, r, "notify", OutcomeUpstreamFailed)
					expectNoOutput(t, r, "archive")
				}}
			},
		},
		{
			name: "merge transform panic", definition: "merge", deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: mergeBindings(mergeKnobs{panicSalesWidget: true}), check: func(t *testing.T, r *Report, _ string) {
					// A failed transform is a failure of its target, under the target's policy (§4.2).
					expectStatusOf(t, r, StatusFailed)
					expectFailures(t, r, "widgets:transform")
					var pe *PanicError
					if !errors.As(r.Failures[0].Err, &pe) {
						t.Errorf("transform panic: %v", r.Failures[0].Err)
					}
					expectOutput(t, r, "page", "stock=7")
					expectOutput(t, r, "archive", "archived 120")
				}}
			},
		},
		{
			name: "merge stop", definition: "merge", adjust: setPolicy("dashboard", "sales", PolicyStop),
			prepare: func(t *testing.T, j *memJournal) run {
				early := &atomic.Int32{}
				return run{bindings: mergeBindings(mergeKnobs{failSales: true, blockStock: true, journal: j, early: early}),
					check: func(t *testing.T, r *Report, journal string) {
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "sales:error")
						if early.Load() != 0 {
							t.Error("a call was cancelled before the stop was durable")
						}
						// The stop cancels the running stock call; it ends as cancelled, not failed.
						stock := callsWith(r, "fetchStock")
						if len(stock) != 1 || stock[0].Status != CallCancelled {
							t.Errorf("stock call: %+v", stock)
						}
						if opIndex(journal, `"type":"terminated"`) < 0 {
							t.Error("the cancelled call is recorded as terminated")
						}
						if len(r.Outputs) != 0 {
							t.Errorf("outputs after the stop: %v", r.Outputs)
						}
					}}
			},
		},
		{
			name: "merge timeout", definition: "merge", adjust: setTimeout("dashboard", "stock", Timeout{CallMs: ptr[uint64](40)}),
			prepare: func(t *testing.T, j *memJournal) run {
				early := &atomic.Int32{}
				return run{bindings: mergeBindings(mergeKnobs{blockStock: true, journal: j, early: early}), check: func(t *testing.T, r *Report, journal string) {
					expectStatusOf(t, r, StatusFailed)
					expectFailures(t, r, "stock:timeout")
					if early.Load() != 0 {
						t.Error("a call was cancelled before its timeout was durable")
					}
					if !errors.Is(r.Failures[0].Err, ErrTimeout) {
						t.Errorf("timeout error: %v", r.Failures[0].Err)
					}
					expectOutput(t, r, "page", "sales=120")
					// The timed out call is cancelled, and terminated when its user code returned.
					if i, k := opIndex(journal, `"type":"timedOut"`), opIndex(journal, `"type":"terminated"`); i < 0 || k < i {
						t.Errorf("timedOut at %d, terminated at %d", i, k)
					}
				}}
			},
		},
		{
			name: "users", definition: "users", input: tenant{Name: "acme", Users: 3}, deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: usersBindings(usersKnobs{}), check: func(t *testing.T, r *Report, _ string) {
					expectStatusOf(t, r, StatusSucceeded)
					var lists []any
					for id := 1; id <= 3; id++ {
						lists = append(lists, []any{
							summary{User: id, Kind: "orders", Text: fmt.Sprint(id * 10)},
							summary{User: id, Kind: "profile", Text: fmt.Sprintf("profile of raw-%d", id)}})
					}
					expectOutputSet(t, r, "all", lists...)
				}}
			},
		},
		{
			name: "users task failure", definition: "users", input: tenant{Name: "acme", Users: 3}, deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: usersBindings(usersKnobs{failOrdersOf: 2}), check: func(t *testing.T, r *Report, _ string) {
					expectStatusOf(t, r, StatusFailed)
					expectFailures(t, r, "perUser/orders:error")
					got, err := outputSet(r, "all")
					if err != nil || len(got) != 3 {
						t.Fatalf("all: %q %v", got, err)
					}
					for _, list := range got {
						if strings.Contains(list, `"user":2`) && strings.Contains(list, "orders") {
							t.Errorf("the list of user 2 keeps its profile only: %s", list)
						}
					}
				}}
			},
		},
		{
			name: "users transform failures", definition: "users", input: tenant{Name: "acme", Users: 3}, deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: usersBindings(usersKnobs{failUserIDOf: 2, failOrdersSummaryOf: 3}),
					check: func(t *testing.T, r *Report, _ string) {
						// The input transforms of both tasks fail for user 2, so its list is empty; the
						// output transform of the orders of user 3 fails, so its list keeps the profile
						// (§4.2, §8.3). Each failure is recorded under the task's policy.
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "perUser/profile:transform", "perUser/orders:transform", "perUser/orders:transform")
						expectOutputSet(t, r, "all", []any{},
							[]any{summary{User: 1, Kind: "orders", Text: "10"}, summary{User: 1, Kind: "profile", Text: "profile of raw-1"}},
							[]any{summary{User: 3, Kind: "profile", Text: "profile of raw-3"}})
					}}
			},
		},
		{
			name: "users sub-workflow failure", definition: "users", input: tenant{Name: "acme", Users: 2}, deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: usersBindings(usersKnobs{failProfileOf: 1}),
					check: func(t *testing.T, r *Report, _ string) {
						// The failure is recorded in the run of the sub-workflow call; the call itself ends
						// without a value (§4.5), so the list of user 1 keeps its orders only.
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "fetch:error")
						if f := r.Failures[0]; len(f.Run) != 1 || f.Task != nil {
							t.Errorf("the failure is not in the sub-workflow run: %+v", f.Failure)
						}
						expectOutputSet(t, r, "all",
							[]any{summary{User: 1, Kind: "orders", Text: "10"}},
							[]any{summary{User: 2, Kind: "orders", Text: "20"}, summary{User: 2, Kind: "profile", Text: "profile of raw-2"}})
					}}
			},
		},
		{
			name: "users stop", definition: "users", input: tenant{Name: "acme", Users: 5},
			prepare: func(t *testing.T, j *memJournal) run {
				s := newSignal()
				return run{bindings: usersBindings(usersKnobs{failAfter: 2, blockOrders: true, signal: s}),
					check: func(t *testing.T, r *Report, _ string) {
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "fetchAllUsers:error")
						// The two users accepted before the failure stay; their running calls are cancelled.
						if n := len(r.State.resultsOf(nil, "fetchAllUsers")); n != 2 {
							t.Errorf("%d users accepted, want 2", n)
						}
						for _, c := range callsWith(r, "fetchOrders") {
							if c.Status != CallCancelled {
								t.Errorf("orders call %s is %v", c.ID, c.Status)
							}
						}
						expectNoOutput(t, r, "all")
					}}
			},
		},
		{
			name: "users cancel", definition: "users", input: tenant{Name: "acme", Users: 3},
			prepare: func(t *testing.T, j *memJournal) run {
				s := newSignal()
				return run{bindings: usersBindings(usersKnobs{blockOrders: true, signal: s}),
					during: func(t *testing.T, x *WorkflowExecution, _ context.CancelFunc) {
						if err := s.await("orders", 3); err != nil {
							t.Error(err)
						}
						x.Cancel()
						x.Cancel()
					},
					check: func(t *testing.T, r *Report, journal string) {
						expectStatusOf(t, r, StatusCancelled)
						expectFailures(t, r)
						if !r.State.Cancelled || strings.Count(journal, `"type":"cancel"`) != 1 {
							t.Error("the cancellation is recorded once")
						}
						for _, c := range r.State.Calls {
							if c.Target.ID == "fetchOrders" && c.Status != CallCancelled {
								t.Errorf("orders call %s is %v", c.ID, c.Status)
							}
						}
						if ops := opsOf(t, journal); ops[len(ops)-1] != (OpConclude{}) {
							t.Errorf("the journal ends with %s, not the conclusion", EncodeOp(ops[len(ops)-1]))
						}
					}}
			},
		},
		{
			name: "users context cancel", definition: "users", input: tenant{Name: "acme", Users: 2},
			prepare: func(t *testing.T, j *memJournal) run {
				s := newSignal()
				return run{bindings: usersBindings(usersKnobs{blockOrders: true, signal: s}),
					during: func(t *testing.T, x *WorkflowExecution, cancel context.CancelFunc) {
						if err := s.await("orders", 2); err != nil {
							t.Error(err)
						}
						cancel()
					},
					check: func(t *testing.T, r *Report, _ string) {
						expectStatusOf(t, r, StatusCancelled)
						expectFailures(t, r)
					}}
			},
		},
		{
			name: "branch", definition: "branch", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: branchBindings(branchKnobs{orders: orders(true, false, true), failAfter: -1, blockAfter: -1,
					journal: j}),
					check: func(t *testing.T, r *Report, _ string) {
						expectStatusOf(t, r, StatusSucceeded)
						expectOutputSet(t, r, "receipts", "receipt-1", "receipt-3")
					}}
			},
		},
		{
			name: "branch skipped", definition: "branch", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: branchBindings(branchKnobs{orders: orders(false, false, false), failAfter: -1, blockAfter: -1}),
					check: func(t *testing.T, r *Report, _ string) {
						// Every order went to the other arm: the arm and its waitStream are skipped (§7.3).
						expectStatusOf(t, r, StatusSkipped)
						expectEndpoint(t, r, "receipts", OutcomeSkipped)
						expectNoOutput(t, r, "receipts")
					}}
			},
		},
		{
			name: "branch empty stream", definition: "branch", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: branchBindings(branchKnobs{failAfter: -1, blockAfter: -1}),
					check: func(t *testing.T, r *Report, _ string) {
						// An empty stream is not a non-selection: the list is empty (§4.1.1, §7.3).
						expectStatusOf(t, r, StatusSucceeded)
						expectOutput(t, r, "receipts", []any{})
					}}
			},
		},
		{
			name: "branch judge failure", definition: "branch", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: branchBindings(branchKnobs{orders: orders(true, true, true), failAfter: -1, blockAfter: -1,
					failJudgeOf: 2}),
					check: func(t *testing.T, r *Report, _ string) {
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "paid:error")
						expectOutputSet(t, r, "receipts", "receipt-1", "receipt-3")
					}}
			},
		},
		{
			name: "branch unknown arm", definition: "branch", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: branchBindings(branchKnobs{orders: orders(true, true), failAfter: -1, blockAfter: -1,
					unknownArmOf: 1}),
					check: func(t *testing.T, r *Report, _ string) {
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "paid:error")
						if err := r.Failures[0].Err; err == nil || !strings.Contains(err.Error(), "refunded") {
							t.Errorf("unknown arm: %v", err)
						}
						expectOutputSet(t, r, "receipts", "receipt-2")
					}}
			},
		},
		{
			name: "branch generator failure", definition: "branch",
			adjust:        adjustAll(scaleTimeouts(60000), setPolicy("shipping", "list", PolicyContinue)),
			deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: branchBindings(branchKnobs{orders: orders(true, true, true, true), failAfter: 2, blockAfter: -1}),
					check: func(t *testing.T, r *Report, _ string) {
						// The elements accepted before the failure stay (§4.1.1).
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "list:error")
						expectOutputSet(t, r, "receipts", "receipt-1", "receipt-2")
					}}
			},
		},
		{
			name: "branch element timeout", definition: "branch",
			adjust: adjustAll(setPolicy("shipping", "list", PolicyContinue),
				// Long enough that the elements before the blocked one never time out on a busy machine.
				setTimeout("shipping", "list", Timeout{CallMs: ptr[uint64](60000), ElementMs: ptr[uint64](250)}),
				setTimeout("shipping", "paid", Timeout{CallMs: ptr[uint64](60000)})),
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: branchBindings(branchKnobs{orders: orders(true, true, true), failAfter: -1, blockAfter: 2}),
					check: func(t *testing.T, r *Report, journal string) {
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "list:timeout")
						expectOutputSet(t, r, "receipts", "receipt-1", "receipt-2")
						if !strings.Contains(journal, `"type":"timedOut","call":`) || !strings.Contains(journal, `"element":true`) {
							t.Error("an element timeout is recorded")
						}
						if list := callsWith(r, "listOrders"); len(list) != 1 || list[0].Status != CallCancelled || list[0].Yields != 2 {
							t.Errorf("list call: %+v", list)
						}
					}}
			},
		},
		{
			name: "branch reads ahead", definition: "branch", adjust: scaleTimeouts(60000),
			prepare: func(t *testing.T, j *memJournal) run {
				// ship waits until the generator has yielded everything: the engine must read on
				// without waiting for downstream work (§4.1.1, §12).
				return run{bindings: branchBindings(branchKnobs{orders: orders(true, true, true, true, true), failAfter: -1,
					blockAfter: -1, shipWaitsForAll: true, signal: newSignal()}),
					check: func(t *testing.T, r *Report, _ string) {
						expectStatusOf(t, r, StatusSucceeded)
						expectOutputSet(t, r, "receipts", "receipt-1", "receipt-2", "receipt-3", "receipt-4", "receipt-5")
					}}
			},
		},
		{
			name: "calls large", definition: "calls", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: callsBindings(callsKnobs{size: "large", lines: 3}),
					check: func(t *testing.T, r *Report, journal string) {
						expectStatusOf(t, r, StatusSucceeded)
						expectOutput(t, r, "notify", "notified")
						if got := resultPayloads(t, journal, "done"); !slices.Equal(got, []string{`["total 600"]`}) {
							t.Errorf("done: %q", got)
						}
					}}
			},
		},
		{
			name: "calls small", definition: "calls", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: callsBindings(callsKnobs{size: "small"}),
					check: func(t *testing.T, r *Report, journal string) {
						expectStatusOf(t, r, StatusSucceeded)
						if got := resultPayloads(t, journal, "done"); !slices.Equal(got, []string{`["audited 7"]`}) {
							t.Errorf("done: %q", got)
						}
					}}
			},
		},
		{
			name: "calls ignored", definition: "calls", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: callsBindings(callsKnobs{size: "ignored"}),
					check: func(t *testing.T, r *Report, _ string) {
						// Both inputs of the Merge are skipped, so is the Merge and its target (§9.2).
						expectStatusOf(t, r, StatusSkipped)
						expectEndpoint(t, r, "notify", OutcomeSkipped)
					}}
			},
		},
		{
			name: "calls audit stop", definition: "calls", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: callsBindings(callsKnobs{size: "small", failAudit: true}),
					check: func(t *testing.T, r *Report, _ string) {
						expectStatusOf(t, r, StatusFailed)
						expectFailures(t, r, "audit:error")
					}}
			},
		},
		{
			name: "fanout", definition: "fanout", adjust: scaleTimeouts(60000), deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				return run{bindings: fanoutBindings(fanoutKnobs{items: 3}),
					check: func(t *testing.T, r *Report, _ string) {
						// The Stream output carries the generator's elements and ping's result, not the
						// sub-workflow task left out of the output (§8.3).
						expectStatusOf(t, r, StatusSucceeded)
						expectOutputSet(t, r, "collect", "item-1", "item-2", "item-3", "pong")
						expectOutputSet(t, r, "solo", "pong", "pong")
					}}
			},
		},
		{
			name: "limit", definition: "limit", deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				k := &limitKnobs{items: 3, signal: newSignal()}
				return run{bindings: limitBindings(k), check: func(t *testing.T, r *Report, _ string) {
					expectStatusOf(t, r, StatusSucceeded)
					for item := 1; item <= 3; item++ {
						if g, ok := k.perItem.Load(item); ok && g.(*gauge).max() > 2 {
							t.Errorf("item %d: %d calls at once, more than the limit", item, g.(*gauge).max())
						}
					}
				}}
			},
		},
		{
			// Not deterministic in the sense of recovery: a resumed run may not reach the barrier.
			name: "limit barrier", definition: "limit",
			prepare: func(t *testing.T, j *memJournal) run {
				k := &limitKnobs{items: 3, barrier: 6, signal: newSignal()}
				return run{bindings: limitBindings(k), check: func(t *testing.T, r *Report, _ string) {
					expectStatusOf(t, r, StatusSucceeded)
					// Two tasks of each execution run at once, never more (§8.2); the limit is per
					// execution, so the executions of the three items overlap.
					if got := k.gauge.max(); got != 6 {
						t.Errorf("%d calls ran at once, want 6", got)
					}
					for item := 1; item <= 3; item++ {
						g, ok := k.perItem.Load(item)
						if !ok || g.(*gauge).max() != 2 {
							t.Errorf("item %d: at most %v calls at once, want 2", item, g)
						}
					}
					var lists []any
					for item := 1; item <= 3; item++ {
						d := fmt.Sprintf("done %d", item)
						lists = append(lists, []any{d, d, d, d, "idle"})
					}
					expectOutputSet(t, r, "all", lists...)
				}}
			},
		},
		{
			name: "limit slot held", definition: "limit",
			adjust: func(p *Definition) {
				mapWorkflow(p, "limits", mapPlacement("each", mapConcurrency(func(c *Concurrency) {
					c.Limit = 1
					mapTask("a", func(t *TaskSpec) {
						t.Input = ptr(Declared("slow"))
						t.Timeout = Timeout{CallMs: ptr[uint64](30)}
					})(c)
					mapTask("b", func(t *TaskSpec) { t.Input = ptr(Declared("fast")) })(c)
				})))
			},
			prepare: func(t *testing.T, j *memJournal) run {
				k := &limitKnobs{items: 1, signal: newSignal(), linger: 150 * time.Millisecond}
				return run{bindings: limitBindings(k), check: func(t *testing.T, r *Report, journal string) {
					expectStatusOf(t, r, StatusFailed)
					expectFailures(t, r, "each/a:timeout")
					// The timed out call keeps its slot until its user code returned (§8.2, §11.5).
					if k.violations.Load() != 0 || k.signal.count("slow returned") != 1 {
						t.Error("a task started before the timed out call returned")
					}
					ops := opsOf(t, journal)
					terminated := firstOp(ops, func(op Op) bool { _, ok := op.(OpTerminated); return ok })
					beginB := firstOp(ops, func(op Op) bool { b, ok := op.(OpBeginTask); return ok && b.Task == "b" })
					if terminated < 0 || beginB < terminated {
						t.Errorf("task b began at %d, the timed out call terminated at %d", beginB, terminated)
					}
					expectOutputSet(t, r, "all", []any{"done 1", "done 1", "fast", "idle"})
				}}
			},
		},
		{
			name: "panic", definition: "merge", deterministic: true,
			prepare: func(t *testing.T, j *memJournal) run {
				bindings := mergeBindings(mergeKnobs{})
				for i, b := range bindings {
					if b.id == "archive" {
						bindings[i] = Func("archive", func(ctx context.Context, s sales) (string, error) { panic("archive broke") })
					}
				}
				return run{bindings: bindings, check: func(t *testing.T, r *Report, _ string) {
					expectStatusOf(t, r, StatusFailed)
					expectFailures(t, r, "archive:error")
					var pe *PanicError
					if !errors.As(r.Failures[0].Err, &pe) || pe.Value != "archive broke" {
						t.Errorf("panic: %v", r.Failures[0].Err)
					}
				}}
			},
		},
	}
}

func TestRuntimeScenarios(t *testing.T) {
	for _, sc := range scenarios() {
		t.Run(sc.name, func(t *testing.T) {
			t.Parallel()
			runOnce(t, sc)
		})
	}
}

// Deterministic scenarios give the same report and the same values in every run, whatever the
// schedule: value identities come from where the values come from (§15.4).
func TestRuntimeDeterminism(t *testing.T) {
	for _, sc := range scenarios() {
		if !sc.deterministic {
			continue
		}
		t.Run(sc.name, func(t *testing.T) {
			t.Parallel()
			_, journalA, a := runOnce(t, sc)
			_, journalB, b := runOnce(t, sc)
			if diff := compareReports(a, b); diff != "" {
				t.Error(diff)
			}
			if pa, pb := journalPayloads(t, journalA), journalPayloads(t, journalB); !maps2Equal(pa, pb) {
				t.Error("the runs accepted different values")
			}
		})
	}
}

// compareReports compares what two runs produced: the status, the outputs, the endpoints and the
// failures, but not the order of the transitions.
func compareReports(a, b *Report) string {
	var diffs []string
	if a.Status != b.Status {
		diffs = append(diffs, fmt.Sprintf("status %v and %v", a.Status, b.Status))
	}
	if len(a.Outputs) != len(b.Outputs) {
		diffs = append(diffs, fmt.Sprintf("outputs %s and %s", a.Outputs, b.Outputs))
	}
	for name, v := range a.Outputs {
		if string(b.Outputs[name]) != string(v) {
			diffs = append(diffs, fmt.Sprintf("output %s: %s and %s", name, v, b.Outputs[name]))
		}
	}
	if fmt.Sprint(a.Endpoints) != fmt.Sprint(b.Endpoints) {
		diffs = append(diffs, fmt.Sprintf("endpoints %v and %v", a.Endpoints, b.Endpoints))
	}
	if fa, fb := failureNames(a), failureNames(b); !slices.Equal(fa, fb) {
		diffs = append(diffs, fmt.Sprintf("failures %q and %q", fa, fb))
	}
	return strings.Join(diffs, "; ")
}

// journalPayloads maps the values of a journal to their payloads.
func journalPayloads(t *testing.T, journal string) map[string]string {
	t.Helper()
	payloads := map[string]string{}
	for _, line := range recordLines(journal) {
		r, err := DecodeRecord(line)
		if err != nil {
			t.Fatal(err)
		}
		for _, v := range r.Values {
			payloads[v.Value] = v.Payload
		}
	}
	return payloads
}

func maps2Equal(a, b map[string]string) bool {
	if len(a) != len(b) {
		return false
	}
	for k, v := range a {
		if w, ok := b[k]; !ok || w != v {
			return false
		}
	}
	return true
}

// Several executions of one engine run at once without sharing state.
func TestRuntimeConcurrentExecutions(t *testing.T) {
	e, err := NewEngine(load(t, "users"), mustRegistry(t, usersBindings(usersKnobs{})...))
	if err != nil {
		t.Fatal(err)
	}
	var wg sync.WaitGroup
	for n := 1; n <= 8; n++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			r, err := e.Run(context.Background(), tenant{Name: fmt.Sprint(n), Users: n})
			if err != nil || r.Status != StatusSucceeded {
				t.Errorf("run %d: %v %v", n, r, err)
				return
			}
			if got, err := outputSet(r, "all"); err != nil || len(got) != n {
				t.Errorf("run %d: %d lists", n, len(got))
			}
		}()
	}
	wg.Wait()
}

func TestRuntimeInputs(t *testing.T) {
	merge, err := NewEngine(load(t, "merge"), mustRegistry(t, mergeBindings(mergeKnobs{})...))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := merge.Start(context.Background(), "unexpected"); err == nil {
		t.Error("a workflow without input takes no input")
	}
	users, err := NewEngine(load(t, "users"), mustRegistry(t, usersBindings(usersKnobs{})...))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := users.Start(context.Background(), func() {}); err == nil {
		t.Error("an input that does not encode is refused")
	}
	// An input of another shape than the entry expects fails the entry call when it decodes.
	r, err := users.Run(context.Background(), []int{1, 2})
	if err != nil {
		t.Fatal(err)
	}
	expectStatusOf(t, r, StatusFailed)
	expectFailures(t, r, "fetchAllUsers:error")
	// A workflow with input accepts nil, as the JSON null.
	r, err = users.Run(context.Background(), nil)
	if err != nil {
		t.Fatal(err)
	}
	expectStatusOf(t, r, StatusSucceeded)
	expectOutput(t, r, "all", []any{})
}

func TestRuntimeRegistry(t *testing.T) {
	merge := load(t, "merge")
	full := mergeBindings(mergeKnobs{})
	without := func(id string) []Binding {
		var out []Binding
		for _, b := range full {
			if b.id != id {
				out = append(out, b)
			}
		}
		return out
	}
	replace := func(id string, b Binding) []Binding { return append(without(id), b) }
	cases := map[string]struct {
		bindings []Binding
		want     string
	}{
		"missing function":  {without("render"), "function render is not bound"},
		"missing transform": {without("salesWidget"), "transform salesWidget is not bound"},
		"stream for single": {replace("fetchSales", StreamNoInput("fetchSales", func(context.Context) iter.Seq2[sales, error] {
			return nil
		})), "declared as a Single function but bound to a Stream function"},
		"input": {replace("fetchSales", Func("fetchSales", func(context.Context, int) (sales, error) { return sales{}, nil })),
			"takes no input, but its binding takes an input"},
	}
	for label, c := range cases {
		_, err := NewEngine(merge, mustRegistry(t, c.bindings...))
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%s: %v, want %q", label, err, c.want)
		}
	}
	branch := load(t, "branch")
	var noJudge []Binding
	for _, b := range branchBindings(branchKnobs{}) {
		if b.kind != bindJudge {
			noJudge = append(noJudge, b)
		}
	}
	if _, err := NewEngine(branch, mustRegistry(t, noJudge...)); err == nil || !strings.Contains(err.Error(), "judge isPaid is not bound") {
		t.Errorf("missing judge: %v", err)
	}
	for label, bindings := range map[string][]Binding{
		"duplicate": {Passthrough("x"), Passthrough("x")},
		"discard":   {Passthrough(DiscardName)},
		"no id":     {{}},
	} {
		if _, err := NewRegistry(bindings...); err == nil {
			t.Errorf("%s: accepted", label)
		}
	}
	// A function and a transform may share an identifier: calls.json names both price.
	if _, err := NewRegistry(Func("price", func(context.Context, int) (int, error) { return 0, nil }), Passthrough("price")); err != nil {
		t.Error(err)
	}
	// A definition built in code must survive recording, which the definition file cannot express an
	// empty id for; validation does not reject an empty id nothing refers to.
	unrecordable := load(t, "merge")
	unrecordable.Functions = append(unrecordable.Functions, FunctionDecl{Output: Contract{Type: Named("T")}})
	for label, newEngine := range map[string]func(*Definition, *Registry) (*Engine, error){
		"NewEngine": NewEngine, "NewUncheckedEngine": NewUncheckedEngine} {
		if _, err := newEngine(unrecordable, mustRegistry(t, full...)); err == nil ||
			!strings.HasPrefix(err.Error(), "suimon: the definition cannot be recorded: ") {
			t.Errorf("%s: an empty function id: %v", label, err)
		}
	}
	invalid := load(t, "merge")
	invalid.Main = "nope"
	if _, err := NewEngine(invalid, mustRegistry(t, full...)); err == nil {
		t.Error("NewEngine validates the definition")
	}
	unchecked, err := NewUncheckedEngine(invalid, mustRegistry(t, full...))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := unchecked.Start(context.Background(), nil); err == nil || !strings.Contains(err.Error(), "UNKNOWN_MAIN") {
		t.Errorf("an unchecked definition without its main workflow: %v", err)
	}
}

// A journal that fails ends the execution with the error; what it holds can be resumed.
func TestRuntimeJournalFailure(t *testing.T) {
	p := load(t, "users")
	e, err := NewEngine(p, mustRegistry(t, usersBindings(usersKnobs{})...))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := e.Start(context.Background(), tenant{Users: 2}, WithJournal(&memJournal{failAt: 1})); err == nil {
		t.Error("Start reports a journal that cannot be written")
	}
	for failAt := 2; ; failAt++ {
		j := &memJournal{failAt: failAt}
		x, err := e.Start(context.Background(), tenant{Users: 2}, WithJournal(j))
		if err != nil {
			t.Fatal(err)
		}
		r, err := wait(t, x)
		if err == nil {
			// The run needed fewer appends: every failing append has been tried.
			if failAt < 5 || r.Status != StatusSucceeded {
				t.Fatalf("fail at %d: %v", failAt, r.Status)
			}
			break
		}
		if r != nil || !strings.Contains(err.Error(), "disk full") {
			t.Fatalf("fail at %d: %v %v", failAt, r, err)
		}
		// The torn record is cut off, and the execution goes on from the committed transitions.
		resumed := newMemJournal(j.text())
		x, err = e.Resume(context.Background(), resumed)
		if err != nil {
			t.Fatal(err)
		}
		r, err = wait(t, x)
		if err != nil {
			t.Fatal(err)
		}
		verifyJournal(t, p, resumed.text(), r)
		if r.Status != StatusSucceeded && r.Status != StatusFailed {
			t.Errorf("fail at %d: %v", failAt, r.Status)
		}
	}
}

// firstSync is a journal that keeps what its first Sync made durable.
type firstSync struct {
	memJournal
	first  string
	synced bool
}

func (j *firstSync) Sync() error {
	if !j.synced {
		j.first, j.synced = j.text(), true
	}
	return j.memJournal.Sync()
}

// The header is appended with the records of the start, before the first sync: no journal is
// durable with the header alone.
func TestRuntimeJournalHeader(t *testing.T) {
	p := load(t, "merge")
	e, err := NewEngine(p, mustRegistry(t, mergeBindings(mergeKnobs{})...))
	if err != nil {
		t.Fatal(err)
	}
	j := &firstSync{}
	r, err := e.Run(context.Background(), nil, WithJournal(j))
	if err != nil {
		t.Fatal(err)
	}
	if want := EncodeHeader(p) + "\n{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"; !strings.HasPrefix(j.first, want) {
		t.Errorf("the first sync made durable %q", j.first)
	}
	verifyJournal(t, p, j.text(), r)
}

// Executions leave no goroutine behind, whether they conclude, stop, time out or are cancelled.
func TestRuntimeNoLeaks(t *testing.T) {
	baseline := runtime.NumGoroutine()
	for _, name := range []string{"merge", "merge stop", "merge timeout", "users stop", "users cancel", "branch element timeout",
		"limit slot held"} {
		runOnce(t, scenarioNamed(t, name))
	}
	deadline := time.Now().Add(5 * time.Second)
	for runtime.NumGoroutine() > baseline {
		if time.Now().After(deadline) {
			buf := make([]byte, 1<<16)
			t.Fatalf("%d goroutines, %d before:\n%s", runtime.NumGoroutine(), baseline, buf[:runtime.Stack(buf, true)])
		}
		time.Sleep(10 * time.Millisecond)
	}
}
