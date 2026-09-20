package suimon

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

func independentLeaves(t *testing.T) Workflow {
	w := newFixtureWorkflow(t, "minimal")
	x, y := w.Graph.Nodes[0], w.Graph.Nodes[0]
	x.ID, y.ID = "x", "y"
	w.Graph = Graph{Nodes: List[Node]{x, y}, Entries: List[PortRef]{{"x", "in"}, {"y", "in"}}, Exits: List[PortRef]{{"x", "out"}, {"y", "out"}}}
	w.Inputs, w.Bindings = workflowInputs(w.Graph), fixtureBindings(w.Graph)
	w.Options.Workers, w.Options.DisableAutoRenew, w.Options.StaleGraceSeconds = 1, true, N(2)
	return w
}

func TestWorkflowStalledMaintenance(t *testing.T) {
	ctx := testContext(t)
	w := independentLeaves(t)
	w.Graph.Nodes[0].Kind.Retry.RetrySeconds = N(20)
	var clock atomic.Uint64
	clock.Store(1000)
	w.Options.Now = func() Nat { return N(clock.Load()) }
	started, release := make(chan struct{}), make(chan struct{})
	var once sync.Once
	t.Cleanup(func() { once.Do(func() { close(release) }) })
	bindingAt(&w, "x").Leaf = func(context.Context, *Task) (Values, error) {
		close(started)
		<-release
		return Values{"out": "late"}, nil
	}
	bindingAt(&w, "y").Leaf = func(context.Context, *Task) (Values, error) {
		t.Error("local worker limit was exceeded")
		return Values{"out": "unexpected"}, nil
	}
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	clock.Store(1003)
	awaitState(t, ctx, e, func(s State) bool { i := s.NodeInstance(nil, "x"); return i != nil && i.Status == "retryWait" })
	clock.Store(1005)
	r, err := e.Wait(ctx)
	if !errors.Is(err, ErrWorkerStalled) || *r.State.NodeInstance(nil, "x").RetryAt != N(1023) {
		t.Fatalf("expected stall with a future retry: %v", err)
	}
	awaitRuntimePolls(t, ctx, e, e.metrics.polls.Load()+3)
	probes := e.metrics.candidates.Load()
	awaitRuntimePolls(t, ctx, e, e.metrics.polls.Load()+3)
	if e.metrics.candidates.Load() != probes {
		t.Fatal("stalled polling re-scanned candidates before a deadline")
	}
	clock.Store(1023)
	r = awaitState(t, ctx, e, func(s State) bool { return s.NodeInstance(nil, "x").Status == "ready" })
	if r.State.Now != N(1023) {
		t.Fatal("retry promotion did not process the clock")
	}
	if _, err := e.Wait(ctx); !errors.Is(err, ErrWorkerStalled) {
		t.Fatal(err)
	}
	y := r.State.NodeInstance(nil, "y")
	auth := Credentials{y.ID, "external", "external-token", N(1023)}
	if err := e.Apply(ctx, Op{Kind: "claim", Auth: auth, Worker: "remote"}, nil); err != nil {
		t.Fatalf("maintenance was left overdue: %v", err)
	}
	if _, err := e.Wait(ctx); !errors.Is(err, ErrWorkerStalled) {
		t.Fatal(err)
	}
	clock.Store(1026)
	r = awaitState(t, ctx, e, func(s State) bool { return s.Instance(y.ID).Status == "retryWait" })
	if r.State.Attempts[len(r.State.Attempts)-1].Status != "abandoned" {
		t.Fatal("external worker's lease was not expired during stall")
	}
	clock.Store(1027)
	r = awaitState(t, ctx, e, func(s State) bool { return s.Instance(y.ID).Status == "ready" })
	assertRuntimeTrace(t, r)
	if err := e.Cancel(ctx); err != nil {
		t.Fatal(err)
	}
}

func TestWorkflowSchedulerClockJump(t *testing.T) {
	// Establish a valid model history with x retrying at 1004, y ready, and a
	// stale local job occupying the only slot. The clock changes exactly between
	// advance's sample/probe and the stall-publication decision.
	w := independentLeaves(t)
	s := Initial(w.Graph)
	values := map[string]json.RawMessage{}
	inputs := List[Input]{}
	for _, in := range w.Inputs {
		input := Input{Entry: in.Entry}
		for _, item := range in.Items {
			input.Items = append(input.Items, item.ID)
			values[item.ID], _ = encodeData(item.Value)
		}
		inputs = append(inputs, input)
	}
	auth := Credentials{InstanceID(nil, "x", nil), "old", "old-token", N(1000)}
	ops := []Op{{Kind: "start", Inputs: inputs}, {Kind: "activate", Node: "x"}, {Kind: "activate", Node: "y"},
		{Kind: "claim", Auth: auth, Worker: "local"}, {Kind: "expireLease", Inst: auth.Instance, Now: N(1003)}}
	events := List[Event]{}
	for n, op := range ops {
		var rows List[Event]
		var rejected *Reject
		s, rows, rejected = RecordTransaction(s, []Op{op}, natLen(events).Inc(), fmt.Sprint("prepare-", n), s.Now)
		if rejected != nil {
			t.Fatal(rejected)
		}
		events = append(events, rows...)
	}
	var samples atomic.Int32
	w.Options.Now = func() Nat {
		if samples.Add(1) <= 2 {
			return N(1003)
		}
		return N(1010)
	}
	w.Options.PollInterval = time.Millisecond
	e := &Execution{requests: make(chan runMessage), done: make(chan struct{}), stop: make(chan struct{}), changed: make(chan struct{})}
	runtime := &workflowRuntime{execution: e, ctx: testContext(t), graph: w.Graph, options: w.Options, state: s, events: events, time: N(1003), values: values, ids: newRuntimeIDs(s, events),
		jobs: map[string]*runtimeJob{auth.Attempt: {kind: "leaf", obsolete: true, staleAt: ptr(N(1000)), scope: DecisionTask{Node: "x"}, auth: auth, cancel: func() {}}}}
	runtime.publish(false, nil)
	go runtime.loop()
	t.Cleanup(e.Stop)
	r, err := e.Wait(testContext(t))
	if !errors.Is(err, ErrWorkerStalled) || r.State.Now != N(1010) || r.State.NodeInstance(nil, "x").Status != "ready" {
		t.Fatalf("stall published before overdue maintenance: now=%s x=%s error=%v", r.State.Now, r.State.NodeInstance(nil, "x").Status, err)
	}
	assertRuntimeTrace(t, r)
}

func TestWorkflowDecisionCommitError(t *testing.T) {
	for _, legacy := range []bool{false, true} {
		for _, rejectCause := range []bool{false, true} {
			t.Run(fmt.Sprintf("legacy=%v/reject-cause=%v", legacy, rejectCause), func(t *testing.T) {
				w := newFixtureWorkflow(t, "branch")
				var cause error = errors.New("storage unavailable")
				if rejectCause {
					cause = reject("STORAGE_REJECT")
				}
				fail := func(events List[Event]) error {
					for n := len(events) - 1; n >= 0; n-- {
						if op := events[n].Op; op != nil {
							if op.Kind == "fireBranch" {
								return cause
							}
							break
						}
					}
					return nil
				}
				if legacy {
					w.Options.Commit = func(_ context.Context, s Snapshot) error { return fail(s.Events) }
				} else {
					w.Options.Append = func(_ context.Context, b CommitBatch) error { return fail(b.Events) }
				}
				r, err := w.Run(testContext(t))
				var decision *DecisionError
				if _, ok := err.(*CommitError); !ok || !errors.Is(err, cause) || errors.As(err, &decision) {
					t.Fatalf("persistence error was classified as a decision error: %T %v", err, err)
				}
				assertRuntimeTrace(t, r)
			})
		}
	}
}
