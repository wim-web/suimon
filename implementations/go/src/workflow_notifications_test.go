package suimon

import (
	"context"
	"errors"
	"io"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

func awaitCounter(t *testing.T, ctx context.Context, counter *atomic.Uint64, minimum uint64) {
	t.Helper()
	tick := time.NewTicker(time.Millisecond)
	defer tick.Stop()
	for counter.Load() < minimum {
		select {
		case <-tick.C:
		case <-ctx.Done():
			t.Fatal(ctx.Err())
		}
	}
}

type changeResult struct {
	update ExecutionUpdate
	err    error
}

func TestWorkflowStableStallNotifications(t *testing.T) {
	ctx := testContext(t)
	w := independentLeaves(t)
	w.Graph.Nodes[0].Kind.Retry.RetrySeconds = N(20)
	var clock atomic.Uint64
	clock.Store(1000)
	w.Options.Now = func() Nat { return N(clock.Load()) }
	started, resumed := make(chan struct{}), make(chan struct{}, 2)
	release, finish := make(chan struct{}), make(chan struct{})
	var once sync.Once
	t.Cleanup(func() { once.Do(func() { close(release) }) })
	handler := func(ctx context.Context, task *Task) (Values, error) {
		if task.Node == "x" && task.Attempt == N(1) {
			close(started)
			<-release
			return Values{"out": "stale"}, nil
		}
		resumed <- struct{}{}
		select {
		case <-finish:
			return Values{"out": "fresh"}, nil
		case <-ctx.Done():
			return nil, ctx.Err()
		}
	}
	bindingAt(&w, "x").Leaf, bindingAt(&w, "y").Leaf = handler, handler
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	clock.Store(1003)
	awaitState(t, ctx, e, func(s State) bool { return s.NodeInstance(nil, "x").Status == "retryWait" })
	clock.Store(1005)
	_, err := e.Wait(ctx)
	if !errors.Is(err, ErrWorkerStalled) {
		t.Fatal(err)
	}
	before := e.Observe()
	if !before.Settled || before.Stopped || !errors.Is(before.Err, ErrWorkerStalled) {
		t.Fatalf("initial status: %+v", before)
	}
	// Returned diagnostics must not change the retained cause or its revision.
	err.(*WorkerStalledError).Handlers[0].Deadline = N(0)
	mutated := e.Observe()
	mutated.Err.(*WorkerStalledError).Handlers[0].Definition[0] = "mutated"
	if e.Observe().Err.(*WorkerStalledError).Handlers[0].Deadline != N(1005) {
		t.Fatal("Wait returned a mutable internal error")
	}
	changed := make(chan changeResult, 1)
	waits := e.metrics.changeWaits.Load()
	go func() { u, err := e.WaitForChange(ctx, before.Cursor); changed <- changeResult{u, err} }()
	awaitCounter(t, ctx, &e.metrics.changeWaits, waits+1)
	notifications := e.metrics.notifications.Load()
	checkUnchanged := func() {
		t.Helper()
		u := e.Observe()
		if u.Cursor != before.Cursor || !u.Settled || !errors.Is(u.Err, ErrWorkerStalled) || e.metrics.notifications.Load() != notifications {
			t.Fatalf("same stall was cleared or re-notified: revision=%s, error=%v", u.Cursor.Revision(), u.Err)
		}
		if e.metrics.changeWaits.Load() != waits+1 {
			t.Fatal("model updates woke the execution-status waiter")
		}
		select {
		case change := <-changed:
			t.Fatalf("same-cause maintenance returned a change: %+v", change)
		default:
		}
	}
	clock.Store(1023)
	awaitState(t, ctx, e, func(s State) bool { return s.NodeInstance(nil, "x").Status == "ready" })
	checkUnchanged()
	if before.Result().State.Now != N(1003) || e.Observe().Result().State.Now != N(1023) {
		t.Fatal("observation did not retain its view, or current model view stopped updating")
	}
	y := e.Result().State.NodeInstance(nil, "y")
	auth := Credentials{y.ID, "external", "external-token", N(1023)}
	if err := e.Apply(ctx, Op{Kind: "claim", Auth: auth, Worker: "external"}, nil); err != nil {
		t.Fatal(err)
	}
	checkUnchanged()
	clock.Store(1026)
	awaitState(t, ctx, e, func(s State) bool { return s.Instance(y.ID).Status == "retryWait" })
	checkUnchanged()
	clock.Store(1027)
	awaitState(t, ctx, e, func(s State) bool { return s.Instance(y.ID).Status == "ready" })
	if err := e.Apply(ctx, Op{Kind: "idle"}, nil); err != nil {
		t.Fatal(err)
	}
	checkUnchanged()
	// Physical capacity actually recovers. No Resume or polling loop is needed.
	once.Do(func() { close(release) })
	change := receive(t, ctx, changed)
	if change.err != nil || change.update.Settled || change.update.Err != nil || change.update.Cursor.Revision() != before.Cursor.Revision().Inc() {
		t.Fatalf("capacity recovery did not produce one running update: %+v", change)
	}
	receive(t, ctx, resumed)
	close(finish)
	after := awaitSuccess(t, ctx, e)
	u, err := e.WaitForChange(ctx, change.update.Cursor)
	if err != nil || !u.Settled || u.Err != nil || u.Result().State.Status != "succeeded" {
		t.Fatalf("success update: %+v %v", u, err)
	}
	assertRuntimeTrace(t, after)
}

func TestWorkflowStallDemandChanges(t *testing.T) {
	ctx := testContext(t)
	w := independentLeaves(t)
	w.Graph.Nodes[0].Kind.Retry.MaxAttempts = N(1)
	var clock atomic.Uint64
	clock.Store(1000)
	w.Options.Now = func() Nat { return N(clock.Load()) }
	started, release := make(chan struct{}), make(chan struct{})
	defer close(release)
	bindingAt(&w, "x").Leaf = func(context.Context, *Task) (Values, error) {
		close(started)
		<-release
		return Values{"out": "late"}, nil
	}
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	clock.Store(1003)
	awaitState(t, ctx, e, func(s State) bool { return s.NodeInstance(nil, "x").Status == "failed" })
	clock.Store(1005)
	_, err := e.Wait(ctx)
	if !errors.Is(err, ErrWorkerStalled) {
		t.Fatal(err)
	}
	stalled := e.Observe()
	// The only ready callback is now handled externally. Local slots are still
	// occupied, but no work currently needs them: the stale cause must clear.
	y := e.Result().State.NodeInstance(nil, "y")
	auth := Credentials{y.ID, "external", "external-token", N(1005)}
	if err := e.Apply(ctx, Op{Kind: "claim", Auth: auth, Worker: "remote"}, nil); err != nil {
		t.Fatal(err)
	}
	running, err := e.WaitForChange(ctx, stalled.Cursor)
	if err != nil || running.Settled || running.Err != nil {
		t.Fatalf("obsolete stall assessment retained: %+v %v", running, err)
	}
	id := PlainItemID(nil, "y", "out")
	if err := e.Apply(ctx, Op{Kind: "complete", Auth: auth, Outputs: List[Output]{{"out", List[string]{id}}}}, Values{id: "done"}); err != nil {
		t.Fatal(err)
	}
	blocked, err := e.WaitForChange(ctx, running.Cursor)
	if err != nil || !blocked.Settled || !errors.Is(blocked.Err, ErrBlocked) || errors.Is(blocked.Err, ErrWorkerStalled) {
		t.Fatalf("failure was not distinguished from a slot stall: %+v %v", blocked, err)
	}
	assertRuntimeTrace(t, blocked.Result())
}

func TestWorkflowWaitForChange(t *testing.T) {
	t.Run("broadcast-to-independent-observers", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		started := make(chan struct{})
		bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
			close(started)
			<-ctx.Done()
			return nil, ctx.Err()
		}
		e := startWorkflow(t, ctx, w)
		receive(t, ctx, started)
		initial := e.Observe()
		updates := make(chan changeResult, 2)
		waits := e.metrics.changeWaits.Load()
		for n := 0; n < 2; n++ {
			go func() { u, err := e.WaitForChange(ctx, initial.Cursor); updates <- changeResult{u, err} }()
		}
		awaitCounter(t, ctx, &e.metrics.changeWaits, waits+2)
		if err := e.Cancel(ctx); err != nil {
			t.Fatal(err)
		}
		first, second := receive(t, ctx, updates), receive(t, ctx, updates)
		if first.err != nil || second.err != nil || first.update.Cursor != second.update.Cursor || !errors.Is(first.update.Err, ErrCancelled) || !errors.Is(second.update.Err, ErrCancelled) {
			t.Fatalf("observers competed for an update: %+v %+v", first, second)
		}
		assertRuntimeTrace(t, first.update.Result())
	})
	for _, finish := range []string{"success", "stop", "cancel"} {
		t.Run(finish, func(t *testing.T) {
			ctx := testContext(t)
			w := newFixtureWorkflow(t, "minimal")
			started, release := make(chan struct{}), make(chan struct{})
			bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
				close(started)
				select {
				case <-release:
					return Values{"out": "done"}, nil
				case <-ctx.Done():
					return nil, ctx.Err()
				}
			}
			e := startWorkflow(t, ctx, w)
			receive(t, ctx, started)
			initial, err := e.WaitForChange(ctx, ExecutionCursor{})
			if err != nil || initial.Settled || initial.Stopped {
				t.Fatalf("initial observation: %+v %v", initial, err)
			}
			cancelled, cancel := context.WithCancel(ctx)
			pending := make(chan changeResult, 1)
			waits := e.metrics.changeWaits.Load()
			go func() { u, err := e.WaitForChange(cancelled, initial.Cursor); pending <- changeResult{u, err} }()
			awaitCounter(t, ctx, &e.metrics.changeWaits, waits+1)
			copies := e.metrics.results.Load()
			for n := 0; n < 3; n++ {
				if err := e.Apply(ctx, Op{Kind: "idle"}, nil); err != nil {
					t.Fatal(err)
				}
			}
			if e.metrics.results.Load() != copies || e.metrics.changeWaits.Load() != waits+1 || e.Observe().Cursor != initial.Cursor {
				t.Fatal("model commits woke the status waiter or copied results")
			}
			cancel()
			cancelledWait := receive(t, ctx, pending)
			if !errors.Is(cancelledWait.err, context.Canceled) || cancelledWait.update.Stopped {
				t.Fatalf("wait cancellation stopped execution: %+v", cancelledWait)
			}
			switch finish {
			case "success":
				close(release)
				awaitSuccess(t, ctx, e)
			case "stop":
				e.Stop()
			case "cancel":
				if err := e.Cancel(ctx); err != nil {
					t.Fatal(err)
				}
			}
			completed, err := e.WaitForChange(ctx, initial.Cursor)
			if err != nil || !completed.Settled {
				t.Fatalf("missed a change that arrived before registration: %+v %v", completed, err)
			}
			if finish == "stop" && !errors.Is(completed.Err, ErrStopped) || finish == "cancel" && !errors.Is(completed.Err, ErrCancelled) || finish == "success" && completed.Err != nil {
				t.Fatalf("wrong workflow outcome: %v", completed.Err)
			}
			e.Stop()
			last := e.Observe()
			if !last.Stopped || !last.Settled {
				t.Fatal("stopped observation missing")
			}
			if u, err := e.WaitForChange(ctx, last.Cursor); !errors.Is(err, io.EOF) || u.Cursor != last.Cursor {
				t.Fatalf("final cursor did not return EOF: %+v %v", u, err)
			}
			if u, err := e.WaitForChange(ctx, initial.Cursor); err != nil || !u.Stopped {
				t.Fatalf("older cursor missed final update: %+v %v", u, err)
			}
			future := ExecutionCursor{execution: e, revision: last.Cursor.Revision().Inc()}
			if _, err := e.WaitForChange(ctx, future); !errors.Is(err, ErrInvalidExecutionCursor) {
				t.Fatal("future cursor accepted:", err)
			}
			other := startWorkflow(t, ctx, newFixtureWorkflow(t, "minimal"))
			if _, err := other.WaitForChange(ctx, initial.Cursor); !errors.Is(err, ErrInvalidExecutionCursor) {
				t.Fatal("foreign execution cursor accepted:", err)
			}
			assertRuntimeTrace(t, last.Result())
		})
	}
	t.Run("cancel-during-failure-commit", func(t *testing.T) {
		ctx, cancel := context.WithCancel(testContext(t))
		defer cancel()
		w := newFixtureWorkflow(t, "minimal")
		bindingAt(&w, "work").Leaf = func(context.Context, *Task) (Values, error) { return nil, errors.New("failed") }
		w.Options.Append = func(_ context.Context, batch CommitBatch) error {
			if batch.Events[0].Op.Kind == "fail" {
				cancel()
			}
			return nil
		}
		r, err := w.Run(ctx)
		if !errors.Is(err, ErrCancelled) || !errors.Is(err, context.Canceled) || r.State.Status != "cancelled" {
			t.Fatalf("failure settled before cancellation: status=%s error=%v", r.State.Status, err)
		}
		assertRuntimeTrace(t, r)
	})
}
