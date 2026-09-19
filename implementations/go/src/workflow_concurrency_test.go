package suimon

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

type runtimeCheck func(*testing.T, RunResult)

func testWorkflowFastProducer(t *testing.T, check runtimeCheck) {
	w := newFixtureWorkflow(t, "streaming")
	consumerStarted := make(chan struct{})
	var once sync.Once
	bindingAt(&w, "each", "work").Leaf = func(context.Context, *Task) (Values, error) {
		once.Do(func() { close(consumerStarted) })
		return Values{"out": "consumed"}, nil
	}
	bindingAt(&w, "emit").Leaf = func(_ context.Context, task *Task) (Values, error) {
		for i := 0; i < 64; i++ {
			if err := task.Emit("out", fmt.Sprint(i), i); err != nil {
				return nil, err
			}
			select {
			case <-consumerStarted:
				return Values{}, nil
			default:
			}
		}
		return nil, &TaskError{Code: "DOWNSTREAM_STARVED"}
	}
	r, err := w.Run(testContext(t))
	if err != nil {
		t.Fatal(err)
	}
	check(t, r)
}

func testContext(t *testing.T) context.Context {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	t.Cleanup(cancel)
	return ctx
}
func newFixtureWorkflow(t *testing.T, name string) Workflow {
	g := readGraph(t, name)
	return Workflow{Graph: g, Bindings: fixtureBindings(g), Inputs: workflowInputs(g), Options: RunOptions{Now: func() Nat { return N(1000) }, PollInterval: time.Millisecond}}
}
func bindingAt(w *Workflow, path ...string) *Binding {
	for i := range w.Bindings {
		if equal(w.Bindings[i].Path, Path(path)) {
			return &w.Bindings[i]
		}
	}
	panic("binding not found")
}
func startWorkflow(t *testing.T, ctx context.Context, w Workflow) *Execution {
	t.Helper()
	e, err := w.Start(ctx)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(e.Stop)
	return e
}
func awaitState(t *testing.T, ctx context.Context, e *Execution, p func(State) bool) RunResult {
	t.Helper()
	r, err := e.WaitFor(ctx, p)
	if err != nil {
		t.Fatalf("wait: %v, state=%s reason=%v", err, r.State.Status, r.State.Reason)
	}
	return r
}
func awaitSuccess(t *testing.T, ctx context.Context, e *Execution) RunResult {
	t.Helper()
	r, err := e.Wait(ctx)
	if err != nil {
		t.Fatalf("run: %v (%s)", err, r.State.Status)
	}
	if !SucceededDrained(r.State) {
		t.Fatal("execution did not succeed and drain")
	}
	return r
}
func receive[T any](t *testing.T, ctx context.Context, ch <-chan T) T {
	t.Helper()
	select {
	case x := <-ch:
		return x
	case <-ctx.Done():
		t.Fatal(ctx.Err())
		var zero T
		return zero
	}
}

func testWorkflowStreaming(t *testing.T, check runtimeCheck) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "streaming")
	w.Graph.Nodes[1].Kind.Body.Nodes[0].Kind.Concurrency = N(2)
	producerFinish := make(chan struct{})
	childrenFinish := make(chan struct{})
	started := make(chan string, 3)
	var live, maxLive atomic.Int32
	bindingAt(&w, "emit").Leaf = func(ctx context.Context, task *Task) (Values, error) {
		for i, item := range []string{"one", "two", "three"} {
			if err := task.Emit("out", fmt.Sprint(i), item); err != nil {
				return nil, err
			}
		}
		select {
		case <-producerFinish:
			return Values{}, nil
		case <-ctx.Done():
			return nil, ctx.Err()
		}
	}
	bindingAt(&w, "each", "work").Leaf = func(ctx context.Context, task *Task) (Values, error) {
		var input string
		if err := task.DecodeInput("in", &input); err != nil {
			return nil, err
		}
		n := live.Add(1)
		defer live.Add(-1)
		for old := maxLive.Load(); n > old && !maxLive.CompareAndSwap(old, n); old = maxLive.Load() {
		}
		started <- input
		select {
		case <-childrenFinish:
			return Values{"out": "mapped-" + input}, nil
		case <-ctx.Done():
			return nil, ctx.Err()
		}
	}
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	receive(t, ctx, started)
	r := awaitState(t, ctx, e, func(s State) bool {
		return len(filter(s.Instances, func(i Instance) bool { return i.Node == "work" && i.Status == "ready" })) == 1
	})
	if r.State.NodeInstance(nil, "emit").Status != "running" || r.State.NodeInstance(nil, "collect") != nil {
		t.Fatal("streaming overlap or AllWait boundary lost")
	}
	if live.Load() != 2 {
		t.Fatalf("want two concurrent body invocations, got %d", live.Load())
	}
	close(childrenFinish)
	r = awaitState(t, ctx, e, func(s State) bool {
		return len(filter(s.Instances, func(i Instance) bool { return i.Node == "work" && i.Status == "succeeded" })) == 3
	})
	if r.State.NodeInstance(nil, "collect") != nil {
		t.Fatal("AllWait ran before the producer closed its stream")
	}
	close(producerFinish)
	r = awaitSuccess(t, ctx, e)
	if maxLive.Load() != 2 {
		t.Fatalf("shared node concurrency limit: %d", maxLive.Load())
	}
	var values []string
	if err := r.Output("collect", "out")[0].Decode(&values); err != nil {
		t.Fatal(err)
	}
	assertJSON(t, "stream values", values, []string{"mapped-one", "mapped-two", "mapped-three"})
	check(t, r)
}

func testWorkflowRetryAndRenew(t *testing.T, check runtimeCheck) {
	t.Run("retry-delay", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		bindingAt(&w, "work").Leaf = func(_ context.Context, task *Task) (Values, error) {
			if task.Attempt == N(1) {
				return nil, &TaskError{Code: "TEMPORARY", Retryable: true}
			}
			return Values{"out": "retried"}, nil
		}
		e := startWorkflow(t, ctx, w)
		r := awaitState(t, ctx, e, func(s State) bool {
			return anyOf(s.Instances, func(i Instance) bool { return i.Status == "retryWait" })
		})
		if len(r.State.Attempts) != 1 || *r.State.Instances[0].RetryAt != N(1001) {
			t.Fatal("retry did not wait for policy deadline")
		}
		clock.Store(1001)
		r = awaitSuccess(t, ctx, e)
		if len(r.State.Attempts) != 2 {
			t.Fatal("retry count")
		}
		check(t, r)
	})
	t.Run("worker-and-automatic-renewal", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		tasks := make(chan *Task, 1)
		finish := make(chan struct{})
		bindingAt(&w, "work").Leaf = func(ctx context.Context, task *Task) (Values, error) {
			tasks <- task
			select {
			case <-finish:
				return Values{"out": "renewed"}, nil
			case <-ctx.Done():
				return nil, ctx.Err()
			}
		}
		e := startWorkflow(t, ctx, w)
		task := receive(t, ctx, tasks)
		clock.Store(1001)
		if err := task.Renew(); err != nil {
			t.Fatal(err)
		}
		awaitState(t, ctx, e, func(s State) bool {
			i := s.Instance(task.ID)
			return i != nil && i.Lease != nil && i.Lease.Until == N(1004)
		})
		clock.Store(1003)
		awaitState(t, ctx, e, func(s State) bool {
			i := s.Instance(task.ID)
			return i != nil && i.Lease != nil && i.Lease.Until == N(1006)
		})
		close(finish)
		r := awaitSuccess(t, ctx, e)
		if len(r.State.Attempts) != 1 {
			t.Fatal("renewal unexpectedly retried")
		}
		if err := task.Emit("out", "late", "late"); !errors.Is(err, ErrTaskClosed) {
			t.Fatalf("closed task: %v", err)
		}
		check(t, r)
	})
	t.Run("expiration-and-stale-result", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		w.Options.DisableAutoRenew = true
		started := make(chan struct{})
		abandoned := make(chan struct{})
		late := make(chan struct{})
		returned := make(chan struct{})
		parentCtx := ctx
		bindingAt(&w, "work").Leaf = func(ctx context.Context, task *Task) (Values, error) {
			if task.Attempt == N(1) {
				close(started)
				<-ctx.Done()
				close(abandoned)
				select {
				case <-late:
				case <-parentCtx.Done():
				}
				close(returned)
				return Values{"out": "stale"}, nil
			}
			return Values{"out": "fresh"}, nil
		}
		e := startWorkflow(t, ctx, w)
		receive(t, ctx, started)
		clock.Store(1003)
		receive(t, ctx, abandoned)
		awaitState(t, ctx, e, func(s State) bool { return s.Instances[0].Status == "retryWait" })
		clock.Store(1004)
		r := awaitSuccess(t, ctx, e)
		close(late)
		receive(t, ctx, returned)
		var output string
		if err := r.Output("work", "out")[0].Decode(&output); err != nil {
			t.Fatal(err)
		}
		if output != "fresh" || r.State.Attempts[0].Status != "abandoned" {
			t.Fatal("stale attempt published its result")
		}
		check(t, r)
	})
	t.Run("exhausted-expired-worker", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		w.Graph.Nodes[0].Kind.Retry.MaxAttempts = N(1)
		w.Options.DisableAutoRenew = true
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		started := make(chan struct{})
		release := make(chan struct{})
		defer close(release)
		bindingAt(&w, "work").Leaf = func(context.Context, *Task) (Values, error) {
			close(started)
			<-release
			return Values{"out": "late"}, nil
		}
		e := startWorkflow(t, ctx, w)
		receive(t, ctx, started)
		clock.Store(1003)
		r, err := e.Wait(ctx)
		if !errors.Is(err, ErrBlocked) || value(r.State.Reason, "") != "LEASE_EXPIRED" {
			t.Fatalf("expired exhausted worker: %v", err)
		}
		check(t, r)
	})
}

func testWorkflowManualRetry(t *testing.T, check runtimeCheck) {
	t.Run("leaf-exhaustion", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		w.Graph.Nodes[0].Kind.Retry.MaxAttempts = N(1)
		bindingAt(&w, "work").Leaf = func(_ context.Context, task *Task) (Values, error) {
			if task.Attempt == N(1) {
				return nil, &TaskError{Code: "EXHAUSTED", Retryable: true}
			}
			return Values{"out": "recovered"}, nil
		}
		e := startWorkflow(t, ctx, w)
		blocked, err := e.Wait(ctx)
		if !errors.Is(err, ErrBlocked) || value(blocked.State.Reason, "") != "EXHAUSTED" {
			t.Fatalf("want blocked: %v", err)
		}
		check(t, blocked)
		if err := e.ManualRetry(ctx, blocked.State.Instances[0].ID); err != nil {
			t.Fatal(err)
		}
		r := awaitSuccess(t, ctx, e)
		if r.State.Instances[0].ExtraAttempts != N(1) {
			t.Fatal("manual retry did not extend this instance")
		}
		check(t, r)
	})
	t.Run("loop-limit", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "loop")
		var finish atomic.Bool
		bindingAt(&w, "loop").Loop = func(context.Context, DecisionTask) (bool, error) { return finish.Load(), nil }
		e := startWorkflow(t, ctx, w)
		blocked, err := e.Wait(ctx)
		if !errors.Is(err, ErrBlocked) || value(blocked.State.Reason, "") != "LOOP_LIMIT" {
			t.Fatalf("want loop limit: %v", err)
		}
		loop := blocked.State.NodeInstance(nil, "loop")
		if loop.Iteration != N(2) {
			t.Fatal("wrong iteration bound")
		}
		check(t, blocked)
		finish.Store(true)
		if err := e.ManualRetry(ctx, loop.ID); err != nil {
			t.Fatal(err)
		}
		r := awaitSuccess(t, ctx, e)
		i := r.State.NodeInstance(nil, "loop")
		if i.Iteration != N(3) || i.ExtraIterations != N(1) {
			t.Fatal("manual loop continuation restarted old iterations")
		}
		check(t, r)
	})
}

func testWorkflowCancelAndTerminal(t *testing.T, check runtimeCheck) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "minimal")
	started := make(chan *Task, 1)
	bindingAt(&w, "work").Leaf = func(ctx context.Context, task *Task) (Values, error) {
		started <- task
		<-ctx.Done()
		return Values{"out": "late"}, nil
	}
	e := startWorkflow(t, ctx, w)
	task := receive(t, ctx, started)
	if err := e.Cancel(ctx); err != nil {
		t.Fatal(err)
	}
	r, err := e.Wait(ctx)
	if !errors.Is(err, ErrCancelled) || r.State.Status != "cancelled" {
		t.Fatalf("cancel: %v", err)
	}
	if anyOf(r.State.Attempts, func(a Attempt) bool { return a.Status == "running" }) {
		t.Fatal("cancel retained active attempts")
	}
	if err := e.ManualRetry(ctx, task.ID); err != nil {
		t.Fatal("terminal absorption:", err)
	}
	auth := task.auth
	auth.Now = N(1000)
	err = e.Apply(ctx, Op{Kind: "emit", Auth: auth, Port: "out", Item: "late"}, Values{"late": "late"})
	var rejected *Reject
	if !errors.As(err, &rejected) || rejected.Code != "INVALID_LEASE" {
		t.Fatalf("stale cancelled worker: %v", err)
	}
	check(t, e.Result())

	t.Run("context-cancellation", func(t *testing.T) {
		ctx, cancel := context.WithCancel(testContext(t))
		w := newFixtureWorkflow(t, "minimal")
		started := make(chan struct{})
		bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
			close(started)
			<-ctx.Done()
			return nil, ctx.Err()
		}
		e := startWorkflow(t, ctx, w)
		receive(t, testContext(t), started)
		cancel()
		r, err := e.Wait(testContext(t))
		if !errors.Is(err, context.Canceled) || r.State.Status != "cancelled" {
			t.Fatalf("context cancellation: %v", err)
		}
		check(t, r)
	})
	t.Run("cancel-pending-decision", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "branch")
		started, cancelled := make(chan struct{}), make(chan struct{})
		bindingAt(&w, "choose").Branch = func(ctx context.Context, _ DecisionTask) (string, error) {
			close(started)
			<-ctx.Done()
			close(cancelled)
			return "", ctx.Err()
		}
		e := startWorkflow(t, ctx, w)
		receive(t, ctx, started)
		if err := e.Cancel(ctx); err != nil {
			t.Fatal(err)
		}
		receive(t, ctx, cancelled)
		r := awaitState(t, ctx, e, func(s State) bool { return s.Status == "cancelled" })
		if _, err := e.Wait(ctx); !errors.Is(err, ErrCancelled) {
			t.Fatalf("cancelled decision replaced terminal result: %v", err)
		}
		check(t, r)
	})
	t.Run("supersede-pending-decision", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "branch")
		w.Options.Workers = 1
		started, cancelled := make(chan struct{}), make(chan struct{})
		bindingAt(&w, "choose").Branch = func(ctx context.Context, _ DecisionTask) (string, error) {
			close(started)
			<-ctx.Done()
			close(cancelled)
			return "", ctx.Err()
		}
		e := startWorkflow(t, ctx, w)
		receive(t, ctx, started)
		if err := e.Apply(ctx, Op{Kind: "fireBranch", Node: "choose", Arm: "right"}, nil); err != nil {
			t.Fatal(err)
		}
		receive(t, ctx, cancelled)
		r := awaitSuccess(t, ctx, e)
		if len(r.Output("right", "out")) != 1 || len(r.Output("left", "out")) != 0 {
			t.Fatal("superseded decision changed the selected branch")
		}
		check(t, r)
	})
}

func testWorkflowRedelivery(t *testing.T, check runtimeCheck) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "minimal")
	e := startWorkflow(t, ctx, w)
	r := awaitSuccess(t, ctx, e)
	receipt := r.State.Receipts[0]
	auth := Credentials{receipt.Instance, receipt.Attempt, receipt.Token, r.State.Now}
	if err := e.Apply(ctx, Op{Kind: "complete", Auth: auth, Outputs: receipt.Outputs}, nil); err != nil {
		t.Fatal(err)
	}
	assertJSON(t, "terminal complete redelivery", e.Result().State, r.State)
	if err := e.Cancel(ctx); err != nil {
		t.Fatal(err)
	}
	assertJSON(t, "terminal cancel absorption", e.Result().State, r.State)
	auth.Token = "wrong"
	err := e.Apply(ctx, Op{Kind: "complete", Auth: auth, Outputs: receipt.Outputs}, nil)
	var rejected *Reject
	if !errors.As(err, &rejected) || rejected.Code != "INVALID_LEASE" {
		t.Fatalf("mismatched terminal credentials: %v", err)
	}
	check(t, e.Result())
}
