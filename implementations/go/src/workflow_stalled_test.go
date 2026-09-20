package suimon

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"testing"
)

func TestWorkflowStalled(t *testing.T) {
	for _, action := range []string{"return", "cancel", "manual-retry"} {
		t.Run(action, func(t *testing.T) {
			ctx := testContext(t)
			w := newFixtureWorkflow(t, "minimal")
			w.Options.Workers, w.Options.DisableAutoRenew, w.Options.StaleGraceSeconds = 1, true, N(2)
			if action == "manual-retry" {
				w.Graph.Nodes[0].Kind.Retry.MaxAttempts = N(1)
			}
			var clock atomic.Uint64
			clock.Store(1000)
			w.Options.Now = func() Nat { return N(clock.Load()) }
			started := make(chan *Task, 2)
			cancelled := make(chan struct{})
			release, finish := make(chan struct{}), make(chan struct{})
			var once sync.Once
			t.Cleanup(func() { once.Do(func() { close(release) }) })
			var live, maxLive atomic.Int32
			bindingAt(&w, "work").Leaf = func(ctx context.Context, task *Task) (Values, error) {
				n := live.Add(1)
				defer live.Add(-1)
				for old := maxLive.Load(); n > old && !maxLive.CompareAndSwap(old, n); old = maxLive.Load() {
				}
				started <- task
				if task.Attempt == N(1) {
					<-ctx.Done()
					close(cancelled)
					<-release // Deliberately ignore cancellation until the test releases it.
					return Values{"out": "stale"}, nil
				}
				select {
				case <-finish:
					return Values{"out": "fresh"}, nil
				case <-ctx.Done():
					return nil, ctx.Err()
				}
			}
			e := startWorkflow(t, ctx, w)
			first := receive(t, ctx, started)
			clock.Store(1003)
			receive(t, ctx, cancelled)
			if action == "manual-retry" {
				if _, err := e.Wait(ctx); !errors.Is(err, ErrBlocked) {
					t.Fatal(err)
				}
				if err := e.ManualRetry(ctx, first.ID); err != nil {
					t.Fatal(err)
				}
			} else {
				awaitState(t, ctx, e, func(s State) bool { return s.Instances[0].Status == "retryWait" })
			}
			clock.Store(1004) // Before the logical grace deadline.
			ready := awaitState(t, ctx, e, func(s State) bool { return s.Instances[0].Status == "ready" })
			awaitRuntimePolls(t, ctx, e, e.metrics.polls.Load()+3)
			if _, settled, err, _ := e.read(); settled {
				t.Fatalf("settled before grace: %v", err)
			}
			clock.Store(1005) // Deadline: stale since 1003, grace 2.
			r, err := e.Wait(ctx)
			var stalled *WorkerStalledError
			if !errors.As(err, &stalled) || !errors.Is(err, ErrWorkerStalled) || errors.Is(err, ErrBlocked) {
				t.Fatalf("stalled error: %v", err)
			}
			if stalled.Workers != 1 || len(stalled.Handlers) != 1 || stalled.Handlers[0].Node != "work" || stalled.Handlers[0].Attempt != first.auth.Attempt || stalled.Handlers[0].Deadline != N(1005) {
				t.Fatalf("stalled context: %+v", stalled)
			}
			assertJSON(t, "stall leaves model unchanged", r.State, ready.State)
			select {
			case <-e.done:
				t.Fatal("stalled driver stopped")
			default:
			}
			if action == "cancel" {
				if err := e.Cancel(ctx); err != nil {
					t.Fatal(err)
				}
				r, err = e.Wait(ctx)
				if !errors.Is(err, ErrCancelled) {
					t.Fatal(err)
				}
			} else {
				clock.Store(1006) // Job completion must wake scheduling, even at a fixed time.
				once.Do(func() { close(release) })
				second := receive(t, ctx, started)
				if second.Attempt != N(2) {
					t.Fatal("retry was not resumed")
				}
				close(finish)
				r = awaitSuccess(t, ctx, e)
				var output string
				if err := r.Output("work", "out")[0].Decode(&output); err != nil || output != "fresh" {
					t.Fatalf("stale output escaped: %s %v", output, err)
				}
			}
			if maxLive.Load() != 1 {
				t.Fatalf("physical worker limit exceeded: %d", maxLive.Load())
			}
			assertRuntimeTrace(t, r)
		})
	}
	t.Run("run-does-not-reclaim-handler", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		w.Options.Workers, w.Options.DisableAutoRenew, w.Options.StaleGraceSeconds = 1, true, N(2)
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		started, cancelled, ready, exited := make(chan struct{}), make(chan struct{}), make(chan struct{}, 1), make(chan struct{})
		release := make(chan struct{})
		var once sync.Once
		t.Cleanup(func() { once.Do(func() { close(release) }) })
		bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
			close(started)
			<-ctx.Done()
			close(cancelled)
			<-release
			close(exited)
			return Values{}, nil
		}
		w.Options.Commit = func(_ context.Context, s Snapshot) error {
			for n := len(s.Events) - 1; n >= 0; n-- {
				if op := s.Events[n].Op; op != nil {
					if op.Kind == "promoteRetry" {
						ready <- struct{}{}
					}
					break
				}
			}
			return nil
		}
		result := make(chan error, 1)
		go func() { _, err := w.Run(ctx); result <- err }()
		receive(t, ctx, started)
		clock.Store(1003)
		receive(t, ctx, cancelled)
		clock.Store(1004)
		receive(t, ctx, ready)
		clock.Store(1005)
		if err := receive(t, ctx, result); !errors.Is(err, ErrWorkerStalled) {
			t.Fatal(err)
		}
		select {
		case <-exited:
			t.Fatal("test handler unexpectedly exited")
		default:
		}
		once.Do(func() { close(release) })
		receive(t, ctx, exited)
	})
}

func TestWorkflowDecisionErrors(t *testing.T) {
	for _, scenario := range []string{"invalid-arm", "callback", "panic", "oracle"} {
		t.Run(scenario, func(t *testing.T) {
			w := newFixtureWorkflow(t, "branch")
			cause := errors.New("decision unavailable")
			bindingAt(&w, "choose").Branch = func(context.Context, DecisionTask) (string, error) {
				switch scenario {
				case "callback":
					return "", cause
				case "panic":
					panic("bad decision")
				case "oracle":
					return "right", nil
				}
				return "unknown", nil
			}
			if scenario == "oracle" {
				w.Options.Oracle = &ScopedOracle{Branch: func(Path, string, string) string { return "left" }}
			}
			r, err := w.Run(testContext(t))
			var decision *DecisionError
			if !errors.As(err, &decision) || decision.Node != "choose" || decision.Operation != "fireBranch" || !equal(decision.Definition, Path{"choose"}) || decision.Item == "" {
				t.Fatalf("missing decision context: %v", err)
			}
			if scenario == "callback" && !errors.Is(err, cause) {
				t.Fatal("cause was lost")
			}
			if scenario == "invalid-arm" || scenario == "oracle" {
				var rejected *Reject
				code := "UNKNOWN_ARM"
				if scenario == "oracle" {
					code = "ORACLE_MISMATCH"
				}
				if !errors.As(err, &rejected) || rejected.Code != code {
					t.Fatal("rejection was lost:", err)
				}
			}
			if r.State.Status != "running" {
				t.Fatal("decision error changed the model status")
			}
			assertRuntimeTrace(t, r)
		})
	}
	t.Run("terminal-condition-not-met", func(t *testing.T) {
		ctx := testContext(t)
		e := startWorkflow(t, ctx, newFixtureWorkflow(t, "minimal"))
		awaitSuccess(t, ctx, e)
		for _, stop := range []bool{false, true} {
			if stop {
				e.Stop()
			}
			r, err := e.WaitFor(ctx, func(State) bool { return false })
			if !errors.Is(err, ErrConditionNotMet) || errors.Is(err, ErrStopped) || r.State.Status != "succeeded" {
				t.Fatalf("terminal predicate: %v", err)
			}
		}
	})
}
