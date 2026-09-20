package suimon

import (
	"context"
	"sync"
	"testing"
	"time"
)

// Observe completed runtime polls, rather than assuming how many polls fit in
// a wall-clock sleep. Wall time is only a timeout if the runtime stops polling.
func awaitRuntimePolls(t *testing.T, ctx context.Context, e *Execution, count uint64) {
	t.Helper()
	tick := time.NewTicker(time.Millisecond)
	defer tick.Stop()
	for e.metrics.polls.Load() < count {
		select {
		case <-tick.C:
		case <-ctx.Done():
			t.Fatal(ctx.Err())
		}
	}
}

func TestWorkflowIdlePolling(t *testing.T) {
	for _, fixture := range []string{"minimal", "streaming"} {
		t.Run(fixture, func(t *testing.T) {
			ctx := testContext(t)
			w := newFixtureWorkflow(t, fixture) // Fixed logical clock: no deadline can expire.
			w.Options.Workers = 1
			release, started := make(chan struct{}), make(chan struct{})
			var once sync.Once
			t.Cleanup(func() { once.Do(func() { close(release) }) })
			node := "work"
			if fixture == "streaming" {
				node = "emit"
			}
			bindingAt(&w, node).Leaf = func(ctx context.Context, task *Task) (Values, error) {
				out := Values{"out": "done"}
				if fixture == "streaming" {
					if err := task.Emit("out", "one", "one"); err != nil {
						return nil, err
					}
					out = Values{}
				}
				close(started)
				select {
				case <-release:
					return out, nil
				case <-ctx.Done():
					return nil, ctx.Err()
				}
			}
			e := startWorkflow(t, ctx, w)
			receive(t, ctx, started)
			awaitRuntimePolls(t, ctx, e, e.metrics.polls.Load()+3)
			if fixture == "streaming" {
				view, _, _, _ := e.observe()
				if !anyOf(view.state.Instances, func(i Instance) bool { return i.Node == "work" && i.Status == "ready" }) {
					t.Fatal("test did not block a ready consumer on worker capacity")
				}
			}
			type completed struct {
				result RunResult
				err    error
			}
			finished := make(chan completed, 1)
			go func() { r, err := e.Wait(ctx); finished <- completed{r, err} }()
			probes, copies := e.metrics.candidates.Load(), e.metrics.results.Load()
			awaitRuntimePolls(t, ctx, e, e.metrics.polls.Load()+5)
			if e.metrics.candidates.Load() != probes || e.metrics.results.Load() != copies {
				t.Fatalf("idle polling did work: probes %d -> %d, result copies %d -> %d", probes, e.metrics.candidates.Load(), copies, e.metrics.results.Load())
			}
			once.Do(func() { close(release) })
			r := receive(t, ctx, finished)
			if r.err != nil || !SucceededDrained(r.result.State) {
				t.Fatalf("job completion did not wake scheduler: %v", r.err)
			}
			assertRuntimeTrace(t, r.result)
		})
	}
}

func TestWorkflowResultIsolation(t *testing.T) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "minimal")
	started, finish := make(chan struct{}), make(chan struct{})
	bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
		close(started)
		select {
		case <-finish:
			return Values{"out": "good"}, nil
		case <-ctx.Done():
			return nil, ctx.Err()
		}
	}
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	original := e.Result()
	mutated := e.Result()
	mutated.State.Instances[0].Lease.Until = N(0)
	mutated.State.Instances[0].Inputs[0][1] = "bad"
	mutated.State.Frames[0].Graph.Nodes[0].Inputs[0].Name = "bad"
	mutated.State.Channels[0].Placed[0].Item = "bad"
	mutated.Snapshot.Graph.Nodes[0].Outputs[0].Name = "bad"
	mutated.Snapshot.Events[0].Op.Inputs[0].Items[0] = "bad"
	mutated.Snapshot.Events[0].Data[0] = 'x'
	for id := range mutated.Snapshot.Values {
		mutated.Snapshot.Values[id][0] = 'x'
	}
	assertJSON(t, "caller cannot mutate published state", e.Result(), original)
	close(finish)
	r := awaitSuccess(t, ctx, e)
	_, err := e.WaitFor(ctx, func(s State) bool {
		s.Receipts[0].Outputs[0].Items[0] = "bad"
		s.Frames[0].Graph.Nodes[0].Outputs[0].Name = "bad"
		return true
	})
	if err != nil {
		t.Fatal(err)
	}
	changed := e.Result()
	changed.Outputs[0].Items[0].Value[0] = 'x'
	changed.State.Receipts[0].Outputs[0].Items[0] = "bad"
	assertJSON(t, "predicate and returned output are isolated", e.Result(), r)
	assertRuntimeTrace(t, r)
}
