package suimon

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"slices"
	"sync"
	"testing"
)

func readSnapshotDelta(t *testing.T, update ExecutionUpdate, after SnapshotCursor) SnapshotDelta {
	t.Helper()
	delta, err := update.SnapshotSince(after)
	if err != nil {
		t.Fatal(err)
	}
	return delta
}

func appendSnapshotDelta(t *testing.T, snapshot *Snapshot, delta SnapshotDelta) {
	t.Helper()
	if delta.Graph != nil {
		snapshot.Graph = *delta.Graph
	}
	for _, event := range delta.Events {
		if event.Sequence != N(uint64(len(snapshot.Events)+1)) {
			t.Fatal("event gap or duplicate")
		}
		snapshot.Events = append(snapshot.Events, event)
	}
	if snapshot.Values == nil {
		snapshot.Values = map[string]json.RawMessage{}
	}
	for id, data := range delta.Values {
		if _, exists := snapshot.Values[id]; exists {
			t.Fatalf("value %s was sent twice", id)
		}
		snapshot.Values[id] = data
	}
	if delta.Cursor.EventCount() != len(snapshot.Events) {
		t.Fatal("cursor does not match received events")
	}
	if _, diagnostic := Check(snapshot.Graph, snapshot.Events); diagnostic != nil {
		t.Fatal(diagnostic)
	}
}

func TestWorkflowSnapshotSince(t *testing.T) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "minimal")
	started, finish := make(chan struct{}), make(chan struct{})
	bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
		close(started)
		select {
		case <-finish:
			return Values{"out": "done"}, nil
		case <-ctx.Done():
			return nil, ctx.Err()
		}
	}
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	first := e.Observe()
	firstCount := first.EventCount()
	var snapshot Snapshot
	delta := readSnapshotDelta(t, first, SnapshotCursor{})
	appendSnapshotDelta(t, &snapshot, delta)
	copies := e.metrics.results.Load()
	for i := range 8 {
		id := fmt.Sprintf("reserved-%d", i)
		if err := e.Apply(ctx, Op{Kind: "idle"}, Values{id: i}); err != nil {
			t.Fatal(err)
		}
		update := e.Observe()
		delta = readSnapshotDelta(t, update, delta.Cursor)
		if delta.Graph != nil || len(delta.Values) != 1 || string(delta.Values[id]) != fmt.Sprint(i) {
			t.Fatalf("expected only the new value: %+v", delta)
		}
		appendSnapshotDelta(t, &snapshot, delta)
		// The exact observation is immutable, even if later commits occur.
		idle := readSnapshotDelta(t, update, delta.Cursor)
		if idle.Graph != nil || len(idle.Events) != 0 || len(idle.Values) != 0 {
			t.Fatal("unchanged observation copied data")
		}
	}
	// Identical redelivery adds journal records, but never republishes a value.
	if err := e.Apply(ctx, Op{Kind: "idle"}, Values{"reserved-0": 0}); err != nil {
		t.Fatal(err)
	}
	delta = readSnapshotDelta(t, e.Observe(), delta.Cursor)
	if len(delta.Events) == 0 || len(delta.Values) != 0 {
		t.Fatal("value redelivery was not deduplicated")
	}
	appendSnapshotDelta(t, &snapshot, delta)
	if first.EventCount() != firstCount || readSnapshotDelta(t, first, SnapshotCursor{}).Cursor.EventCount() != firstCount {
		t.Fatal("old observation changed after publication")
	}
	if e.metrics.results.Load() != copies {
		t.Fatal("delta reads copied full results")
	}
	close(finish)
	result := awaitSuccess(t, ctx, e)
	update := e.Observe()
	appendSnapshotDelta(t, &snapshot, readSnapshotDelta(t, update, delta.Cursor))
	assertJSON(t, "reconstructed snapshot", snapshot, result.Snapshot)
	copies = e.metrics.results.Load()
	assertJSON(t, "outputs without Result", update.Outputs(), result.Outputs)
	if e.metrics.results.Load() != copies {
		t.Fatal("output-only read copied the complete result")
	}
	assertRuntimeTrace(t, result)
}

func TestWorkflowSnapshotDeltaIsolation(t *testing.T) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "streaming")
	started := make(chan struct{})
	bindingAt(&w, "emit").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
		close(started)
		<-ctx.Done()
		return nil, ctx.Err()
	}
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	u := e.Observe()
	delta := readSnapshotDelta(t, u, SnapshotCursor{})
	want := u.Result().Snapshot
	delta.Graph.Nodes[0].ID = "changed"
	delta.Graph.Nodes[1].Kind.Body.Nodes[0].ID = "changed-child"
	for i := range delta.Events {
		event := &delta.Events[i]
		if len(event.Data) > 0 {
			event.Data[0] = '!'
		}
		if event.Op != nil {
			event.Op.Kind = "changed-op"
			for j := range event.Op.Inputs {
				if len(event.Op.Inputs[j].Items) > 0 {
					event.Op.Inputs[j].Items[0] = "changed-input"
				}
			}
		}
	}
	for id, data := range delta.Values {
		data[0] = '!'
		delete(delta.Values, id)
	}
	assertJSON(t, "delta mutation cannot reach runtime", u.Result().Snapshot, want)
	again := readSnapshotDelta(t, u, SnapshotCursor{})
	assertJSON(t, "later delta is still pristine", Snapshot{*again.Graph, again.Events, again.Values}, want)

	completed, err := newFixtureWorkflow(t, "minimal").Start(ctx)
	if err != nil {
		t.Fatal(err)
	}
	defer completed.Stop()
	awaitSuccess(t, ctx, completed)
	end := completed.Observe()
	ports := end.Outputs()
	ports[0].Items[0].Value[0] = '!'
	ports[0].Port.Node = "changed"
	assertJSON(t, "output copies are independent", end.Outputs(), end.Result().Outputs)
}

func TestWorkflowSnapshotDeltaCommitBoundary(t *testing.T) {
	for _, fail := range []bool{false, true} {
		t.Run(fmt.Sprint("fail=", fail), func(t *testing.T) {
			ctx := testContext(t)
			w := newFixtureWorkflow(t, "minimal")
			started, persisting, release := make(chan struct{}), make(chan struct{}), make(chan struct{})
			var releaseOnce sync.Once
			unblock := func() { releaseOnce.Do(func() { close(release) }) }
			injected := errors.New("storage failed")
			bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
				close(started)
				<-ctx.Done()
				return nil, ctx.Err()
			}
			w.Options.Append = func(ctx context.Context, batch CommitBatch) error {
				if batch.Values["candidate"] == nil {
					return nil
				}
				close(persisting)
				select {
				case <-release:
					if fail {
						return injected
					}
					return nil
				case <-ctx.Done():
					return ctx.Err()
				}
			}
			e := startWorkflow(t, ctx, w)
			t.Cleanup(unblock)
			receive(t, ctx, started)
			applied := make(chan error, 1)
			go func() { applied <- e.Apply(ctx, Op{Kind: "idle"}, Values{"candidate": "new"}) }()
			receive(t, ctx, persisting)
			before := e.Observe()
			baseline := readSnapshotDelta(t, before, SnapshotCursor{})
			if _, exists := baseline.Values["candidate"]; exists {
				t.Fatal("uncommitted value became visible")
			}
			unblock()
			err := receive(t, ctx, applied)
			if (err != nil) != fail || fail && !errors.Is(err, injected) {
				t.Fatalf("unexpected append result: %v", err)
			}
			delta := readSnapshotDelta(t, e.Observe(), baseline.Cursor)
			if fail {
				if len(delta.Events) != 0 || len(delta.Values) != 0 {
					t.Fatal("failed commit advanced the public cursor")
				}
			} else if len(delta.Events) == 0 || string(delta.Values["candidate"]) != `"new"` {
				t.Fatal("successful commit missing from delta")
			}
			if len(readSnapshotDelta(t, before, baseline.Cursor).Events) != 0 {
				t.Fatal("old observation read across its commit boundary")
			}
		})
	}
}

func TestWorkflowSnapshotDeltaRestoreAndCursors(t *testing.T) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "minimal")
	started := make(chan struct{}, 2)
	bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) {
		started <- struct{}{}
		<-ctx.Done()
		return nil, ctx.Err()
	}
	e := startWorkflow(t, ctx, w)
	receive(t, ctx, started)
	if err := e.Apply(ctx, Op{Kind: "idle"}, Values{"reserved": "ahead of use"}); err != nil {
		t.Fatal(err)
	}
	e.Stop()
	base := e.Result()
	old := readSnapshotDelta(t, e.Observe(), SnapshotCursor{}).Cursor
	for _, torn := range []bool{false, true} {
		t.Run(fmt.Sprint("torn=", torn), func(t *testing.T) {
			snapshot, err := copySnapshot(base.Snapshot)
			if err != nil {
				t.Fatal(err)
			}
			if torn {
				_, tail, reject := RecordTransaction(base.State, []Op{{Kind: "idle"}}, natLen(snapshot.Events).Inc(), "uncommitted-tail", base.State.Now)
				if reject != nil {
					t.Fatal(reject)
				}
				snapshot.Events = append(snapshot.Events, tail[:len(tail)-1]...)
				snapshot.Values["uncommitted"] = json.RawMessage(`"discard"`)
			}
			restored, err := w.Restore(ctx, snapshot)
			if err != nil {
				t.Fatal(err)
			}
			defer restored.Stop()
			u := restored.Observe()
			delta := readSnapshotDelta(t, u, SnapshotCursor{})
			if len(delta.Events) < len(base.Snapshot.Events) || delta.Values["uncommitted"] != nil || slices.ContainsFunc(delta.Events, func(e Event) bool { return e.Txn == "uncommitted-tail" }) {
				t.Fatal("restore lost committed history or exposed a torn suffix")
			}
			if (delta.Values["reserved"] == nil) != torn {
				t.Fatal("restored value prefix does not follow snapshot recovery rules")
			}
			assertJSON(t, "restored baseline", Snapshot{*delta.Graph, delta.Events, delta.Values}, u.Result().Snapshot)
			for _, bad := range []SnapshotCursor{old, {execution: restored, events: u.EventCount() + 1}, {execution: restored, values: len(u.view.valueIDs) + 1}, {execution: restored, events: -1}, {events: 1}} {
				if _, err := u.SnapshotSince(bad); !errors.Is(err, ErrInvalidSnapshotCursor) {
					t.Fatalf("invalid cursor accepted: %+v: %v", bad, err)
				}
			}
			if err := restored.Apply(ctx, Op{Kind: "idle"}, Values{"later": 42}); err != nil {
				t.Fatal(err)
			}
			next := readSnapshotDelta(t, restored.Observe(), delta.Cursor)
			if next.Graph != nil || len(next.Values) != 1 || string(next.Values["later"]) != "42" {
				t.Fatal("restored baseline was retransmitted")
			}
			if _, err := u.SnapshotSince(next.Cursor); !errors.Is(err, ErrInvalidSnapshotCursor) {
				t.Fatal("future cursor accepted by an older observation")
			}
		})
	}
	if _, err := (ExecutionUpdate{}).SnapshotSince(SnapshotCursor{}); !errors.Is(err, ErrInvalidSnapshotCursor) {
		t.Fatal("empty update accepted")
	}
}

func TestWorkflowSnapshotDeltaConcurrentObservers(t *testing.T) {
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
	finished := make(chan struct{})
	var readers sync.WaitGroup
	for range 4 {
		readers.Add(1)
		go func() {
			defer readers.Done()
			var cursor SnapshotCursor
			var snapshot Snapshot
			read := func() {
				delta := readSnapshotDelta(t, e.Observe(), cursor)
				appendSnapshotDelta(t, &snapshot, delta)
				cursor = delta.Cursor
			}
			for range 32 {
				read()
			}
			<-finished
			read()
			if string(snapshot.Values["v31"]) != "31" {
				t.Error("concurrent observer missed the final value")
			}
		}()
	}
	for i := range 32 {
		if err := e.Apply(ctx, Op{Kind: "idle"}, Values{fmt.Sprintf("v%d", i): i}); err != nil {
			t.Fatal(err)
		}
	}
	close(finished)
	readers.Wait()
}

func benchmarkDeltaView(count int) (ExecutionUpdate, SnapshotCursor) {
	v := &runtimeView{snapshot: Snapshot{Values: make(map[string]json.RawMessage, count)}}
	for i := range count {
		id := fmt.Sprint(i)
		v.valueIDs = append(v.valueIDs, id)
		v.snapshot.Values[id] = json.RawMessage(`{"value":"payload"}`)
		v.snapshot.Events = append(v.snapshot.Events, Event{SchemaVersion: N(2), Sequence: N(uint64(i + 1)), Type: "transaction.committed", Data: json.RawMessage(`{}`)})
	}
	e := &Execution{view: v}
	return ExecutionUpdate{execution: e, view: v}, SnapshotCursor{execution: e, events: count - 1, values: count - 1}
}

func TestWorkflowSnapshotDeltaIdleAllocations(t *testing.T) {
	u, _ := benchmarkDeltaView(10000)
	cursor := SnapshotCursor{execution: u.execution, events: u.EventCount(), values: len(u.view.valueIDs)}
	if allocations := testing.AllocsPerRun(100, func() {
		delta, err := u.SnapshotSince(cursor)
		if err != nil || len(delta.Events) != 0 || len(delta.Values) != 0 || delta.Graph != nil {
			panic("unexpected idle delta")
		}
	}); allocations != 0 {
		t.Fatalf("unchanged prefix allocated %.0f objects", allocations)
	}
}

func BenchmarkWorkflowSnapshotDelta(b *testing.B) {
	for _, count := range []int{100, 10000, 100000} {
		u, after := benchmarkDeltaView(count)
		b.Run(fmt.Sprintf("history=%d/new=1", count), func(b *testing.B) {
			b.ReportAllocs()
			for range b.N {
				delta, err := u.SnapshotSince(after)
				if err != nil || len(delta.Events) != 1 || len(delta.Values) != 1 {
					b.Fatal("invalid suffix")
				}
			}
		})
		after = SnapshotCursor{execution: u.execution, events: count, values: count}
		b.Run(fmt.Sprintf("history=%d/unchanged", count), func(b *testing.B) {
			b.ReportAllocs()
			for range b.N {
				if _, err := u.SnapshotSince(after); err != nil {
					b.Fatal(err)
				}
			}
		})
	}
}
