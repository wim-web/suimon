package suimon

import (
	"context"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"sync/atomic"
	"testing"
)

func testWorkflowPersistence(t *testing.T, check runtimeCheck) {
	t.Run("lease-expires-during-claim-commit", func(t *testing.T) {
		w := newFixtureWorkflow(t, "minimal")
		w.Graph.Nodes[0].Kind.Retry.MaxAttempts = N(1)
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		w.Options.Commit = func(_ context.Context, s Snapshot) error {
			for _, event := range s.Events {
				if event.Op != nil && event.Op.Kind == "claim" {
					clock.Store(1003)
				}
			}
			return nil
		}
		var calls atomic.Int32
		bindingAt(&w, "work").Leaf = func(context.Context, *Task) (Values, error) {
			calls.Add(1)
			return Values{"out": "too-late"}, nil
		}
		r, err := w.Run(testContext(t))
		if !errors.Is(err, ErrBlocked) || value(r.State.Reason, "") != "LEASE_EXPIRED" || calls.Load() != 0 {
			t.Fatalf("started with an expired lease: calls=%d error=%v", calls.Load(), err)
		}
		check(t, r)
	})
	t.Run("atomic-file-and-terminal-restore", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		store := SnapshotFile{Path: filepath.Join(t.TempDir(), "checkpoint.json")}
		w.Options.Commit = store.Save
		var calls atomic.Int32
		bindingAt(&w, "work").Leaf = func(context.Context, *Task) (Values, error) { calls.Add(1); return Values{"out": "persisted"}, nil }
		result, err := w.Run(ctx)
		if err != nil {
			t.Fatal(err)
		}
		saved, err := store.Load(ctx)
		if err != nil {
			t.Fatal(err)
		}
		assertJSON(t, "saved snapshot", saved, result.Snapshot)
		resumed, err := w.Resume(ctx, saved)
		if err != nil {
			t.Fatal(err)
		}
		assertJSON(t, "terminal restore", resumed, result)
		if calls.Load() != 1 {
			t.Fatal("successful work was executed again")
		}
		check(t, resumed)
		cancelled, cancel := context.WithCancel(ctx)
		cancel()
		if err := store.Save(cancelled, Snapshot{}); !errors.Is(err, context.Canceled) {
			t.Fatal(err)
		}
		unchanged, err := store.Load(ctx)
		if err != nil {
			t.Fatal(err)
		}
		assertJSON(t, "cancelled save", unchanged, saved)
		bad, err := copySnapshot(saved)
		if err != nil {
			t.Fatal(err)
		}
		for id := range bad.Values {
			delete(bad.Values, id)
			break
		}
		if _, err := w.Restore(ctx, bad); err == nil {
			t.Fatal("missing payload accepted")
		}
		bad, err = copySnapshot(saved)
		if err != nil {
			t.Fatal(err)
		}
		bad.Events[0].Data = []byte(`{"extra":true}`)
		if _, err := w.Restore(ctx, bad); err == nil {
			t.Fatal("corrupt journal accepted")
		}
		other := w
		other.Graph = cloneGraph(w.Graph)
		other.Graph.Nodes[0].Kind.Concurrency = N(99)
		if _, err := other.Restore(ctx, saved); err == nil {
			t.Fatal("different graph accepted")
		}
		if err := os.WriteFile(store.Path, []byte(`{"events":`), 0600); err != nil {
			t.Fatal(err)
		}
		if _, err := store.Load(ctx); err == nil {
			t.Fatal("torn checkpoint JSON accepted")
		}
	})
	t.Run("failed-commit-is-not-published", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		var persisted Snapshot
		commits := 0
		calls := atomic.Int32{}
		bindingAt(&w, "work").Leaf = func(context.Context, *Task) (Values, error) { calls.Add(1); return Values{"out": "ok"}, nil }
		w.Options.Commit = func(_ context.Context, s Snapshot) error {
			commits++
			if commits == 2 {
				return fmt.Errorf("disk full")
			}
			persisted = s
			return nil
		}
		r, err := w.Run(ctx)
		var commitErr *CommitError
		if !errors.As(err, &commitErr) {
			t.Fatalf("want commit error: %v", err)
		}
		if !r.State.Started || len(r.State.Instances) != 0 || calls.Load() != 0 {
			t.Fatal("uncommitted activation escaped")
		}
		assertJSON(t, "last durable snapshot", r.Snapshot, persisted)
		check(t, r)
		w.Options.Commit = nil
		resumed, err := w.Resume(ctx, persisted)
		if err != nil {
			t.Fatal(err)
		}
		if calls.Load() != 1 {
			t.Fatal("resumed work count")
		}
		check(t, resumed)
	})
	t.Run("stream-recovery-and-torn-tail", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "streaming")
		w.Options.DisableAutoRenew = true
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		var mu sync.Mutex
		calls := map[string]int{}
		bindingAt(&w, "emit").Leaf = func(ctx context.Context, task *Task) (Values, error) {
			if err := task.Emit("out", "one", "one"); err != nil {
				return nil, err
			}
			if task.Attempt == N(1) {
				<-ctx.Done()
				return nil, ctx.Err()
			}
			if err := task.Emit("out", "two", "two"); err != nil {
				return nil, err
			}
			return Values{}, nil
		}
		bindingAt(&w, "each", "work").Leaf = func(_ context.Context, task *Task) (Values, error) {
			var input string
			if err := task.DecodeInput("in", &input); err != nil {
				return nil, err
			}
			mu.Lock()
			calls[input]++
			mu.Unlock()
			return Values{"out": "mapped-" + input}, nil
		}
		e := startWorkflow(t, ctx, w)
		before := awaitState(t, ctx, e, func(s State) bool {
			return anyOf(s.Instances, func(i Instance) bool { return i.Node == "work" && i.Status == "succeeded" })
		})
		e.Stop()
		before = e.Result()
		if before.State.Status != "running" {
			t.Fatal("suspension changed model status")
		}
		snapshot := before.Snapshot
		producer := before.State.NodeInstance(nil, "emit")
		lease := producer.Lease
		auth := Credentials{producer.ID, lease.Attempt, lease.Token, N(1001)}
		_, tail, rejected := RecordTransaction(before.State, []Op{{Kind: "renew", Auth: auth}}, natLen(snapshot.Events).Inc(), "torn", snapshot.Events[len(snapshot.Events)-1].RecordedAt)
		if rejected != nil {
			t.Fatal(rejected)
		}
		snapshot.Events = append(snapshot.Events, tail[:len(tail)-1]...)
		clock.Store(1003)
		restored, err := w.Restore(ctx, snapshot)
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(restored.Stop)
		awaitState(t, ctx, restored, func(s State) bool { i := s.NodeInstance(nil, "emit"); return i != nil && i.Status == "retryWait" })
		clock.Store(1004)
		after := awaitSuccess(t, ctx, restored)
		mu.Lock()
		if calls["one"] != 1 || calls["two"] != 1 {
			t.Errorf("successful child replayed: %v", calls)
		}
		mu.Unlock()
		for _, event := range after.Snapshot.Events {
			if event.Txn == "torn" {
				t.Fatal("uncommitted tail retained")
			}
		}
		var outputs []string
		if err := after.Output("collect", "out")[0].Decode(&outputs); err != nil {
			t.Fatal(err)
		}
		assertJSON(t, "restored stream values", outputs, []string{"mapped-one", "mapped-two"})
		check(t, after)
	})
}

func testWorkflowOracleAndFailures(t *testing.T, check runtimeCheck) {
	t.Run("stream-completeness", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "streaming")
		w.Options.Oracle = &ScopedOracle{Leaf: func(path Path, node string, _ List[[2]string]) List[Output] {
			if node == "emit" {
				return List[Output]{{"out", List[string]{StreamItemID(path, node, "out", "0"), StreamItemID(path, node, "out", "1")}}}
			}
			return List[Output]{{"out", List[string]{PlainItemID(path, node, "out")}}}
		}}
		bindingAt(&w, "emit").Leaf = func(_ context.Context, task *Task) (Values, error) {
			if err := task.Emit("out", "0", "only-first"); err != nil {
				return nil, err
			}
			return Values{}, nil
		}
		r, err := w.Run(ctx)
		if !errors.Is(err, ErrBlocked) || value(r.State.Reason, "") != "ORACLE_MISMATCH" {
			t.Fatalf("truncated successful stream: %v/%v", err, r.State.Reason)
		}
		check(t, r)
	})
	t.Run("retry-may-retain-committed-prefix", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "streaming")
		var clock atomic.Uint64
		clock.Store(1000)
		w.Options.Now = func() Nat { return N(clock.Load()) }
		w.Options.Oracle = &ScopedOracle{Leaf: func(path Path, node string, _ List[[2]string]) List[Output] {
			if node == "emit" {
				return List[Output]{{"out", List[string]{StreamItemID(path, node, "out", "one")}}}
			}
			return List[Output]{{"out", List[string]{PlainItemID(path, node, "out")}}}
		}}
		bindingAt(&w, "emit").Leaf = func(_ context.Context, task *Task) (Values, error) {
			if task.Attempt == N(1) {
				if err := task.Emit("out", "one", "one"); err != nil {
					return nil, err
				}
				return nil, &TaskError{Code: "TRANSIENT", Retryable: true}
			}
			return Values{}, nil
		}
		e := startWorkflow(t, ctx, w)
		awaitState(t, ctx, e, func(s State) bool { i := s.NodeInstance(nil, "emit"); return i != nil && i.Status == "retryWait" })
		clock.Store(1001)
		r := awaitSuccess(t, ctx, e)
		check(t, r)
	})
	for _, tc := range []struct {
		name, code string
		handler    Handler
	}{
		{"handler-panic", "HANDLER_PANIC", func(context.Context, *Task) (Values, error) { panic("broken worker") }},
		{"missing-output", "OUTPUT_MISMATCH", func(context.Context, *Task) (Values, error) { return Values{}, nil }},
		{"invalid-payload", "INVALID_VALUE", func(context.Context, *Task) (Values, error) { return Values{"out": make(chan int)}, nil }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			w := newFixtureWorkflow(t, "minimal")
			bindingAt(&w, "work").Leaf = tc.handler
			r, err := w.Run(testContext(t))
			if !errors.Is(err, ErrBlocked) || value(r.State.Reason, "") != tc.code {
				t.Fatalf("%s: %v/%v", tc.name, err, r.State.Reason)
			}
			check(t, r)
		})
	}
	t.Run("decision-errors", func(t *testing.T) {
		w := newFixtureWorkflow(t, "branch")
		bindingAt(&w, "choose").Branch = func(context.Context, DecisionTask) (string, error) { return "", fmt.Errorf("decision unavailable") }
		r, err := w.Run(testContext(t))
		if err == nil || err.Error() != "decision unavailable" {
			t.Fatalf("decision error lost: %v", err)
		}
		check(t, r)
	})
	t.Run("binding-validation", func(t *testing.T) {
		w := newFixtureWorkflow(t, "minimal")
		w.Bindings = nil
		if _, err := w.Start(testContext(t)); err == nil {
			t.Fatal("missing handler accepted")
		}
		w = newFixtureWorkflow(t, "minimal")
		w.Bindings = append(w.Bindings, w.Bindings[0])
		if _, err := w.Start(testContext(t)); err == nil {
			t.Fatal("duplicate handler accepted")
		}
		w = newFixtureWorkflow(t, "minimal")
		w.Inputs = nil
		if _, err := w.Start(testContext(t)); err == nil {
			t.Fatal("missing input accepted")
		}
	})
}
