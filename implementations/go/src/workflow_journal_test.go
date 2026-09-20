package suimon

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"
)

func openTestJournal(t *testing.T, ctx context.Context, path string, graph Graph) (*JournalFile, Snapshot) {
	t.Helper()
	store, snapshot, err := OpenJournalFile(ctx, path, graph)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { store.Close() })
	return store, snapshot
}

func journalFrame(t *testing.T, batch CommitBatch) []byte {
	t.Helper()
	data, err := json.Marshal(batch)
	if err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	if err := writeJournalFrame(buf.Write, data); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

func TestWorkflowJournal(t *testing.T) {
	t.Run("deltas-and-growth", func(t *testing.T) {
		var previous int64
		for _, count := range []int{10, 40} {
			t.Run(fmt.Sprint(count), func(t *testing.T) {
				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
				defer cancel()
				w := newFixtureWorkflow(t, "streaming")
				bindingAt(&w, "emit").Leaf = func(_ context.Context, task *Task) (Values, error) {
					for n := 0; n < count; n++ {
						if err := task.Emit("out", fmt.Sprint(n), n); err != nil {
							return nil, err
						}
					}
					return Values{}, nil
				}
				path := filepath.Join(t.TempDir(), "run.journal")
				store, initial := openTestJournal(t, ctx, path, w.Graph)
				info, _ := store.file.Stat()
				written := info.Size()
				store.write = func(data []byte) (int, error) {
					n, err := store.file.Write(data)
					written += int64(n)
					return n, err
				}
				values, events := map[string]int{}, 0
				w.Options.Append = func(ctx context.Context, batch CommitBatch) error {
					events += len(batch.Events)
					for id := range batch.Values {
						values[id]++
					}
					if err := store.Append(ctx, batch); err != nil {
						return err
					}
					// Storage callbacks own their copies, never the engine's data.
					batch.Events[0].Data[0] = 'x'
					if batch.Events[0].Op != nil {
						batch.Events[0].Op.Kind = "corrupted-copy"
					}
					for _, v := range batch.Values {
						v[0] = 'x'
					}
					return nil
				}
				r, err := w.Resume(ctx, initial)
				if err != nil {
					t.Fatal(err)
				}
				if events != len(r.Snapshot.Events) || len(values) != len(r.Snapshot.Values) {
					t.Fatal("missing or duplicated deltas")
				}
				for id, copies := range values {
					if copies != 1 {
						t.Fatalf("value %s persisted %d times", id, copies)
					}
				}
				info, _ = store.file.Stat()
				if written != info.Size() {
					t.Fatalf("journal rewrote old bytes: written=%d size=%d", written, info.Size())
				}
				if previous != 0 && written > previous*6 {
					t.Fatalf("fourfold input grew writes excessively: %d -> %d", previous, written)
				}
				previous = written
				data, _ := json.Marshal(r.Snapshot)
				t.Logf("items=%d attempt_id_bytes=%d snapshot_bytes=%d cumulative_write_bytes=%d", count, len(r.State.Attempts[len(r.State.Attempts)-1].ID), len(data), written)
				store.Close()
				reopened, recovered := openTestJournal(t, ctx, path, w.Graph)
				assertJSON(t, "journal roundtrip", recovered, r.Snapshot)
				w.Options.Append = reopened.Append
				again, err := w.Resume(ctx, recovered)
				if err != nil {
					t.Fatal(err)
				}
				assertJSON(t, "terminal journal restore", again, r)
				assertRuntimeTrace(t, again)
			})
		}
	})
	t.Run("failed-append", func(t *testing.T) {
		for _, failure := range []string{"before-write", "partial-body", "sync-uncertain"} {
			t.Run(failure, func(t *testing.T) {
				ctx := testContext(t)
				w := newFixtureWorkflow(t, "minimal")
				path := filepath.Join(t.TempDir(), "run.journal")
				store, initial := openTestJournal(t, ctx, path, w.Graph)
				injected := errors.New("storage unavailable")
				calls, writes, syncs := 0, 0, 0
				bindingAt(&w, "work").Leaf = func(context.Context, *Task) (Values, error) { calls++; return Values{"out": "ok"}, nil }
				store.write = func(data []byte) (int, error) {
					writes++
					if failure == "partial-body" && writes == 4 {
						n, _ := store.file.Write(data[:len(data)/2])
						return n, injected
					}
					return store.file.Write(data)
				}
				store.syncFile = func() error {
					syncs++
					if err := store.file.Sync(); err != nil {
						return err
					}
					if failure == "sync-uncertain" && syncs == 2 {
						return injected // The write is present, but the acknowledgement failed.
					}
					return nil
				}
				w.Options.Append = func(ctx context.Context, batch CommitBatch) error {
					if failure == "before-write" && batch.Events[0].Op.Kind == "activate" {
						return injected
					}
					return store.Append(ctx, batch)
				}
				r, err := w.Resume(ctx, initial)
				var commit *CommitError
				if !errors.As(err, &commit) || !errors.Is(err, injected) || !r.State.Started || len(r.State.Instances) != 0 || calls != 0 {
					t.Fatalf("failed append was published: %v, calls=%d", err, calls)
				}
				if failure != "before-write" && !errors.Is(store.Append(ctx, CommitBatch{}), injected) {
					t.Fatal("uncertain writer allowed another append")
				}
				store.Close()
				store, recovered := openTestJournal(t, ctx, path, w.Graph)
				if failure == "sync-uncertain" {
					state, err := Recover(w.Graph, recovered.Events)
					if err != nil || len(state.Instances) != 1 || state.Instances[0].Status != "ready" {
						t.Fatalf("lost acknowledged-on-disk transaction: %v", err)
					}
				} else {
					assertJSON(t, "previous durable boundary", recovered, r.Snapshot)
				}
				w.Options.Append = store.Append
				after, err := w.Resume(ctx, recovered)
				if err != nil || calls != 1 {
					t.Fatalf("recovery: %v, calls=%d", err, calls)
				}
				assertRuntimeTrace(t, after)
			})
		}
	})
	t.Run("stream-recovery-and-torn-suffix", testJournalStreamRecovery)
	t.Run("retain-committed-values-before-first-use", func(t *testing.T) {
		ctx := testContext(t)
		w := newFixtureWorkflow(t, "minimal")
		bindingAt(&w, "work").Leaf = func(ctx context.Context, _ *Task) (Values, error) { <-ctx.Done(); return nil, ctx.Err() }
		path := filepath.Join(t.TempDir(), "run.journal")
		store, initial := openTestJournal(t, ctx, path, w.Graph)
		w.Options.Append = store.Append
		e, err := w.Restore(ctx, initial)
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(e.Stop)
		awaitState(t, ctx, e, func(s State) bool { return len(s.Attempts) == 1 })
		if err := e.Apply(ctx, Op{Kind: "idle"}, Values{"reserved": "original"}); err != nil {
			t.Fatal(err)
		}
		e.Stop()
		store.Close()
		store, recovered := openTestJournal(t, ctx, path, w.Graph)
		w.Options.Append = store.Append
		e, err = w.Restore(ctx, recovered)
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(e.Stop)
		err = e.Apply(ctx, Op{Kind: "idle"}, Values{"reserved": "changed"})
		var rejected *Reject
		if !errors.As(err, &rejected) || rejected.Code != "NONDETERMINISTIC_VALUE" {
			t.Fatalf("committed value forgotten across recovery: %v", err)
		}
		if string(e.Result().Snapshot.Values["reserved"]) != `"original"` {
			t.Fatal("reserved payload changed")
		}
		assertRuntimeTrace(t, e.Result())
	})
	t.Run("reject-corruption", testJournalCorruption)
	t.Run("mutually-exclusive-stores", func(t *testing.T) {
		w := newFixtureWorkflow(t, "minimal")
		w.Options.Commit = func(context.Context, Snapshot) error { t.Fatal("store was called"); return nil }
		w.Options.Append = func(context.Context, CommitBatch) error { t.Fatal("store was called"); return nil }
		if _, err := w.Start(testContext(t)); err == nil {
			t.Fatal("both storage callbacks accepted")
		}
	})
}

func testJournalStreamRecovery(t *testing.T) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "streaming")
	w.Graph.Nodes[0].Kind.Retry.RetrySeconds = N(0)
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
		return Values{"out": input}, nil
	}
	path := filepath.Join(t.TempDir(), "base.journal")
	store, initial := openTestJournal(t, ctx, path, w.Graph)
	w.Options.Append = store.Append
	e, err := w.Restore(ctx, initial)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(e.Stop)
	awaitState(t, ctx, e, func(s State) bool {
		return anyOf(s.Instances, func(i Instance) bool { return i.Node == "work" && i.Status == "succeeded" })
	})
	e.Stop()
	before := e.Result()
	store.Close()
	base, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	producer := before.State.NodeInstance(nil, "emit")
	lost := StreamItemID(nil, "emit", "out", "lost")
	_, events, rejected := RecordTransaction(before.State, []Op{{Kind: "emit", Auth: Credentials{producer.ID, producer.Lease.Attempt, producer.Lease.Token, N(1000)}, Port: "out", Item: lost}}, natLen(before.Snapshot.Events).Inc(), "uncommitted", N(1000))
	if rejected != nil {
		t.Fatal(rejected)
	}
	batch := CommitBatch{events, map[string]json.RawMessage{lost: json.RawMessage(`"lost"`)}}
	frame := journalFrame(t, batch)
	incomplete := batch
	incomplete.Events = incomplete.Events[:len(incomplete.Events)-1]
	suffixes := map[string][]byte{"short-header": frame[:7], "short-body": frame[:journalFrameHeader+12], "last-byte": frame[:len(frame)-1], "valid-uncommitted": journalFrame(t, incomplete)}
	for name, suffix := range suffixes {
		t.Run(name, func(t *testing.T) {
			ctx := testContext(t)
			path := filepath.Join(t.TempDir(), "recovered.journal")
			if err := os.WriteFile(path, append(bytes.Clone(base), suffix...), 0600); err != nil {
				t.Fatal(err)
			}
			store, recovered := openTestJournal(t, ctx, path, w.Graph)
			assertJSON(t, "only committed records and values recovered", recovered, before.Snapshot)
			info, _ := store.file.Stat()
			if info.Size() != int64(len(base)) {
				t.Fatal("uncommitted bytes retained")
			}
			restored := w
			restored.Options.Append = store.Append
			restored.Options.Now = func() Nat { return N(1003) }
			r, err := restored.Resume(ctx, recovered)
			if err != nil {
				t.Fatal(err)
			}
			var output []string
			if err := r.Output("collect", "out")[0].Decode(&output); err != nil {
				t.Fatal(err)
			}
			assertJSON(t, "resumed stream", output, []string{"one", "two"})
			mu.Lock()
			if calls["one"] != 1 {
				t.Errorf("successful body replayed: %v", calls)
			}
			mu.Unlock()
			assertRuntimeTrace(t, r)
			store.Close()
			_, loaded := openTestJournal(t, ctx, path, w.Graph)
			assertJSON(t, "append after tail removal", loaded, r.Snapshot)
		})
	}
}

func testJournalCorruption(t *testing.T) {
	ctx := testContext(t)
	w := newFixtureWorkflow(t, "minimal")
	path := filepath.Join(t.TempDir(), "header.journal")
	store, _ := openTestJournal(t, ctx, path, w.Graph)
	store.Close()
	header, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	input := w.Inputs[0].Items[0]
	_, events, rejected := RecordTransaction(Initial(w.Graph), []Op{{Kind: "start", Inputs: List[Input]{{w.Graph.Entries[0], List[string]{input.ID}}}}}, N(1), "start", N(1000))
	if rejected != nil {
		t.Fatal(rejected)
	}
	data, _ := encodeData(input.Value)
	batch := CommitBatch{events, map[string]json.RawMessage{input.ID: data}}
	frame := journalFrame(t, batch)
	badHash := bytes.Clone(frame)
	badHash[len(badHash)-2] ^= 1
	badLength := bytes.Clone(frame)
	badLength[7] ^= 1
	badEvents := CommitBatch{copyEvents(events), copyValues(batch.Values)}
	badEvents.Events[0].Sequence = N(99)
	missing := CommitBatch{events, map[string]json.RawMessage{}}
	badTail := CommitBatch{copyEvents(events[:len(events)-1]), copyValues(batch.Values)}
	badTail.Events[0].Sequence = N(99)
	for name, suffix := range map[string][]byte{"checksum": badHash, "length": badLength, "sequence": journalFrame(t, badEvents), "missing-value": journalFrame(t, missing), "invalid-uncommitted": journalFrame(t, badTail)} {
		t.Run(name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "corrupt.journal")
			corrupted := append(bytes.Clone(header), suffix...)
			if err := os.WriteFile(path, corrupted, 0600); err != nil {
				t.Fatal(err)
			}
			j, _, err := OpenJournalFile(ctx, path, w.Graph)
			if err == nil {
				j.Close()
				t.Fatal("corruption accepted")
			}
			unchanged, _ := os.ReadFile(path)
			if !bytes.Equal(unchanged, corrupted) {
				t.Fatal("corruption was silently truncated")
			}
		})
	}
	t.Run("wrong-graph-and-cancelled-open", func(t *testing.T) {
		g := cloneGraph(w.Graph)
		g.Nodes[0].Kind.Concurrency = N(9)
		if j, _, err := OpenJournalFile(ctx, path, g); err == nil {
			j.Close()
			t.Fatal("different graph accepted")
		}
		cancelled, cancel := context.WithCancel(ctx)
		cancel()
		if _, _, err := OpenJournalFile(cancelled, filepath.Join(t.TempDir(), "cancelled"), g); !errors.Is(err, context.Canceled) {
			t.Fatal(err)
		}
	})
	t.Run("reject-invalid-append-without-writing", func(t *testing.T) {
		store, _ := openTestJournal(t, ctx, path, w.Graph)
		before, _ := store.file.Seek(0, io.SeekCurrent)
		for _, invalid := range []CommitBatch{{}, badEvents, badTail} {
			if err := store.Append(ctx, invalid); err == nil {
				t.Fatal("invalid append accepted")
			}
		}
		if err := store.Append(ctx, batch); err != nil {
			t.Fatal(err)
		}
		if err := store.Append(ctx, batch); err == nil {
			t.Fatal("duplicate append accepted")
		}
		info, _ := store.file.Stat()
		if info.Size() != before+int64(len(frame)) {
			t.Fatal("rejected append wrote bytes")
		}
	})
}
