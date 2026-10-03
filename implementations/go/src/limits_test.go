package suimon

import (
	"context"
	"errors"
	"fmt"
	"iter"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

// An infinite producer feeds callbacks that wait for cancellation. Each input can instead
// create its own concurrency execution; limit=1 in each must not multiply the host budget.
func quotaEngine(t *testing.T, limits Limits, concurrency, blocked bool, overrides ...Binding) (*Definition, *Engine, *atomic.Int64) {
	t.Helper()
	definition := streamDefinition
	if concurrency {
		definition = strings.Replace(definition, `{"type": "function", "function": "double"}`, `{
		"type":"concurrency", "input":"Int", "limit":1, "output":"stream", "element":"Int",
		"tasks":[{"name":"double", "body":{"type":"function","function":"double"},
		"inputTransform":"int", "outputTransform":"int", "policy":"continue"}]}`, 1)
	}
	p, err := ParseDefinition([]byte(definition))
	if err != nil {
		t.Fatal(err)
	}
	active := &atomic.Int64{}
	bindings := []Binding{
		Stream("numbers", func(ctx context.Context, n int) iter.Seq2[int, error] {
			return func(yield func(int, error) bool) {
				active.Add(1)
				defer active.Add(-1)
				for i := 0; n < 0 || i < n; i++ {
					if !yield(i, nil) {
						return
					}
				}
			}
		}),
		Func("double", func(ctx context.Context, n int) (int, error) {
			active.Add(1)
			defer active.Add(-1)
			if blocked {
				<-ctx.Done()
				return 0, ctx.Err()
			}
			return 2 * n, nil
		}),
		Func("sum", func(_ context.Context, ns []int) (int, error) {
			total := 0
			for _, n := range ns {
				total += n
			}
			return total, nil
		}),
		Passthrough("int"), Passthrough("ints"),
	}
	for _, b := range overrides {
		bindings = replaceBinding(bindings, b)
	}
	e, err := NewEngine(p, mustRegistry(t, bindings...), WithLimits(limits))
	if err != nil {
		t.Fatal(err)
	}
	return p, e, active
}

func runQuota(t *testing.T, e *Engine, input int) (*Report, *memJournal) {
	t.Helper()
	j := newMemJournal("")
	x, err := e.Start(context.Background(), input, WithJournal(j))
	if err != nil {
		t.Fatal(err)
	}
	r, err := wait(t, x)
	if !errors.Is(err, ErrQuotaExceeded) || r == nil {
		t.Fatalf("Wait: report=%v, error=%v", r, err)
	}
	expectStatusOf(t, r, StatusCancelled)
	verifyJournal(t, e.definition, j.text(), r)
	c, err := Check(j.text(), sameDefinition(e.definition))
	if err != nil {
		t.Fatal(err)
	}
	var bytes, elements, tasks int64
	for _, v := range c.Values {
		bytes += int64(len(v.Payload))
	}
	for _, call := range r.State.Calls {
		elements += int64(call.Yields)
	}
	for _, execution := range r.State.Executions {
		tasks += int64(len(execution.Tasks))
	}
	if bytes > e.limits.MaxPayloadBytes || elements > e.limits.MaxStreamElements || tasks > e.limits.MaxTasks ||
		int64(len(r.State.Executions)) > e.limits.MaxExecutions || int64(len(j.text())) > e.limits.MaxJournalBytes ||
		int64(2*c.Committed) > e.limits.MaxRecords {
		t.Fatal("the terminal journal exceeds a quota")
	}
	// Replay every prefix to check the peak, including calls reserved before goroutines start.
	s := &State{}
	for _, op := range opsOf(t, j.text()) {
		s, err = Step(e.definition, s, op)
		if err != nil {
			t.Fatal(err)
		}
		var active int64
		for _, call := range s.Calls {
			if !call.Status.ended() {
				active++
			}
		}
		if active > e.limits.MaxCalls {
			t.Fatalf("active calls %d exceed %d", active, e.limits.MaxCalls)
		}
	}
	return r, j
}

func TestRuntimeQuotas(t *testing.T) {
	for _, tc := range []struct {
		name        string
		limits      Limits
		concurrency bool
	}{
		{"calls", Limits{MaxCalls: 4}, false},
		{"calls across executions", Limits{MaxCalls: 4}, true},
		{"executions", Limits{MaxExecutions: 3}, true},
		{"tasks", Limits{MaxTasks: 3}, true},
		{"elements", Limits{MaxStreamElements: 5}, false},
		{"payloads", Limits{MaxPayloadBytes: 12}, false},
		{"records", Limits{MaxRecords: 40}, false},
		{"journal bytes", Limits{MaxJournalBytes: 6000}, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			_, e, active := quotaEngine(t, tc.limits, tc.concurrency, true)
			r, j := runQuota(t, e, -1)
			if active.Load() != 0 {
				t.Fatal("Wait returned before callbacks exited")
			}
			x, err := e.Resume(context.Background(), j)
			if err != nil {
				t.Fatal(err)
			}
			replayed, err := wait(t, x)
			if err != nil || !replayed.State.Equal(r.State) {
				t.Fatalf("terminal Resume: %v", err)
			}
		})
	}
}

func TestQuotaAggregatePayload(t *testing.T) {
	_, baseline, _ := quotaEngine(t, Limits{}, false, false)
	j := newMemJournal("")
	if _, err := baseline.Run(context.Background(), 3, WithJournal(j)); err != nil {
		t.Fatal(err)
	}
	c, err := Check(j.text(), sameDefinition(baseline.definition))
	if err != nil {
		t.Fatal(err)
	}
	var limit int64
	for _, v := range c.Values {
		limit += int64(len(v.Payload))
		if strings.HasPrefix(v.Payload, "[") {
			break
		}
	}
	_, e, _ := quotaEngine(t, Limits{MaxPayloadBytes: limit - 1}, false, false)
	_, limited := runQuota(t, e, 3)
	for _, op := range opsOf(t, limited.text()) {
		if settle, ok := op.(OpSettle); ok && settle.Placement == "all" {
			t.Fatal("oversized list was accepted")
		}
	}
}

func TestQuotaDurationAndEngineAdmission(t *testing.T) {
	_, e, active := quotaEngine(t, Limits{MaxWorkflows: 1, MaxDuration: 100 * time.Millisecond}, false, true)
	x, err := e.Start(context.Background(), 1)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := e.Start(context.Background(), 1); !errors.Is(err, ErrQuotaExceeded) {
		t.Fatalf("concurrent Start: %v", err)
	}
	if _, err := e.Resume(context.Background(), newMemJournal("")); !errors.Is(err, ErrQuotaExceeded) {
		t.Fatalf("concurrent Resume: %v", err)
	}
	if r, err := wait(t, x); !errors.Is(err, ErrQuotaExceeded) || r == nil {
		t.Fatalf("deadline: %v", err)
	}
	if active.Load() != 0 {
		t.Fatal("callbacks did not exit")
	}
	// Wait makes the admission slot available, including when Start itself failed.
	if _, err := e.Start(context.Background(), make(chan int)); err == nil {
		t.Fatal("bad input accepted")
	}
	x, err = e.Start(context.Background(), 0)
	if err != nil {
		t.Fatal(err)
	}
	if _, err = wait(t, x); err != nil {
		t.Fatal(err)
	}
}

func TestQuotaOversizedStartAndResume(t *testing.T) {
	_, e, _ := quotaEngine(t, Limits{MaxPayloadBytes: 1}, false, false)
	j := newMemJournal("")
	if _, err := e.Start(context.Background(), 100, WithJournal(j)); !errors.Is(err, ErrQuotaExceeded) {
		t.Fatalf("input: %v", err)
	}
	if j.text() != "" {
		t.Fatal("Start wrote an oversized input")
	}
	_, small, _ := quotaEngine(t, Limits{MaxJournalBytes: 10}, false, false)
	if _, err := small.Resume(context.Background(), newMemJournal(strings.Repeat("x", 11))); !errors.Is(err, ErrQuotaExceeded) {
		t.Fatalf("Resume: %v", err)
	}
	path := filepath.Join(t.TempDir(), "journal")
	if err := os.WriteFile(path, []byte(strings.Repeat("x", 11)), 0600); err != nil {
		t.Fatal(err)
	}
	file, err := OpenJournal(path)
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()
	if _, err = small.Resume(context.Background(), file); !errors.Is(err, ErrQuotaExceeded) {
		t.Fatalf("file Resume: %v", err)
	}
}

func TestConformanceQuotas(t *testing.T) {
	cli := leanCLI(t)
	p, e, _ := quotaEngine(t, Limits{MaxCalls: 4}, true, true)
	r, j := runQuota(t, e, -1)
	leanAgrees(t, cli, t.TempDir(), p, j.text(), r.State)
}

// journalBefore returns the committed prefix before the first matching operation.
func journalBefore(t *testing.T, journal string, match func(Op) bool) string {
	t.Helper()
	lines := strings.SplitAfter(journal, "\n")
	for i, line := range lines[1:] {
		if strings.TrimSpace(line) == "" {
			continue
		}
		r, err := DecodeRecord(strings.TrimSuffix(line, "\n"))
		if err != nil {
			t.Fatal(err)
		}
		if !r.Commit && match(r.Op) {
			return strings.Join(lines[:i+1], "")
		}
	}
	t.Fatal("operation missing from journal")
	return ""
}

func TestQuotaResumeCountsRetainedPayloads(t *testing.T) {
	_, baseline, _ := quotaEngine(t, Limits{}, false, false)
	j := newMemJournal("")
	if _, err := baseline.Run(context.Background(), 3, WithJournal(j)); err != nil {
		t.Fatal(err)
	}
	prefix := journalBefore(t, j.text(), func(op Op) bool { s, ok := op.(OpSettle); return ok && s.Placement == "all" })
	c, err := Check(prefix, sameDefinition(baseline.definition))
	if err != nil {
		t.Fatal(err)
	}
	var retained int64
	for _, v := range c.Values {
		retained += int64(len(v.Payload))
	}
	_, e, _ := quotaEngine(t, Limits{MaxPayloadBytes: retained}, false, false)
	resumed := newMemJournal(prefix)
	x, err := e.Resume(context.Background(), resumed)
	if err != nil {
		t.Fatal(err)
	}
	r, err := wait(t, x)
	if !errors.Is(err, ErrQuotaExceeded) || r == nil {
		t.Fatalf("resumed payload quota: %v", err)
	}
	verifyJournal(t, e.definition, resumed.text(), r)
}

func TestQuotaShutdownReserveAndRecovery(t *testing.T) {
	for _, records := range []int64{6, 8, 10, 20, 40} {
		t.Run(fmt.Sprint(records), func(t *testing.T) {
			_, e, _ := quotaEngine(t, Limits{MaxRecords: records}, false, true)
			_, j := runQuota(t, e, -1)
			// Crash after cancellation, before any call termination or conclusion.
			prefix := journalBefore(t, j.text(), func(op Op) bool {
				switch op.(type) {
				case OpTerminated, OpConclude:
					return true
				}
				return false
			})
			resumed := newMemJournal(prefix)
			x, err := e.Resume(context.Background(), resumed)
			if err != nil {
				t.Fatal(err)
			}
			r, err := wait(t, x)
			if err != nil {
				t.Fatal(err)
			}
			expectStatusOf(t, r, StatusCancelled)
			verifyJournal(t, e.definition, resumed.text(), r)
			if int64(len(recordLines(resumed.text()))) > records {
				t.Fatal("recovery consumed shutdown reserve twice")
			}
		})
	}
}

func TestQuotaExactStreamLimitSucceeds(t *testing.T) {
	_, e, _ := quotaEngine(t, Limits{MaxStreamElements: 3}, false, false)
	if r, err := e.Run(context.Background(), 3); err != nil || r.Status != StatusSucceeded {
		t.Fatalf("exact quota: %v", err)
	}
}

func TestQuotaOptions(t *testing.T) {
	for _, limits := range []Limits{{MaxCalls: -1}, {MaxDuration: -1}} {
		if _, err := engineLimits([]EngineOption{WithLimits(limits)}); err == nil {
			t.Fatal("negative quota accepted")
		}
	}
	l, err := engineLimits([]EngineOption{WithLimits(Limits{MaxCalls: 2})})
	if err != nil || l.MaxCalls != 2 || l.MaxPayloadBytes != DefaultLimits().MaxPayloadBytes {
		t.Fatal("partial override lost defaults")
	}
}

func TestQuotaAdmissionLeavesMachineUnchanged(t *testing.T) {
	refused := errors.New("admission refused")
	for _, name := range []string{"users", "merge", "branch", "fanout", "limit"} {
		t.Run(name, func(t *testing.T) {
			p, journal, _ := runOnce(t, scenarioNamed(t, name))
			m := newMachine(p, p.derive(), &State{})
			for _, op := range opsOf(t, journal) {
				before := cloneState(m.s)
				if _, err := m.applyAdmitted(op, func(*string) error { return refused }); !errors.Is(err, refused) {
					t.Fatalf("%s admission: %v", EncodeOp(op), err)
				}
				if !m.s.Equal(before) {
					t.Fatalf("%s mutated before admission", EncodeOp(op))
				}
				checkMachine(t, EncodeOp(op), m)
				if _, err := m.apply(op); err != nil {
					t.Fatal(err)
				}
			}
		})
	}
}

func TestQuotaCallbackOutputs(t *testing.T) {
	for _, stream := range []bool{false, true} {
		t.Run(fmt.Sprint(stream), func(t *testing.T) {
			var finished atomic.Bool
			b := Func("double", func(context.Context, int) (string, error) {
				defer finished.Store(true)
				return strings.Repeat("x", 100), nil
			})
			if stream {
				b = Stream("numbers", func(context.Context, int) iter.Seq2[string, error] {
					return func(yield func(string, error) bool) { defer finished.Store(true); yield(strings.Repeat("x", 100), nil) }
				})
			}
			_, e, _ := quotaEngine(t, Limits{MaxPayloadBytes: 20}, false, false, b)
			r, _ := runQuota(t, e, 1)
			if !finished.Load() || len(r.Failures) != 0 {
				t.Fatal("oversized callback output did not cancel cleanly")
			}
		})
	}
}
