package suimon

import (
	"context"
	"errors"
	"fmt"
	"iter"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

var errTestSync = errors.New("test: sync failed")

// Block the selected Sync so the test can observe whether a call/fetch escaped before durability.
// The crash image is durable(), not the bytes Append accepted but Sync never persisted.
type syncFailureJournal struct {
	memJournal
	failOn  string
	blocked chan struct{}
	release chan struct{}
	failed  bool
	fetches int
}

func (j *syncFailureJournal) Sync() error {
	pending := strings.TrimSuffix(j.text()[len(j.durable()):], "\n")
	for _, line := range strings.Split(pending, "\n") {
		if strings.HasPrefix(line, `{"definition":`) {
			continue
		}
		r, err := DecodeRecord(line)
		if err != nil {
			return fmt.Errorf("test: decoding pending record: %w", err)
		}
		match := false
		switch r.Op.(type) {
		case OpStart:
			match = j.failOn == "start"
		case OpInvoke:
			match = j.failOn == "invoke"
		case OpFetch:
			j.fetches++
			match = j.failOn == "fetch" && j.fetches == 2
		}
		if match {
			j.failed = true
			close(j.blocked)
			<-j.release
			return errTestSync
		}
	}
	return j.memJournal.Sync()
}

func TestRuntimeJournalSyncFailure(t *testing.T) {
	for _, stage := range []string{"start", "invoke", "fetch"} {
		t.Run(stage, func(t *testing.T) {
			p := &Definition{
				Main:      "main",
				Functions: []FunctionDecl{{ID: "source", Output: Contract{Kind: KindSingle, Type: Named("Int")}}},
				Workflows: []Workflow{{ID: "main", Placements: []Placement{{
					Name: "source", Control: CallControl{Body: FunctionBody("source")}, Policy: PolicyStop,
				}}}},
			}
			var calls atomic.Int32
			called := make(chan struct{}, 1)
			noteCall := func() {
				calls.Add(1)
				select {
				case called <- struct{}{}:
				default:
				}
			}
			bindings := []Binding{FuncNoInput("source", func(context.Context) (int, error) {
				noteCall()
				return 1, nil
			})}
			if stage == "fetch" {
				p.Functions[0].Output.Kind = KindStream
				p.Transforms = []TransformDecl{{ID: "int", Input: Named("Int"), Output: Named("Int")}}
				p.Workflows[0].Placements = append(p.Workflows[0].Placements,
					Placement{Name: "all", Control: WaitStreamControl{Element: Named("Int")}, Policy: PolicyStop})
				p.Workflows[0].Connections = []Connection{{Source: "source", Target: "all", Transform: Declared("int")}}
				bindings = []Binding{StreamNoInput("source", func(context.Context) iter.Seq2[int, error] {
					return func(yield func(int, error) bool) {
						for n := 1; n <= 2; n++ {
							noteCall()
							if !yield(n, nil) {
								return
							}
						}
					}
				}), Passthrough("int")}
			}
			e, err := NewEngine(p, mustRegistry(t, bindings...))
			if err != nil {
				t.Fatal(err)
			}
			j := &syncFailureJournal{failOn: stage, blocked: make(chan struct{}), release: make(chan struct{})}
			ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
			defer cancel()
			type outcome struct {
				report *Report
				err    error
			}
			finished := make(chan outcome, 1)
			go func() {
				r, err := e.Run(ctx, nil, WithJournal(j))
				finished <- outcome{r, err}
			}()
			select {
			case <-j.blocked:
			case <-ctx.Done():
				close(j.release)
				t.Fatal("execution did not reach the selected Sync")
			}
			wantCalls := int32(0)
			if stage == "fetch" {
				wantCalls = 1 // The first fetch is durable; the second must remain unpublished.
			}
			if calls.Load() != wantCalls {
				t.Errorf("callbacks before failed Sync: %d, want %d", calls.Load(), wantCalls)
			}
			for len(called) > 0 {
				<-called
			}
			// Keep Sync unresolved while giving any prematurely published effect a chance to run.
			select {
			case <-called:
				t.Error("user code ran before its call/fetch was durable")
			case <-time.After(50 * time.Millisecond):
			}
			close(j.release)
			var result outcome
			select {
			case result = <-finished:
			case <-ctx.Done():
				t.Fatal("execution did not finish after Sync failed")
			}
			if !j.failed || !errors.Is(result.err, errTestSync) || result.report != nil || calls.Load() != wantCalls {
				t.Fatalf("Sync failure: injected=%t report=%v error=%v callbacks=%d", j.failed, result.report, result.err, calls.Load())
			}
			if j.text() == j.durable() {
				t.Fatal("failure did not leave an unsynced suffix")
			}
			crashed := newMemJournal(j.durable())
			x, err := e.Resume(ctx, crashed)
			if stage == "start" {
				if !errors.Is(err, ErrNotStarted) || x != nil || crashed.text() != "" {
					t.Fatalf("unsynced start was recovered: %v %v", x, err)
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			r, err := wait(t, x)
			if err != nil {
				t.Fatal(err)
			}
			verifyJournal(t, p, crashed.text(), r)
			if stage == "invoke" {
				expectStatusOf(t, r, StatusSucceeded)
				expectOutput(t, r, "source", 1)
				if calls.Load() != 1 {
					t.Fatalf("resumed call ran %d times", calls.Load())
				}
			} else {
				expectStatusOf(t, r, StatusFailed)
				expectFailures(t, r, "source:lost")
				if calls.Load() != 1 {
					t.Fatal("the durable stream invocation was executed again after losing its executor")
				}
			}
		})
	}
}
