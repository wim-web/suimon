package suimon

import (
	"context"
	"errors"
	"fmt"
	"strings"
	"testing"
)

func parserLimitDefinition() *Definition {
	return &Definition{
		Main:      "main",
		Functions: []FunctionDecl{{ID: "source", Output: Contract{Kind: KindSingle, Type: Named("Int")}}},
		Workflows: []Workflow{{ID: "main", Placements: []Placement{{
			Name: "out", Control: CallControl{Body: FunctionBody("source")}, Policy: PolicyStop,
		}}}},
	}
}

func parserLimitRegistry(t *testing.T, output string) *Registry {
	t.Helper()
	return mustRegistry(t, FuncNoInput("source", func(context.Context) (string, error) { return output, nil }))
}

// The default reader and Engine.Resume must both read everything an engine commits,
// including the cancellation it records when a later value exceeds the line budget.
func assertParserLimitResume(t *testing.T, e *Engine, j *memJournal, report *Report) {
	t.Helper()
	text := j.text()
	checked, err := Check(text, LoadHeader)
	if err != nil || !checked.State.Equal(report.State) {
		t.Fatalf("Check of generated journal: %v", err)
	}
	copy := newMemJournal(text)
	x, err := e.Resume(context.Background(), copy)
	if err != nil {
		t.Fatalf("Resume of generated journal: %v", err)
	}
	resumed, err := wait(t, x)
	if err != nil || !resumed.State.Equal(report.State) || copy.text() != text {
		t.Fatalf("terminal Resume changed state or journal: %v", err)
	}
}

func TestRuntimeParserRecordSize(t *testing.T) {
	p := parserLimitDefinition()
	baseline, err := NewEngine(p, parserLimitRegistry(t, ""))
	if err != nil {
		t.Fatal(err)
	}
	j := newMemJournal("")
	if _, err := baseline.Run(context.Background(), nil, WithJournal(j)); err != nil {
		t.Fatal(err)
	}
	var overhead int
	for _, line := range strings.Split(strings.TrimSpace(j.text()), "\n")[1:] {
		r, err := DecodeRecord(line)
		if err != nil {
			t.Fatal(err)
		}
		if _, ok := r.Op.(OpReturned); ok {
			overhead = len(line)
		}
	}
	if overhead == 0 {
		t.Fatal("missing returned record")
	}
	for _, tc := range []struct {
		name, output string
		accepted     bool
	}{
		{"at limit", strings.Repeat("x", DefaultMaxInputBytes-overhead), true},
		{"limit plus one", strings.Repeat("x", DefaultMaxInputBytes-overhead+1), false},
		{"reported regression", strings.Repeat("x", 1<<20), false},
		{"escaped payload", strings.Repeat("\n", DefaultMaxInputBytes/3), false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e, err := NewEngine(p, parserLimitRegistry(t, tc.output))
			if err != nil {
				t.Fatal(err)
			}
			j := newMemJournal("")
			r, err := e.Run(context.Background(), nil, WithJournal(j))
			if tc.accepted {
				if err != nil || r == nil || r.Status != StatusSucceeded {
					t.Fatalf("allowed output: %v", err)
				}
			} else if !errors.Is(err, ErrQuotaExceeded) || r == nil || r.Status != StatusCancelled {
				t.Fatalf("oversized record must cancel before committing the value: report=%v, err=%v", r != nil, err)
			}
			assertParserLimitResume(t, e, j, r)
			var longest int
			for _, line := range strings.Split(j.text(), "\n") {
				longest = max(longest, len(line))
			}
			if longest > DefaultMaxInputBytes || tc.accepted && longest != DefaultMaxInputBytes {
				t.Fatalf("longest journal line: %d", longest)
			}
			if !tc.accepted {
				for _, op := range opsOf(t, j.text()) {
					if _, returned := op.(OpReturned); returned {
						t.Fatal("oversized result was committed")
					}
				}
				// A crash after cancellation must also remain resumable.
				prefix := journalBefore(t, j.text(), func(op Op) bool { _, ok := op.(OpTerminated); return ok })
				partial := newMemJournal(prefix)
				x, err := e.Resume(context.Background(), partial)
				if err != nil {
					t.Fatal(err)
				}
				recovered, err := wait(t, x)
				if err != nil || recovered.Status != StatusCancelled {
					t.Fatalf("Resume during quota shutdown: %v", err)
				}
				assertParserLimitResume(t, e, partial, recovered)
			}
		})
	}
}

func TestRuntimeParserHeaderLimits(t *testing.T) {
	for _, validated := range []bool{false, true} {
		for _, depth := range []int{MaxInputDepth - 1, MaxInputDepth, MaxInputDepth + 1} {
			t.Run(fmt.Sprintf("validated=%t/depth=%d", validated, depth), func(t *testing.T) {
				p := parserLimitDefinition()
				// Header -> definition -> functions -> function -> output -> list wrappers.
				p.Functions[0].Output.Type.Lists = depth - 5
				testParserLimitHeader(t, p, validated, depth <= MaxInputDepth)
			})
		}
		for _, delta := range []int{-1, 0, 1} {
			t.Run(fmt.Sprintf("validated=%t/bytes=%d", validated, DefaultMaxInputBytes+delta), func(t *testing.T) {
				p := parserLimitDefinition()
				name := &p.Functions[0].Output.Type.Name
				*name = strings.Repeat("T", DefaultMaxInputBytes+delta-len(EncodeHeader(p, validated))+len(*name))
				testParserLimitHeader(t, p, validated, delta <= 0)
			})
		}
	}
}

func testParserLimitHeader(t *testing.T, p *Definition, validated, accepted bool) {
	t.Helper()
	constructor := NewEngine
	if !validated {
		constructor = NewUncheckedEngine
	}
	e, err := constructor(p, parserLimitRegistry(t, "value"))
	if !accepted {
		if e != nil || err == nil || !strings.Contains(err.Error(), "input exceeds maximum") {
			t.Fatalf("unreadable header accepted: %v", err)
		}
		return
	}
	if err != nil {
		t.Fatal(err)
	}
	j := newMemJournal("")
	r, err := e.Run(context.Background(), nil, WithJournal(j))
	if err != nil || r == nil || r.Status != StatusSucceeded {
		t.Fatalf("run at header boundary: %v", err)
	}
	assertParserLimitResume(t, e, j, r)
}

func TestRuntimeParserOversizedStart(t *testing.T) {
	p := parserLimitDefinition()
	inputType := Named("Text")
	p.Functions[0].Input = &inputType
	p.Workflows[0].Input = &Entry{Type: inputType, Placement: "out"}
	r := mustRegistry(t, Func("source", func(context.Context, string) (int, error) {
		t.Error("callback ran for an input that could not be recorded")
		return 0, nil
	}))
	e, err := NewEngine(p, r)
	if err != nil {
		t.Fatal(err)
	}
	j := newMemJournal("")
	x, err := e.Start(context.Background(), strings.Repeat("x", 1<<20), WithJournal(j))
	if x != nil {
		_, _ = wait(t, x)
	}
	if !errors.Is(err, ErrQuotaExceeded) {
		t.Fatalf("oversized start: %v", err)
	}
	if j.text() != "" {
		t.Fatal("oversized start wrote to the journal")
	}
}

func TestConformanceParserJournalLimits(t *testing.T) {
	cli := leanCLI(t)
	for _, boundary := range []string{"header depth", "header bytes", "oversized output"} {
		t.Run(boundary, func(t *testing.T) {
			p := parserLimitDefinition()
			output := "value"
			switch boundary {
			case "header depth":
				p.Functions[0].Output.Type.Lists = MaxInputDepth - 5
			case "header bytes":
				name := &p.Functions[0].Output.Type.Name
				*name = strings.Repeat("T", DefaultMaxInputBytes-len(EncodeHeader(p, true))+len(*name))
			case "oversized output":
				output = strings.Repeat("x", 1<<20)
			}
			e, err := NewEngine(p, parserLimitRegistry(t, output))
			if err != nil {
				t.Fatal(err)
			}
			j := newMemJournal("")
			r, err := e.Run(context.Background(), nil, WithJournal(j))
			if r == nil || err != nil && !errors.Is(err, ErrQuotaExceeded) {
				t.Fatalf("run: %v", err)
			}
			assertParserLimitResume(t, e, j, r)
			leanAgrees(t, cli, t.TempDir(), p, j.text(), r.State)
		})
	}
}
