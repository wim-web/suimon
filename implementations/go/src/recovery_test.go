package suimon

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"unicode/utf8"
)

// Crash recovery (§12.1): a journal cut anywhere, at a line boundary or inside a line, resumes to
// the result of the run that wrote it when no call was running at the cut; calls that were running
// are reported lost (§11.6).

// cutPoints are the lengths at which a crash may cut a journal: every line boundary, and the
// middle of every line (a torn write), kept at a character boundary.
func cutPoints(journal string) []int {
	var cuts []int
	start := 0
	for _, line := range strings.SplitAfter(journal, "\n") {
		if line == "" {
			continue
		}
		cuts = append(cuts, start)
		middle := start + len(line)/2
		for middle > start && !utf8.RuneStart(journal[middle]) {
			middle--
		}
		if middle > start {
			cuts = append(cuts, middle)
		}
		start += len(line)
	}
	return append(cuts, len(journal))
}

// resumeAt resumes the execution recorded in prefix with fresh bindings of sc, and returns the
// report, the journal after the run, and what the prefix establishes.
func resumeAt(t *testing.T, sc scenario, p *Definition, prefix string) (*Report, *memJournal, Checked, error) {
	t.Helper()
	c, err := Check(prefix, sameDefinition(p))
	if err != nil {
		t.Fatalf("the prefix does not replay: %v", err)
	}
	j := newMemJournal(prefix)
	e, err := NewEngine(p, mustRegistry(t, sc.prepare(t, j).bindings...))
	if err != nil {
		t.Fatal(err)
	}
	x, err := e.Resume(context.Background(), j)
	if err != nil {
		return nil, j, c, err
	}
	r, err := wait(t, x)
	if err != nil {
		t.Fatalf("Wait: %v", err)
	}
	return r, j, c, nil
}

// checkResumed checks a resumed run against the run that wrote the journal: the committed part of
// the prefix is kept, and either nothing was lost and the result is the same, or each call that
// was running at the cut is lost.
func checkResumed(t *testing.T, p *Definition, want *Report, r *Report, j *memJournal, c Checked, prefix string) {
	t.Helper()
	verifyJournal(t, p, j.text(), r)
	// The committed records are kept, and the new ones follow them where the uncommitted tail was.
	if rest := j.text()[min(c.Length, len(j.text())):]; !strings.HasPrefix(j.text(), prefix[:c.Length]) ||
		(rest != "" && !strings.HasPrefix(rest, fmt.Sprintf(`{"seq":%d,`, 2*c.Committed+1))) {
		t.Fatal("the resumed journal does not continue the committed records")
	}
	if !hasRunningCall(c.State) {
		if diff := compareReports(want, r); diff != "" {
			t.Errorf("nothing was lost, but the result differs: %s", diff)
		}
		return
	}
	// Resume first reports the calls that were running lost, in the order they were created: each
	// fails under its policy, and once one stops the workflow the others end as cancelled (Step).
	expected, lost := c.State, []Op{}
	for _, call := range c.State.Calls {
		if !call.Status.ended() {
			next, err := Step(p, expected, OpLost{Call: call.ID})
			if err != nil {
				t.Fatalf("lost %s: %v", call.ID, err)
			}
			expected, lost = next, append(lost, OpLost{Call: call.ID})
		}
	}
	ops := opsOf(t, j.text()[c.Length:])
	if len(ops) < len(lost) || !slices.Equal(ops[:len(lost)], lost) {
		t.Errorf("the resumed journal starts with %v, want the lost calls %v", ops, lost)
	}
	final := map[string]CallStatus{}
	for _, call := range r.State.Calls {
		final[call.ID] = call.Status
	}
	for _, call := range expected.Calls {
		if call.Status != final[call.ID] {
			t.Errorf("call %s ends %v, want %v", call.ID, final[call.ID], call.Status)
		}
	}
	lostFailures := 0
	for i, f := range r.Failures {
		if i >= len(c.State.Failures) && f.Cause == CauseLost {
			lostFailures++
			if !errors.Is(f.Err, ErrLost) {
				t.Errorf("a lost call's error: %v", f.Err)
			}
		}
	}
	if want := len(expected.Failures) - len(c.State.Failures); lostFailures != want {
		t.Errorf("%d lost failures, want %d", lostFailures, want)
	}
	if lostFailures > 0 && r.Status != StatusFailed {
		t.Errorf("a lost call fails the workflow, status %v", r.Status)
	}
}

func TestRuntimeRecovery(t *testing.T) {
	for _, sc := range scenarios() {
		if !sc.deterministic {
			continue
		}
		t.Run(sc.name, func(t *testing.T) {
			t.Parallel()
			p, journal, want := runOnce(t, sc)
			cuts, compared := cutPoints(journal), 0
			for _, cut := range cuts {
				prefix := journal[:cut]
				r, j, c, err := resumeAt(t, sc, p, prefix)
				if c.Committed == 0 {
					if !errors.Is(err, ErrNotStarted) {
						t.Errorf("cut %d: resuming before the start: %v", cut, err)
					}
					continue
				}
				if err != nil {
					t.Fatalf("cut %d: %v", cut, err)
				}
				checkResumed(t, p, want, r, j, c, prefix)
				if t.Failed() {
					t.Fatalf("cut %d of %d:\n%s", cut, len(journal), prefix)
				}
				if !hasRunningCall(c.State) {
					compared++
				}
			}
			if compared == 0 {
				t.Error("no cut point without a running call")
			}
			t.Logf("%d cut points, %d compared with the uninterrupted run", len(cuts), compared)
		})
	}
}

func hasRunningCall(s *State) bool {
	for _, c := range s.Calls {
		if !c.Status.ended() {
			return true
		}
	}
	return false
}

// A resumed execution can crash and be resumed again.
func TestRuntimeRecoveryTwice(t *testing.T) {
	sc := scenarioNamed(t, "users")
	p, journal, want := runOnce(t, sc)
	cuts, resumed := cutPoints(journal), 0
	for _, cut := range cuts[len(cuts)/4 : len(cuts)/4+12] {
		_, first, c1, err := resumeAt(t, sc, p, journal[:cut])
		if err != nil {
			t.Fatal(err)
		}
		// Cut again inside what the first recovery wrote.
		again, later := first.text(), 0
		for _, second := range cutPoints(again) {
			if second <= c1.Length {
				continue
			}
			if later++; later%4 != 1 {
				continue
			}
			prefix := again[:second]
			r, j, c, err := resumeAt(t, sc, p, prefix)
			if err != nil {
				t.Fatal(err)
			}
			resumed++
			verifyJournal(t, p, j.text(), r)
			if !strings.HasPrefix(j.text(), prefix[:c.Length]) {
				t.Fatal("the committed records are not kept")
			}
			if !hasRunningCall(c.State) && !hasRunningCall(mustCheck(t, p, journal[:cut]).State) {
				if diff := compareReports(want, r); diff != "" {
					t.Errorf("cut %d then %d: %s", cut, second, diff)
				}
			}
		}
	}
	if resumed < 12 {
		t.Errorf("%d executions resumed twice, want one or more after each first cut", resumed)
	}
}

func mustCheck(t *testing.T, p *Definition, text string) Checked {
	t.Helper()
	c, err := Check(text, sameDefinition(p))
	if err != nil {
		t.Fatal(err)
	}
	return c
}

func scenarioNamed(t *testing.T, name string) scenario {
	t.Helper()
	for _, sc := range scenarios() {
		if sc.name == name {
			return sc
		}
	}
	t.Fatalf("no scenario %s", name)
	return scenario{}
}

// A concluded journal resumes to an execution that is already done, with the same report.
func TestRuntimeResumeConcluded(t *testing.T) {
	sc := scenarioNamed(t, "merge continue failure")
	p, journal, want := runOnce(t, sc)
	r, j, _, err := resumeAt(t, sc, p, journal)
	if err != nil {
		t.Fatal(err)
	}
	if diff := compareReports(want, r); diff != "" || j.text() != journal {
		t.Errorf("%s; journal changed: %v", diff, j.text() != journal)
	}
	if r.Failures[0].Err != nil {
		t.Error("errors are not in the journal")
	}
}

func TestRuntimeResumeErrors(t *testing.T) {
	p := load(t, "merge")
	e, err := NewEngine(p, mustRegistry(t, mergeBindings(mergeKnobs{})...))
	if err != nil {
		t.Fatal(err)
	}
	header := EncodeHeader(p) + "\n"
	start := "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n"
	for label, text := range map[string]string{
		"empty":       "",
		"torn header": header[:len(header)/2],
		"header only": header,
		"torn start":  header + start + "{\"seq\":2,\"com",
	} {
		if _, err := e.Resume(context.Background(), newMemJournal(text)); !errors.Is(err, ErrNotStarted) {
			t.Errorf("%s: %v", label, err)
		}
	}
	for label, text := range map[string]string{
		"corrupt":   header + start + "{\"seq\":2,\"commit\":tru}\n",
		"no header": start + "{\"seq\":2,\"commit\":true}\n",
	} {
		if _, err := e.Resume(context.Background(), newMemJournal(text)); err == nil || errors.Is(err, ErrNotStarted) ||
			errors.Is(err, ErrDefinitionMismatch) {
			t.Errorf("%s: %v", label, err)
		}
	}
	// A journal of another definition is not resumed, however little the definitions differ: here
	// by one policy, which the functions bound to the engine do not show.
	_, journal, _ := runOnce(t, scenarioNamed(t, "merge"))
	other := load(t, "merge")
	setPolicy("dashboard", "archive", PolicyStop)(other)
	if EncodeHeader(other) == EncodeHeader(p) {
		t.Fatal("the definitions are the same")
	}
	otherEngine, err := NewEngine(other, mustRegistry(t, mergeBindings(mergeKnobs{})...))
	if err != nil {
		t.Fatal(err)
	}
	for label, text := range map[string]string{
		"another definition": journal,
		"cut inside a line":  journal[:len(journal)-5],
		"only the start":     header + start + "{\"seq\":2,\"commit\":true}\n",
	} {
		j := newMemJournal(text)
		if _, err := otherEngine.Resume(context.Background(), j); err != ErrDefinitionMismatch {
			t.Errorf("%s: %v", label, err)
		}
		if j.text() != text {
			t.Errorf("%s: the journal changed", label)
		}
	}
	// The same definition in another form is the same definition: the header is compared in its
	// canonical form, whatever the key order and the white space.
	file, err := os.ReadFile(filepath.Join(repoRoot(t), "Test", "definitions", "merge.json"))
	if err != nil {
		t.Fatal(err)
	}
	var fields map[string]any
	if err := json.Unmarshal(file, &fields); err != nil {
		t.Fatal(err)
	}
	sorted, err := json.MarshalIndent(fields, "", "")
	if err != nil {
		t.Fatal(err)
	}
	reformatted := "{ \"definition\" : " + strings.ReplaceAll(string(sorted), "\n", " ") + " }\n" + journal[len(header):]
	if reformatted == journal || strings.HasPrefix(reformatted, header) {
		t.Fatal("the header was not reformatted")
	}
	x, err := e.Resume(context.Background(), newMemJournal(reformatted))
	if err != nil {
		t.Fatalf("a header in another form: %v", err)
	}
	if _, err := wait(t, x); err != nil {
		t.Fatal(err)
	}
}

// A file journal survives the process: it is read back, its torn tail is cut off, and the
// execution continues in the same file.
func TestFileJournal(t *testing.T) {
	sc := scenarioNamed(t, "users")
	p := load(t, sc.definition)
	path := filepath.Join(t.TempDir(), "users.jsonl")
	j, err := CreateJournal(path)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := CreateJournal(path); err == nil {
		t.Error("CreateJournal does not overwrite a journal")
	}
	e, err := NewEngine(p, mustRegistry(t, sc.prepare(t, nil).bindings...))
	if err != nil {
		t.Fatal(err)
	}
	want, err := e.Run(context.Background(), sc.input, WithJournal(j))
	if err != nil {
		t.Fatal(err)
	}
	if err := j.Close(); err != nil {
		t.Fatal(err)
	}
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	verifyJournal(t, p, string(data), want)
	// Crash in the middle of a line; the process starts again and resumes from the file.
	cuts := cutPoints(string(data))
	cut := cuts[len(cuts)/2]
	if strings.HasSuffix(string(data[:cut]), "\n") {
		cut = cuts[len(cuts)/2+1]
	}
	if err := os.WriteFile(path, data[:cut], 0o644); err != nil {
		t.Fatal(err)
	}
	opened, err := OpenJournal(path)
	if err != nil {
		t.Fatal(err)
	}
	defer opened.Close()
	x, err := e.Resume(context.Background(), opened)
	if err != nil {
		t.Fatal(err)
	}
	r, err := wait(t, x)
	if err != nil {
		t.Fatal(err)
	}
	resumed, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	verifyJournal(t, p, string(resumed), r)
	c := mustCheck(t, p, string(data[:cut]))
	if !strings.HasPrefix(string(resumed), string(data[:c.Length])) || !c.Uncommitted {
		t.Error("the committed lines are kept and the torn line is replaced")
	}
	if contents, err := opened.Contents(); err != nil || string(contents) != string(resumed) {
		t.Errorf("Contents: %v", err)
	}
	if _, err := OpenJournal(filepath.Join(t.TempDir(), "missing.jsonl")); err == nil {
		t.Error("OpenJournal needs an existing file")
	}
}
