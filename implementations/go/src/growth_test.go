package suimon

import (
	"context"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Identities grow linearly with the nesting of runs (Test/Trace.lean): a run path holds one label per
// level, and an identity holds its run path once. The chains of Test/definitions/chains nest 16 runs,
// sub-workflow calls or concurrency tasks and sub-workflow calls in turn, and 8 when started at w8.

// chainNames are the chains of Test/definitions/chains.
var chainNames = []string{"nested", "alternating"}

// loadChain decodes Test/definitions/chains/<name>.json, run from the workflow start.
func loadChain(t testing.TB, name, start string) *Definition {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(repoRoot(t), "Test", "definitions", "chains", name+".json"))
	if err != nil {
		t.Fatal(err)
	}
	p, err := ParseDefinition(data)
	if err != nil {
		t.Fatalf("%s: %v", name, err)
	}
	p.Main = start
	return p
}

// runChain runs a chain with functions that count the levels, and returns its journal and report.
func runChain(t *testing.T, p *Definition, input any) (string, *Report) {
	t.Helper()
	bindings := []Binding{
		FuncNoInput("source", func(context.Context) (int, error) { return 0, nil }),
		Func("work", func(_ context.Context, n int) (int, error) { return n + 1, nil }),
	}
	for _, tr := range p.Transforms {
		bindings = append(bindings, Passthrough(tr.ID))
	}
	e, err := NewEngine(p, mustRegistry(t, bindings...))
	if err != nil {
		t.Fatal(err)
	}
	j := newMemJournal("")
	r, err := e.Run(context.Background(), input, WithJournal(j))
	if err != nil {
		t.Fatal(err)
	}
	expectStatusOf(t, r, StatusSucceeded)
	return j.text(), r
}

// longestRecordLine is the length in bytes of the longest line of a journal, the header aside.
func longestRecordLine(journal string) int {
	lines := strings.Split(strings.TrimSuffix(journal, "\n"), "\n")
	longest := 0
	for _, line := range lines[1:] {
		longest = max(longest, len(line))
	}
	return longest
}

// maxDepth is the number of labels of the deepest run of s.
func maxDepth(s *State) int {
	depth := 0
	for _, r := range s.Runs {
		depth = max(depth, len(r.Path))
	}
	return depth
}

// The journal the runtime writes for 16 levels has lines within 2.5 times those of 8 levels, and
// under 8 KiB, and Check replays it; identities that embed their run path at every level grow
// exponentially instead.
func TestRuntimeIdentifierGrowth(t *testing.T) {
	for _, name := range chainNames {
		p16, p8 := loadChain(t, name, "w0"), loadChain(t, name, "w8")
		deep, r16 := runChain(t, p16, nil)
		shallow, r8 := runChain(t, p8, 0)
		if maxDepth(r16.State) != 16 || maxDepth(r8.State) != 8 {
			t.Fatalf("%s: the deepest runs have %d and %d labels", name, maxDepth(r16.State), maxDepth(r8.State))
		}
		for _, x := range []struct {
			p       *Definition
			journal string
			state   *State
		}{{p16, deep, r16.State}, {p8, shallow, r8.State}} {
			c, err := Check(x.journal, sameDefinition(x.p))
			if err != nil {
				t.Fatalf("%s: Check: %v", name, err)
			}
			if !c.State.Equal(x.state) {
				t.Fatalf("%s: Check replays the journal to another state", name)
			}
		}
		l16, l8 := longestRecordLine(deep), longestRecordLine(shallow)
		t.Logf("%s: the longest line has %d bytes at depth 16 and %d at depth 8", name, l16, l8)
		if 2*l16 > 5*l8 || l16 > 8192 {
			t.Errorf("%s: the longest line has %d bytes at depth 16 and %d at depth 8", name, l16, l8)
		}
	}
}
