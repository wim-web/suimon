package suimon

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// repoRoot is the repository root, found from the package directory.
func repoRoot(t testing.TB) string {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "lakefile.lean")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("repository root not found")
		}
		dir = parent
	}
}

// definitionNames are the definitions of the Lean tests (Test/definitions); extraDefinitions
// (testdata) cover sub-workflow calls, Merge of skipped inputs, Stream concurrency output and tasks
// without input.
var (
	definitionNames  = []string{"users", "branch", "merge"}
	extraDefinitions = []string{"calls", "fanout"}
)

// load decodes Test/definitions/<name>.json, or testdata/<name>.json; every call returns a fresh
// definition.
func load(t testing.TB, name string) *Definition {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(repoRoot(t), "Test", "definitions", name+".json"))
	if os.IsNotExist(err) {
		data, err = os.ReadFile(filepath.Join("testdata", name+".json"))
	}
	if err != nil {
		t.Fatal(err)
	}
	p, err := ParseDefinition(data)
	if err != nil {
		t.Fatalf("%s: %v", name, err)
	}
	return p
}

func hasFragment(text, fragment string) bool { return strings.Contains(text, fragment) }

func mapWorkflow(p *Definition, id string, f func(*Workflow)) *Definition {
	for i := range p.Workflows {
		if p.Workflows[i].ID == id {
			f(&p.Workflows[i])
		}
	}
	return p
}

func mapPlacement(name string, f func(*Placement)) func(*Workflow) {
	return func(w *Workflow) {
		for i := range w.Placements {
			if w.Placements[i].Name == name {
				f(&w.Placements[i])
			}
		}
	}
}

func mapConnection(source, target string, f func(*Connection)) func(*Workflow) {
	return func(w *Workflow) {
		for i := range w.Connections {
			if w.Connections[i].Source == source && w.Connections[i].Target == target {
				f(&w.Connections[i])
			}
		}
	}
}

func dropConnection(w *Workflow, source, target string) {
	var kept []Connection
	for _, c := range w.Connections {
		if !(c.Source == source && c.Target == target) {
			kept = append(kept, c)
		}
	}
	w.Connections = kept
}

func mapConcurrency(f func(*Concurrency)) func(*Placement) {
	return func(pl *Placement) {
		if c, ok := pl.Control.(ConcurrencyControl); ok {
			c.Spec.Tasks = append([]TaskSpec(nil), c.Spec.Tasks...)
			f(&c.Spec)
			pl.Control = c
		}
	}
}

func mapTask(name string, f func(*TaskSpec)) func(*Concurrency) {
	return func(c *Concurrency) {
		for i := range c.Tasks {
			if c.Tasks[i].Name == name {
				f(&c.Tasks[i])
			}
		}
	}
}

// Lookups of a state for tests, by scanning its lists.

func (s *State) resultsOf(path Path, name string) []Result {
	var out []Result
	for r := range s.view().resultsOf(path, name) {
		out = append(out, *r)
	}
	return out
}

func (s *State) deliveriesOn(path Path, index int) []Delivery {
	var out []Delivery
	for d := range s.view().deliveriesOn(path, index) {
		out = append(out, *d)
	}
	return out
}

func (s *State) invocationsOf(path Path, name string) []Invocation {
	var out []Invocation
	for i := range s.view().invocationsOf(path, name) {
		out = append(out, *i)
	}
	return out
}

func (s *State) concurrencyOf(p *Definition, e *Execution) (*Concurrency, error) {
	return s.view().concurrencyOf(p, e)
}

func (s *State) slotsHeld(e *Execution) int { return s.view().slotsHeld(e) }
