package suimon

import (
	"context"
	"fmt"
	"math/rand/v2"
	"testing"
	"time"
)

// kindReference is Lean's Workflow.kind? as it is written: the recursion that derives the kind of a
// source once for each path to it. The kind tables must give what it gives at every fuel.
func (w *Workflow) kindReference(p *Definition, fuel int, name string) (Kind, bool) {
	if fuel == 0 {
		return 0, false
	}
	pl, ok := w.placement(name)
	if !ok {
		return 0, false
	}
	var sources []Kind
	for _, c := range w.incoming(name) {
		k, ok := w.kindReference(p, fuel-1, c.Source)
		if !ok {
			return 0, false
		}
		sources = append(sources, k)
	}
	input, ok := w.combineInput(name, sources)
	if !ok {
		return 0, false
	}
	return p.outputKind(pl.Control, input)
}

// inputKindReference is Lean's Workflow.inputKind? over kindReference.
func (w *Workflow) inputKindReference(p *Definition, name string) (*Kind, bool) {
	var sources []Kind
	for _, c := range w.incoming(name) {
		k, ok := w.kindReference(p, w.depth(), c.Source)
		if !ok {
			return nil, false
		}
		sources = append(sources, k)
	}
	return w.combineInput(name, sources)
}

// mergeChain is a function followed by n Merges, each with two connections from the one before:
// kindReference derives the kind of each placement twice for each one after it.
func mergeChain(n int) *Definition {
	w := Workflow{ID: "w", Placements: []Placement{{Name: "p0", Control: CallControl{FunctionBody("f")}, Policy: PolicyStop}}}
	for i := 1; i <= n; i++ {
		first, second := "l1", "l2"
		if i == 1 {
			first, second = "t1", "t2"
		}
		source, target := fmt.Sprintf("p%d", i-1), fmt.Sprintf("p%d", i)
		w.Placements = append(w.Placements, Placement{Name: target, Control: MergeControl{Named("T")}, Policy: PolicyStop})
		w.Connections = append(w.Connections, Connection{Source: source, Target: target, Transform: Declared(first)},
			Connection{Source: source, Target: target, Transform: Declared(second)})
	}
	return &Definition{
		Main:      "w",
		Functions: []FunctionDecl{{ID: "f", Output: Contract{KindSingle, Named("T")}}},
		Transforms: []TransformDecl{{ID: "t1", Input: Named("T"), Output: Named("T")},
			{ID: "t2", Input: Named("T"), Output: Named("T")},
			{ID: "l1", Input: ListOf(Named("T")), Output: Named("T")},
			{ID: "l2", Input: ListOf(Named("T")), Output: Named("T")}},
		Workflows: []Workflow{w},
	}
}

// diamonds is a function followed by n diamonds: two calls after the end of the previous diamond,
// whose results a Merge collects.
func diamonds(n int) *Definition {
	w := Workflow{ID: "w", Placements: []Placement{{Name: "s0", Control: CallControl{FunctionBody("f")}, Policy: PolicyStop}}}
	for i := 1; i <= n; i++ {
		into := "l"
		if i == 1 {
			into = "t"
		}
		end := fmt.Sprintf("s%d", i)
		for _, side := range []string{"b", "c"} {
			name := fmt.Sprintf("%s%d", side, i)
			w.Placements = append(w.Placements, Placement{Name: name, Control: CallControl{FunctionBody("g")}, Policy: PolicyStop})
			w.Connections = append(w.Connections, Connection{Source: fmt.Sprintf("s%d", i-1), Target: name, Transform: Declared(into)},
				Connection{Source: name, Target: end, Transform: Declared("t")})
		}
		w.Placements = append(w.Placements, Placement{Name: end, Control: MergeControl{Named("T")}, Policy: PolicyStop})
	}
	return &Definition{
		Main: "w",
		Functions: []FunctionDecl{{ID: "f", Output: Contract{KindSingle, Named("T")}},
			{ID: "g", Input: ptr(Named("T")), Output: Contract{KindSingle, Named("T")}}},
		Transforms: []TransformDecl{{ID: "t", Input: Named("T"), Output: Named("T")},
			{ID: "l", Input: ListOf(Named("T")), Output: Named("T")}},
		Workflows: []Workflow{w},
	}
}

// randomDefinition has a small random workflow w, whose kinds exercise every rule of outputKind and
// combineInput, and what validation rejects: cycles, repeated placement names, connections from or
// to no placement, unknown references, and an entry with input connections.
func randomDefinition(rng *rand.Rand) *Definition {
	names := []string{"a", "b", "c", "d", "e"}
	pick := func(xs ...string) string { return xs[rng.IntN(len(xs))] }
	controls := []func() Control{
		func() Control {
			return CallControl{FunctionBody(pick("single", "stream", "singleIn", "streamIn", "unknown"))}
		},
		func() Control { return CallControl{WorkflowBody(pick("sub", "unknown"), "out")} },
		func() Control { return BranchControl{Judge: "judge", Arms: []string{"x"}} },
		func() Control { return WaitStreamControl{Named("T")} },
		func() Control { return MergeControl{Named("T")} },
		func() Control {
			return ConcurrencyControl{Concurrency{Limit: 1, Output: Collect(rng.IntN(2)), Element: Named("T")}}
		},
	}
	w := Workflow{ID: "w"}
	for range 1 + rng.IntN(5) {
		w.Placements = append(w.Placements, Placement{Name: pick(names...), Control: controls[rng.IntN(len(controls))](),
			Policy: PolicyStop})
	}
	ends := append(names, "nowhere")
	for range rng.IntN(7) {
		w.Connections = append(w.Connections, Connection{Source: pick(ends...), Target: pick(ends...), Transform: Declared("t")})
	}
	if rng.IntN(3) == 0 {
		w.Input = &Entry{Type: Named("T"), Placement: pick(names...)}
	}
	return &Definition{
		Main: "w",
		Functions: []FunctionDecl{
			{ID: "single", Output: Contract{KindSingle, Named("T")}},
			{ID: "stream", Output: Contract{KindStream, Named("T")}},
			{ID: "singleIn", Input: ptr(Named("T")), Output: Contract{KindSingle, Named("T")}},
			{ID: "streamIn", Input: ptr(Named("T")), Output: Contract{KindStream, Named("T")}},
		},
		Judges: []JudgeDecl{{ID: "judge", Input: Named("T")}},
		Workflows: []Workflow{w,
			{ID: "sub", Placements: []Placement{{Name: "out", Control: CallControl{FunctionBody("single")}, Policy: PolicyStop}}}},
	}
}

// checkKindTables compares the kind tables of w with kindReference at every fuel up to past the one
// of Lean's outputKind?, and the input kinds with inputKindReference, for every name w mentions.
func checkKindTables(t *testing.T, label string, p *Definition, w *Workflow) {
	t.Helper()
	names := []string{"nowhere"}
	for _, pl := range w.Placements {
		names = append(names, pl.Name)
	}
	for _, c := range w.Connections {
		names = append(names, c.Source, c.Target)
	}
	for fuel := 0; fuel <= w.depth()+1; fuel++ {
		table := w.kindsAt(p, fuel)
		for _, name := range names {
			want, wantOK := w.kindReference(p, fuel, name)
			if got, ok := table[name]; ok != wantOK || got != want {
				t.Fatalf("%s: the kind of %s at fuel %d is %v (%t), want %v (%t)", label, name, fuel, got, ok, want, wantOK)
			}
		}
	}
	table := w.deriveKinds(p)
	for _, name := range names {
		want, wantOK := w.inputKindReference(p, name)
		if got, ok := table.inputKind(w, name); ok != wantOK || !equalPtr(got, want) {
			t.Fatalf("%s: the input kind of %s is %v (%t), want %v (%t)", label, name, got, ok, want, wantOK)
		}
	}
}

// The kind tables derive the kinds of Lean's kind? for every workflow and every fuel, including
// invalid and cyclic workflows, where the fuel bounds the connection paths.
func TestKindTables(t *testing.T) {
	for _, name := range append(append(append([]string{}, definitionNames...), extraDefinitions...), "limit") {
		p := load(t, name)
		for i := range p.Workflows {
			checkKindTables(t, name, p, &p.Workflows[i])
		}
	}
	for label, p := range map[string]*Definition{"merge chain": mergeChain(6), "diamonds": diamonds(4), "cycle": cycleDefinition()} {
		checkKindTables(t, label, p, &p.Workflows[0])
	}
	rng := rand.New(rand.NewPCG(1, 2))
	for i := range 3000 {
		p := randomDefinition(rng)
		checkKindTables(t, fmt.Sprintf("random definition %d", i), p, &p.Workflows[0])
	}
}

// chainBindings implement the functions and transforms of mergeChain and diamonds.
func chainBindings() []Binding {
	first := func(values []string) (string, error) { return values[0], nil }
	return []Binding{
		FuncNoInput("f", func(context.Context) (string, error) { return "x", nil }),
		Func("g", func(_ context.Context, v string) (string, error) { return v, nil }),
		Passthrough("t"), Passthrough("t1"), Passthrough("t2"),
		Transform("l", first), Transform("l1", first), Transform("l2", first),
	}
}

// Deriving kinds by recursion takes time exponential in the length of these chains; validation, the
// engine and each step derive them in polynomial time, and the engine derives them once.
func TestLongMergeChains(t *testing.T) {
	for _, c := range []struct {
		label string
		p     *Definition
		end   string
	}{{"merge chain 20", mergeChain(20), "p20"}, {"merge chain 40", mergeChain(40), "p40"}, {"30 diamonds", diamonds(30), "s30"}} {
		start := time.Now()
		accepted(t, c.label, c.p)
		if elapsed := time.Since(start); elapsed > time.Second {
			t.Errorf("%s: validation took %v", c.label, elapsed)
		}
		start = time.Now()
		e, err := NewEngine(c.p, mustRegistry(t, chainBindings()...))
		if err != nil {
			t.Fatal(err)
		}
		r, err := e.Run(context.Background(), nil)
		if err != nil {
			t.Fatal(err)
		}
		if elapsed := time.Since(start); elapsed > 5*time.Second {
			t.Errorf("%s: creating the engine and running took %v", c.label, elapsed)
		}
		expectStatusOf(t, r, StatusSucceeded)
		expectOutput(t, r, c.end, []string{"x", "x"})
	}
}
