package suimon

import (
	"context"
	"errors"
	"fmt"
	"math/rand/v2"
	"strings"
	"testing"
)

func TestDefinitionResourceLimits(t *testing.T) {
	cases := []struct {
		name string
		make func(*Definition)
	}{
		{"workflow", func(p *Definition) { p.Workflows = make([]Workflow, MaxDefinitionWorkflows+1) }},
		{"declaration", func(p *Definition) { p.Functions = make([]FunctionDecl, MaxDefinitionDeclarations+1) }},
		{"placement", func(p *Definition) { p.Workflows[0].Placements = make([]Placement, MaxDefinitionPlacements+1) }},
		{"connection", func(p *Definition) { p.Workflows[0].Connections = make([]Connection, MaxDefinitionConnections+1) }},
		{"task", func(p *Definition) {
			p.Workflows[0].Placements[0].Control = ConcurrencyControl{Concurrency{Tasks: make([]TaskSpec, MaxDefinitionTasks+1)}}
		}},
		{"arm", func(p *Definition) {
			p.Workflows[0].Placements[0].Control = BranchControl{Arms: make([]string, MaxDefinitionArms+1)}
		}},
		{"name byte", func(p *Definition) { p.Main = strings.Repeat("あ", MaxDefinitionNameBytes/3+1) }},
		{"type depth", func(p *Definition) { p.Functions[0].Output.Type.Lists = MaxDefinitionTypeDepth + 1 }},
		{"validation work", func(p *Definition) { *p = *mergeChain(150) }},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			p := mergeChain(0)
			c.make(p)
			want := "definition: " + c.name + " limit exceeded"
			check := func(err error) {
				t.Helper()
				if err == nil || !strings.HasPrefix(err.Error(), want) {
					t.Fatalf("got %v, want %s", err, want)
				}
			}
			check(p.Validate())
			// A nil registry would panic if admission ran after engine construction.
			for _, opts := range [][]EngineOption{nil, {WithLimits(Limits{MaxWorkflows: 1})}} {
				_, err := NewEngine(p, nil, opts...)
				check(err)
				_, err = NewUncheckedEngine(p, nil, opts...)
				check(err)
			}
			if _, ok := p.OutputKind("w", "p0"); ok {
				t.Fatal("oversized definition derived a kind")
			}
			// Even a custom header loader cannot bypass admission before derivation.
			_, err := Check("{\"definition\":{},\"validated\":false}\n", func([]byte, bool) (*Definition, error) { return p, nil })
			if err == nil || !strings.Contains(err.Error(), want) {
				t.Fatalf("Check: %v", err)
			}
		})
	}
}

// A definition admitted by either constructor still runs under the host's quota.
func TestDefinitionAndRuntimeLimits(t *testing.T) {
	p, baseline, _ := quotaEngine(t, Limits{}, false, false)
	for name, constructor := range map[string]func(*Definition, *Registry, ...EngineOption) (*Engine, error){
		"validated": NewEngine, "unchecked": NewUncheckedEngine,
	} {
		t.Run(name, func(t *testing.T) {
			e, err := constructor(p, baseline.registry, WithLimits(Limits{MaxStreamElements: 2}))
			if err != nil {
				t.Fatal(err)
			}
			j := newMemJournal("")
			x, err := e.Start(context.Background(), -1, WithJournal(j))
			if err != nil {
				t.Fatal(err)
			}
			r, err := wait(t, x)
			if !errors.Is(err, ErrQuotaExceeded) || r == nil {
				t.Fatalf("Wait: report=%v, error=%v", r, err)
			}
			expectStatusOf(t, r, StatusCancelled)
			checked, err := Check(j.text(), LoadHeader)
			if err != nil || !checked.State.Equal(r.State) {
				t.Fatalf("quota cancellation replay: %v", err)
			}
			var elements int
			for _, call := range r.State.Calls {
				elements += call.Yields
			}
			if elements != 2 {
				t.Fatalf("accepted %d stream elements, want 2", elements)
			}
		})
	}
}

func TestResourceBoundaries(t *testing.T) {
	// These test admission alone; semantic errors still belong to Validate.
	for name, edit := range map[string]func(*Definition){
		"workflows":    func(p *Definition) { p.Workflows = make([]Workflow, MaxDefinitionWorkflows) },
		"declarations": func(p *Definition) { p.Functions = make([]FunctionDecl, MaxDefinitionDeclarations); p.Transforms = nil },
		"placements": func(p *Definition) {
			p.Workflows = make([]Workflow, 32)
			for i := range p.Workflows {
				p.Workflows[i].Placements = make([]Placement, MaxDefinitionPlacements/32)
			}
		},
		"connections": func(p *Definition) { p.Workflows[0].Connections = make([]Connection, MaxDefinitionConnections) },
		"tasks": func(p *Definition) {
			p.Workflows[0].Placements[0].Control = ConcurrencyControl{Concurrency{Tasks: make([]TaskSpec, MaxDefinitionTasks)}}
		},
		"arms": func(p *Definition) {
			p.Workflows[0].Placements[0].Control = BranchControl{Arms: make([]string, MaxDefinitionArms)}
		},
		"name": func(p *Definition) { p.Main = strings.Repeat("x", MaxDefinitionNameBytes) },
		"type": func(p *Definition) { p.Functions[0].Output.Type.Lists = MaxDefinitionTypeDepth },
	} {
		t.Run(name, func(t *testing.T) {
			p := mergeChain(0)
			edit(p)
			if err := p.checkResources(); err != nil {
				t.Fatal(err)
			}
		})
	}
	// Declaration/name checks also apply when there are no workflows to visit.
	for _, p := range []*Definition{
		{Main: strings.Repeat("x", MaxDefinitionNameBytes+1)},
		{Functions: []FunctionDecl{{Output: Contract{Type: ValueType{Lists: MaxDefinitionTypeDepth + 1}}}}},
	} {
		if err := p.checkResources(); err == nil {
			t.Fatal("declaration resource error was dropped without workflows")
		}
	}
	// Counts are aggregate, including across separately small workflows.
	p := mergeChain(0)
	p.Workflows = []Workflow{{Placements: make([]Placement, 600)}, {Placements: make([]Placement, 600)}}
	if err := p.checkResources(); err == nil || !strings.Contains(err.Error(), "placement limit") {
		t.Fatalf("aggregate placements: %v", err)
	}
}

func TestDefinitionTextLimits(t *testing.T) {
	for _, c := range []struct{ text, want string }{
		{strings.Repeat(" ", MaxDefinitionBytes+1), "maximum size"},
		{strings.Repeat("[", MaxDefinitionJSONDepth+1), "maximum nesting depth"},
	} {
		if _, err := ParseDefinition([]byte(c.text)); err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("ParseDefinition: %v", err)
		}
	}
	for _, s := range []string{strings.Repeat(" ", MaxDefinitionBytes), strings.Repeat("[", MaxDefinitionJSONDepth), `"\\\"` + strings.Repeat("[", 100) + `"`} {
		if err := (InputLimits{}).check(s); err != nil {
			t.Fatal(err)
		}
	}
}

// The indexed cycle checker must retain the reference's fuel, duplicate vertex,
// parallel edge, and missing endpoint behavior, even on malformed definitions.
func acyclicReference(edges []edge, fuel int, vertices []string) bool {
	for ; fuel > 0 && len(vertices) > 0; fuel-- {
		contains := func(xs []string, x string) bool {
			for _, v := range xs {
				if v == x {
					return true
				}
			}
			return false
		}
		var roots, rest []string
		for _, v := range vertices {
			root := true
			for _, e := range edges {
				if e.dst == v && contains(vertices, e.src) {
					root = false
					break
				}
			}
			if root {
				roots = append(roots, v)
			}
		}
		if len(roots) == 0 {
			return false
		}
		for _, v := range vertices {
			if !contains(roots, v) {
				rest = append(rest, v)
			}
		}
		vertices = rest
	}
	return len(vertices) == 0
}

func TestIndexedAcyclic(t *testing.T) {
	rng := rand.New(rand.NewPCG(5, 7))
	for range 3000 {
		var vertices []string
		var edges []edge
		for range rng.IntN(8) {
			vertices = append(vertices, fmt.Sprint(rng.IntN(6)))
		}
		for range rng.IntN(20) {
			edges = append(edges, edge{fmt.Sprint(rng.IntN(8)), fmt.Sprint(rng.IntN(8))})
		}
		for fuel := 0; fuel <= len(vertices)+1; fuel++ {
			if got, want := acyclic(edges, fuel, vertices), acyclicReference(edges, fuel, vertices); got != want {
				t.Fatalf("vertices %v edges %v fuel %d: %t != %t", vertices, edges, fuel, got, want)
			}
		}
	}
}

func BenchmarkAcyclic(b *testing.B) {
	for _, shape := range []string{"line", "fan-in", "dense"} {
		for _, n := range []int{128, 256, 512} {
			vertices := make([]string, n)
			var edges []edge
			for i := range vertices {
				vertices[i] = fmt.Sprint(i)
			}
			for i := 0; i < n; i++ {
				for j := i + 1; j < n; j++ {
					if shape == "dense" || (shape == "line" && j == i+1) || (shape == "fan-in" && j == n-1) {
						edges = append(edges, edge{vertices[i], vertices[j]})
					}
				}
			}
			b.Run(fmt.Sprintf("%s/%d", shape, n), func(b *testing.B) {
				b.ReportAllocs()
				b.ReportMetric(float64(n+len(edges)), "vertices+edges")
				for i := 0; i < b.N; i++ {
					if !acyclic(edges, n, vertices) {
						b.Fatal("acyclic graph rejected")
					}
				}
			})
		}
	}
}

func BenchmarkKindChain(b *testing.B) {
	for _, n := range []int{128, 256, 512} {
		p := mergeChain(n)
		b.Run(fmt.Sprint(n), func(b *testing.B) {
			b.ReportAllocs()
			for i := 0; i < b.N; i++ {
				if len(p.Workflows[0].deriveKinds(p)) != n+1 {
					b.Fatal("missing kind")
				}
			}
		})
	}
}
