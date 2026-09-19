package suimon

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"
)

func workflowInputs(g Graph) []ValueInput {
	inputs := []ValueInput{}
	for _, p := range g.Entries {
		inputs = append(inputs, ValueInput{Entry: p, Items: []InputItem{{ID: Identity([]string{"input", p.Node, p.Port}), Value: "seed"}}})
	}
	return inputs
}
func fixtureBindings(g Graph) []Binding {
	bindings := []Binding{}
	var visit func(Graph, Path)
	visit = func(g Graph, path Path) {
		for _, n := range g.Nodes {
			p := append(slices.Clone(path), n.ID)
			b := Binding{Path: p}
			switch n.Kind.Type {
			case "leaf":
				b.Leaf = func(ctx context.Context, task *Task) (Values, error) {
					out := Values{}
					for _, p := range n.Outputs {
						if p.Kind == "plain" {
							out[p.Name] = "value:" + task.ID
						} else {
							for i := 0; i < 3; i++ {
								if err := task.Emit(p.Name, fmt.Sprint(i), fmt.Sprintf("item-%d", i)); err != nil {
									return nil, err
								}
							}
						}
					}
					return out, nil
				}
			case "branch":
				b.Branch = func(context.Context, DecisionTask) (string, error) { return n.Kind.Arms[0], nil }
			case "filter":
				b.Filter = func(_ context.Context, d DecisionTask) (bool, error) {
					var v string
					if err := d.Item.Decode(&v); err != nil {
						return false, err
					}
					return v != "item-1", nil
				}
			case "loop":
				b.Loop = func(_ context.Context, d DecisionTask) (bool, error) { return d.Iteration.Cmp(N(2)) >= 0, nil }
			}
			if b.Leaf != nil || b.Branch != nil || b.Filter != nil || b.Loop != nil {
				bindings = append(bindings, b)
			}
			if n.Kind.Body != nil {
				visit(*n.Kind.Body, p)
			}
		}
	}
	visit(g, nil)
	return bindings
}

func assertRuntimeTrace(t *testing.T, result RunResult) {
	t.Helper()
	s, d := Check(result.Snapshot.Graph, result.Snapshot.Events)
	if d != nil {
		t.Fatal(d)
	}
	assertJSON(t, "runtime journal replay", s, result.State)
	if !Invariants(s) {
		t.Fatal("runtime broke model invariants")
	}
	if os.Getenv("SUIMON_LEAN_ORACLE") != "" {
		o := newOracle(t)
		var want struct {
			State      State           `json:"state"`
			Diagnostic *Diagnostic     `json:"diagnostic"`
			Bags       json.RawMessage `json:"bags"`
			Drained    bool            `json:"drained"`
		}
		o.ask(map[string]any{"action": "check", "graph": result.Snapshot.Graph, "lines": mapped(result.Snapshot.Events, EncodeEvent)}, &want)
		if want.Diagnostic != nil {
			t.Fatal(want.Diagnostic)
		}
		assertJSON(t, "Lean replay of actual runtime", s, want.State)
		assertJSON(t, "Lean channel bags", ChannelBags(s), want.Bags)
		if SucceededDrained(s) != want.Drained {
			t.Fatal("Lean drain predicate differs")
		}
	}
}

func testWorkflowGraphFixtures(t *testing.T, check runtimeCheck) {
	paths, err := filepath.Glob("../../../Test/graphs/*.json")
	if err != nil || len(paths) == 0 {
		t.Fatalf("fixtures: %v", err)
	}
	for _, path := range paths {
		t.Run(filepath.Base(path), func(t *testing.T) {
			g := readGraph(t, strings.TrimSuffix(filepath.Base(path), ".json"))
			bindings := fixtureBindings(g)
			// Listing nodes backwards must not change dependency scheduling.
			var reverse func(*Graph)
			reverse = func(g *Graph) {
				slices.Reverse(g.Nodes)
				for j := range g.Nodes {
					if g.Nodes[j].Kind.Body != nil {
						reverse(g.Nodes[j].Kind.Body)
					}
				}
			}
			reverse(&g)
			w := Workflow{Graph: g, Bindings: bindings, Inputs: workflowInputs(g), Options: RunOptions{Now: func() Nat { return N(1000) }, PollInterval: time.Millisecond}}
			ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
			defer cancel()
			result, err := w.Run(ctx)
			if err != nil {
				t.Fatalf("run: %v, status=%s reason=%v", err, result.State.Status, result.State.Reason)
			}
			if result.State.Status != "succeeded" {
				t.Fatal(result.State.Status)
			}
			if !SucceededDrained(result.State) {
				t.Fatal("successful workflow did not drain")
			}
			check(t, result)
		})
	}
}
