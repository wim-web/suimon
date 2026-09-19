package suimon

import (
	"context"
	"fmt"
	"os"
	"regexp"
	"slices"
	"strings"
	"testing"
)

func TestWorkflowRuntime(t *testing.T) {
	operations := map[string]bool{}
	kinds := map[string]bool{}
	check := func(t *testing.T, result RunResult) {
		t.Helper()
		assertRuntimeTrace(t, result)
		for _, event := range result.Snapshot.Events {
			if event.Op != nil {
				operations[event.Op.Kind] = true
			}
		}
		for _, instance := range result.State.Instances {
			if n := result.State.Node(instance.Path, instance.Node); n != nil {
				kinds[n.Kind.Type] = true
			}
		}
	}
	cases := []struct {
		name string
		run  func(*testing.T, runtimeCheck)
	}{
		{"graphs", testWorkflowGraphFixtures},
		{"streaming", testWorkflowStreaming},
		{"fast-producer", testWorkflowFastProducer},
		{"retry-and-renew", testWorkflowRetryAndRenew},
		{"manual-retry", testWorkflowManualRetry},
		{"cancel-and-terminal", testWorkflowCancelAndTerminal},
		{"redelivery", testWorkflowRedelivery},
		{"persistence", testWorkflowPersistence},
		{"oracle-and-errors", testWorkflowOracleAndFailures},
		{"ordering-and-boundaries", testWorkflowOrdering},
	}
	executed := 0
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) { executed++; tc.run(t, check) })
	}
	if executed != len(cases) {
		return
	}
	// Read Lean's constructors so a new operation or node kind needs a runtime case.
	constructors := regexp.MustCompile(`(?m)^\s*\| ([A-Za-z][A-Za-z0-9_]*)\b`)
	opSource, err := os.ReadFile("../../../Suimon/Op.lean")
	if err != nil {
		t.Fatal(err)
	}
	for _, match := range constructors.FindAllStringSubmatch(string(opSource), -1) {
		if !operations[match[1]] {
			t.Errorf("no actual runtime trace covers Op.%s", match[1])
		}
	}
	graphSource, err := os.ReadFile("../../../Suimon/Graph.lean")
	if err != nil {
		t.Fatal(err)
	}
	nodeKinds := strings.SplitN(strings.SplitN(string(graphSource), "inductive NodeKind where", 2)[1], "deriving Repr", 2)[0]
	for _, match := range constructors.FindAllStringSubmatch(nodeKinds, -1) {
		if !kinds[match[1]] {
			t.Errorf("no executed instance covers NodeKind.%s", match[1])
		}
	}
	t.Logf("actual runtime traces cover %d operations and %d node kinds", len(operations), len(kinds))
}

func testWorkflowOrdering(t *testing.T, check runtimeCheck) {
	for _, name := range []string{"diamond", "streaming", "merge", "filter", "coalesce-loop"} {
		t.Run(name, func(t *testing.T) {
			var bags List[ChannelBag]
			var outputs List[ResultPort]
			for _, workers := range []int{1, 3, 0} {
				w := newFixtureWorkflow(t, name)
				w.Options.Workers = workers
				if workers != 1 {
					var reverse func(*Graph)
					reverse = func(g *Graph) {
						slices.Reverse(g.Nodes)
						for j := range g.Nodes {
							if g.Nodes[j].Kind.Body != nil {
								reverse(g.Nodes[j].Kind.Body)
							}
						}
					}
					reverse(&w.Graph)
					var bindEmitters func(Graph, Path)
					bindEmitters = func(g Graph, path Path) {
						for _, n := range g.Nodes {
							p := append(slices.Clone(path), n.ID)
							if n.Kind.Type == "leaf" && anyOf(n.Outputs, func(p Port) bool { return p.Kind == "stream" }) {
								bindingAt(&w, p...).Leaf = func(_ context.Context, task *Task) (Values, error) {
									for _, port := range n.Outputs {
										if port.Kind == "stream" {
											for i := 2; i >= 0; i-- {
												if err := task.Emit(port.Name, fmt.Sprint(i), fmt.Sprintf("item-%d", i)); err != nil {
													return nil, err
												}
											}
										}
									}
									return Values{}, nil
								}
							}
							if n.Kind.Body != nil {
								bindEmitters(*n.Kind.Body, p)
							}
						}
					}
					bindEmitters(w.Graph, nil)
				}
				r, err := w.Run(testContext(t))
				if err != nil {
					t.Fatal(err)
				}
				if workers == 1 {
					bags = ChannelBags(r.State)
					outputs = r.Outputs
				} else {
					assertJSON(t, "schedule-independent channel bags", ChannelBags(r.State), bags)
					assertJSON(t, "schedule-independent application output", r.Outputs, outputs)
				}
				check(t, r)
			}
		})
	}
	t.Run("empty-stream", func(t *testing.T) {
		w := newFixtureWorkflow(t, "streaming")
		bindingAt(&w, "emit").Leaf = func(context.Context, *Task) (Values, error) { return Values{}, nil }
		bindingAt(&w, "each", "work").Leaf = func(context.Context, *Task) (Values, error) { return nil, fmt.Errorf("empty stream launched a body") }
		r, err := w.Run(testContext(t))
		if err != nil {
			t.Fatal(err)
		}
		var values []any
		if err := r.Output("collect", "out")[0].Decode(&values); err != nil || len(values) != 0 {
			t.Fatalf("empty collection: %v %v", values, err)
		}
		check(t, r)
	})
	t.Run("merge-preserves-shared-occurrences", func(t *testing.T) {
		base := readGraph(t, "merge")
		g := Graph{Nodes: List[Node]{*base.Node("merge"), *base.Node("collect")}, Edges: List[Edge]{{PortRef{"merge", "out"}, PortRef{"collect", "in"}}}, Entries: List[PortRef]{{"merge", "a"}, {"merge", "b"}}, Exits: List[PortRef]{{"collect", "out"}}}
		w := Workflow{Graph: g, Inputs: []ValueInput{{g.Entries[0], []InputItem{{"shared", "same"}}}, {g.Entries[1], []InputItem{{"shared", "same"}}}}, Options: RunOptions{Now: func() Nat { return N(1000) }}}
		r, err := w.Run(testContext(t))
		if err != nil {
			t.Fatal(err)
		}
		var values []string
		if err := r.Output("collect", "out")[0].Decode(&values); err != nil {
			t.Fatal(err)
		}
		assertJSON(t, "merge multiplicity", values, []string{"same", "same"})
		check(t, r)
	})
	t.Run("nested-streaming-body", func(t *testing.T) {
		g := readGraph(t, "nested")
		body := readGraph(t, "streaming")
		g.Nodes[0].Kind.Body = &body
		w := Workflow{Graph: g, Bindings: fixtureBindings(g), Inputs: workflowInputs(g), Options: RunOptions{Now: func() Nat { return N(1000) }}}
		r, err := w.Run(testContext(t))
		if err != nil {
			t.Fatal(err)
		}
		if !SucceededDrained(r.State) {
			t.Fatal("nested streams did not drain")
		}
		check(t, r)
	})
}
