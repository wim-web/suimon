package suimon

import (
	"context"
	"os"
	"testing"
)

func TestOracleContractAgainstLean(t *testing.T) {
	if os.Getenv("SUIMON_LEAN_ORACLE") == "" {
		t.Skip("run bin/test-go for the Lean oracle contract comparison")
	}
	o := newOracle(t)
	for _, name := range []string{"streaming", "filter", "coalesce-loop"} {
		w := newFixtureWorkflow(t, name)
		result, err := w.Run(testContext(t))
		if err != nil {
			t.Fatal(err)
		}
		state := Initial(w.Graph)
		for _, event := range result.Snapshot.Events {
			if event.Op == nil {
				continue
			}
			op := *event.Op
			leaf := List[Output]{}
			if i := result.State.Instance(op.Auth.Instance); i != nil {
				n := result.State.Node(i.Path, i.Node)
				for _, p := range n.Outputs {
					ids := List[string]{PlainItemID(i.Path, i.Node, p.Name)}
					if p.Kind == "stream" {
						cs := result.State.Outgoing(i.Path, i.Node, p.Name)
						if len(cs) > 0 {
							ids = cs[0].Items()
						} else {
							ids = nil
						}
					}
					leaf = append(leaf, Output{p.Name, ids})
				}
			}
			oracle := ScopedOracle{Leaf: func(Path, string, List[[2]string]) List[Output] { return leaf }, Branch: func(Path, string, string) string { return op.Arm }, Filter: func(Path, string, string) bool { return op.Keep }, Loop: func(Path, string, Nat, string) bool { return op.Done }}
			compare := func(probe Op) {
				var want bool
				o.ask(map[string]any{"action": "conforms", "state": state, "op": probe, "leaf": leaf, "arm": op.Arm, "keep": op.Keep, "done": op.Done}, &want)
				if got := OracleConforms(oracle, state, probe); got != want {
					t.Fatalf("oracle %s: Go=%v Lean=%v", probe.Kind, got, want)
				}
			}
			compare(op)
			wrong := op
			switch op.Kind {
			case "emit":
				wrong.Item = "forbidden"
				compare(wrong)
			case "complete":
				leaf = append(leaf, Output{"out", List[string]{"missing"}})
				compare(op)
			case "fireBranch":
				wrong.Arm = "wrong"
				compare(wrong)
			case "fireFilter":
				wrong.Keep = !op.Keep
				compare(wrong)
			case "loopIterate":
				wrong.Done = !op.Done
				compare(wrong)
			}
			var rejected *Reject
			state, rejected = Step(state, op)
			if rejected != nil {
				t.Fatal(rejected)
			}
		}
	}
}

func TestWorkflowMixedOutputs(t *testing.T) {
	w := newFixtureWorkflow(t, "minimal")
	w.Graph.Nodes[0].Outputs = List[Port]{{"a", "plain"}, {"events", "stream"}, {"b", "plain"}}
	w.Graph.Exits = List[PortRef]{{"work", "a"}, {"work", "events"}, {"work", "b"}}
	bindingAt(&w, "work").Leaf = func(_ context.Context, task *Task) (Values, error) {
		if err := task.Emit("events", "one", 1); err != nil {
			return nil, err
		}
		if err := task.Emit("events", "one", 1); err != nil {
			return nil, err
		}
		return Values{"b": 2, "a": 1}, nil
	}
	r, err := w.Run(testContext(t))
	if err != nil {
		t.Fatal(err)
	}
	if len(r.Output("work", "events")) != 1 {
		t.Fatal("duplicate emit was not idempotent")
	}
	assertRuntimeTrace(t, r)
}
