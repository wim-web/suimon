package suimon

import (
	"fmt"
	"testing"
)

func TestGraphUTF8Names(t *testing.T) {
	for _, field := range []string{"node", "input", "output"} {
		for _, nested := range []bool{false, true} {
			for _, tc := range []struct {
				name, value string
				valid       bool
			}{
				{"ascii", "name", true}, {"unicode", "日本語😀", true}, {"replacement", "\ufffd", true},
				{"invalid-ff", "\xff", false}, {"invalid-fe", "\xfe", false}, {"truncated", "あ"[:1], false},
			} {
				t.Run(fmt.Sprintf("%s/nested=%v/%s", field, nested, tc.name), func(t *testing.T) {
					g := readGraph(t, "minimal")
					switch field {
					case "node":
						g.Nodes[0].ID, g.Entries[0].Node, g.Exits[0].Node = tc.value, tc.value, tc.value
					case "input":
						g.Nodes[0].Inputs[0].Name, g.Entries[0].Port = tc.value, tc.value
					case "output":
						g.Nodes[0].Outputs[0].Name, g.Exits[0].Port = tc.value, tc.value
					}
					if nested {
						body := g
						g = Graph{Nodes: List[Node]{{ID: "parent", Kind: NodeKind{Type: "subworkflow", Body: &body},
							Inputs: List[Port]{{"in", "plain"}}, Outputs: List[Port]{{"out", "plain"}}}},
							Entries: List[PortRef]{{"parent", "in"}}, Exits: List[PortRef]{{"parent", "out"}}}
					}
					if err := g.Validate(); (err == nil) != tc.valid {
						t.Fatalf("Validate: got %v, want valid=%v", err, tc.valid)
					}
				})
			}
		}
	}
	t.Run("branch-arm", func(t *testing.T) {
		g := Graph{Nodes: List[Node]{{ID: "choose", Kind: NodeKind{Type: "branch", Arms: List[string]{"\ufffd"}},
			Inputs: List[Port]{{"in", "plain"}}, Outputs: List[Port]{{"\ufffd", "plain"}}}},
			Entries: List[PortRef]{{"choose", "in"}}, Exits: List[PortRef]{{"choose", "\ufffd"}}}
		if err := g.Validate(); err != nil {
			t.Fatal(err)
		}
		for _, arm := range []string{"\xff", "\xfe"} {
			g.Nodes[0].Kind.Arms[0] = arm
			if err := g.Validate(); err == nil {
				t.Errorf("invalid arm %q matched the replacement-character output", arm)
			}
		}
	})
}
