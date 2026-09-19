package main

import (
	"fmt"
	"strings"

	suimon "github.com/wim-web/suimon/implementations/go"
)

// leaf creates one node with a plain input and output for this example.
func leaf(id string) suimon.Node {
	return suimon.Node{
		ID: id,
		Kind: suimon.NodeKind{
			Type:        "leaf",
			Concurrency: suimon.N(1),
			Retry: suimon.RetryPolicy{
				MaxAttempts:  suimon.N(1),
				LeaseSeconds: suimon.N(30),
			},
		},
		Inputs:  suimon.List[suimon.Port]{{Name: "in", Kind: "plain"}},
		Outputs: suimon.List[suimon.Port]{{Name: "out", Kind: "plain"}},
	}
}

func main() {
	// 1. Create and connect two nodes: input -> trim -> uppercase -> result.
	graph := suimon.Graph{
		Nodes: suimon.List[suimon.Node]{leaf("trim"), leaf("uppercase")},
		Edges: suimon.List[suimon.Edge]{
			{Src: suimon.PortRef{Node: "trim", Port: "out"}, Dst: suimon.PortRef{Node: "uppercase", Port: "in"}},
		},
		Entries: suimon.List[suimon.PortRef]{{Node: "trim", Port: "in"}},
		Exits:   suimon.List[suimon.PortRef]{{Node: "uppercase", Port: "out"}},
	}
	if err := graph.Validate(); err != nil {
		panic(err)
	}

	state := suimon.Initial(graph)
	apply := func(op suimon.Op) {
		next, rejected := suimon.Step(state, op)
		if rejected != nil {
			panic(rejected)
		}
		state = next
	}

	// 2. The application stores actual values; Suimon passes their item IDs.
	values := map[string]string{"input": "  hello suimon  "}
	handlers := map[string]func(string) string{
		"trim":      strings.TrimSpace,
		"uppercase": strings.ToUpper,
	}
	apply(suimon.Op{Kind: "start", Inputs: suimon.List[suimon.Input]{
		{Entry: graph.Entries[0], Items: suimon.List[string]{"input"}},
	}})

	// 3. This example executes the two nodes sequentially in their graph order.
	for _, node := range graph.Nodes {
		apply(suimon.Op{Kind: "activate", Node: node.ID})
		auth := suimon.Credentials{
			Instance: suimon.InstanceID(nil, node.ID, nil),
			Attempt:  node.ID + "/attempt-1",
			Token:    node.ID + "/lease-1",
			Now:      state.Now,
		}
		apply(suimon.Op{Kind: "claim", Auth: auth, Worker: "example-worker"})

		instance := state.Instance(auth.Instance)
		inputID := instance.Inputs[0][1]
		input := values[inputID]
		output := handlers[node.ID](input)
		outputID := suimon.DerivedItem("example", nil, node.ID, []string{inputID})
		values[outputID] = output

		apply(suimon.Op{Kind: "complete", Auth: auth, Outputs: suimon.List[suimon.Output]{
			{Port: "out", Items: suimon.List[string]{outputID}},
		}})
		fmt.Printf("%s: %q -> %q\n", node.ID, input, output)
	}

	// 4. Confirm completion and read the value at the workflow's exit.
	apply(suimon.Op{Kind: "idle"})
	if state.Status != "succeeded" {
		panic("workflow did not succeed: " + state.Status)
	}
	exit := graph.Exits[0]
	resultID := state.Outgoing(nil, exit.Node, exit.Port)[0].Items()[0]
	fmt.Println("result:", values[resultID])
	fmt.Println("status:", state.Status)
}
