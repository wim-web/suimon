package main

import (
	"fmt"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

// runnableGraph is the example's driver for sequential, single-input/output
// leaf nodes. It adapts the example's handlers to the Suimon state machine.
type runnableGraph struct {
	definition suimon.Graph
	input      string
	handlers   map[string]func(string) string
}

func (g runnableGraph) run() {
	if err := g.definition.Validate(); err != nil {
		panic(err)
	}

	state := suimon.Initial(g.definition)
	apply := func(op suimon.Op) {
		next, rejected := suimon.Step(state, op)
		if rejected != nil {
			panic(rejected)
		}
		state = next
	}

	// The application stores actual values; Suimon passes their item IDs.
	values := map[string]string{"input": g.input}
	apply(suimon.Op{Kind: "start", Inputs: suimon.List[suimon.Input]{
		{Entry: g.definition.Entries[0], Items: suimon.List[string]{"input"}},
	}})

	// Execute the two nodes sequentially in their graph order.
	for _, node := range g.definition.Nodes {
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
		output := g.handlers[node.ID](input)
		outputID := suimon.DerivedItem("example", nil, node.ID, []string{inputID})
		values[outputID] = output

		apply(suimon.Op{Kind: "complete", Auth: auth, Outputs: suimon.List[suimon.Output]{
			{Port: "out", Items: suimon.List[string]{outputID}},
		}})
		fmt.Printf("%s: %q -> %q\n", node.ID, input, output)
	}

	// Confirm completion and read the value at the workflow's exit.
	apply(suimon.Op{Kind: "idle"})
	if state.Status != "succeeded" {
		panic("workflow did not succeed: " + state.Status)
	}
	exit := g.definition.Exits[0]
	resultID := state.Outgoing(nil, exit.Node, exit.Port)[0].Items()[0]
	fmt.Println("result:", values[resultID])
	fmt.Println("status:", state.Status)
}
