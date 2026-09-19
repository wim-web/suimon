package main

import suimon "github.com/wim-web/suimon/implementations/go/src"

// createGraph defines the topology, input, and processing functions.
func createGraph() suimon.Workflow {
	return suimon.Workflow{
		Graph: suimon.Graph{
			Nodes: suimon.List[suimon.Node]{leaf("trim"), leaf("uppercase")},
			Edges: suimon.List[suimon.Edge]{
				{Src: suimon.PortRef{Node: "trim", Port: "out"}, Dst: suimon.PortRef{Node: "uppercase", Port: "in"}},
			},
			Entries: suimon.List[suimon.PortRef]{{Node: "trim", Port: "in"}},
			Exits:   suimon.List[suimon.PortRef]{{Node: "uppercase", Port: "out"}},
		},
		Inputs: []suimon.ValueInput{
			{Entry: suimon.PortRef{Node: "trim", Port: "in"}, Items: []suimon.InputItem{{ID: "input", Value: "  hello suimon  "}}},
		},
		Bindings: []suimon.Binding{
			{Path: suimon.Path{"trim"}, Leaf: trim},
			{Path: suimon.Path{"uppercase"}, Leaf: uppercase},
		},
	}
}

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
