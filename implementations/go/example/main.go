package main

import "context"

func main() {
	graph := createGraph()
	printResult(graph.Run(context.Background()))
}
