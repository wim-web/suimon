package main

import "context"

func Example() {
	printResult(createGraph().Run(context.Background()))
	// Output:
	// trim: "  hello suimon  " -> "hello suimon"
	// uppercase: "hello suimon" -> "HELLO SUIMON"
	// result uppercase.out: "HELLO SUIMON"
	// status: succeeded
}
