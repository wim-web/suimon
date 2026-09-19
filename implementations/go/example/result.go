package main

import (
	"fmt"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

func printResult(result suimon.RunResult, err error) {
	if err != nil {
		panic(err)
	}
	var output string
	if err := result.Output("uppercase", "out")[0].Decode(&output); err != nil {
		panic(err)
	}
	fmt.Println("result:", output)
	fmt.Println("status:", result.State.Status)
}
