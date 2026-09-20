package main

import (
	"fmt"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

func printResult(result suimon.RunResult, err error) {
	if err != nil {
		panic(err)
	}
	for _, output := range result.Outputs {
		for _, item := range output.Items {
			fmt.Printf("result %s.%s: %s\n", output.Port.Node, output.Port.Port, item.Value)
		}
	}
	fmt.Println("status:", result.State.Status)
}
