package main

import (
	"context"
	"fmt"
	"strings"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

func trim(_ context.Context, task *suimon.Task) (suimon.Values, error) {
	var input string
	if err := task.DecodeInput("in", &input); err != nil {
		return nil, err
	}
	output := strings.TrimSpace(input)
	fmt.Printf("trim: %q -> %q\n", input, output)
	return suimon.Values{"out": output}, nil
}

func uppercase(_ context.Context, task *suimon.Task) (suimon.Values, error) {
	var input string
	if err := task.DecodeInput("in", &input); err != nil {
		return nil, err
	}
	output := strings.ToUpper(input)
	fmt.Printf("uppercase: %q -> %q\n", input, output)
	return suimon.Values{"out": output}, nil
}
