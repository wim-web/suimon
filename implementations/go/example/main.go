package main

import (
	"context"
	"flag"
	"fmt"
	"log"
	"time"
)

var (
	ui       = flag.Bool("ui", false, "serve the browser example")
	listen   = flag.String("listen", "127.0.0.1:8080", "UI listen address")
	uiDir    = flag.String("ui-dir", "example/ui/dist", "built example UI directory (relative to the working directory)")
	sampleID = flag.String("scenario", "streaming", "streaming, batch, or basic")
	delay    = flag.Duration("delay", 600*time.Millisecond, "duration of one simulated I/O step")
)

func main() {
	flag.Parse()
	if *ui {
		if err := serveUI(*listen, *uiDir); err != nil {
			log.Fatal(err)
		}
		return
	}
	input := streamInput
	if *sampleID == "basic" {
		input = "  hello suimon  "
	}
	started := time.Now()
	graph, err := scenario(*sampleID, input, demoConfig{delay: *delay, logf: func(format string, args ...any) {
		log.Printf("[%5.2fs] %s", time.Since(started).Seconds(), fmt.Sprintf(format, args...))
	}})
	if err != nil {
		log.Fatal(err)
	}
	printResult(graph.Run(context.Background()))
}
