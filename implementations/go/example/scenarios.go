package main

import (
	"context"
	"fmt"
	"strings"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

const streamInput = "alpha bravo #skip charlie delta echo"

type demoConfig struct {
	delay time.Duration
	sleep func(context.Context, time.Duration) error
	logf  func(string, ...any)
}

func (c demoConfig) defaults() demoConfig {
	if c.delay == 0 {
		c.delay = 600 * time.Millisecond
	}
	if c.sleep == nil {
		c.sleep = sleep
	}
	if c.logf == nil {
		c.logf = func(string, ...any) {}
	}
	return c
}

// sleep simulates external I/O while allowing disconnect/cancellation to stop it.
func sleep(ctx context.Context, delay time.Duration) error {
	timer := time.NewTimer(delay)
	defer timer.Stop()
	select {
	case <-timer.C:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

type sample struct {
	ID          string       `json:"id"`
	Title       string       `json:"title"`
	Description string       `json:"description"`
	Input       string       `json:"input"`
	Graph       suimon.Graph `json:"graph"`
}

func samples() []sample {
	stream := streamingGraph()
	return []sample{
		{"streaming", "Streaming pipeline", "一定間隔で Emit。生成が続いている間に、下流で最大2件を並列処理します。", streamInput, stream},
		{"batch", "Batch comparison", "同じグラフ・同じ待ち時間。全件生成後にまとめて Emit し、下流の開始時刻を比較します。", streamInput, stream},
		{"basic", "Text processing", "trim → uppercase の基本例。", "  hello suimon  ", createGraph().Graph},
	}
}

func scenario(id, input string, config demoConfig) (suimon.Workflow, error) {
	if id == "basic" {
		w := createGraph()
		w.Inputs[0].Items[0].Value = input
		return w, nil
	}
	if id != "streaming" && id != "batch" {
		return suimon.Workflow{}, fmt.Errorf("unknown scenario %q", id)
	}
	if len(strings.Fields(input)) > 12 {
		return suimon.Workflow{}, fmt.Errorf("stream demo supports at most 12 items")
	}
	return streamingWorkflow(input, id == "batch", config.defaults()), nil
}

func streamingGraph() suimon.Graph {
	worker := leaf("uppercase")
	worker.Kind.Concurrency = suimon.N(2)
	body := suimon.Graph{Nodes: suimon.List[suimon.Node]{worker}, Entries: suimon.List[suimon.PortRef]{{Node: "uppercase", Port: "in"}}, Exits: suimon.List[suimon.PortRef]{{Node: "uppercase", Port: "out"}}}
	producer := leaf("source")
	producer.Outputs = suimon.List[suimon.Port]{{Name: "items", Kind: "stream"}}
	return suimon.Graph{
		Nodes: suimon.List[suimon.Node]{
			producer,
			{ID: "filter", Kind: suimon.NodeKind{Type: "filter"}, Inputs: suimon.List[suimon.Port]{{Name: "in", Kind: "stream"}}, Outputs: suimon.List[suimon.Port]{{Name: "out", Kind: "stream"}}},
			{ID: "each", Kind: suimon.NodeKind{Type: "forEach", Body: &body}, Inputs: suimon.List[suimon.Port]{{Name: "in", Kind: "stream"}}, Outputs: suimon.List[suimon.Port]{{Name: "out", Kind: "stream"}}},
			{ID: "collect", Kind: suimon.NodeKind{Type: "collect"}, Inputs: suimon.List[suimon.Port]{{Name: "in", Kind: "stream"}}, Outputs: suimon.List[suimon.Port]{{Name: "out", Kind: "plain"}}},
		},
		Edges: suimon.List[suimon.Edge]{
			{Src: suimon.PortRef{Node: "source", Port: "items"}, Dst: suimon.PortRef{Node: "filter", Port: "in"}},
			{Src: suimon.PortRef{Node: "filter", Port: "out"}, Dst: suimon.PortRef{Node: "each", Port: "in"}},
			{Src: suimon.PortRef{Node: "each", Port: "out"}, Dst: suimon.PortRef{Node: "collect", Port: "in"}},
		},
		Entries: suimon.List[suimon.PortRef]{{Node: "source", Port: "in"}},
		Exits:   suimon.List[suimon.PortRef]{{Node: "collect", Port: "out"}},
	}
}

type streamItem struct {
	Index int    `json:"index"`
	Text  string `json:"text"`
}

func streamingWorkflow(input string, batch bool, config demoConfig) suimon.Workflow {
	return suimon.Workflow{
		Graph:  streamingGraph(),
		Inputs: []suimon.ValueInput{{Entry: suimon.PortRef{Node: "source", Port: "in"}, Items: []suimon.InputItem{{ID: "input", Value: input}}}},
		Bindings: []suimon.Binding{
			{Path: suimon.Path{"source"}, Leaf: func(ctx context.Context, task *suimon.Task) (suimon.Values, error) {
				var text string
				if err := task.DecodeInput("in", &text); err != nil {
					return nil, err
				}
				words := strings.Fields(text)
				emit := func(i int, word string) error {
					if err := task.Emit("items", fmt.Sprintf("item-%02d", i), streamItem{i, word}); err != nil {
						return err
					}
					config.logf("source emit #%d %q", i+1, word)
					return nil
				}
				for i, word := range words {
					if err := config.sleep(ctx, config.delay); err != nil {
						return nil, err
					}
					config.logf("source generated #%d %q", i+1, word)
					if !batch {
						if err := emit(i, word); err != nil {
							return nil, err
						}
					}
				}
				// Keep the producer open after its last item so EOS is observable.
				if err := config.sleep(ctx, config.delay); err != nil {
					return nil, err
				}
				if batch {
					for i, word := range words {
						if err := emit(i, word); err != nil {
							return nil, err
						}
					}
				}
				config.logf("source finished / EOS (%d items)", len(words))
				return suimon.Values{}, nil
			}},
			{Path: suimon.Path{"filter"}, Filter: func(_ context.Context, task suimon.DecisionTask) (bool, error) {
				var item streamItem
				if err := task.Item.Decode(&item); err != nil {
					return false, err
				}
				keep := !strings.HasPrefix(item.Text, "#")
				config.logf("filter #%d keep=%t", item.Index+1, keep)
				return keep, nil
			}},
			{Path: suimon.Path{"each", "uppercase"}, Leaf: func(ctx context.Context, task *suimon.Task) (suimon.Values, error) {
				var item streamItem
				if err := task.DecodeInput("in", &item); err != nil {
					return nil, err
				}
				// Different sleep lengths make overlapping work and out-of-order
				// completion visible. Concurrency=2 is enforced across all bodies.
				delay := time.Duration([]int{4, 2, 3}[item.Index%3]) * config.delay
				config.logf("worker start #%d %q (sleep %s)", item.Index+1, item.Text, delay)
				if err := config.sleep(ctx, delay); err != nil {
					return nil, err
				}
				item.Text = strings.ToUpper(item.Text)
				config.logf("worker done #%d %q", item.Index+1, item.Text)
				return suimon.Values{"out": item}, nil
			}},
		},
		Options: suimon.RunOptions{PollInterval: 25 * time.Millisecond},
	}
}
