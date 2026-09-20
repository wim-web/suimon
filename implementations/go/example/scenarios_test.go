package main

import (
	"context"
	"encoding/json"
	"slices"
	"sync/atomic"
	"testing"
	"time"

	suimon "github.com/wim-web/suimon/implementations/go/src"
)

func TestStreamingOverlapAndCollect(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	producerPaused, releaseProducer, releaseWorkers := make(chan struct{}), make(chan struct{}), make(chan struct{})
	var producerSleeps atomic.Int32
	w, err := scenario("streaming", streamInput, demoConfig{delay: time.Millisecond, sleep: func(ctx context.Context, delay time.Duration) error {
		if delay == time.Millisecond {
			if producerSleeps.Add(1) != 5 {
				return nil
			}
			close(producerPaused)
			select {
			case <-releaseProducer:
				return nil
			case <-ctx.Done():
				return ctx.Err()
			}
		}
		select {
		case <-releaseWorkers:
			return nil
		case <-ctx.Done():
			return ctx.Err()
		}
	}})
	if err != nil {
		t.Fatal(err)
	}
	e, err := w.Start(ctx)
	if err != nil {
		t.Fatal(err)
	}
	defer e.Stop()
	select {
	case <-producerPaused:
	case <-ctx.Done():
		t.Fatal(ctx.Err())
	}
	partial, err := e.WaitFor(ctx, func(state suimon.State) bool {
		running, ready := 0, 0
		for _, instance := range state.Instances {
			if instance.Node == "uppercase" {
				if instance.Status == "running" {
					running++
				}
				if instance.Status == "ready" {
					ready++
				}
			}
		}
		return running == 2 && ready == 1
	})
	if err != nil {
		t.Fatal(err)
	}
	if partial.State.NodeInstance(nil, "source").Status != "running" || partial.State.NodeInstance(nil, "collect") != nil {
		t.Fatal("producer/consumer overlap or collect boundary lost")
	}
	close(releaseWorkers)
	_, err = e.WaitFor(ctx, func(state suimon.State) bool {
		done := 0
		for _, instance := range state.Instances {
			if instance.Node == "uppercase" && instance.Status == "succeeded" {
				done++
			}
		}
		return done == 3
	})
	if err != nil {
		t.Fatal(err)
	}
	if e.Result().State.NodeInstance(nil, "collect") != nil {
		t.Fatal("collect ran before source EOS")
	}
	// Items arrive at Collect before it is instantiated or consumes anything.
	queued, err := e.WaitFor(ctx, func(state suimon.State) bool {
		channels := state.Incoming(nil, "collect")
		return len(channels) == 1 && len(channels[0].Items()) == 3
	})
	if err != nil {
		t.Fatal(err)
	}
	channel := queued.State.Incoming(nil, "collect")[0]
	if channel.Closed() || !channel.Consumed.IsZero() || queued.State.NodeInstance(nil, "collect") != nil {
		t.Fatal("Collect must retain pending input until EOS")
	}
	close(releaseProducer)
	result, err := e.Wait(ctx)
	if err != nil {
		t.Fatal(err)
	}
	assertStreamOutput(t, result)
}

func TestBatchWaitsForGeneration(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	paused, release := make(chan struct{}), make(chan struct{})
	var sleeps atomic.Int32
	w, err := scenario("batch", streamInput, demoConfig{delay: time.Millisecond, sleep: func(ctx context.Context, delay time.Duration) error {
		if delay == time.Millisecond && sleeps.Add(1) == 5 {
			close(paused)
			select {
			case <-release:
			case <-ctx.Done():
				return ctx.Err()
			}
		}
		return nil
	}})
	if err != nil {
		t.Fatal(err)
	}
	e, err := w.Start(ctx)
	if err != nil {
		t.Fatal(err)
	}
	defer e.Stop()
	select {
	case <-paused:
	case <-ctx.Done():
		t.Fatal(ctx.Err())
	}
	for _, event := range e.Result().Snapshot.Events {
		if event.Op != nil && (event.Op.Kind == "emit" || event.Op.Kind == "spawn") {
			t.Fatal("batch released an item while generation was in progress")
		}
	}
	close(release)
	result, err := e.Wait(ctx)
	if err != nil {
		t.Fatal(err)
	}
	assertStreamOutput(t, result)
}

func assertStreamOutput(t *testing.T, result suimon.RunResult) {
	t.Helper()
	if state, diagnostic := suimon.Check(result.Snapshot.Graph, result.Snapshot.Events); diagnostic != nil || state.Status != "succeeded" {
		t.Fatalf("invalid trace: %v", diagnostic)
	}
	var output []streamItem
	if err := result.Output("collect", "out")[0].Decode(&output); err != nil {
		t.Fatal(err)
	}
	slices.SortFunc(output, func(a, b streamItem) int { return a.Index - b.Index })
	want := []streamItem{{0, "ALPHA"}, {1, "BRAVO"}, {3, "CHARLIE"}, {4, "DELTA"}, {5, "ECHO"}}
	if !slices.Equal(output, want) {
		t.Fatalf("got %#v", output)
	}
}

func TestStreamingEmptyAndFilteredInput(t *testing.T) {
	for _, input := range []string{"", "#one #two"} {
		w, _ := scenario("streaming", input, demoConfig{sleep: func(context.Context, time.Duration) error { return nil }})
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		result, err := w.Run(ctx)
		cancel()
		if err != nil {
			t.Fatal(err)
		}
		var output []json.RawMessage
		if err := result.Output("collect", "out")[0].Decode(&output); err != nil || len(output) != 0 {
			t.Fatalf("unexpected output: %v %#v", err, output)
		}
	}
}

func TestSleepCancellation(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	if err := sleep(ctx, time.Hour); err != context.Canceled {
		t.Fatalf("sleep ignored cancellation: %v", err)
	}
}
