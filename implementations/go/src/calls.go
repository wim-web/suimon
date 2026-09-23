package suimon

import (
	"context"
	"errors"
	"iter"
	"runtime/debug"
	"time"
)

// The goroutines that run user code. Each call gets one; it reports to the driver with events and
// never touches the state. A call's context is cancelled by the driver only, after the operation
// that cancels the call (a timeout, a stop, the caller's cancellation) is durable.

// start runs the user code of a call whose creation is durable, and arms its call timeout, which
// counts from here (§11.5).
func (d *driver) start(c *Call) {
	ctx, cancel := context.WithCancel(d.base)
	fetch := make(chan struct{}, 1)
	cr := &callRuntime{cancel: cancel, fetch: fetch}
	d.calls[c.ID] = cr
	var input []byte
	if c.Input != nil {
		input = []byte(d.payloadOf(*c.Input))
	}
	id, target := c.ID, c.Target.ID
	if c.Timeout.CallMs != nil {
		cr.callTimer = time.AfterFunc(duration(*c.Timeout.CallMs), func() { d.send(event{call: id, kind: evTimer}) })
	}
	var body func(report func(event))
	switch {
	case c.Target.Judge:
		b, ok := d.registry.judges[target]
		body = func(report func(event)) {
			if !ok {
				report(event{kind: evFailed, err: errors.New("suimon: judge " + target + " is not bound")})
				return
			}
			arm, err := b.judge(ctx, input)
			if err != nil {
				report(event{kind: evFailed, err: err})
				return
			}
			report(event{kind: evJudged, arm: arm})
		}
	case c.Stream:
		b, ok := d.registry.functions[target]
		body = func(report func(event)) {
			if !ok || b.stream == nil {
				report(event{kind: evFailed, err: errors.New("suimon: Stream function " + target + " is not bound")})
				return
			}
			generate(ctx, fetch, b.stream(ctx, input), report)
		}
	default:
		b, ok := d.registry.functions[target]
		body = func(report func(event)) {
			if !ok || b.function == nil {
				report(event{kind: evFailed, err: errors.New("suimon: function " + target + " is not bound")})
				return
			}
			out, err := b.function(ctx, input)
			if err != nil {
				report(event{kind: evFailed, err: err})
				return
			}
			report(event{kind: evReturned, value: out})
		}
	}
	go d.guard(id, body)
}

// guard runs body in the call's goroutine and makes sure the goroutine reports its end once: a
// panic, or a runtime.Goexit in user code, fails the call.
func (d *driver) guard(id string, body func(report func(event))) {
	ended := false
	report := func(ev event) {
		ev.call = id
		ended = ended || ev.terminal()
		d.send(ev)
	}
	defer func() {
		p := recover()
		switch {
		case ended:
			// The end is reported; what follows it changes nothing.
		case p != nil:
			report(event{kind: evFailed, err: &PanicError{Value: p, Stack: debug.Stack()}})
		default:
			report(event{kind: evFailed, err: errors.New("suimon: the user code exited its goroutine")})
		}
	}()
	body(report)
}

// generate reads a Stream generator one element at a time: it pulls the next element only when
// the driver has recorded a fetch, and after the call was cancelled it pulls nothing more, ends
// the generator, and reports that the user code has returned (§4.1.1, §11.3). A panic of the
// generator reaches guard.
func generate(ctx context.Context, fetch <-chan struct{}, seq iter.Seq2[[]byte, error], report func(event)) {
	next, stop := iter.Pull2(seq)
	defer stop()
	exit := func() {
		stop()
		report(event{kind: evExited})
	}
	for index := 0; ; index++ {
		select {
		case <-fetch:
		case <-ctx.Done():
			exit()
			return
		}
		if ctx.Err() != nil {
			exit()
			return
		}
		value, err, ok := next()
		switch {
		case ctx.Err() != nil:
			exit()
		case !ok:
			report(event{kind: evEnded})
		case err != nil:
			stop()
			report(event{kind: evFailed, err: err})
		default:
			report(event{kind: evYielded, value: value, index: index})
			continue
		}
		return
	}
}
