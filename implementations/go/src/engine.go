package suimon

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"sync"
	"unicode/utf8"
)

// The runtime: an Engine runs a program with the Go implementations of a Registry. Each execution
// is driven by one goroutine that owns its state and changes it only by the rules of Step, in
// place since nothing else holds it (machine); every accepted operation is recorded (the Journal,
// when there is one) before its effects are published. User code runs in goroutines of its own
// and reports to the driver.

var (
	// ErrTimeout is wrapped by the error of a failure caused by a timeout (§11.5).
	ErrTimeout = errors.New("suimon: timed out")
	// ErrLost is the error of a failure caused by the loss of a call's executor (§11.6), which
	// Resume reports for the calls that were running at the crash.
	ErrLost = errors.New("suimon: the executor of the call was lost")
	// ErrNotStarted is returned by Resume for a journal without a committed start: there is
	// nothing to resume, and the input is not known.
	ErrNotStarted = errors.New("suimon: the journal records no start")
	// ErrStuck is returned by Wait when no operation is possible and no call is running before the
	// execution ends. A valid program does not get there; a program run without validation may.
	ErrStuck = errors.New("suimon: the execution cannot progress")
	// ErrNoOutput is returned by Report.Output for an endpoint without a value.
	ErrNoOutput = errors.New("suimon: no output")
)

// A PanicError is the error of a failure caused by a panic in user code.
type PanicError struct {
	Value any
	Stack []byte
}

func (e *PanicError) Error() string { return fmt.Sprintf("suimon: panic in user code: %v", e.Value) }

// Engine runs one program with the implementations of a registry. It is safe for concurrent use:
// each Start or Resume drives its own execution. The program must not change after NewEngine.
//
// The timeouts of the program are durations here (§11.5): a call fails when it runs longer than
// callMs from the start of its user code (a task's wait for a slot is not counted), and a Stream
// call also when it waits longer than elementMs for its next element. The engine then cancels the
// call's context and accepts nothing more from it; the call keeps its concurrency slot until its
// user code returns.
type Engine struct {
	program  *Program
	registry *Registry
	plans    map[string]*workflowPlan
}

// NewEngine validates p (run, §14) and returns an engine for it. Every function, judge and
// transform the program uses must be bound in r with the declared shape: a Single or a Stream
// function, with or without input. The Go types of the values are not checked against the type
// names of the program; that they match is up to the caller (§4.4).
func NewEngine(p *Program, r *Registry) (*Engine, error) {
	if err := p.Validate(); err != nil {
		return nil, err
	}
	return NewUncheckedEngine(p, r)
}

// NewUncheckedEngine is NewEngine without validating the program (runUnchecked, §14). The engine
// still records, applies the policies, timeouts and limits, and checks each operation with Step,
// but for a program that validation would reject nothing guarantees that the execution ends: Wait
// may return ErrStuck.
func NewUncheckedEngine(p *Program, r *Registry) (*Engine, error) {
	if err := r.check(p); err != nil {
		return nil, err
	}
	return &Engine{program: p, registry: r, plans: newPlans(p)}, nil
}

// A StartOption configures Start and Run.
type StartOption func(*startOptions)

type startOptions struct{ journal Journal }

// WithJournal writes the execution record to j (§12.1), which must be empty, like a journal from
// CreateJournal. Without a journal the record is kept only in memory, and the execution cannot be
// resumed after a crash.
func WithJournal(j Journal) StartOption { return func(o *startOptions) { o.journal = j } }

// Start starts an execution of the main workflow with input, the value of the workflow's Input
// type, encoded as JSON; input must be nil for a workflow without input (§3.1). Start returns once
// the start is recorded; the execution then runs until it concludes or fails to record.
//
// Cancelling ctx cancels the execution, like WorkflowExecution.Cancel. The contexts passed to user
// code carry the values of ctx but are cancelled by the engine alone: on a timeout, a stop, or a
// cancellation, after it is recorded.
func (e *Engine) Start(ctx context.Context, input any, opts ...StartOption) (*WorkflowExecution, error) {
	var o startOptions
	for _, opt := range opts {
		opt(&o)
	}
	d := e.newDriver(ctx, newOwnedRecorder(e.program, &State{}, nil, 0), o.journal)
	op := OpStart{}
	if main, ok := e.program.workflow(e.program.Main); ok && main.Input != nil {
		data, err := encodeValue(input)
		if err != nil {
			return nil, err
		}
		id := inputValue()
		d.payloads[id] = string(data)
		op.Input = &id
	} else if input != nil {
		return nil, errors.New("suimon: the main workflow takes no input")
	}
	if err := d.begin(func() error {
		if err := d.apply(op, nil); err != nil {
			return fmt.Errorf("suimon: the start is rejected: %w", err)
		}
		return nil
	}); err != nil {
		return nil, err
	}
	go d.run(ctx)
	return d.exec, nil
}

// Run starts an execution and waits for its report.
func (e *Engine) Run(ctx context.Context, input any, opts ...StartOption) (*Report, error) {
	x, err := e.Start(ctx, input, opts...)
	if err != nil {
		return nil, err
	}
	return x.Wait()
}

// Resume continues the execution recorded in j after a crash (§12.1). It replays the committed
// transitions with Check, cuts off an uncommitted tail, and restores the state and the payloads
// of its values.
//
// Calls that were running at the crash are reported lost (§11.6) before anything else, and are
// not called again: this engine runs user code in its own process, so the executor that held each
// such call ended with the process, and no lease of it can still be valid; an engine whose calls
// run in other processes would wait for their leases to expire instead. The calls are reported in
// the order they were created. Each fails under its policy, as a call whose lease expired, until
// one of them stops the workflow: the calls after it, like calls that were already being cancelled
// at the crash, end as cancelled (Step). The execution then continues from the recovered state.
//
// The journal must record an execution of this engine's program, and no other execution may write
// it meanwhile; a journal whose execution has concluded gives an execution that is already done.
// ctx is used as in Start.
func (e *Engine) Resume(ctx context.Context, j RecoverableJournal) (*WorkflowExecution, error) {
	data, err := j.Contents()
	if err != nil {
		return nil, err
	}
	c, err := Check(e.program, string(data))
	if err != nil {
		return nil, fmt.Errorf("suimon: the journal does not replay: %w", err)
	}
	if c.Committed == 0 {
		return nil, ErrNotStarted
	}
	if c.Length < len(data) {
		if err := j.Truncate(int64(c.Length)); err != nil {
			return nil, err
		}
	}
	var running []string
	for _, call := range c.State.Calls {
		if !call.Status.ended() {
			running = append(running, call.ID)
		}
	}
	// The driver takes the state of c over and changes it in place.
	d := e.newDriver(ctx, newOwnedRecorder(e.program, c.State, c.Values, c.Committed), j)
	for _, v := range c.Values {
		d.payloads[v.Value] = v.Payload
	}
	d.errs = make([]error, len(c.State.Failures))
	if err := d.begin(func() error {
		for _, call := range running {
			if err := d.apply(OpLost{Call: call}, ErrLost); err != nil {
				return fmt.Errorf("suimon: reporting call %s lost: %w", call, err)
			}
		}
		return nil
	}); err != nil {
		return nil, err
	}
	go d.run(ctx)
	return d.exec, nil
}

// WorkflowExecution is a running or ended execution of a workflow.
type WorkflowExecution struct {
	cancelOnce sync.Once
	cancel     chan struct{}
	done       chan struct{}
	// report and err are set before done is closed.
	report *Report
	err    error
}

// Cancel cancels the execution, as its caller (§11.3): the engine records the cancellation,
// starts nothing new, accepts no new result, cancels the contexts of the running calls, waits for
// their user code to return, and concludes. The status is cancelled, or failed when a failure was
// recorded. Cancel does not wait; use Wait. After the execution ended it does nothing.
func (x *WorkflowExecution) Cancel() { x.cancelOnce.Do(func() { close(x.cancel) }) }

// Done is closed when the execution has ended.
func (x *WorkflowExecution) Done() <-chan struct{} { return x.done }

// Wait waits for the execution to end and returns its report. The report tells how the workflow
// ended, failures included; the error is not nil only when the engine could not continue: when
// the journal failed (the record written so far can still be resumed), or ErrStuck. The report is
// nil then.
func (x *WorkflowExecution) Wait() (*Report, error) {
	<-x.done
	return x.report, x.err
}

// Report is how a workflow execution ended.
type Report struct {
	// Status is the final status: succeeded, failed, cancelled or skipped (§13.3).
	Status Status
	// Outputs holds the value of each endpoint of the main workflow that has one, as JSON, by
	// placement name (§13.3). An endpoint without a value has no entry. The list of a waitStream,
	// a Merge or a List concurrency is a JSON array whose order means nothing (§5.4), though equal
	// runs give the same order.
	Outputs map[string]json.RawMessage
	// Endpoints holds how each settled endpoint of the main workflow ended. After a stop or a
	// cancellation, an endpoint that did not settle has no entry.
	Endpoints map[string]Outcome
	// Failures are the recorded failures, in the order they were accepted.
	Failures []FailureReport
	// State is the final state; for the journal of the execution, Lean's check --state prints
	// the same state.
	State *State
}

// FailureReport is a recorded failure with the error behind it.
type FailureReport struct {
	Failure
	// Err is the error the user code returned, the transform failed with, or ErrTimeout or ErrLost
	// wrapped. It is nil for a failure recovered from a journal, since the journal does not keep
	// errors.
	Err error
}

// Output decodes the value of the endpoint name into v.
func (r *Report) Output(name string, v any) error {
	data, ok := r.Outputs[name]
	if !ok {
		return fmt.Errorf("%w: %s", ErrNoOutput, name)
	}
	return json.Unmarshal(data, v)
}

// report is the report of the ended execution.
func (d *driver) report() *Report {
	s := d.state
	r := &Report{Status: s.Status, Outputs: map[string]json.RawMessage{}, Endpoints: map[string]Outcome{}, State: s}
	if w, ok := d.program.workflow(d.program.Main); ok {
		for _, pl := range w.Placements {
			if !w.isEndpoint(pl.Name) {
				continue
			}
			if x, ok := d.v.settledOf(Path{}, pl.Name); ok {
				r.Endpoints[pl.Name] = x.Outcome
			}
			if result, ok := d.v.firstResultOf(Path{}, pl.Name); ok {
				r.Outputs[pl.Name] = json.RawMessage(d.payloadOf(result.Value))
			}
		}
	}
	for i, f := range s.Failures {
		r.Failures = append(r.Failures, FailureReport{Failure: f, Err: d.errs[i]})
	}
	return r
}

// validPayload reports whether a payload can be recorded: journals are UTF-8 text.
func validPayload(data []byte) bool { return utf8.Valid(data) }
