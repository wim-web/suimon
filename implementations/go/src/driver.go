package suimon

import (
	"context"
	"errors"
	"fmt"
	"runtime/debug"
	"slices"
	"strconv"
	"strings"
	"time"
)

// The driver of one execution. Its goroutine owns the state: it applies the engine's operations
// whenever Step accepts them, turns what user code reports into operations, and publishes the
// effects of the accepted operations after they are durable. Nothing else touches the fields of a
// driver, except where a comment says so. The state changes in place (ownedRecorder), and the
// driver reads it through the index the recorder keeps.

// Value identities (§15.1). The runtime names each value it introduces after where the value comes
// from, never after the schedule, with the scheme of Lean's Explore.value, so equal runs write
// equal records. Lists are named by the model (listValue).

func inputValue() string             { return ExploreValue("input") }
func returnValue(call string) string { return ExploreValue("return", call) }
func yieldValue(call string, i int) string {
	return ExploreValue("yield", call, strconv.Itoa(i))
}
func transformValue(connection int, source string) string {
	return ExploreValue("transform", strconv.Itoa(connection), source)
}
func taskInputValue(execution, task string) string { return ExploreValue("input", execution, task) }
func taskOutputValue(execution, task string, i int) string {
	return ExploreValue("output", execution, task, strconv.Itoa(i))
}

// Plans: what candidate generation needs to know of each placement, derived once per engine.

type workflowPlan struct {
	workflow   *Workflow
	placements map[string]*placementPlan
}

type placementPlan struct {
	placement *Placement
	// shape is where the placement gets its input from; shaped is false when it cannot be derived,
	// which validation rules out.
	shape  shape
	shaped bool
	// outgoing are the indices of the connections from the placement.
	outgoing []int
}

func newPlans(p *Definition) map[string]*workflowPlan {
	plans := map[string]*workflowPlan{}
	for i := range p.Workflows {
		w := &p.Workflows[i]
		if _, dup := plans[w.ID]; dup {
			continue // the first workflow of an id counts, as in lookups
		}
		wp := &workflowPlan{workflow: w, placements: map[string]*placementPlan{}}
		for j := range w.Placements {
			pl := &w.Placements[j]
			if _, dup := wp.placements[pl.Name]; dup {
				continue
			}
			sh, ok := w.shape(p, pl.Name)
			pp := &placementPlan{placement: pl, shape: sh, shaped: ok}
			for k, c := range w.Connections {
				if c.Source == pl.Name {
					pp.outgoing = append(pp.outgoing, k)
				}
			}
			wp.placements[pl.Name] = pp
		}
		plans[w.ID] = wp
	}
	return plans
}

// Events: what the goroutines of user code and the timers report.

type eventKind int

const (
	evReturned eventKind = iota
	evJudged
	evYielded
	evEnded
	evFailed
	// evExited: the user code returned after its call was cancelled.
	evExited
	evTimer
)

type event struct {
	call  string
	kind  eventKind
	value []byte
	arm   string
	err   error
	// index is the index of a yielded element, or, for an element timer, of the element it waits for.
	index int
	// element marks the timer of an element timeout.
	element bool
}

// terminal reports an event after which the goroutine of the call reports nothing more.
func (e event) terminal() bool { return e.kind != evYielded && e.kind != evTimer }

// Effects: what the driver does outside the state once the operations that call for it are durable.

type effectKind int

const (
	effectStart effectKind = iota
	effectFetch
	effectCancel
)

type effect struct {
	kind effectKind
	call string
}

// callRuntime is the user code of a call whose goroutine has not reported its end.
type callRuntime struct {
	cancel context.CancelFunc
	// fetch lets a Stream call read its next element; the driver sends once per fetch.
	fetch                   chan struct{}
	callTimer, elementTimer *time.Timer
}

func (cr *callRuntime) stopTimers() {
	if cr.callTimer != nil {
		cr.callTimer.Stop()
	}
	cr.stopElementTimer()
}

func (cr *callRuntime) stopElementTimer() {
	if cr.elementTimer != nil {
		cr.elementTimer.Stop()
		cr.elementTimer = nil
	}
}

// internalError is a broken invariant of the driver; the execution ends with it.
type internalError struct{ err error }

type driver struct {
	definition *Definition
	registry   *Registry
	plans      map[string]*workflowPlan
	recorder   *ownedRecorder
	journal    Journal
	// state is the state of the recorder, which changes in place; v reads it through its index.
	state *State
	v     view
	exec  *WorkflowExecution

	// base carries the values of the caller's context to user code, without its cancellation.
	base context.Context

	// payloads maps value identities to their JSON.
	payloads map[string]string
	// errs holds the error behind each failure of the state, in the same order.
	errs []error

	// buffer holds the records not yet appended to the journal; effects wait for them.
	buffer  []byte
	effects []effect

	calls map[string]*callRuntime
	// local holds events of the driver itself, handled before waiting for others.
	local  []event
	events chan event
	// exited is closed when the driver ends, so that late senders give up.
	exited chan struct{}

	// Positions of the runs, executions and calls that may not have ended, pruned lazily.
	openRuns, openExecutions, openCalls []int

	// cur holds how far each list has been followed up: the invocations of a run's placements
	// without input, the invocation a delivery triggers, the deliveries of a result, the input
	// transforms of an execution's tasks, and the output transform of a task result.
	cur struct {
		runs, deliveries, results, executions, taskResults int
	}
}

func (e *Engine) newDriver(ctx context.Context, r *ownedRecorder, j Journal) *driver {
	d := &driver{
		definition: e.definition, registry: e.registry, plans: e.plans, recorder: r, journal: j,
		state: r.machine.s, v: r.machine.view,
		exec:     &WorkflowExecution{cancel: make(chan struct{}), done: make(chan struct{})},
		base:     context.WithoutCancel(ctx),
		payloads: map[string]string{},
		calls:    map[string]*callRuntime{},
		events:   make(chan event, 64),
		exited:   make(chan struct{}),
	}
	d.opened(0, 0, 0)
	return d
}

// begin runs the first operations of an execution in the caller's goroutine and makes them
// durable, so that Start and Resume report a journal that cannot be written.
func (d *driver) begin(first func() error) (err error) {
	defer func() {
		if p := recover(); p != nil {
			err = recovered(p)
		}
	}()
	if err := first(); err != nil {
		return err
	}
	return d.flush()
}

func recovered(p any) error {
	if ie, ok := p.(internalError); ok {
		return ie.err
	}
	return fmt.Errorf("suimon: internal error: %v\n%s", p, debug.Stack())
}

// run drives the execution until it ends.
func (d *driver) run(ctx context.Context) {
	report, err := d.loop(ctx)
	if err != nil {
		d.abandon()
	}
	d.exec.report, d.exec.err = report, err
	close(d.exited)
	close(d.exec.done)
}

func (d *driver) loop(ctx context.Context) (report *Report, err error) {
	defer func() {
		if p := recover(); p != nil {
			report, err = nil, recovered(p)
		}
	}()
	cancel, done := d.exec.cancel, ctx.Done()
	for {
		for d.pass() {
		}
		if err := d.flush(); err != nil {
			return nil, err
		}
		if d.state.Status.Terminal() {
			return d.report(), nil
		}
		if len(d.local) > 0 {
			ev := d.local[0]
			d.local = d.local[1:]
			d.handle(ev)
			continue
		}
		if len(d.calls) == 0 {
			// Nothing runs that could report, and no operation is possible.
			return nil, fmt.Errorf("%w in status %s", ErrStuck, d.state.Status)
		}
		select {
		case ev := <-d.events:
			d.handle(ev)
			d.drain()
		case <-cancel:
			cancel = nil
			d.cancel()
		case <-done:
			done = nil
			d.cancel()
		}
	}
}

// drain handles the events that are already waiting, so that one sync covers them.
func (d *driver) drain() {
	for range cap(d.events) {
		select {
		case ev := <-d.events:
			d.handle(ev)
		default:
			return
		}
	}
}

// cancel records the caller's cancellation (§11.3).
func (d *driver) cancel() {
	if !d.state.Cancelled && !d.state.Status.Terminal() {
		d.apply(OpCancel{}, nil)
	}
}

// abandon ends the user code of an execution that cannot continue, recording nothing more.
func (d *driver) abandon() {
	for _, cr := range d.calls {
		cr.cancel()
		cr.stopTimers()
	}
	for len(d.calls) > 0 {
		if ev := <-d.events; ev.terminal() {
			delete(d.calls, ev.call)
		}
	}
}

// send delivers an event to the driver; it is called from other goroutines.
func (d *driver) send(ev event) {
	select {
	case d.events <- ev:
	case <-d.exited:
	}
}

// apply records op and makes it the state; cause is the error behind the failure op records, if
// it records one. It returns the Rejection of Step when op is not accepted.
func (d *driver) apply(op Op, cause error) error {
	s := d.state
	before := counts{s.Status, len(s.Runs), len(s.Calls), len(s.Executions)}
	records, err := d.recorder.recordWith(op, func(v string) (string, error) { return d.payloadOf(v), nil })
	if err != nil {
		var rejection *Rejection
		if errors.As(err, &rejection) {
			return err
		}
		panic(internalError{fmt.Errorf("suimon: recording %s: %w", EncodeOp(op), err)})
	}
	for _, r := range records {
		d.buffer = append(d.buffer, EncodeRecord(r)...)
		d.buffer = append(d.buffer, '\n')
	}
	d.observe(before, op, cause)
	return nil
}

// counts are what observe compares: the status, and the lengths of the lists of runs, calls and
// executions.
type counts struct {
	status                  Status
	runs, calls, executions int
}

// payloadOf is the JSON of a value: a payload the driver holds, or the JSON array of the payloads
// of a list the model built, in the order of the list identity.
func (d *driver) payloadOf(v string) string {
	if p, ok := d.payloads[v]; ok {
		return p
	}
	parts, ok := DecodeIdentity(v)
	if !ok || len(parts) == 0 || parts[0] != "list" || Identity(parts...) != v {
		panic(internalError{fmt.Errorf("suimon: no payload for value %q", v)})
	}
	var b strings.Builder
	b.WriteByte('[')
	for i, element := range parts[1:] {
		if i > 0 {
			b.WriteByte(',')
		}
		b.WriteString(d.payloadOf(element))
	}
	b.WriteByte(']')
	d.payloads[v] = b.String()
	return b.String()
}

// observe follows up an accepted operation: it notes the new runs, calls and executions, and
// queues the effects of the operation.
func (d *driver) observe(before counts, op Op, cause error) {
	after := d.state
	for len(d.errs) < len(after.Failures) {
		d.errs = append(d.errs, cause)
	}
	for i := before.calls; i < len(after.Calls); i++ {
		d.effects = append(d.effects, effect{effectStart, after.Calls[i].ID})
	}
	switch op := op.(type) {
	case OpFetch:
		d.effects = append(d.effects, effect{effectFetch, op.Call})
	case OpTimedOut:
		d.effects = append(d.effects, effect{effectCancel, op.Call})
	}
	if before.status == StatusRunning && after.Status == StatusStopping {
		for _, c := range after.Calls {
			if c.Status == CallCancelling {
				d.effects = append(d.effects, effect{effectCancel, c.ID})
			}
		}
	}
	d.opened(before.runs, before.calls, before.executions)
}

// opened notes the runs, calls and executions from the given positions on as open.
func (d *driver) opened(runs, calls, executions int) {
	s := d.state
	for i := runs; i < len(s.Runs); i++ {
		d.openRuns = append(d.openRuns, i)
	}
	for i := calls; i < len(s.Calls); i++ {
		d.openCalls = append(d.openCalls, i)
	}
	for i := executions; i < len(s.Executions); i++ {
		d.openExecutions = append(d.openExecutions, i)
	}
}

// flush makes the recorded operations durable, then publishes their effects.
func (d *driver) flush() error {
	if len(d.buffer) > 0 {
		if d.journal != nil {
			if err := d.journal.Append(d.buffer); err != nil {
				return fmt.Errorf("suimon: writing the journal: %w", err)
			}
			if err := d.journal.Sync(); err != nil {
				return fmt.Errorf("suimon: syncing the journal: %w", err)
			}
		}
		d.buffer = d.buffer[:0]
	}
	effects := d.effects
	d.effects = nil
	for _, e := range effects {
		d.publish(e)
	}
	return nil
}

func (d *driver) call(id string) *Call {
	pos, ok := d.v.callPos(id)
	if !ok {
		panic(internalError{fmt.Errorf("suimon: unknown call %q", id)})
	}
	return &d.state.Calls[pos]
}

func (d *driver) planOf(path Path) *workflowPlan {
	r, ok := d.v.run(path)
	if !ok {
		return nil
	}
	return d.plans[r.Workflow]
}

// publish carries out one effect, in view of the current state: a call that a later operation
// already cancelled is not started, and gets no element.
func (d *driver) publish(e effect) {
	c := d.call(e.call)
	switch e.kind {
	case effectStart:
		switch c.Status {
		case CallRunning, CallFetching:
			d.start(c)
		case CallCancelling:
			// Stopped before its user code started (§11.3): there is nothing to wait for.
			d.local = append(d.local, event{call: c.ID, kind: evExited})
		}
	case effectFetch:
		cr := d.calls[c.ID]
		if cr == nil || c.Status != CallFetching {
			return
		}
		cr.fetch <- struct{}{}
		if c.Timeout.ElementMs != nil {
			id, index := c.ID, c.Yields
			cr.elementTimer = time.AfterFunc(duration(*c.Timeout.ElementMs), func() {
				d.send(event{call: id, kind: evTimer, element: true, index: index})
			})
		}
	case effectCancel:
		if cr := d.calls[c.ID]; cr != nil {
			cr.cancel()
			cr.stopTimers()
		}
	}
}

func duration(ms uint64) time.Duration {
	const most = uint64(1<<63-1) / uint64(time.Millisecond)
	return time.Duration(min(ms, most)) * time.Millisecond
}

// handle turns a report of user code into an operation (§10.2): a value is accepted only while
// its call runs; after the call was cancelled, only the end of its user code counts.
func (d *driver) handle(ev event) {
	c := *d.call(ev.call)
	cr := d.calls[ev.call]
	switch ev.kind {
	case evTimer:
		if cr == nil {
			return
		}
		if ev.element {
			if c.Status == CallFetching && c.Yields == ev.index {
				d.apply(OpTimedOut{Call: c.ID, Element: true},
					fmt.Errorf("%w: no element within %d ms", ErrTimeout, *c.Timeout.ElementMs))
			}
		} else if c.Status == CallRunning || c.Status == CallFetching {
			d.apply(OpTimedOut{Call: c.ID}, fmt.Errorf("%w: the call took longer than %d ms", ErrTimeout, *c.Timeout.CallMs))
		}
		return
	case evYielded:
		if c.Status != CallFetching || c.Yields != ev.index {
			return // not accepted after a cancellation (§10.2)
		}
		cr.stopElementTimer()
		if !validPayload(ev.value) {
			d.apply(OpFailed{Call: c.ID}, errors.New("suimon: the element is not valid UTF-8 JSON"))
			return
		}
		id := yieldValue(c.ID, c.Yields)
		d.payloads[id] = string(ev.value)
		d.apply(OpYielded{Call: c.ID, Value: id}, nil)
		return
	}
	// The user code has returned.
	if cr != nil {
		cr.stopTimers()
		delete(d.calls, ev.call)
	}
	switch c.Status {
	case CallCancelling:
		d.apply(OpTerminated{Call: c.ID}, nil)
		return
	case CallRunning, CallFetching:
	default:
		panic(internalError{fmt.Errorf("suimon: call %s reported after it ended", c.ID)})
	}
	var op Op
	var cause error
	switch ev.kind {
	case evReturned:
		if validPayload(ev.value) {
			id := returnValue(c.ID)
			d.payloads[id] = string(ev.value)
			op = OpReturned{Call: c.ID, Value: id}
		} else {
			op, cause = OpFailed{Call: c.ID}, errors.New("suimon: the result is not valid UTF-8 JSON")
		}
	case evJudged:
		if arms := d.armsOf(&c); slices.Contains(arms, ev.arm) {
			op = OpJudged{Call: c.ID, Arm: ev.arm}
		} else {
			op, cause = OpFailed{Call: c.ID}, fmt.Errorf("suimon: judge %s returned %q, which is not one of the arms %q",
				c.Target.ID, ev.arm, arms)
		}
	case evEnded:
		op = OpEnded{Call: c.ID}
	case evFailed:
		op, cause = OpFailed{Call: c.ID}, ev.err
	default:
		op, cause = OpFailed{Call: c.ID}, errors.New("suimon: the user code ended without a result")
	}
	if err := d.apply(op, cause); err != nil {
		// A report that does not fit the call, such as a Single result of a Stream call, fails it.
		if err := d.apply(OpFailed{Call: c.ID}, fmt.Errorf("suimon: unexpected report of the user code: %w", err)); err != nil {
			panic(internalError{fmt.Errorf("suimon: call %s cannot end: %w", c.ID, err)})
		}
	}
}

func (d *driver) armsOf(c *Call) []string { return armsOf(d.definition, d.v, c) }

// pass tries the engine's operations once and reports whether one was accepted. The driver
// repeats passes until none is, so every operation Step accepts is applied (§12: nothing waits
// for slow downstream work).
func (d *driver) pass() bool {
	progress := false
	try := func(op Op, cause error) {
		if d.apply(op, cause) == nil {
			progress = true
		}
	}
	d.openCalls = slices.DeleteFunc(d.openCalls, func(pos int) bool { return d.state.Calls[pos].Status.ended() })
	d.openRuns = slices.DeleteFunc(d.openRuns, func(pos int) bool { return d.state.Runs[pos].Complete })
	d.openExecutions = slices.DeleteFunc(d.openExecutions, func(pos int) bool { return d.state.Executions[pos].Complete })
	if d.state.Status == StatusRunning {
		d.fetches(try)
		d.invocations(try)
		d.deliveries(try)
		d.tasks(try)
		d.settles(try)
	}
	d.conclude(try)
	return progress
}

func (d *driver) running() bool { return d.state.Status == StatusRunning }

// fetches asks each running Stream call for its next element at once (§4.1.1): the engine reads
// a generator as soon as the previous element is accepted, without waiting for downstream work.
func (d *driver) fetches(try func(Op, error)) {
	for i, n := 0, len(d.openCalls); i < n && d.running(); i++ {
		if c := &d.state.Calls[d.openCalls[i]]; c.Stream && c.Status == CallRunning {
			try(OpFetch{Call: c.ID}, nil)
		}
	}
}

// invocations invokes the placements without input and with the workflow input once per run
// (§3.1), and each target of a delivery once per delivered value (§5.3).
func (d *driver) invocations(try func(Op, error)) {
	for ; d.cur.runs < len(d.state.Runs) && d.running(); d.cur.runs++ {
		r := d.state.Runs[d.cur.runs]
		wp := d.plans[r.Workflow]
		if wp == nil {
			continue
		}
		for _, pl := range wp.workflow.Placements {
			pp := wp.placements[pl.Name]
			if pp.shaped && (pp.shape.kind == shapeNone || pp.shape.kind == shapeEntry) &&
				!d.invoked(r.Path, pl.Name, nil) {
				try(OpInvoke{Run: r.Path, Placement: pl.Name}, nil)
			}
		}
	}
	for ; d.cur.deliveries < len(d.state.Deliveries) && d.running(); d.cur.deliveries++ {
		x := d.state.Deliveries[d.cur.deliveries]
		wp := d.planOf(x.Run)
		if x.Outcome.Kind == DeliveredFailed || wp == nil || x.Connection >= len(wp.workflow.Connections) {
			continue
		}
		target := wp.workflow.Connections[x.Connection].Target
		pp := wp.placements[target]
		if pp == nil || !pp.shaped || (pp.shape.kind != shapeSingle && pp.shape.kind != shapeStream) ||
			pp.shape.index != x.Connection {
			continue
		}
		source := x.Source
		if !d.invoked(x.Run, target, &source) {
			try(OpInvoke{Run: x.Run, Placement: target, Trigger: &source}, nil)
		}
	}
}

func (d *driver) invoked(path Path, placement string, trigger *string) bool {
	_, ok := d.v.findInvocation(path, placement, trigger)
	return ok
}

// deliveries applies the transform of each connection to each result it carries (§6), calling
// declared transforms synchronously.
func (d *driver) deliveries(try func(Op, error)) {
	for ; d.cur.results < len(d.state.Results); d.cur.results++ {
		r := d.state.Results[d.cur.results]
		wp := d.planOf(r.Run)
		if wp == nil || wp.placements[r.Placement] == nil {
			continue
		}
		for _, index := range wp.placements[r.Placement].outgoing {
			c := wp.workflow.Connections[index]
			if c.Arm != nil && !equalPtr(c.Arm, r.Arm) {
				continue
			}
			if _, delivered := d.v.delivery(r.Run, index, r.ID); delivered {
				continue
			}
			if !d.running() {
				return // nothing is delivered after a stop (§11.3)
			}
			if c.Transform.Discard {
				try(OpDeliver{Run: r.Run, Connection: index, Source: r.ID}, nil)
				continue
			}
			out, err := d.transform(c.Transform.ID, r.Value)
			if err != nil {
				try(OpTransformFailed{Run: r.Run, Connection: index, Source: r.ID}, err)
				continue
			}
			id := transformValue(index, r.ID)
			d.payloads[id] = out
			try(OpDeliver{Run: r.Run, Connection: index, Source: r.ID, Value: &id}, nil)
		}
	}
}

// transform applies the transform id to the value v and returns the JSON of the result.
func (d *driver) transform(id, v string) (out string, err error) {
	b, ok := d.registry.transforms[id]
	if !ok {
		return "", fmt.Errorf("suimon: transform %s is not bound", id)
	}
	input := d.payloadOf(v)
	defer func() {
		if p := recover(); p != nil {
			err = &PanicError{Value: p, Stack: debug.Stack()}
		}
	}()
	data, err := b.transform([]byte(input))
	if err != nil {
		return "", err
	}
	if !validPayload(data) {
		return "", errors.New("suimon: the transformed value is not valid UTF-8 JSON")
	}
	return string(data), nil
}

func (d *driver) concurrencyOf(e *Execution) *Concurrency {
	c, err := d.v.concurrencyOf(d.definition, e)
	if err != nil {
		panic(internalError{fmt.Errorf("suimon: execution %s: %w", e.ID, err)})
	}
	return c
}

// tasks applies the input transforms of new executions, the output transforms of new task
// results, and begins ready tasks while the execution has a free slot (§8.2).
func (d *driver) tasks(try func(Op, error)) {
	for ; d.cur.executions < len(d.state.Executions); d.cur.executions++ {
		e := &d.state.Executions[d.cur.executions]
		c := d.concurrencyOf(e)
		for i := range e.Tasks {
			if !d.running() {
				return
			}
			e = &d.state.Executions[d.cur.executions]
			t := e.Tasks[i]
			spec := &c.Tasks[i]
			if t.Status != TaskPending || spec.Name != t.Name || spec.Input == nil {
				continue
			}
			if spec.Input.Discard {
				try(OpTaskInput{Execution: e.ID, Task: t.Name}, nil)
				continue
			}
			if e.Input == nil {
				continue // rejected by validation
			}
			out, err := d.transform(spec.Input.ID, *e.Input)
			if err != nil {
				try(OpTaskInputFailed{Execution: e.ID, Task: t.Name}, err)
				continue
			}
			id := taskInputValue(e.ID, t.Name)
			d.payloads[id] = out
			try(OpTaskInput{Execution: e.ID, Task: t.Name, Value: &id}, nil)
		}
	}
	for ; d.cur.taskResults < len(d.state.TaskResults); d.cur.taskResults++ {
		r := d.state.TaskResults[d.cur.taskResults]
		if r.Output.Kind != TaskOutputPending {
			continue
		}
		e, ok := d.v.execution(r.Execution)
		if !ok {
			continue
		}
		spec, err := d.v.taskSpec(d.definition, e, r.Task)
		if err != nil || spec.Output == nil {
			continue
		}
		if !d.running() {
			return
		}
		out, err := d.transform(*spec.Output, r.Value)
		if err != nil {
			try(OpTaskOutputFailed{Execution: r.Execution, Task: r.Task, Index: r.Index}, err)
			continue
		}
		id := taskOutputValue(r.Execution, r.Task, r.Index)
		d.payloads[id] = out
		try(OpTaskOutput{Execution: r.Execution, Task: r.Task, Index: r.Index, Value: id}, nil)
	}
	for k, n := 0, len(d.openExecutions); k < n; k++ {
		pos := d.openExecutions[k]
		c := d.concurrencyOf(&d.state.Executions[pos])
		for i := range d.state.Executions[pos].Tasks {
			if !d.running() {
				return
			}
			e := &d.state.Executions[pos]
			if e.Tasks[i].Status != TaskReady {
				continue
			}
			if uint64(d.v.slotsHeld(e)) >= c.Limit {
				break
			}
			try(OpBeginTask{Execution: e.ID, Task: e.Tasks[i].Name}, nil)
		}
	}
}

// settles settles each placement whose invocations ended and whose input is complete, closes
// executions whose tasks ended and sub-workflow runs whose placements settled. The checks here
// only avoid trying operations that cannot be accepted; Step decides.
func (d *driver) settles(try func(Op, error)) {
	for k, n := 0, len(d.openRuns); k < n; k++ {
		r := d.state.Runs[d.openRuns[k]]
		wp := d.plans[r.Workflow]
		if wp == nil {
			continue
		}
		run := runKey(r.Path)
		for _, pl := range wp.workflow.Placements {
			if d.running() && !d.settled(run, pl.Name) && d.settleable(run, wp, pl.Name) {
				try(OpSettle{Run: r.Path, Placement: pl.Name}, nil)
			}
		}
		if len(r.Path) > 0 && d.running() && d.v.ix.settledIn[run] >= len(wp.workflow.Placements) {
			try(OpCloseRun{Run: r.Path}, nil)
		}
	}
	for k, n := 0, len(d.openExecutions); k < n; k++ {
		e := &d.state.Executions[d.openExecutions[k]]
		ended := true
		for _, t := range e.Tasks {
			ended = ended && t.Status.ended()
		}
		if ended && d.running() {
			try(OpCloseExecution{Execution: e.ID}, nil)
		}
	}
}

func (d *driver) settled(run, placement string) bool {
	return len(d.v.ix.settled[placementRef{run, placement}]) > 0
}

// settleable: no invocation of the placement is active, and its input is complete.
func (d *driver) settleable(run string, wp *workflowPlan, name string) bool {
	pp := wp.placements[name]
	if pp == nil || !pp.shaped {
		return false
	}
	ix := d.v.ix
	key := placementRef{run, name}
	if ix.active[key] > 0 {
		return false
	}
	resolved := func(index int, source string) bool {
		return len(ix.deliveriesOn[connectionRef{run, index}]) > 0 || d.settled(run, source)
	}
	switch pp.shape.kind {
	case shapeNone, shapeEntry:
		return len(ix.invocationsOf[key]) > 0
	case shapeSingle:
		return resolved(pp.shape.index, pp.shape.connection.Source)
	case shapeStream:
		return d.settled(run, pp.shape.connection.Source)
	case shapeMerge:
		for _, in := range pp.shape.merged {
			if !resolved(in.index, in.connection.Source) {
				return false
			}
		}
		return true
	}
	return false
}

// conclude decides the final status once the root run settled, or once the cancelled calls of a
// stopped execution have all ended (§11.3, §13.3).
func (d *driver) conclude(try func(Op, error)) {
	switch d.state.Status {
	case StatusRunning:
		if wp := d.planOf(Path{}); wp != nil && d.v.ix.settledIn[runKey(Path{})] >= len(wp.workflow.Placements) {
			try(OpConclude{}, nil)
		}
	case StatusStopping:
		for _, pos := range d.openCalls {
			if !d.state.Calls[pos].Status.ended() {
				return
			}
		}
		try(OpConclude{}, nil)
	}
}
