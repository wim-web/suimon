package suimon

import (
	"cmp"
	"slices"
)

// The operational rules of Suimon/Step.lean. Each rule checks its own preconditions in the Lean
// order and returns the Lean error code of the first one that fails; a rejected operation changes
// nothing. Lists keep the Lean order: new records are appended and updates replace in place.
//
// A rule makes every check before its first change, so the same rules serve two callers: Step,
// which leaves its state unchanged and copies each list before the list changes, and a machine,
// which owns its state and changes it in place, keeping the indexes of the state up to date.

// Rejection is the refusal of an operation; Code is the error code of Step.lean, such as
// NOT_RUNNING or DUPLICATE_RESULT.
type Rejection struct{ Code string }

func (r *Rejection) Error() string { return r.Code }

func reject(code string) error { return &Rejection{Code: code} }

func require(ok bool, code string) error {
	if ok {
		return nil
	}
	return reject(code)
}

// Step applies one operation. It returns a new state and leaves s unchanged.
func Step(p *Definition, s *State, op Op) (*State, error) {
	t := *s
	st := &stepper{view: view{s: &t}, p: p}
	if err := st.apply(op); err != nil {
		return nil, err
	}
	return st.s, nil
}

// machine owns a state and applies operations to it in place, keeping its index and the set of
// the values it mentions. Nothing else may hold the state while the machine changes it.
type machine struct {
	view
	p *Definition
	// seen holds every value the state mentions.
	seen map[string]struct{}
}

// newMachine takes s over; s must not be used elsewhere while the machine changes it.
func newMachine(p *Definition, s *State) *machine {
	m := &machine{view: view{s: s, ix: newStateIndex(s)}, p: p, seen: map[string]struct{}{}}
	for _, v := range s.Values() {
		m.seen[v] = struct{}{}
	}
	return m
}

// apply applies op in place and returns the values it introduces, in the order of Introduced. A
// rejected op changes nothing.
func (m *machine) apply(op Op) ([]string, error) {
	st := &stepper{view: m.view, p: m.p}
	if err := st.apply(op); err != nil {
		return nil, err
	}
	introduced := st.introduced(m.seen)
	for _, v := range introduced {
		m.seen[v] = struct{}{}
	}
	return introduced, nil
}

// stepper applies one operation to s. Without an index, s is a copy of the caller's state whose
// lists are still shared: each list is copied before its first change (owned). With an index, s
// is owned and changes in place.
type stepper struct {
	view
	p     *Definition
	owned uint16
	// mentions are the values of the records the step added or changed, where they are mentioned.
	mentions []mention
}

// A mention is a value at its place in the order of State.Values: the list, the position in the
// list, and the place in the record.
type mention struct {
	list, pos, part int
	value           string
}

// The lists of a state, in the order of State.Values; each is also its bit in owned.
const (
	listRuns = iota
	listInvocations
	listCalls
	listExecutions
	listResults
	listDeliveries
	listTaskResults
	listSettled
	listFailures
)

func (st *stepper) mention(list, pos, part int, value *string) {
	if value != nil {
		st.mentions = append(st.mentions, mention{list, pos, part, *value})
	}
}

// introduced are the mentioned values that seen does not hold, each once, in the order of their
// first mention in State.Values. Values are never removed from a state, so these are the values
// that Introduced finds, in the same order, when seen holds the values of the state before.
func (st *stepper) introduced(seen map[string]struct{}) []string {
	slices.SortStableFunc(st.mentions, func(a, b mention) int {
		return cmp.Or(cmp.Compare(a.list, b.list), cmp.Compare(a.pos, b.pos), cmp.Compare(a.part, b.part))
	})
	var out []string
	for _, m := range st.mentions {
		if _, ok := seen[m.value]; !ok && !slices.Contains(out, m.value) {
			out = append(out, m.value)
		}
	}
	return out
}

// own makes the list writable: without an index, it copies the list once per step.
func own[T any](st *stepper, list int, xs *[]T) {
	if st.ix == nil && st.owned&(1<<list) == 0 {
		*xs = append(make([]T, 0, len(*xs)+1), *xs...)
		st.owned |= 1 << list
	}
}

// Changes. Records are added at the end of their list. A record that changes is replaced where
// it is; without an index every record with its identity is replaced, as Lean's replacement of
// matching records does, and with one the record at the position, the only one in a state that
// Step built.

func (st *stepper) addRun(r Run) {
	own(st, listRuns, &st.s.Runs)
	pos := len(st.s.Runs)
	st.s.Runs = append(st.s.Runs, r)
	st.mention(listRuns, pos, 0, r.Input)
	if st.ix != nil {
		st.ix.addRun(pos, &st.s.Runs[pos])
	}
}

func (st *stepper) completeRun(pos int) {
	own(st, listRuns, &st.s.Runs)
	if st.ix != nil {
		st.s.Runs[pos].Complete = true
		return
	}
	path := st.s.Runs[pos].Path
	for i := range st.s.Runs {
		if slices.Equal(st.s.Runs[i].Path, path) {
			st.s.Runs[i].Complete = true
		}
	}
}

func (st *stepper) addInvocation(i Invocation) {
	own(st, listInvocations, &st.s.Invocations)
	pos := len(st.s.Invocations)
	st.s.Invocations = append(st.s.Invocations, i)
	st.mention(listInvocations, pos, 0, i.Input)
	if st.ix != nil {
		st.ix.addInvocation(pos, &st.s.Invocations[pos])
	}
}

// setInvocation sets the status and the arm of the invocation at pos.
func (st *stepper) setInvocation(pos int, status InvocationStatus, arm *string) {
	own(st, listInvocations, &st.s.Invocations)
	next := st.s.Invocations[pos]
	next.Status, next.Arm = status, arm
	if st.ix != nil {
		old := st.s.Invocations[pos].Status
		st.s.Invocations[pos] = next
		st.ix.setInvocationStatus(&st.s.Invocations[pos], old)
		return
	}
	for i := range st.s.Invocations {
		if st.s.Invocations[i].ID == next.ID {
			st.s.Invocations[i] = next
		}
	}
}

func (st *stepper) setInvocationStatus(pos int, status InvocationStatus) {
	st.setInvocation(pos, status, st.s.Invocations[pos].Arm)
}

func (st *stepper) addCall(c Call) {
	own(st, listCalls, &st.s.Calls)
	pos := len(st.s.Calls)
	st.s.Calls = append(st.s.Calls, c)
	st.mention(listCalls, pos, 0, c.Input)
	if st.ix != nil {
		st.ix.addCall(pos, &st.s.Calls[pos])
	}
}

// setCall sets the status and the yields of the call at pos.
func (st *stepper) setCall(pos int, status CallStatus, yields int) {
	own(st, listCalls, &st.s.Calls)
	next := st.s.Calls[pos]
	next.Status, next.Yields = status, yields
	if st.ix != nil {
		st.s.Calls[pos] = next
		return
	}
	for i := range st.s.Calls {
		if st.s.Calls[i].ID == next.ID {
			st.s.Calls[i] = next
		}
	}
}

func (st *stepper) setCallStatus(pos int, status CallStatus) {
	st.setCall(pos, status, st.s.Calls[pos].Yields)
}

func (st *stepper) addExecution(e Execution) {
	own(st, listExecutions, &st.s.Executions)
	pos := len(st.s.Executions)
	st.s.Executions = append(st.s.Executions, e)
	st.mention(listExecutions, pos, 0, e.Input)
	for j := range e.Tasks {
		st.mention(listExecutions, pos, 1+j, e.Tasks[j].Input)
	}
	if st.ix != nil {
		st.ix.addExecution(pos, &st.s.Executions[pos])
	}
}

func (st *stepper) completeExecution(pos int) {
	own(st, listExecutions, &st.s.Executions)
	if st.ix != nil {
		st.s.Executions[pos].Complete = true
		return
	}
	next := st.s.Executions[pos]
	next.Complete = true
	st.replaceExecution(next)
}

func (st *stepper) replaceExecution(next Execution) {
	for i := range st.s.Executions {
		if st.s.Executions[i].ID == next.ID {
			st.s.Executions[i] = next
		}
	}
}

// setTask replaces the tasks named like task in the execution at pos.
func (st *stepper) setTask(pos int, task TaskState) {
	own(st, listExecutions, &st.s.Executions)
	next := st.s.Executions[pos]
	if st.ix == nil {
		next.Tasks = slices.Clone(next.Tasks)
	}
	for j := range next.Tasks {
		if next.Tasks[j].Name == task.Name {
			if !equalPtr(next.Tasks[j].Input, task.Input) {
				st.mention(listExecutions, pos, 1+j, task.Input)
			}
			next.Tasks[j] = task
		}
	}
	if st.ix != nil {
		st.s.Executions[pos] = next
		return
	}
	st.replaceExecution(next)
}

func (st *stepper) setTaskStatus(pos, task int, status TaskStatus) {
	next := st.s.Executions[pos].Tasks[task]
	next.Status = status
	st.setTask(pos, next)
}

func (st *stepper) addResult(r Result) {
	own(st, listResults, &st.s.Results)
	pos := len(st.s.Results)
	st.s.Results = append(st.s.Results, r)
	st.mention(listResults, pos, 0, &r.Value)
	if st.ix != nil {
		st.ix.addResult(pos, &st.s.Results[pos])
	}
}

func (st *stepper) addTaskResult(r TaskResult) {
	own(st, listTaskResults, &st.s.TaskResults)
	pos := len(st.s.TaskResults)
	st.s.TaskResults = append(st.s.TaskResults, r)
	st.mention(listTaskResults, pos, 0, &r.Value)
	if v, ok := r.Output.value(); ok {
		st.mention(listTaskResults, pos, 1, &v)
	}
	if st.ix != nil {
		st.ix.addTaskResult(pos, &st.s.TaskResults[pos])
	}
}

// setTaskOutput sets the output of the task result at pos.
func (st *stepper) setTaskOutput(pos int, output TaskOutput) {
	own(st, listTaskResults, &st.s.TaskResults)
	next := st.s.TaskResults[pos]
	next.Output = output
	if v, ok := output.value(); ok {
		st.mention(listTaskResults, pos, 1, &v)
	}
	if st.ix != nil {
		st.s.TaskResults[pos] = next
		return
	}
	for i := range st.s.TaskResults {
		x := &st.s.TaskResults[i]
		if x.Execution == next.Execution && x.Task == next.Task && x.Index == next.Index {
			*x = next
		}
	}
}

func (st *stepper) addDelivery(d Delivery) {
	own(st, listDeliveries, &st.s.Deliveries)
	pos := len(st.s.Deliveries)
	st.s.Deliveries = append(st.s.Deliveries, d)
	if d.Outcome.Kind == DeliveredValue {
		st.mention(listDeliveries, pos, 0, &d.Outcome.Value)
	}
	if st.ix != nil {
		st.ix.addDelivery(pos, &st.s.Deliveries[pos])
	}
}

func (st *stepper) addSettled(x Settled) {
	own(st, listSettled, &st.s.Settled)
	pos := len(st.s.Settled)
	st.s.Settled = append(st.s.Settled, x)
	if st.ix != nil {
		st.ix.addSettled(pos, &st.s.Settled[pos])
	}
}

// stop cancels running calls and leaves waiting tasks unstarted, in one transition (§11.3).
func (st *stepper) stop() {
	st.s.Status = StatusStopping
	own(st, listCalls, &st.s.Calls)
	for i := range st.s.Calls {
		if c := &st.s.Calls[i]; c.Status == CallRunning || c.Status == CallFetching {
			c.Status = CallCancelling
		}
	}
	own(st, listExecutions, &st.s.Executions)
	for i := range st.s.Executions {
		e := &st.s.Executions[i]
		if st.ix == nil {
			e.Tasks = slices.Clone(e.Tasks)
		}
		for j := range e.Tasks {
			if t := &e.Tasks[j]; t.Status == TaskPending || t.Status == TaskReady {
				t.Status = TaskNotStarted
			}
		}
	}
}

// fail records a failure; the policy is chosen where the failure happened, never again by an
// enclosing placement (§11.2).
func (st *stepper) fail(f Failure, policy Policy) {
	own(st, listFailures, &st.s.Failures)
	st.s.Failures = append(st.s.Failures, f)
	if policy == PolicyStop {
		st.stop()
	}
}

func taskIndex(e *Execution, name string) (int, error) {
	for j := range e.Tasks {
		if e.Tasks[j].Name == name {
			return j, nil
		}
	}
	return 0, reject("UNKNOWN_TASK")
}

// owner is where the owner of a call is: an invocation, or a task of an execution.
type owner struct {
	ofTask                      bool
	invocation, execution, task int
}

func (st *stepper) ownerOf(c *Call) (owner, error) {
	if c.Task == nil {
		pos, ok := st.invocationPos(c.Owner)
		if !ok {
			return owner{}, reject("UNKNOWN_INVOCATION")
		}
		return owner{invocation: pos}, nil
	}
	pos, ok := st.executionPos(c.Owner)
	if !ok {
		return owner{}, reject("UNKNOWN_EXECUTION")
	}
	j, err := taskIndex(&st.s.Executions[pos], *c.Task)
	if err != nil {
		return owner{}, err
	}
	return owner{ofTask: true, execution: pos, task: j}, nil
}

func (st *stepper) callFailure(c *Call, cause Cause) (Failure, error) {
	if c.Task == nil {
		i, ok := st.invocation(c.Owner)
		if !ok {
			return Failure{}, reject("UNKNOWN_INVOCATION")
		}
		return Failure{Run: i.Run, Placement: i.Placement, Cause: cause}, nil
	}
	e, ok := st.execution(c.Owner)
	if !ok {
		return Failure{}, reject("UNKNOWN_EXECUTION")
	}
	return Failure{Run: e.Run, Placement: e.Placement, Task: ptr(*c.Task), Cause: cause}, nil
}

// acceptance is one value of a call accepted as a result of its owner (§10.2): a result, or a task
// result.
type acceptance struct {
	result     *Result
	taskResult *TaskResult
}

func (st *stepper) accept(c *Call, index int, value string, arm *string) (acceptance, error) {
	if c.Task == nil {
		i, ok := st.invocation(c.Owner)
		if !ok {
			return acceptance{}, reject("UNKNOWN_INVOCATION")
		}
		r := Result{ID: keyCallResult(c.ID, index), Run: i.Run, Placement: i.Placement, Producer: c.ID,
			Arm: arm, Value: value}
		if _, dup := st.result(r.ID); dup {
			return acceptance{}, reject("DUPLICATE_RESULT")
		}
		return acceptance{result: &r}, nil
	}
	if _, dup := st.taskResultPos(c.Owner, *c.Task, index); dup {
		return acceptance{}, reject("DUPLICATE_RESULT")
	}
	return acceptance{taskResult: &TaskResult{Execution: c.Owner, Task: *c.Task, Index: index, Value: value}}, nil
}

func (st *stepper) addAccepted(a acceptance) {
	if a.result != nil {
		st.addResult(*a.result)
	} else {
		st.addTaskResult(*a.taskResult)
	}
}

func (st *stepper) settleOwner(o owner, invocation InvocationStatus, task TaskStatus) {
	if o.ofTask {
		st.setTaskStatus(o.execution, o.task, task)
	} else {
		st.setInvocationStatus(o.invocation, invocation)
	}
}

// cancelOwner ends the owner of a terminated call as cancelled, unless the owner already failed.
func (st *stepper) cancelOwner(o owner) {
	if o.ofTask {
		if st.s.Executions[o.execution].Tasks[o.task].Status == TaskActive {
			st.setTaskStatus(o.execution, o.task, TaskCancelled)
		}
	} else if st.s.Invocations[o.invocation].Status == InvocationActive {
		st.setInvocationStatus(o.invocation, InvocationCancelled)
	}
}

func (st *stepper) failCall(pos int, status CallStatus, cause Cause) error {
	c := st.s.Calls[pos]
	f, err := st.callFailure(&c, cause)
	if err != nil {
		return err
	}
	o, err := st.ownerOf(&c)
	if err != nil {
		return err
	}
	st.setCallStatus(pos, status)
	st.settleOwner(o, InvocationFailed, TaskFailed)
	st.fail(f, c.Policy)
	return nil
}

func invocationOutcome(kind Kind, status InvocationStatus) Outcome {
	switch status {
	case InvocationSucceeded:
		return OutcomeNormal
	case InvocationSkipped:
		return OutcomeSkipped
	case InvocationUpstreamFailed:
		if kind == KindStream {
			return OutcomeNormal
		}
		return OutcomeUpstreamFailed
	}
	if kind == KindStream {
		return OutcomeNormal
	}
	return OutcomeFailed
}

// missingOutcome: a Stream output that got no value ends normally unless it was not selected (§7.3).
func missingOutcome(kind Kind, reason Outcome) Outcome {
	if kind == KindStream && reason != OutcomeSkipped {
		return OutcomeNormal
	}
	return reason
}

// settleOutcome says how a placement settles when it has taken all its input and its invocations
// ended, or false when it is not ready (§7.3, §9, §10.3).
func (v view) settleOutcome(path Path, pl *Placement, sh shape, kind Kind) (Settled, *Result, bool) {
	for i := range v.invocationsOf(path, pl.Name) {
		if !v.invocationEnded(i) {
			return Settled{}, nil, false
		}
	}
	done := func(outcome Outcome) (Settled, *Result, bool) {
		return Settled{Run: path, Placement: pl.Name, Outcome: outcome}, nil, true
	}
	key := keyAggregate(path, pl.Name)
	aggregate := func(values []string) (Settled, *Result, bool) {
		r := &Result{ID: key, Run: path, Placement: pl.Name, Producer: key, Value: listValue(values)}
		return Settled{Run: path, Placement: pl.Name, Outcome: OutcomeNormal}, r, true
	}
	triggered := func(index int) bool {
		for d := range v.deliveriesOn(path, index) {
			if d.Outcome.Kind == DeliveredFailed {
				continue
			}
			if _, ok := v.findInvocation(path, pl.Name, ptr(d.Source)); !ok {
				return false
			}
		}
		return true
	}
	ownFailures := func(index int) int {
		n := 0
		for d := range v.deliveriesOn(path, index) {
			if d.Outcome.Kind == DeliveredFailed {
				n++
			}
		}
		for i := range v.invocationsOf(path, pl.Name) {
			if i.Status == InvocationFailed || i.Status == InvocationCancelled {
				n++
			}
		}
		return n
	}
	switch control := pl.Control.(type) {
	case WaitStreamControl:
		if sh.kind != shapeStream {
			return Settled{}, nil, false
		}
		ended, ok := v.streamEnd(path, sh.index, sh.connection)
		if !ok {
			return Settled{}, nil, false
		}
		if ended == OutcomeSkipped {
			return done(OutcomeSkipped)
		}
		var values []string
		for d := range v.deliveriesOn(path, sh.index) {
			if d.Outcome.Kind == DeliveredValue {
				values = append(values, d.Outcome.Value)
			}
		}
		return aggregate(values)
	case MergeControl:
		if sh.kind != shapeMerge {
			return Settled{}, nil, false
		}
		resolutions := make([]resolution, len(sh.merged))
		allSkipped := true
		for n, in := range sh.merged {
			resolutions[n] = v.resolveSingle(path, in.index, in.connection)
			if resolutions[n].kind == resolutionPending {
				return Settled{}, nil, false
			}
			allSkipped = allSkipped && resolutions[n].kind == resolutionSkipped
		}
		if allSkipped {
			return done(OutcomeSkipped)
		}
		var values []string
		for _, r := range resolutions {
			if r.kind == resolutionValue && r.input != nil {
				values = append(values, *r.input)
			}
		}
		return aggregate(values)
	case BranchControl:
		settleArms := func(outcome Outcome, arm func(string) Outcome) (Settled, *Result, bool) {
			arms := make([]ArmOutcome, len(control.Arms))
			for n, a := range control.Arms {
				arms[n] = ArmOutcome{Arm: a, Outcome: arm(a)}
			}
			return Settled{Run: path, Placement: pl.Name, Outcome: outcome, Arms: arms}, nil, true
		}
		all := func(o Outcome) func(string) Outcome { return func(string) Outcome { return o } }
		byInvocation := func(inv *Invocation) (Settled, *Result, bool) {
			switch inv.Status {
			case InvocationSucceeded:
				return settleArms(OutcomeNormal, func(a string) Outcome {
					if inv.Arm != nil && *inv.Arm == a {
						return OutcomeNormal
					}
					return OutcomeSkipped
				})
			case InvocationSkipped:
				return settleArms(OutcomeSkipped, all(OutcomeSkipped))
			case InvocationUpstreamFailed:
				return settleArms(OutcomeUpstreamFailed, all(OutcomeUpstreamFailed))
			}
			return settleArms(OutcomeFailed, all(OutcomeFailed))
		}
		switch sh.kind {
		case shapeEntry:
			inv, ok := v.findInvocation(path, pl.Name, nil)
			if !ok {
				return Settled{}, nil, false
			}
			return byInvocation(inv)
		case shapeSingle:
			r := v.resolveSingle(path, sh.index, sh.connection)
			switch r.kind {
			case resolutionPending:
				return Settled{}, nil, false
			case resolutionValue:
				inv, ok := v.findInvocation(path, pl.Name, ptr(r.source))
				if !ok {
					return Settled{}, nil, false
				}
				return byInvocation(inv)
			case resolutionTransformFailed:
				return settleArms(OutcomeFailed, all(OutcomeFailed))
			case resolutionSkipped:
				return settleArms(OutcomeSkipped, all(OutcomeSkipped))
			}
			return settleArms(OutcomeUpstreamFailed, all(OutcomeUpstreamFailed))
		case shapeStream:
			ended, ok := v.streamEnd(path, sh.index, sh.connection)
			if !ok || !triggered(sh.index) {
				return Settled{}, nil, false
			}
			if ended == OutcomeSkipped {
				return settleArms(OutcomeSkipped, all(OutcomeSkipped))
			}
			chosen := map[string]bool{}
			for r := range v.resultsOf(path, pl.Name) {
				if r.Arm != nil {
					chosen[*r.Arm] = true
				}
			}
			own := ownFailures(sh.index)
			return settleArms(OutcomeNormal, func(a string) Outcome {
				if len(chosen) > 0 && !chosen[a] && own == 0 {
					return OutcomeSkipped
				}
				return OutcomeNormal
			})
		}
		return Settled{}, nil, false
	case CallControl, ConcurrencyControl:
		switch sh.kind {
		case shapeNone, shapeEntry:
			inv, ok := v.findInvocation(path, pl.Name, nil)
			if !ok {
				return Settled{}, nil, false
			}
			return done(invocationOutcome(kind, inv.Status))
		case shapeSingle:
			r := v.resolveSingle(path, sh.index, sh.connection)
			switch r.kind {
			case resolutionPending:
				return Settled{}, nil, false
			case resolutionValue:
				inv, ok := v.findInvocation(path, pl.Name, ptr(r.source))
				if !ok {
					return Settled{}, nil, false
				}
				return done(invocationOutcome(kind, inv.Status))
			case resolutionTransformFailed:
				return done(missingOutcome(kind, OutcomeFailed))
			case resolutionSkipped:
				return done(OutcomeSkipped)
			}
			return done(missingOutcome(kind, OutcomeUpstreamFailed))
		case shapeStream:
			ended, ok := v.streamEnd(path, sh.index, sh.connection)
			if !ok || !triggered(sh.index) {
				return Settled{}, nil, false
			}
			if ended == OutcomeSkipped {
				return done(OutcomeSkipped)
			}
			any, allSkipped := false, true
			for i := range v.invocationsOf(path, pl.Name) {
				any = true
				allSkipped = allSkipped && i.Status == InvocationSkipped
			}
			if any && allSkipped && ownFailures(sh.index) == 0 {
				return done(OutcomeSkipped)
			}
			return done(OutcomeNormal)
		}
	}
	return Settled{}, nil, false
}

// designatedOutput is the endpoint whose result a sub-workflow call returns.
func (v view) designatedOutput(p *Definition, r *Run) (string, error) {
	if r.Owner == nil {
		return "", reject("ROOT_RUN")
	}
	owner := *r.Owner
	var body Body
	if r.Task == nil {
		i, ok := v.invocation(owner)
		if !ok {
			return "", reject("UNKNOWN_INVOCATION")
		}
		pl, err := v.placementOf(p, i.Run, i.Placement)
		if err != nil {
			return "", err
		}
		call, ok := pl.Control.(CallControl)
		if !ok {
			return "", reject("NOT_A_CALL")
		}
		body = call.Body
	} else {
		e, ok := v.execution(owner)
		if !ok {
			return "", reject("UNKNOWN_EXECUTION")
		}
		spec, err := v.taskSpec(p, e, *r.Task)
		if err != nil {
			return "", err
		}
		body = spec.Body
	}
	if !body.Workflow {
		return "", reject("NOT_A_WORKFLOW_CALL")
	}
	return body.Output, nil
}

// apply applies one operation.
func (st *stepper) apply(op Op) error {
	switch op := op.(type) {
	case OpStart:
		return st.start(op.Input)
	case OpInvoke:
		return st.invoke(op.Run, op.Placement, op.Trigger)
	case OpFetch:
		return st.fetch(op.Call)
	case OpReturned:
		return st.returned(op.Call, op.Value)
	case OpJudged:
		return st.judged(op.Call, op.Arm)
	case OpYielded:
		return st.yielded(op.Call, op.Value)
	case OpEnded:
		return st.ended(op.Call)
	case OpFailed:
		return st.failed(op.Call)
	case OpTimedOut:
		return st.timedOut(op.Call, op.Element)
	case OpLost:
		return st.lost(op.Call)
	case OpTerminated:
		return st.terminated(op.Call)
	case OpDeliver:
		return st.deliver(op.Run, op.Connection, op.Source, op.Value)
	case OpTransformFailed:
		return st.transformFailed(op.Run, op.Connection, op.Source)
	case OpTaskInput:
		return st.taskInput(op.Execution, op.Task, op.Value)
	case OpTaskInputFailed:
		return st.taskInputFailed(op.Execution, op.Task)
	case OpBeginTask:
		return st.beginTask(op.Execution, op.Task)
	case OpTaskOutput:
		return st.taskOutput(op.Execution, op.Task, op.Index, op.Value)
	case OpTaskOutputFailed:
		return st.taskOutputFailed(op.Execution, op.Task, op.Index)
	case OpSettle:
		return st.settle(op.Run, op.Placement)
	case OpCloseExecution:
		return st.closeExecution(op.Execution)
	case OpCloseRun:
		return st.closeRun(op.Run)
	case OpCancel:
		return st.cancel()
	case OpConclude:
		return st.conclude()
	}
	return reject("UNKNOWN_OP")
}

func (st *stepper) running() error {
	return require(st.s.Started && st.s.Status == StatusRunning, "NOT_RUNNING")
}

// getCall is the position of the call and a copy of it.
func (st *stepper) getCall(id string) (int, Call, error) {
	pos, ok := st.callPos(id)
	if !ok {
		return 0, Call{}, reject("UNKNOWN_CALL")
	}
	return pos, st.s.Calls[pos], nil
}

func (st *stepper) getExecution(id string) (int, *Execution, error) {
	pos, ok := st.executionPos(id)
	if !ok {
		return 0, nil, reject("UNKNOWN_EXECUTION")
	}
	return pos, &st.s.Executions[pos], nil
}

func (st *stepper) start(input *string) error {
	s := st.s
	if err := require(!s.Started && s.Status == StatusRunning, "ALREADY_STARTED"); err != nil {
		return err
	}
	w, ok := st.p.workflow(st.p.Main)
	if !ok {
		return reject("UNKNOWN_MAIN")
	}
	if err := require((w.Input != nil) == (input != nil), "INPUT_MISMATCH"); err != nil {
		return err
	}
	s.Started = true
	s.Runs = nil
	st.owned |= 1 << listRuns
	if st.ix != nil {
		st.ix.runs, st.ix.runsOf = map[string][]int{}, map[string][]int{}
	}
	st.addRun(Run{Path: Path{}, Workflow: st.p.Main, Input: input})
	return nil
}

// invocationInput is the input one invocation takes, if its trigger is available (§3.1, §5.3).
func (st *stepper) invocationInput(r *Run, w *Workflow, name string, trigger *string) (*string, error) {
	sh, ok := w.shape(st.p, name)
	if !ok {
		return nil, reject("INVALID_SHAPE")
	}
	switch {
	case sh.kind == shapeNone && trigger == nil:
		return nil, nil
	case sh.kind == shapeEntry && trigger == nil:
		return r.Input, nil
	case sh.kind == shapeSingle && trigger != nil:
		res := st.resolveSingle(r.Path, sh.index, sh.connection)
		if res.kind != resolutionValue {
			return nil, reject("INPUT_NOT_READY")
		}
		if res.source != *trigger {
			return nil, reject("WRONG_TRIGGER")
		}
		return res.input, nil
	case sh.kind == shapeStream && trigger != nil:
		d, ok := st.delivery(r.Path, sh.index, *trigger)
		if ok && d.Outcome.Kind == DeliveredValue {
			return ptr(d.Outcome.Value), nil
		}
		if ok && d.Outcome.Kind == DeliveredTrigger {
			return nil, nil
		}
		return nil, reject("INPUT_NOT_READY")
	}
	return nil, reject("INVALID_TRIGGER")
}

func (st *stepper) invoke(path Path, name string, trigger *string) error {
	if err := st.running(); err != nil {
		return err
	}
	r, ok := st.run(path)
	if !ok {
		return reject("UNKNOWN_RUN")
	}
	if r.Complete {
		return reject("RUN_COMPLETE")
	}
	w, ok := st.p.workflow(r.Workflow)
	if !ok {
		return reject("UNKNOWN_WORKFLOW")
	}
	pl, ok := w.placement(name)
	if !ok {
		return reject("UNKNOWN_PLACEMENT")
	}
	input, err := st.invocationInput(r, w, name, trigger)
	if err != nil {
		return err
	}
	id := keyInvocation(path, name, trigger)
	if _, dup := st.findInvocation(path, name, trigger); dup {
		return reject("DUPLICATE_INVOCATION")
	}
	if _, dup := st.invocation(id); dup {
		return reject("DUPLICATE_INVOCATION")
	}
	invocation := Invocation{ID: id, Run: path, Placement: name, Trigger: trigger, Input: input}
	switch c := pl.Control.(type) {
	case CallControl:
		if !c.Body.Workflow {
			decl, ok := st.p.function(c.Body.ID)
			if !ok {
				return reject("UNKNOWN_FUNCTION")
			}
			if _, dup := st.call(id); dup {
				return reject("DUPLICATE_CALL")
			}
			st.addInvocation(invocation)
			st.addCall(Call{ID: id, Owner: id, Target: CallTarget{ID: c.Body.ID}, Input: input,
				Stream: decl.Output.Kind == KindStream, Timeout: pl.Timeout, Policy: pl.Policy})
			return nil
		}
		child := appendOne(path, id)
		if _, dup := st.run(child); dup {
			return reject("DUPLICATE_RUN")
		}
		st.addInvocation(invocation)
		st.addRun(Run{Path: child, Workflow: c.Body.ID, Input: input, Owner: ptr(id)})
		return nil
	case BranchControl:
		if _, dup := st.call(id); dup {
			return reject("DUPLICATE_CALL")
		}
		st.addInvocation(invocation)
		st.addCall(Call{ID: id, Owner: id, Target: CallTarget{Judge: true, ID: c.Judge}, Input: input,
			Timeout: pl.Timeout, Policy: pl.Policy})
		return nil
	case ConcurrencyControl:
		if _, dup := st.execution(id); dup {
			return reject("DUPLICATE_EXECUTION")
		}
		tasks := make([]TaskState, len(c.Spec.Tasks))
		for n, task := range c.Spec.Tasks {
			status := TaskReady
			if c.Spec.Input != nil {
				status = TaskPending
			}
			tasks[n] = TaskState{Name: task.Name, Status: status}
		}
		st.addInvocation(invocation)
		st.addExecution(Execution{ID: id, Run: path, Placement: name, Input: input, Tasks: tasks})
		return nil
	}
	return reject("NOT_INVOCABLE")
}

// appendOne is xs with x appended, in a new list.
func appendOne[T any](xs []T, x T) []T {
	out := make([]T, len(xs), len(xs)+1)
	copy(out, xs)
	return append(out, x)
}

func (st *stepper) fetch(id string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	if err := require(c.Stream && c.Status == CallRunning, "NOT_FETCHABLE"); err != nil {
		return err
	}
	st.setCallStatus(pos, CallFetching)
	return nil
}

func (st *stepper) returned(id, value string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	if err := require(!c.Stream && c.Status == CallRunning && !c.Target.Judge, "NOT_RETURNABLE"); err != nil {
		return err
	}
	a, err := st.accept(&c, 0, value, nil)
	if err != nil {
		return err
	}
	o, err := st.ownerOf(&c)
	if err != nil {
		return err
	}
	st.addAccepted(a)
	st.setCallStatus(pos, CallReturned)
	st.settleOwner(o, InvocationSucceeded, TaskSucceeded)
	return nil
}

func (st *stepper) judged(id, arm string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	if err := require(c.Status == CallRunning && c.Target.Judge && c.Task == nil, "NOT_JUDGING"); err != nil {
		return err
	}
	ipos, ok := st.invocationPos(c.Owner)
	if !ok {
		return reject("UNKNOWN_INVOCATION")
	}
	i := &st.s.Invocations[ipos]
	pl, err := st.placementOf(st.p, i.Run, i.Placement)
	if err != nil {
		return err
	}
	branch, ok := pl.Control.(BranchControl)
	if !ok {
		return reject("NOT_BRANCH")
	}
	if err := require(slices.Contains(branch.Arms, arm), "UNKNOWN_ARM"); err != nil {
		return err
	}
	input := ""
	if i.Input != nil {
		input = *i.Input
	}
	a, err := st.accept(&c, 0, input, ptr(arm))
	if err != nil {
		return err
	}
	st.addAccepted(a)
	st.setCallStatus(pos, CallReturned)
	st.setInvocation(ipos, InvocationSucceeded, ptr(arm))
	return nil
}

func (st *stepper) yielded(id, value string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	if err := require(c.Stream && c.Status == CallFetching, "NOT_FETCHING"); err != nil {
		return err
	}
	a, err := st.accept(&c, c.Yields, value, nil)
	if err != nil {
		return err
	}
	st.addAccepted(a)
	st.setCall(pos, CallRunning, c.Yields+1)
	return nil
}

func (st *stepper) ended(id string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	if err := require(c.Stream && c.Status == CallFetching, "NOT_FETCHING"); err != nil {
		return err
	}
	o, err := st.ownerOf(&c)
	if err != nil {
		return err
	}
	st.setCallStatus(pos, CallReturned)
	st.settleOwner(o, InvocationSucceeded, TaskSucceeded)
	return nil
}

func (st *stepper) failed(id string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	if err := require(c.Status == CallRunning || c.Status == CallFetching, "NOT_RUNNING"); err != nil {
		return err
	}
	return st.failCall(pos, CallFailed, CauseError)
}

func (st *stepper) timedOut(id string, element bool) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	var ok bool
	if element {
		ok = c.Status == CallFetching && c.Timeout.ElementMs != nil
	} else {
		ok = (c.Status == CallRunning || c.Status == CallFetching) && c.Timeout.CallMs != nil
	}
	if err := require(ok, "NO_TIMEOUT"); err != nil {
		return err
	}
	return st.failCall(pos, CallCancelling, CauseTimeout)
}

func (st *stepper) lost(id string) error {
	s := st.s
	if err := require(s.Started && (s.Status == StatusRunning || s.Status == StatusStopping), "TERMINAL"); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	switch c.Status {
	case CallRunning, CallFetching:
		return st.failCall(pos, CallLost, CauseLost)
	case CallCancelling:
		return st.cancelled(pos, &c)
	}
	return reject("NOT_RUNNING")
}

// cancelled ends a cancelled call and its owner.
func (st *stepper) cancelled(pos int, c *Call) error {
	o, err := st.ownerOf(c)
	if err != nil {
		return err
	}
	st.setCallStatus(pos, CallCancelled)
	st.cancelOwner(o)
	return nil
}

func (st *stepper) terminated(id string) error {
	s := st.s
	if err := require(s.Started && (s.Status == StatusRunning || s.Status == StatusStopping), "TERMINAL"); err != nil {
		return err
	}
	pos, c, err := st.getCall(id)
	if err != nil {
		return err
	}
	if err := require(c.Status == CallCancelling, "NOT_CANCELLING"); err != nil {
		return err
	}
	return st.cancelled(pos, &c)
}

// deliveryTarget is the connection and workflow of one delivery, checked for eligibility.
func (st *stepper) deliveryTarget(path Path, index int, source string) (*Workflow, *Connection, error) {
	w, ok := st.workflow(st.p, path)
	if !ok {
		return nil, nil, reject("UNKNOWN_RUN")
	}
	if index < 0 || index >= len(w.Connections) {
		return nil, nil, reject("UNKNOWN_CONNECTION")
	}
	c := &w.Connections[index]
	r, ok := st.result(source)
	if !ok {
		return nil, nil, reject("UNKNOWN_RESULT")
	}
	if err := require(slices.Equal(r.Run, path) && r.Placement == c.Source && (c.Arm == nil || equalPtr(r.Arm, c.Arm)),
		"NOT_ELIGIBLE"); err != nil {
		return nil, nil, err
	}
	if _, dup := st.delivery(path, index, source); dup {
		return nil, nil, reject("DUPLICATE_DELIVERY")
	}
	return w, c, nil
}

func (st *stepper) deliver(path Path, index int, source string, value *string) error {
	if err := st.running(); err != nil {
		return err
	}
	_, c, err := st.deliveryTarget(path, index, source)
	if err != nil {
		return err
	}
	var outcome Delivered
	switch {
	case !c.Transform.Discard && value != nil:
		outcome = Delivered{Kind: DeliveredValue, Value: *value}
	case c.Transform.Discard && value == nil:
		outcome = Delivered{Kind: DeliveredTrigger}
	default:
		return reject("TRANSFORM_MISMATCH")
	}
	st.addDelivery(Delivery{Run: path, Connection: index, Source: source, Outcome: outcome})
	return nil
}

func (st *stepper) transformFailed(path Path, index int, source string) error {
	if err := st.running(); err != nil {
		return err
	}
	w, c, err := st.deliveryTarget(path, index, source)
	if err != nil {
		return err
	}
	if err := require(!c.Transform.Discard, "DISCARD_CANNOT_FAIL"); err != nil {
		return err
	}
	target, ok := w.placement(c.Target)
	if !ok {
		return reject("UNKNOWN_PLACEMENT")
	}
	st.addDelivery(Delivery{Run: path, Connection: index, Source: source, Outcome: Delivered{Kind: DeliveredFailed}})
	st.fail(Failure{Run: path, Placement: c.Target, Cause: CauseTransform}, target.Policy)
	return nil
}

func (st *stepper) taskInput(eid, name string, value *string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, e, err := st.getExecution(eid)
	if err != nil {
		return err
	}
	j, err := taskIndex(e, name)
	if err != nil {
		return err
	}
	t := e.Tasks[j]
	if err := require(t.Status == TaskPending, "NOT_PENDING"); err != nil {
		return err
	}
	spec, err := st.taskSpec(st.p, e, name)
	if err != nil {
		return err
	}
	if spec.Input == nil || spec.Input.Discard != (value == nil) {
		return reject("TRANSFORM_MISMATCH")
	}
	t.Status = TaskReady
	t.Input = value
	st.setTask(pos, t)
	return nil
}

func (st *stepper) taskInputFailed(eid, name string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, e, err := st.getExecution(eid)
	if err != nil {
		return err
	}
	j, err := taskIndex(e, name)
	if err != nil {
		return err
	}
	if err := require(e.Tasks[j].Status == TaskPending, "NOT_PENDING"); err != nil {
		return err
	}
	spec, err := st.taskSpec(st.p, e, name)
	if err != nil {
		return err
	}
	if err := require(spec.Input != nil && !spec.Input.Discard, "DISCARD_CANNOT_FAIL"); err != nil {
		return err
	}
	failure := Failure{Run: e.Run, Placement: e.Placement, Task: ptr(name), Cause: CauseTransform}
	st.setTaskStatus(pos, j, TaskFailed)
	st.fail(failure, spec.Policy)
	return nil
}

func (st *stepper) beginTask(eid, name string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, e, err := st.getExecution(eid)
	if err != nil {
		return err
	}
	if err := require(!e.Complete, "EXECUTION_COMPLETE"); err != nil {
		return err
	}
	c, err := st.concurrencyOf(st.p, e)
	if err != nil {
		return err
	}
	j, err := taskIndex(e, name)
	if err != nil {
		return err
	}
	task := e.Tasks[j]
	if err := require(task.Status == TaskReady, "NOT_READY"); err != nil {
		return err
	}
	if err := require(uint64(st.slotsHeld(e)) < c.Limit, "NO_SLOT"); err != nil {
		return err
	}
	spec, err := st.taskSpec(st.p, e, name)
	if err != nil {
		return err
	}
	id := taskID(e.ID, name)
	run := e.Run
	if !spec.Body.Workflow {
		decl, ok := st.p.function(spec.Body.ID)
		if !ok {
			return reject("UNKNOWN_FUNCTION")
		}
		if _, dup := st.call(id); dup {
			return reject("DUPLICATE_CALL")
		}
		st.setTaskStatus(pos, j, TaskActive)
		st.addCall(Call{ID: id, Owner: eid, Task: ptr(name), Target: CallTarget{ID: spec.Body.ID},
			Input: task.Input, Stream: decl.Output.Kind == KindStream, Timeout: spec.Timeout, Policy: spec.Policy})
		return nil
	}
	child := appendOne(run, id)
	if _, dup := st.run(child); dup {
		return reject("DUPLICATE_RUN")
	}
	st.setTaskStatus(pos, j, TaskActive)
	st.addRun(Run{Path: child, Workflow: spec.Body.ID, Input: task.Input, Owner: ptr(eid), Task: ptr(name)})
	return nil
}

func (st *stepper) taskResult(eid, name string, index int) (int, error) {
	pos, ok := st.taskResultPos(eid, name, index)
	if !ok {
		return 0, reject("UNKNOWN_RESULT")
	}
	return pos, nil
}

func (st *stepper) taskOutput(eid, name string, index int, value string) error {
	if err := st.running(); err != nil {
		return err
	}
	_, e, err := st.getExecution(eid)
	if err != nil {
		return err
	}
	c, err := st.concurrencyOf(st.p, e)
	if err != nil {
		return err
	}
	spec, err := st.taskSpec(st.p, e, name)
	if err != nil {
		return err
	}
	if err := require(spec.Output != nil, "NOT_IN_OUTPUT"); err != nil {
		return err
	}
	pos, err := st.taskResult(eid, name, index)
	if err != nil {
		return err
	}
	if err := require(st.s.TaskResults[pos].Output.Kind == TaskOutputPending, "ALREADY_TRANSFORMED"); err != nil {
		return err
	}
	output := TaskOutput{Kind: TaskOutputValue, Value: value}
	if c.Output == CollectList {
		st.setTaskOutput(pos, output)
		return nil
	}
	result := Result{ID: keyTaskOutput(eid, name, index), Run: e.Run, Placement: e.Placement, Producer: eid,
		Value: value}
	if _, dup := st.result(result.ID); dup {
		return reject("DUPLICATE_RESULT")
	}
	st.setTaskOutput(pos, output)
	st.addResult(result)
	return nil
}

func (st *stepper) taskOutputFailed(eid, name string, index int) error {
	if err := st.running(); err != nil {
		return err
	}
	_, e, err := st.getExecution(eid)
	if err != nil {
		return err
	}
	spec, err := st.taskSpec(st.p, e, name)
	if err != nil {
		return err
	}
	if err := require(spec.Output != nil, "NOT_IN_OUTPUT"); err != nil {
		return err
	}
	pos, err := st.taskResult(eid, name, index)
	if err != nil {
		return err
	}
	if err := require(st.s.TaskResults[pos].Output.Kind == TaskOutputPending, "ALREADY_TRANSFORMED"); err != nil {
		return err
	}
	failure := Failure{Run: e.Run, Placement: e.Placement, Task: ptr(name), Cause: CauseTransform}
	st.setTaskOutput(pos, TaskOutput{Kind: TaskOutputFailed})
	st.fail(failure, spec.Policy)
	return nil
}

func (st *stepper) settle(path Path, name string) error {
	if err := st.running(); err != nil {
		return err
	}
	r, ok := st.run(path)
	if !ok {
		return reject("UNKNOWN_RUN")
	}
	if r.Complete {
		return reject("RUN_COMPLETE")
	}
	w, ok := st.p.workflow(r.Workflow)
	if !ok {
		return reject("UNKNOWN_WORKFLOW")
	}
	pl, ok := w.placement(name)
	if !ok {
		return reject("UNKNOWN_PLACEMENT")
	}
	if _, dup := st.settledOf(path, name); dup {
		return reject("ALREADY_SETTLED")
	}
	sh, ok := w.shape(st.p, name)
	if !ok {
		return reject("INVALID_SHAPE")
	}
	kind, ok := w.outputKind(st.p, name)
	if !ok {
		return reject("INVALID_KIND")
	}
	settled, result, ok := st.settleOutcome(path, pl, sh, kind)
	if !ok {
		return reject("NOT_READY")
	}
	if result != nil {
		if _, dup := st.result(result.ID); dup {
			return reject("DUPLICATE_RESULT")
		}
	}
	st.addSettled(settled)
	if result != nil {
		st.addResult(*result)
	}
	return nil
}

func (st *stepper) closeExecution(eid string) error {
	if err := st.running(); err != nil {
		return err
	}
	pos, e, err := st.getExecution(eid)
	if err != nil {
		return err
	}
	if err := require(!e.Complete, "EXECUTION_COMPLETE"); err != nil {
		return err
	}
	c, err := st.concurrencyOf(st.p, e)
	if err != nil {
		return err
	}
	for j := range e.Tasks {
		if !st.taskEnded(e, &e.Tasks[j]) {
			return reject("TASKS_RUNNING")
		}
	}
	var included []string
	for _, task := range c.Tasks {
		if task.Output != nil {
			included = append(included, task.Name)
		}
	}
	var outputs []*TaskResult
	for x := range st.taskResultsOf(eid) {
		if slices.Contains(included, x.Task) {
			outputs = append(outputs, x)
		}
	}
	for _, x := range outputs {
		if x.Output.Kind == TaskOutputPending {
			return reject("OUTPUT_PENDING")
		}
	}
	ipos, ok := st.invocationPos(eid)
	if !ok {
		return reject("UNKNOWN_INVOCATION")
	}
	allSkipped := true
	for _, task := range e.Tasks {
		if slices.Contains(included, task.Name) && task.Status != TaskSkipped {
			allSkipped = false
		}
	}
	if allSkipped {
		st.completeExecution(pos)
		st.setInvocationStatus(ipos, InvocationSkipped)
		return nil
	}
	if c.Output == CollectStream {
		st.completeExecution(pos)
		st.setInvocationStatus(ipos, InvocationSucceeded)
		return nil
	}
	var values []string
	for _, x := range outputs {
		if v, ok := x.Output.value(); ok {
			values = append(values, v)
		}
	}
	result := Result{ID: keyList(eid), Run: e.Run, Placement: e.Placement, Producer: eid, Value: listValue(values)}
	if _, dup := st.result(result.ID); dup {
		return reject("DUPLICATE_RESULT")
	}
	st.completeExecution(pos)
	st.setInvocationStatus(ipos, InvocationSucceeded)
	st.addResult(result)
	return nil
}

func (st *stepper) closeRun(path Path) error {
	if err := st.running(); err != nil {
		return err
	}
	rpos, ok := st.runPos(path)
	if !ok {
		return reject("UNKNOWN_RUN")
	}
	r := st.s.Runs[rpos]
	if err := require(!r.Complete && len(path) != 0, "NOT_CLOSABLE"); err != nil {
		return err
	}
	w, ok := st.p.workflow(r.Workflow)
	if !ok {
		return reject("UNKNOWN_WORKFLOW")
	}
	for _, pl := range w.Placements {
		if _, settled := st.settledOf(path, pl.Name); !settled {
			return reject("NOT_SETTLED")
		}
	}
	output, err := st.designatedOutput(st.p, &r)
	if err != nil {
		return err
	}
	x, ok := st.settledOf(path, output)
	if !ok {
		return reject("NOT_SETTLED")
	}
	outcome := x.Outcome
	var value *string
	if first, ok := st.firstResultOf(path, output); ok {
		value = ptr(first.Value)
	}
	if r.Owner == nil {
		return reject("ROOT_RUN")
	}
	owner := *r.Owner
	if r.Task == nil {
		ipos, ok := st.invocationPos(owner)
		if !ok {
			return reject("UNKNOWN_INVOCATION")
		}
		i := &st.s.Invocations[ipos]
		status := i.Status
		switch outcome {
		case OutcomeNormal:
			if value == nil {
				return reject("MISSING_RESULT")
			}
			result := Result{ID: keyReturned(i.ID), Run: i.Run, Placement: i.Placement, Producer: i.ID, Value: *value}
			if _, dup := st.result(result.ID); dup {
				return reject("DUPLICATE_RESULT")
			}
			st.completeRun(rpos)
			st.setInvocationStatus(ipos, InvocationSucceeded)
			st.addResult(result)
			return nil
		case OutcomeSkipped:
			status = InvocationSkipped
		case OutcomeFailed:
			status = InvocationFailed
		case OutcomeUpstreamFailed:
			status = InvocationUpstreamFailed
		}
		st.completeRun(rpos)
		st.setInvocationStatus(ipos, status)
		return nil
	}
	name := *r.Task
	epos, e, err := st.getExecution(owner)
	if err != nil {
		return err
	}
	j, err := taskIndex(e, name)
	if err != nil {
		return err
	}
	status := e.Tasks[j].Status
	switch outcome {
	case OutcomeNormal:
		if value == nil {
			return reject("MISSING_RESULT")
		}
		if _, dup := st.taskResultPos(e.ID, name, 0); dup {
			return reject("DUPLICATE_RESULT")
		}
		st.completeRun(rpos)
		st.setTaskStatus(epos, j, TaskSucceeded)
		st.addTaskResult(TaskResult{Execution: e.ID, Task: name, Index: 0, Value: *value})
		return nil
	case OutcomeSkipped:
		status = TaskSkipped
	case OutcomeFailed:
		status = TaskFailed
	case OutcomeUpstreamFailed:
		status = TaskUpstreamFailed
	}
	st.completeRun(rpos)
	st.setTaskStatus(epos, j, status)
	return nil
}

func (st *stepper) cancel() error {
	s := st.s
	if err := require(s.Started, "NOT_STARTED"); err != nil {
		return err
	}
	switch s.Status {
	case StatusRunning:
		st.stop()
		s.Cancelled = true
		return nil
	case StatusStopping:
		s.Cancelled = true
		return nil
	}
	return reject("TERMINAL")
}

// conclude decides the final status (§11.3, §13.3).
func (st *stepper) conclude() error {
	s := st.s
	if err := require(s.Started, "NOT_STARTED"); err != nil {
		return err
	}
	switch s.Status {
	case StatusRunning:
		rpos, ok := st.runPos(Path{})
		if !ok {
			return reject("NO_ROOT")
		}
		w, ok := st.p.workflow(s.Runs[rpos].Workflow)
		if !ok {
			return reject("UNKNOWN_WORKFLOW")
		}
		for _, pl := range w.Placements {
			if _, settled := st.settledOf(Path{}, pl.Name); !settled {
				return reject("NOT_SETTLED")
			}
		}
		status := StatusSucceeded
		if len(s.Failures) > 0 {
			status = StatusFailed
		} else {
			allSkipped := true
			for _, pl := range w.Placements {
				if !w.isEndpoint(pl.Name) {
					continue
				}
				if x, ok := st.settledOf(Path{}, pl.Name); !ok || x.Outcome != OutcomeSkipped {
					allSkipped = false
				}
			}
			if allSkipped {
				status = StatusSkipped
			}
		}
		st.completeRun(rpos)
		s.Status = status
		return nil
	case StatusStopping:
		for _, c := range s.Calls {
			if !c.Status.ended() {
				return reject("CALLS_RUNNING")
			}
		}
		s.Status = StatusCancelled
		if len(s.Failures) > 0 {
			s.Status = StatusFailed
		}
		return nil
	}
	return reject("TERMINAL")
}
