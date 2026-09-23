package suimon

import (
	"iter"
	"slices"
)

// Reading a state. The rules look records up by identity and by where they belong; a view does
// that with the indexes of an owned state (stateIndex), and by scanning the lists otherwise. Both
// find the same records in the same order: an index maps a key to the positions of the matching
// records in list order, and a lookup of one record takes the first, as a scan does.

// Keys of the indexes. A run is keyed by runKey, which is injective.

type placementRef struct{ run, placement string }

type invocationRef struct {
	run, placement string
	triggered      bool
	trigger        string
}

type deliveryRef struct {
	run        string
	connection int
	source     string
}

type connectionRef struct {
	run        string
	connection int
}

type taskResultRef struct {
	execution, task string
	index           int
}

func runKey(path Path) string { return Identity(path...) }

func invocationRefOf(path Path, placement string, trigger *string) invocationRef {
	if trigger == nil {
		return invocationRef{run: runKey(path), placement: placement}
	}
	return invocationRef{run: runKey(path), placement: placement, triggered: true, trigger: *trigger}
}

// stateIndex indexes the lists of one state by the keys the rules and the driver look up. Lists
// only grow at the end, and a record that changes keeps its keys, so positions stay valid; the
// only change that moves keys, the status of an invocation, updates active.
type stateIndex struct {
	runs map[string][]int
	// runsOf are the runs by owner: the invocation or the execution that called them.
	runsOf        map[string][]int
	invocations   map[string][]int
	invoked       map[invocationRef][]int
	invocationsOf map[placementRef][]int
	// active counts the active invocations of each placement of a run.
	active map[placementRef]int
	calls  map[string][]int
	// callsOf are the calls by owner.
	callsOf       map[string][]int
	executions    map[string][]int
	results       map[string][]int
	resultsOf     map[placementRef][]int
	deliveries    map[deliveryRef][]int
	deliveriesOn  map[connectionRef][]int
	settled       map[placementRef][]int
	settledIn     map[string]int
	taskResults   map[taskResultRef][]int
	taskResultsOf map[string][]int
}

func newStateIndex(s *State) *stateIndex {
	ix := &stateIndex{
		runs: map[string][]int{}, runsOf: map[string][]int{},
		invocations: map[string][]int{}, invoked: map[invocationRef][]int{},
		invocationsOf: map[placementRef][]int{}, active: map[placementRef]int{},
		calls: map[string][]int{}, callsOf: map[string][]int{},
		executions: map[string][]int{},
		results:    map[string][]int{}, resultsOf: map[placementRef][]int{},
		deliveries: map[deliveryRef][]int{}, deliveriesOn: map[connectionRef][]int{},
		settled: map[placementRef][]int{}, settledIn: map[string]int{},
		taskResults: map[taskResultRef][]int{}, taskResultsOf: map[string][]int{},
	}
	for i := range s.Runs {
		ix.addRun(i, &s.Runs[i])
	}
	for i := range s.Invocations {
		ix.addInvocation(i, &s.Invocations[i])
	}
	for i := range s.Calls {
		ix.addCall(i, &s.Calls[i])
	}
	for i := range s.Executions {
		ix.addExecution(i, &s.Executions[i])
	}
	for i := range s.Results {
		ix.addResult(i, &s.Results[i])
	}
	for i := range s.Deliveries {
		ix.addDelivery(i, &s.Deliveries[i])
	}
	for i := range s.Settled {
		ix.addSettled(i, &s.Settled[i])
	}
	for i := range s.TaskResults {
		ix.addTaskResult(i, &s.TaskResults[i])
	}
	return ix
}

func (ix *stateIndex) addRun(pos int, r *Run) {
	key := runKey(r.Path)
	ix.runs[key] = append(ix.runs[key], pos)
	if r.Owner != nil {
		ix.runsOf[*r.Owner] = append(ix.runsOf[*r.Owner], pos)
	}
}

func (ix *stateIndex) addInvocation(pos int, i *Invocation) {
	ix.invocations[i.ID] = append(ix.invocations[i.ID], pos)
	ref := invocationRefOf(i.Run, i.Placement, i.Trigger)
	ix.invoked[ref] = append(ix.invoked[ref], pos)
	key := placementRef{ref.run, i.Placement}
	ix.invocationsOf[key] = append(ix.invocationsOf[key], pos)
	if i.Status == InvocationActive {
		ix.active[key]++
	}
}

// setInvocationStatus records that the invocation i, which had the status old, changed status.
func (ix *stateIndex) setInvocationStatus(i *Invocation, old InvocationStatus) {
	if (old == InvocationActive) == (i.Status == InvocationActive) {
		return
	}
	key := placementRef{runKey(i.Run), i.Placement}
	if i.Status == InvocationActive {
		ix.active[key]++
	} else if ix.active[key]--; ix.active[key] == 0 {
		delete(ix.active, key)
	}
}

func (ix *stateIndex) addCall(pos int, c *Call) {
	ix.calls[c.ID] = append(ix.calls[c.ID], pos)
	ix.callsOf[c.Owner] = append(ix.callsOf[c.Owner], pos)
}

func (ix *stateIndex) addExecution(pos int, e *Execution) {
	ix.executions[e.ID] = append(ix.executions[e.ID], pos)
}

func (ix *stateIndex) addResult(pos int, r *Result) {
	ix.results[r.ID] = append(ix.results[r.ID], pos)
	key := placementRef{runKey(r.Run), r.Placement}
	ix.resultsOf[key] = append(ix.resultsOf[key], pos)
}

func (ix *stateIndex) addDelivery(pos int, d *Delivery) {
	run := runKey(d.Run)
	ref := deliveryRef{run, d.Connection, d.Source}
	ix.deliveries[ref] = append(ix.deliveries[ref], pos)
	key := connectionRef{run, d.Connection}
	ix.deliveriesOn[key] = append(ix.deliveriesOn[key], pos)
}

func (ix *stateIndex) addSettled(pos int, x *Settled) {
	run := runKey(x.Run)
	key := placementRef{run, x.Placement}
	ix.settled[key] = append(ix.settled[key], pos)
	ix.settledIn[run]++
}

func (ix *stateIndex) addTaskResult(pos int, r *TaskResult) {
	ref := taskResultRef{r.Execution, r.Task, r.Index}
	ix.taskResults[ref] = append(ix.taskResults[ref], pos)
	ix.taskResultsOf[r.Execution] = append(ix.taskResultsOf[r.Execution], pos)
}

// view reads a state: through ix when the state has an index, by scanning its lists when ix is nil.
type view struct {
	s  *State
	ix *stateIndex
}

// find is the position of the first record of xs that matches, through the positions of an index
// (indexed) or by a scan.
func find[T any](xs []T, indexed bool, positions []int, match func(*T) bool) (int, bool) {
	if indexed {
		if len(positions) == 0 {
			return 0, false
		}
		return positions[0], true
	}
	for i := range xs {
		if match(&xs[i]) {
			return i, true
		}
	}
	return 0, false
}

// all are the records of xs that match, in list order.
func all[T any](xs []T, indexed bool, positions []int, match func(*T) bool) iter.Seq[*T] {
	return func(yield func(*T) bool) {
		if indexed {
			for _, pos := range positions {
				if !yield(&xs[pos]) {
					return
				}
			}
			return
		}
		for i := range xs {
			if match(&xs[i]) && !yield(&xs[i]) {
				return
			}
		}
	}
}

func (v view) indexed() bool { return v.ix != nil }

func (v view) runPos(path Path) (int, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.runs[runKey(path)]
	}
	return find(v.s.Runs, v.indexed(), positions, func(r *Run) bool { return slices.Equal(r.Path, path) })
}

func (v view) run(path Path) (*Run, bool) {
	pos, ok := v.runPos(path)
	if !ok {
		return nil, false
	}
	return &v.s.Runs[pos], true
}

func (v view) workflow(p *Program, path Path) (*Workflow, bool) {
	r, ok := v.run(path)
	if !ok {
		return nil, false
	}
	return p.workflow(r.Workflow)
}

// runsOf are the runs whose owner is owner.
func (v view) runsOf(owner string) iter.Seq[*Run] {
	var positions []int
	if v.indexed() {
		positions = v.ix.runsOf[owner]
	}
	return all(v.s.Runs, v.indexed(), positions, func(r *Run) bool { return r.Owner != nil && *r.Owner == owner })
}

func (v view) invocationPos(id string) (int, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.invocations[id]
	}
	return find(v.s.Invocations, v.indexed(), positions, func(i *Invocation) bool { return i.ID == id })
}

func (v view) invocation(id string) (*Invocation, bool) {
	pos, ok := v.invocationPos(id)
	if !ok {
		return nil, false
	}
	return &v.s.Invocations[pos], true
}

func (v view) invocationsOf(path Path, name string) iter.Seq[*Invocation] {
	var positions []int
	if v.indexed() {
		positions = v.ix.invocationsOf[placementRef{runKey(path), name}]
	}
	return all(v.s.Invocations, v.indexed(), positions, func(i *Invocation) bool {
		return slices.Equal(i.Run, path) && i.Placement == name
	})
}

// findInvocation is the first invocation of a placement in a run with the trigger.
func (v view) findInvocation(path Path, name string, trigger *string) (*Invocation, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.invoked[invocationRefOf(path, name, trigger)]
	}
	pos, ok := find(v.s.Invocations, v.indexed(), positions, func(i *Invocation) bool {
		return slices.Equal(i.Run, path) && i.Placement == name && equalPtr(i.Trigger, trigger)
	})
	if !ok {
		return nil, false
	}
	return &v.s.Invocations[pos], true
}

func (v view) callPos(id string) (int, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.calls[id]
	}
	return find(v.s.Calls, v.indexed(), positions, func(c *Call) bool { return c.ID == id })
}

func (v view) call(id string) (*Call, bool) {
	pos, ok := v.callPos(id)
	if !ok {
		return nil, false
	}
	return &v.s.Calls[pos], true
}

// callsOf are the calls whose owner is owner.
func (v view) callsOf(owner string) iter.Seq[*Call] {
	var positions []int
	if v.indexed() {
		positions = v.ix.callsOf[owner]
	}
	return all(v.s.Calls, v.indexed(), positions, func(c *Call) bool { return c.Owner == owner })
}

func (v view) executionsWith(id string) iter.Seq[*Execution] {
	var positions []int
	if v.indexed() {
		positions = v.ix.executions[id]
	}
	return all(v.s.Executions, v.indexed(), positions, func(e *Execution) bool { return e.ID == id })
}

func (v view) executionPos(id string) (int, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.executions[id]
	}
	return find(v.s.Executions, v.indexed(), positions, func(e *Execution) bool { return e.ID == id })
}

func (v view) execution(id string) (*Execution, bool) {
	pos, ok := v.executionPos(id)
	if !ok {
		return nil, false
	}
	return &v.s.Executions[pos], true
}

func (v view) result(id string) (*Result, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.results[id]
	}
	pos, ok := find(v.s.Results, v.indexed(), positions, func(r *Result) bool { return r.ID == id })
	if !ok {
		return nil, false
	}
	return &v.s.Results[pos], true
}

func (v view) resultsOf(path Path, name string) iter.Seq[*Result] {
	var positions []int
	if v.indexed() {
		positions = v.ix.resultsOf[placementRef{runKey(path), name}]
	}
	return all(v.s.Results, v.indexed(), positions, func(r *Result) bool {
		return slices.Equal(r.Run, path) && r.Placement == name
	})
}

// firstResultOf is the first result of a placement in a run.
func (v view) firstResultOf(path Path, name string) (*Result, bool) {
	for r := range v.resultsOf(path, name) {
		return r, true
	}
	return nil, false
}

func (v view) settledOf(path Path, name string) (*Settled, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.settled[placementRef{runKey(path), name}]
	}
	pos, ok := find(v.s.Settled, v.indexed(), positions, func(x *Settled) bool {
		return slices.Equal(x.Run, path) && x.Placement == name
	})
	if !ok {
		return nil, false
	}
	return &v.s.Settled[pos], true
}

func (v view) delivery(path Path, index int, source string) (*Delivery, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.deliveries[deliveryRef{runKey(path), index, source}]
	}
	pos, ok := find(v.s.Deliveries, v.indexed(), positions, func(d *Delivery) bool {
		return slices.Equal(d.Run, path) && d.Connection == index && d.Source == source
	})
	if !ok {
		return nil, false
	}
	return &v.s.Deliveries[pos], true
}

func (v view) deliveriesOn(path Path, index int) iter.Seq[*Delivery] {
	var positions []int
	if v.indexed() {
		positions = v.ix.deliveriesOn[connectionRef{runKey(path), index}]
	}
	return all(v.s.Deliveries, v.indexed(), positions, func(d *Delivery) bool {
		return slices.Equal(d.Run, path) && d.Connection == index
	})
}

func (v view) taskResultPos(execution, task string, index int) (int, bool) {
	var positions []int
	if v.indexed() {
		positions = v.ix.taskResults[taskResultRef{execution, task, index}]
	}
	return find(v.s.TaskResults, v.indexed(), positions, func(r *TaskResult) bool {
		return r.Execution == execution && r.Task == task && r.Index == index
	})
}

// taskResultsOf are the task results of an execution.
func (v view) taskResultsOf(execution string) iter.Seq[*TaskResult] {
	var positions []int
	if v.indexed() {
		positions = v.ix.taskResultsOf[execution]
	}
	return all(v.s.TaskResults, v.indexed(), positions, func(r *TaskResult) bool { return r.Execution == execution })
}

// invocationEnded: calls, child runs and executions record their owner, so ending checks follow
// ownership.
func (v view) invocationEnded(i *Invocation) bool {
	if i.Status == InvocationActive {
		return false
	}
	for c := range v.callsOf(i.ID) {
		if c.Task == nil && !c.Status.ended() {
			return false
		}
	}
	for r := range v.runsOf(i.ID) {
		if r.Task == nil && !r.Complete {
			return false
		}
	}
	for e := range v.executionsWith(i.ID) {
		if !e.Complete {
			return false
		}
	}
	return true
}

// eligible are the results a connection carries: those of its source, on its arm for a branch.
func (v view) eligible(path Path, c Connection) iter.Seq[*Result] {
	return func(yield func(*Result) bool) {
		for r := range v.resultsOf(path, c.Source) {
			if (c.Arm == nil || equalPtr(r.Arm, c.Arm)) && !yield(r) {
				return
			}
		}
	}
}

func (v view) resolveSingle(path Path, index int, c Connection) resolution {
	for d := range v.deliveriesOn(path, index) {
		switch d.Outcome.Kind {
		case DeliveredValue:
			return resolution{kind: resolutionValue, source: d.Source, input: ptr(d.Outcome.Value)}
		case DeliveredTrigger:
			return resolution{kind: resolutionValue, source: d.Source}
		default:
			return resolution{kind: resolutionTransformFailed}
		}
	}
	x, ok := v.settledOf(path, c.Source)
	if !ok {
		return resolution{kind: resolutionPending}
	}
	switch armOutcome(x, c.Arm) {
	case OutcomeNormal:
		return resolution{kind: resolutionPending}
	case OutcomeSkipped:
		return resolution{kind: resolutionSkipped}
	default:
		return resolution{kind: resolutionFailure}
	}
}

// streamEnd: a Stream connection ends once its source settled and each of its results was
// delivered.
func (v view) streamEnd(path Path, index int, c Connection) (Outcome, bool) {
	x, ok := v.settledOf(path, c.Source)
	if !ok {
		return 0, false
	}
	for r := range v.eligible(path, c) {
		if _, delivered := v.delivery(path, index, r.ID); !delivered {
			return 0, false
		}
	}
	return armOutcome(x, c.Arm), true
}

// holdsSlot: a task holds a slot while its body runs, including a cancelled call that has not
// terminated.
func (v view) holdsSlot(e *Execution, t *TaskState) bool {
	if t.Status == TaskActive {
		return true
	}
	for c := range v.callsOf(e.ID) {
		if c.Task != nil && *c.Task == t.Name && c.Status == CallCancelling {
			return true
		}
	}
	return false
}

func (v view) taskEnded(e *Execution, t *TaskState) bool {
	if !t.Status.ended() || v.holdsSlot(e, t) {
		return false
	}
	for r := range v.runsOf(e.ID) {
		if r.Task != nil && *r.Task == t.Name && !r.Complete {
			return false
		}
	}
	return true
}

func (v view) slotsHeld(e *Execution) int {
	n := 0
	for i := range e.Tasks {
		if v.holdsSlot(e, &e.Tasks[i]) {
			n++
		}
	}
	return n
}

func (v view) placementOf(p *Program, path Path, name string) (*Placement, error) {
	w, ok := v.workflow(p, path)
	if !ok {
		return nil, reject("UNKNOWN_RUN")
	}
	pl, ok := w.placement(name)
	if !ok {
		return nil, reject("UNKNOWN_PLACEMENT")
	}
	return pl, nil
}

func (v view) concurrencyOf(p *Program, e *Execution) (*Concurrency, error) {
	pl, err := v.placementOf(p, e.Run, e.Placement)
	if err != nil {
		return nil, err
	}
	c, ok := pl.Control.(ConcurrencyControl)
	if !ok {
		return nil, reject("NOT_CONCURRENCY")
	}
	return &c.Spec, nil
}

func (v view) taskSpec(p *Program, e *Execution, name string) (*TaskSpec, error) {
	c, err := v.concurrencyOf(p, e)
	if err != nil {
		return nil, err
	}
	for i := range c.Tasks {
		if c.Tasks[i].Name == name {
			return &c.Tasks[i], nil
		}
	}
	return nil, reject("UNKNOWN_TASK")
}
