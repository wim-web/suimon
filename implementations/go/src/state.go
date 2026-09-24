package suimon

import (
	"strconv"
)

// The execution state of Suimon/State.lean. Values stay opaque: the model moves their identities,
// which are strings. Step never modifies a state in place; every step builds a new one. Only an
// owner that holds the one reference to a state, the runtime driver and Check, changes it in place
// (machine, step.go).

// Path identifies a run: nil for the root run, and each sub-workflow call appends the identity of
// its owner.
type Path []string

// Identities of the records the engine creates (Lean namespace Key). Each kind starts with its own
// tag, so identities of different kinds never coincide, and each is a function of where the record
// comes from, never of the schedule.

// keyInvocation identifies the invocation of a placement in a run by its trigger, nil for none.
func keyInvocation(path Path, placement string, trigger *string) string {
	parts := []string{"invocation", Identity(path...), placement}
	if trigger != nil {
		parts = append(parts, *trigger)
	}
	return Identity(parts...)
}

// keyTask identifies the call or run of a task in an execution.
func keyTask(execution, task string) string { return Identity("task", execution, task) }

// keyCallResult identifies the index-th value a call returned or yielded.
func keyCallResult(call string, index int) string {
	return Identity("result", call, strconv.Itoa(index))
}

// keyAggregate identifies the list of a waitStream or Merge placement in a run.
func keyAggregate(path Path, placement string) string {
	return Identity("aggregate", Identity(path...), placement)
}

// keyTaskOutput identifies a result of a Stream concurrency output: the output transform of the
// index-th result of a task.
func keyTaskOutput(execution, task string, index int) string {
	return Identity("output", execution, task, strconv.Itoa(index))
}

// keyList identifies the list of a List concurrency output.
func keyList(execution string) string { return Identity("list", execution) }

// keyReturned identifies the result a sub-workflow call returned.
func keyReturned(invocation string) string { return Identity("return", invocation) }

// Cause is why a failure was recorded.
type Cause int

const (
	CauseError Cause = iota
	CauseTimeout
	CauseLost
	CauseTransform
)

var causeNames = []string{"error", "timeout", "lost", "transform"}

func (c Cause) String() string { return causeNames[c] }

// Outcome is how a placement ended in one run. A Single output has a value (normal) or the reason
// it has none; a Stream output ends normal or skipped, and failures stay in the failure records.
type Outcome int

const (
	OutcomeNormal Outcome = iota
	OutcomeSkipped
	OutcomeFailed
	OutcomeUpstreamFailed
)

var outcomeNames = []string{"normal", "skipped", "failed", "upstreamFailed"}

func (o Outcome) String() string { return outcomeNames[o] }

// Status is the status of the workflow execution.
type Status int

const (
	StatusRunning Status = iota
	StatusStopping
	StatusSucceeded
	StatusFailed
	StatusCancelled
	StatusSkipped
)

var statusNames = []string{"running", "stopping", "succeeded", "failed", "cancelled", "skipped"}

func (s Status) String() string { return statusNames[s] }

// Terminal reports whether the status is final.
func (s Status) Terminal() bool { return s != StatusRunning && s != StatusStopping }

// CallStatus is the status of a call of a user process.
type CallStatus int

const (
	CallRunning CallStatus = iota
	CallFetching
	CallCancelling
	CallReturned
	CallFailed
	CallLost
	CallCancelled
)

var callStatusNames = []string{"running", "fetching", "cancelling", "returned", "failed", "lost", "cancelled"}

func (s CallStatus) String() string { return callStatusNames[s] }

// ended: a cancelled call keeps running until it terminates (§8.2, §11.5).
func (s CallStatus) ended() bool {
	return s != CallRunning && s != CallFetching && s != CallCancelling
}

// InvocationStatus is the status of one application of a placement.
type InvocationStatus int

const (
	InvocationActive InvocationStatus = iota
	InvocationSucceeded
	InvocationSkipped
	InvocationFailed
	InvocationUpstreamFailed
	InvocationCancelled
)

var invocationStatusNames = []string{"active", "succeeded", "skipped", "failed", "upstreamFailed", "cancelled"}

func (s InvocationStatus) String() string { return invocationStatusNames[s] }

// TaskStatus is the status of one task in one execution of a concurrency.
type TaskStatus int

const (
	TaskPending TaskStatus = iota
	TaskReady
	TaskActive
	TaskSucceeded
	TaskSkipped
	TaskFailed
	TaskUpstreamFailed
	TaskNotStarted
	TaskCancelled
)

var taskStatusNames = []string{"pending", "ready", "active", "succeeded", "skipped", "failed",
	"upstreamFailed", "notStarted", "cancelled"}

func (s TaskStatus) String() string { return taskStatusNames[s] }

func (s TaskStatus) ended() bool { return s != TaskPending && s != TaskReady && s != TaskActive }

// Run is a workflow executed as the root or as one sub-workflow call.
type Run struct {
	Path     Path
	Workflow string
	Input    *string
	// Owner is the invocation, or the execution of the task, that called this workflow; nil for
	// the root.
	Owner    *string
	Task     *string
	Complete bool
}

// Invocation is one application of a placement: once for a Single input, once per element of a
// Stream.
type Invocation struct {
	ID        string
	Run       Path
	Placement string
	Trigger   *string
	Input     *string
	Status    InvocationStatus
	// Arm is the arm a branch judge selected.
	Arm *string
}

// CallTarget is the user process a call runs: a function, or a judge.
type CallTarget struct {
	Judge bool
	ID    string
}

// Call is a call of a user process. Its owner is an invocation, or the execution of a task.
type Call struct {
	ID      string
	Owner   string
	Task    *string
	Target  CallTarget
	Input   *string
	Stream  bool
	Status  CallStatus
	Yields  int
	Timeout Timeout
	Policy  Policy
}

// TaskState is one task of an execution.
type TaskState struct {
	Name   string
	Input  *string
	Status TaskStatus
}

// Execution is one execution of a concurrency placement for one input.
type Execution struct {
	ID        string
	Run       Path
	Placement string
	Input     *string
	Tasks     []TaskState
	Complete  bool
}

// TaskOutputKind is what the output transform of a task made of one task result.
type TaskOutputKind int

const (
	TaskOutputPending TaskOutputKind = iota
	TaskOutputValue
	TaskOutputFailed
)

// TaskOutput is the output transform of a task applied to one task result: pending, a value, or
// failed.
type TaskOutput struct {
	Kind TaskOutputKind
	// Value is the transformed value of TaskOutputValue.
	Value string
}

// value is Lean's TaskOutput.value?.
func (o TaskOutput) value() (string, bool) { return o.Value, o.Kind == TaskOutputValue }

// TaskResult is a result of a task body, before the task's output transform.
type TaskResult struct {
	Execution string
	Task      string
	Index     int
	Value     string
	Output    TaskOutput
}

// Result is an accepted result of a placement in a run. A branch result carries its selected arm.
type Result struct {
	ID        string
	Run       Path
	Placement string
	// Producer is what produced the result: the call for a call result, the execution for a
	// concurrency result, the invocation for a sub-workflow call result, and
	// keyAggregate(run, placement) for the list of a waitStream or Merge.
	Producer string
	Arm      *string
	Value    string
}

// DeliveredKind is what a connection transform made of one result.
type DeliveredKind int

const (
	DeliveredValue DeliveredKind = iota
	DeliveredTrigger
	DeliveredFailed
)

// Delivered is a transformed value, a trigger from discard, or a failed transform.
type Delivered struct {
	Kind DeliveredKind
	// Value is the transformed value of DeliveredValue.
	Value string
}

// Delivery is the transform of one connection applied to one result.
type Delivery struct {
	Run        Path
	Connection int
	Source     string
	Outcome    Delivered
}

// ArmOutcome is how one arm of a branch settled.
type ArmOutcome struct {
	Arm     string
	Outcome Outcome
}

// Settled records how a placement ended in a run. A branch settles each arm separately.
type Settled struct {
	Run       Path
	Placement string
	Outcome   Outcome
	Arms      []ArmOutcome
}

// Failure is a recorded failure.
type Failure struct {
	Run       Path
	Placement string
	Task      *string
	Cause     Cause
}

// State is the state of one workflow execution. The zero value is the state before the start.
type State struct {
	Status  Status
	Started bool
	// Cancelled records that the caller cancelled the workflow.
	Cancelled   bool
	Runs        []Run
	Invocations []Invocation
	Calls       []Call
	Executions  []Execution
	Results     []Result
	TaskResults []TaskResult
	Deliveries  []Delivery
	Settled     []Settled
	Failures    []Failure
}

// Input connections with their indices, which identify connections in a run.
type indexedConnection struct {
	index      int
	connection Connection
}

func (w *Workflow) inputs(name string) []indexedConnection {
	var out []indexedConnection
	for i, c := range w.Connections {
		if c.Target == name {
			out = append(out, indexedConnection{i, c})
		}
	}
	return out
}

// shapeKind says where one placement gets its input from.
type shapeKind int

const (
	shapeNone shapeKind = iota
	shapeEntry
	shapeSingle
	shapeStream
	shapeMerge
)

type shape struct {
	kind shapeKind
	// index and connection are the input of shapeSingle and shapeStream.
	index      int
	connection Connection
	// merged are the inputs of shapeMerge.
	merged []indexedConnection
}

// shape is Lean's shape? of a placement of w, whose kinds are k.
func (w *Workflow) shape(k kindTable, name string) (shape, bool) {
	pl, ok := w.placement(name)
	if !ok {
		return shape{}, false
	}
	if _, isMerge := pl.Control.(MergeControl); isMerge {
		return shape{kind: shapeMerge, merged: w.inputs(name)}, true
	}
	if w.isEntry(name) {
		return shape{kind: shapeEntry}, true
	}
	inputs := w.inputs(name)
	switch len(inputs) {
	case 0:
		return shape{kind: shapeNone}, true
	case 1:
		source, ok := k.outputKind(inputs[0].connection.Source)
		if !ok {
			return shape{}, false
		}
		kind := shapeSingle
		if source == KindStream {
			kind = shapeStream
		}
		return shape{kind: kind, index: inputs[0].index, connection: inputs[0].connection}, true
	}
	return shape{}, false
}

func armOutcome(x *Settled, arm *string) Outcome {
	if arm == nil {
		return x.Outcome
	}
	for _, a := range x.Arms {
		if a.Arm == *arm {
			return a.Outcome
		}
	}
	return x.Outcome
}

type resolutionKind int

const (
	resolutionPending resolutionKind = iota
	resolutionValue
	resolutionTransformFailed
	resolutionSkipped
	resolutionFailure
)

// resolution is what a Single connection resolves to: its delivered value (source and input), or
// why no value will come.
type resolution struct {
	kind   resolutionKind
	source string
	input  *string
}

func taskID(execution, task string) string { return keyTask(execution, task) }

// Lookups of the state by scanning its lists; view.go reads through an index when there is one.

func (s *State) view() view { return view{s: s} }

func (s *State) run(path Path) (*Run, bool) { return s.view().run(path) }

func (s *State) workflow(p *Definition, path Path) (*Workflow, bool) {
	return s.view().workflow(p, path)
}

func (s *State) invocation(id string) (*Invocation, bool) { return s.view().invocation(id) }

func (s *State) call(id string) (*Call, bool) { return s.view().call(id) }

func (s *State) settledOf(path Path, name string) (*Settled, bool) {
	return s.view().settledOf(path, name)
}

// Values are every value the state mentions, with repeats, in the order of Lean's State.values.
func (s *State) Values() []string {
	var values []string
	add := func(v *string) {
		if v != nil {
			values = append(values, *v)
		}
	}
	for _, r := range s.Runs {
		add(r.Input)
	}
	for _, i := range s.Invocations {
		add(i.Input)
	}
	for _, c := range s.Calls {
		add(c.Input)
	}
	for _, e := range s.Executions {
		add(e.Input)
		for _, t := range e.Tasks {
			add(t.Input)
		}
	}
	for _, r := range s.Results {
		values = append(values, r.Value)
	}
	for _, d := range s.Deliveries {
		if d.Outcome.Kind == DeliveredValue {
			values = append(values, d.Outcome.Value)
		}
	}
	for _, r := range s.TaskResults {
		values = append(values, r.Value)
		if v, ok := r.Output.value(); ok {
			values = append(values, v)
		}
	}
	return values
}
