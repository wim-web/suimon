package suimon

// FunctionDecl declares a user function; Input is nil for a function without input.
type FunctionDecl struct {
	ID     string
	Input  *ValueType
	Output Contract
}

// JudgeDecl declares a branch judge, which receives the branch input and names one arm.
type JudgeDecl struct {
	ID    string
	Input ValueType
}

// TransformDecl declares a connection transform.
type TransformDecl struct {
	ID     string
	Input  ValueType
	Output ValueType
}

// Body is what a call runs: a function, or a workflow whose endpoint Output is the call output.
type Body struct {
	// Workflow is false for a function call and true for a sub-workflow call.
	Workflow bool
	ID       string
	// Output names the endpoint of the called workflow; unused for a function.
	Output string
}

// FunctionBody calls the function id.
func FunctionBody(id string) Body { return Body{ID: id} }

// WorkflowBody calls the workflow id and returns the result of its endpoint output.
func WorkflowBody(id, output string) Body { return Body{Workflow: true, ID: id, Output: output} }

// Collect is how a concurrency returns the results of its tasks.
type Collect int

const (
	CollectList Collect = iota
	CollectStream
)

func (c Collect) String() string {
	if c == CollectStream {
		return "stream"
	}
	return "list"
}

// DiscardName is the name of the library transform for a target without input: it accepts any
// value, never fails, and passes nothing. A definition cannot declare a transform with this name.
const DiscardName = "discard"

// TransformRef is a declared transform, or discard.
type TransformRef struct {
	Discard bool
	// ID names the declared transform; unused for discard.
	ID string
}

// Declared refers to the declared transform id.
func Declared(id string) TransformRef { return TransformRef{ID: id} }

// Discard is the library transform that passes no value.
var Discard = TransformRef{Discard: true}

// TaskSpec is one task of a concurrency.
type TaskSpec struct {
	Name string
	Body Body
	// Input is nil when the concurrency has no input and the body takes none.
	Input *TransformRef
	// Output is nil for a task whose results are left out of the concurrency output.
	Output  *string
	Policy  Policy
	Timeout Timeout
}

// Concurrency runs its tasks for each input and collects their results.
type Concurrency struct {
	Input   *ValueType
	Limit   uint64
	Tasks   []TaskSpec
	Output  Collect
	Element ValueType
}

// Control is the kind of a placement: CallControl, BranchControl, WaitStreamControl,
// MergeControl or ConcurrencyControl (Lean Control).
type Control interface{ isControl() }

// CallControl calls a function or a sub-workflow.
type CallControl struct{ Body Body }

// BranchControl lets the judge select one of the arms for each input.
type BranchControl struct {
	Judge string
	Arms  []string
}

// WaitStreamControl collects a Stream into a Single list.
type WaitStreamControl struct{ Element ValueType }

// MergeControl collects Single inputs into a Single list.
type MergeControl struct{ Element ValueType }

// ConcurrencyControl runs the tasks of Spec.
type ConcurrencyControl struct{ Spec Concurrency }

func (CallControl) isControl()        {}
func (BranchControl) isControl()      {}
func (WaitStreamControl) isControl()  {}
func (MergeControl) isControl()       {}
func (ConcurrencyControl) isControl() {}

// Placement is one use of a node in a workflow graph.
type Placement struct {
	Name    string
	Control Control
	Policy  Policy
	Timeout Timeout
}

// Connection passes the results of Source, on Arm for a branch, through Transform to Target.
type Connection struct {
	Source    string
	Arm       *string
	Target    string
	Transform TransformRef
}

// Entry is the placement that receives the value passed to run.
type Entry struct {
	Type      ValueType
	Placement string
}

// Workflow is one graph of placements and connections.
type Workflow struct {
	ID          string
	Input       *Entry
	Placements  []Placement
	Connections []Connection
}

// Definition is a set of workflows with the type contracts of what they reference.
type Definition struct {
	Functions  []FunctionDecl
	Judges     []JudgeDecl
	Transforms []TransformDecl
	Workflows  []Workflow
	Main       string
}

// Lookups return the first declaration with the given id, like Lean's List.find?.

func (p *Definition) function(id string) (*FunctionDecl, bool) {
	for i := range p.Functions {
		if p.Functions[i].ID == id {
			return &p.Functions[i], true
		}
	}
	return nil, false
}

func (p *Definition) judge(id string) (*JudgeDecl, bool) {
	for i := range p.Judges {
		if p.Judges[i].ID == id {
			return &p.Judges[i], true
		}
	}
	return nil, false
}

func (p *Definition) transform(id string) (*TransformDecl, bool) {
	for i := range p.Transforms {
		if p.Transforms[i].ID == id {
			return &p.Transforms[i], true
		}
	}
	return nil, false
}

func (p *Definition) workflow(id string) (*Workflow, bool) {
	for i := range p.Workflows {
		if p.Workflows[i].ID == id {
			return &p.Workflows[i], true
		}
	}
	return nil, false
}

func (w *Workflow) placement(name string) (*Placement, bool) {
	for i := range w.Placements {
		if w.Placements[i].Name == name {
			return &w.Placements[i], true
		}
	}
	return nil, false
}

func (w *Workflow) incoming(name string) []Connection {
	var out []Connection
	for _, c := range w.Connections {
		if c.Target == name {
			out = append(out, c)
		}
	}
	return out
}

func (w *Workflow) outgoing(name string) []Connection {
	var out []Connection
	for _, c := range w.Connections {
		if c.Source == name {
			out = append(out, c)
		}
	}
	return out
}

func (w *Workflow) isEntry(name string) bool {
	return w.Input != nil && w.Input.Placement == name
}

// isEndpoint: a placement without outgoing connections is an endpoint.
func (w *Workflow) isEndpoint(name string) bool {
	for _, c := range w.Connections {
		if c.Source == name {
			return false
		}
	}
	return true
}
