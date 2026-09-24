package suimon

// Op is an engine decision or a report from a user process (Lean Op). Each accepted operation is
// one state transition; the order of operations is left to the scheduler.
type Op interface{ isOp() }

type (
	// OpStart starts the workflow with the external input, nil when the main workflow takes none.
	OpStart struct{ Input *string }
	// OpInvoke applies a placement once; Trigger is the result that supplies its input.
	OpInvoke struct {
		Run       Path
		Placement string
		Trigger   *string
	}
	// OpFetch asks a Stream call for its next element.
	OpFetch struct{ Call string }
	// OpReturned reports the value a Single function call returned.
	OpReturned struct{ Call, Value string }
	// OpJudged reports the arm a branch judge selected.
	OpJudged struct{ Call, Arm string }
	// OpYielded reports the element a fetching Stream call yielded.
	OpYielded struct{ Call, Value string }
	// OpEnded reports that a fetching Stream call ended without another element.
	OpEnded struct{ Call string }
	// OpFailed reports that a call failed.
	OpFailed struct{ Call string }
	// OpTimedOut reports that a call exceeded its call timeout, or its element timeout.
	OpTimedOut struct {
		Call    string
		Element bool
	}
	// OpLost reports that the lease of a call expired.
	OpLost struct{ Call string }
	// OpTerminated reports that a cancelled call terminated.
	OpTerminated struct{ Call string }
	// OpDeliver applies the transform of a connection to a result; Value is nil for discard.
	OpDeliver struct {
		Run        Path
		Connection int
		Source     string
		Value      *string
	}
	// OpTransformFailed reports that the transform of a connection failed for a result.
	OpTransformFailed struct {
		Run        Path
		Connection int
		Source     string
	}
	// OpTaskInput applies the input transform of a task; Value is nil for discard.
	OpTaskInput struct {
		Execution, Task string
		Value           *string
	}
	// OpTaskInputFailed reports that the input transform of a task failed.
	OpTaskInputFailed struct{ Execution, Task string }
	// OpBeginTask starts the body of a ready task when a slot is free.
	OpBeginTask struct{ Execution, Task string }
	// OpTaskOutput applies the output transform of a task to one of its results.
	OpTaskOutput struct {
		Execution, Task string
		Index           int
		Value           string
	}
	// OpTaskOutputFailed reports that the output transform of a task failed for one result.
	OpTaskOutputFailed struct {
		Execution, Task string
		Index           int
	}
	// OpSettle records how a placement ended in a run.
	OpSettle struct {
		Run       Path
		Placement string
	}
	// OpCloseExecution completes an execution of a concurrency once its tasks ended.
	OpCloseExecution struct{ Execution string }
	// OpCloseRun completes a sub-workflow run once its placements settled.
	OpCloseRun struct{ Run Path }
	// OpCancel is the caller's cancellation of the workflow.
	OpCancel struct{}
	// OpConclude decides the final status.
	OpConclude struct{}
)

func (OpStart) isOp()            {}
func (OpInvoke) isOp()           {}
func (OpFetch) isOp()            {}
func (OpReturned) isOp()         {}
func (OpJudged) isOp()           {}
func (OpYielded) isOp()          {}
func (OpEnded) isOp()            {}
func (OpFailed) isOp()           {}
func (OpTimedOut) isOp()         {}
func (OpLost) isOp()             {}
func (OpTerminated) isOp()       {}
func (OpDeliver) isOp()          {}
func (OpTransformFailed) isOp()  {}
func (OpTaskInput) isOp()        {}
func (OpTaskInputFailed) isOp()  {}
func (OpBeginTask) isOp()        {}
func (OpTaskOutput) isOp()       {}
func (OpTaskOutputFailed) isOp() {}
func (OpSettle) isOp()           {}
func (OpCloseExecution) isOp()   {}
func (OpCloseRun) isOp()         {}
func (OpCancel) isOp()           {}
func (OpConclude) isOp()         {}
