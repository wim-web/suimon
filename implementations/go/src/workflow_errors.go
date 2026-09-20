package suimon

import (
	"errors"
	"fmt"
)

var (
	ErrWorkerStalled          = errors.New("worker slots occupied by stale handlers")
	ErrConditionNotMet        = errors.New("workflow ended without satisfying the condition")
	ErrInvalidExecutionCursor = errors.New("cursor does not identify an observed execution status")
)

type StalledHandler struct {
	Node       string
	Path       Path
	Definition Path
	Instance   string
	Attempt    string
	Since      Nat
	Deadline   Nat
}

// WorkerStalledError settles Wait without stopping a Start/Restore execution.
// Returning handlers release their slots and wake the scheduler automatically.
// Run/Resume stop on return; they cannot reclaim handlers that ignore context.
// Same-cause maintenance retains this assessment. Use Observe/WaitForChange
// to await recovery without repeatedly reading the same settled result.
type WorkerStalledError struct {
	Workers  int
	Handlers []StalledHandler
}

func (e *WorkerStalledError) Error() string {
	return fmt.Sprintf("%v (%d slots): %v", ErrWorkerStalled, e.Workers, e.Handlers)
}
func (e *WorkerStalledError) Unwrap() error { return ErrWorkerStalled }

// DecisionError reports a callback failure against the last committed state.
// Decision nodes have no modeled fail operation; the driver stops for recovery.
type DecisionError struct {
	Node       string
	Path       Path
	Definition Path
	Operation  string
	Item       string
	Iteration  Nat
	Cause      error
}

func (e *DecisionError) Error() string {
	return fmt.Sprintf("%s at %s/%s: %v", e.Operation, Identity(e.Path), e.Node, e.Cause)
}
func (e *DecisionError) Unwrap() error { return e.Cause }
