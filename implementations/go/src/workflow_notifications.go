package suimon

import (
	"context"
	"fmt"
	"io"
	"slices"
)

// ExecutionCursor identifies an execution-status observation. It belongs to
// one Execution and is not a persistent checkpoint. Its zero value requests
// the first available observation.
type ExecutionCursor struct {
	execution *Execution
	revision  Nat
}

func (c ExecutionCursor) Revision() Nat { return c.revision }

// ExecutionUpdate describes the latest scheduler assessment. Workflow errors
// are in Err; WaitForChange's separate error concerns waiting for an update.
// Multiple changes may coalesce into the latest update.
type ExecutionUpdate struct {
	Cursor    ExecutionCursor
	Settled   bool
	Stopped   bool
	Err       error
	view      *runtimeView
	execution *Execution
}

// Result copies the committed view captured with this observation, on demand.
func (u ExecutionUpdate) Result() RunResult {
	if u.view == nil || u.execution == nil {
		return RunResult{}
	}
	return u.execution.result(u.view)
}

func (e *Execution) observeUpdate() (ExecutionUpdate, <-chan struct{}) {
	e.mu.Lock()
	defer e.mu.Unlock()
	return ExecutionUpdate{
		Cursor: ExecutionCursor{e, e.revision}, Settled: e.settled, Stopped: e.stopped,
		Err: copyExecutionError(e.err), view: e.view, execution: e,
	}, e.statusChanged
}

// Observe reads status without copying the model state, history, or values.
func (e *Execution) Observe() ExecutionUpdate {
	update, _ := e.observeUpdate()
	return update
}

// WaitForChange waits for a newer scheduler assessment, not for every model
// commit. A same-cause stall does not wake it. If the final update was already
// observed, it returns that update and io.EOF. Cursors from another execution
// or from the future are rejected. Cancelling ctx does not stop the execution.
func (e *Execution) WaitForChange(ctx context.Context, after ExecutionCursor) (ExecutionUpdate, error) {
	if ctx == nil {
		return e.Observe(), fmt.Errorf("nil wait context")
	}
	if after.execution != nil && after.execution != e {
		return e.Observe(), ErrInvalidExecutionCursor
	}
	for {
		update, changed := e.observeUpdate()
		if err := ctx.Err(); err != nil {
			return update, err
		}
		if after.revision.Cmp(update.Cursor.revision) > 0 {
			return update, ErrInvalidExecutionCursor
		}
		if after.revision.Cmp(update.Cursor.revision) < 0 {
			return update, nil
		}
		if update.Stopped {
			return update, io.EOF
		}
		e.metrics.changeWaits.Add(1)
		select {
		case <-changed:
		case <-ctx.Done():
			return e.Observe(), ctx.Err()
		}
	}
}

func executionErrorKey(err error) string {
	if err == nil {
		return ""
	}
	if stalled, ok := err.(*WorkerStalledError); ok {
		return "stalled:" + compact(stalled)
	}
	return fmt.Sprintf("%T:%s", err, err)
}

// Preserve causes for errors.Is while isolating mutable diagnostic fields.
func copyExecutionError(err error) error {
	switch err := err.(type) {
	case *WorkerStalledError:
		copy := *err
		copy.Handlers = slices.Clone(err.Handlers)
		for n := range copy.Handlers {
			copy.Handlers[n].Path = slices.Clone(copy.Handlers[n].Path)
			copy.Handlers[n].Definition = slices.Clone(copy.Handlers[n].Definition)
		}
		return &copy
	case *DecisionError:
		copy := *err
		copy.Path, copy.Definition = slices.Clone(err.Path), slices.Clone(err.Definition)
		return &copy
	case *CommitError:
		copy := *err
		return &copy
	case *Reject:
		copy := *err
		return &copy
	default:
		return err
	}
}
