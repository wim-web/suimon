package suimon

import (
	"errors"
	"fmt"
)

func (r *workflowRuntime) blockedError() error {
	return fmt.Errorf("%w: %s", ErrBlocked, value(r.state.Reason, "DEPENDENCIES_UNRESOLVED"))
}

func (r *workflowRuntime) terminalError() error {
	if r.state.Status != "cancelled" {
		return nil
	}
	if r.ctx.Err() != nil {
		return errors.Join(ErrCancelled, r.ctx.Err())
	}
	return ErrCancelled
}

// slotDemand reassesses an existing stall against the new committed state.
// It probes only operations needing a local callback; it never runs callbacks
// or reserves claim credentials. Due maintenance is handled before this check.
func (r *workflowRuntime) slotDemand(now Nat) bool {
	eligible := func(op Op) bool {
		next, rejected := r.probe(op)
		return rejected == nil && !equal(next, r.state)
	}
	for _, i := range r.state.Instances {
		if i.Status == "ready" {
			auth := Credentials{i.ID, r.ids.attempt.peek(), r.ids.token.peek(), now}
			if eligible(Op{Kind: "claim", Auth: auth, Worker: "local"}) {
				return true
			}
		}
		if i.Status == "waitingInputs" && eligible(Op{Kind: "loopIterate", Inst: i.ID, Done: true}) {
			return true
		}
	}
	for _, frame := range r.state.Frames {
		if frame.Closed {
			continue
		}
		for _, node := range frame.Graph.Nodes {
			if node.Kind.Type != "branch" && node.Kind.Type != "filter" {
				continue
			}
			for _, op := range nodeCandidates(r.state, frame.Path, node) {
				if (op.Kind == "fireBranch" || op.Kind == "fireFilter") && eligible(op) {
					return true
				}
			}
		}
	}
	return false
}

// A model commit is not evidence that worker capacity recovered. Keep the
// existing assessment through maintenance; once deadlines are serviced, check
// whether there is still runnable callback work waiting on the same slots.
func (r *workflowRuntime) publishProgress() {
	if terminal(r.state.Status) {
		r.stall = nil
		r.publish(true, r.terminalError())
		return
	}
	if r.ctx.Err() != nil {
		// An in-flight callback/commit may finish as cancellation arrives. Do
		// not settle a transient failure before the driver records cancellation.
		r.stall = nil
		r.publish(false, nil)
		return
	}
	if r.stall != nil {
		if r.slot() || r.hasActiveJobs() {
			r.stall = nil
		} else {
			now := r.now()
			// A claim may be temporarily rejected with MAINTENANCE_REQUIRED;
			// that is not a release of the physical worker slots.
			if !schedulerDue(schedulerEarliest(r.timers()), now) && !r.slotDemand(now) {
				r.stall = nil
			}
		}
	}
	if r.stall != nil {
		r.publish(true, r.stall)
	} else if r.state.Status == "blocked" && !r.hasTimedWork() && !r.hasActiveJobs() && !r.state.HasWork() {
		r.publish(true, r.blockedError())
	} else {
		r.publish(false, nil)
	}
}
