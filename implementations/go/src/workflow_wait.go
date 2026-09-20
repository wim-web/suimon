package suimon

import "time"

func (r *workflowRuntime) probe(op Op) (State, *Reject) {
	r.execution.metrics.candidates.Add(1)
	return Step(r.state, op)
}

func (r *workflowRuntime) timers() List[schedulerTimer] {
	owned := []string{}
	for _, job := range r.jobs {
		if job.kind == "leaf" && !job.obsolete {
			owned = append(owned, job.auth.Attempt)
		}
	}
	return schedulerTimers(r.state, owned, !r.options.DisableAutoRenew)
}

func (r *workflowRuntime) staleDeadline() *Nat {
	if r.needsSlot && !r.slot() && !r.hasActiveJobs() {
		last := Nat{}
		for _, job := range r.jobs {
			if job.staleAt == nil {
				return nil
			}
			last = maxNat(last, job.staleAt.Add(r.options.StaleGraceSeconds))
		}
		return &last
	}
	return nil
}

// Cache all state deadlines even when a stall is already announced.
func (r *workflowRuntime) nextDeadline() *Nat {
	return schedulerWaitDeadline(r.timers(), r.staleDeadline(), r.stall != nil)
}

func (r *workflowRuntime) wait(ticks <-chan time.Time) error {
	deadline := r.nextDeadline()
	if schedulerWake(deadline, r.now(), false) {
		return nil
	}
	if !schedulerPollEnabled(deadline) {
		ticks = nil
	}
	r.execution.metrics.waits.Add(1)
	for {
		select {
		case <-r.ctx.Done():
			return nil
		case <-r.execution.stop:
			return nil
		case m := <-r.execution.requests:
			// In particular, a stale job's return releases physical worker capacity.
			return r.handle(m)
		case <-ticks:
			r.execution.metrics.polls.Add(1)
			if schedulerWake(deadline, r.now(), false) {
				return nil
			}
		}
	}
}
