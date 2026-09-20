package suimon

import (
	"math/big"
	"time"
)

func (r *workflowRuntime) probe(op Op) (State, *Reject) {
	r.execution.metrics.candidates.Add(1)
	return Step(r.state, op)
}

func (r *workflowRuntime) renewAt(i Instance) *Nat {
	if i.Lease == nil || r.options.DisableAutoRenew {
		return nil
	}
	job := r.jobs[i.Lease.Attempt]
	if job == nil || job.obsolete {
		return nil
	}
	lease := r.state.Node(i.Path, i.Node).Kind.Retry.LeaseSeconds
	half := maxNat(N(1), fromBig(new(big.Int).Div(lease.big(), big.NewInt(2))))
	// Natural seconds must both precede expiry and strictly extend the lease.
	at := maxNat(i.Lease.Until.Sub(half), i.Lease.Until.Sub(lease).Inc())
	if at.Cmp(i.Lease.Until) >= 0 {
		return nil
	}
	return &at
}

// Compute the next logical deadline once on entering a wait. Ticks compare
// only Now with this value; a custom clock is never converted to wall time.
func (r *workflowRuntime) nextDeadline() *Nat {
	var next *Nat
	add := func(at Nat) {
		if next == nil || at.Cmp(*next) < 0 {
			next = &at
		}
	}
	for _, i := range r.state.Instances {
		if i.Status == "running" && i.Lease != nil {
			add(i.Lease.Until)
			if at := r.renewAt(i); at != nil {
				add(*at)
			}
		}
		if i.Status == "retryWait" && i.RetryAt != nil {
			add(*i.RetryAt)
		}
	}
	if r.stall == nil && r.needsSlot && !r.slot() && !r.hasActiveJobs() {
		last := Nat{}
		for _, job := range r.jobs {
			if job.staleAt != nil {
				last = maxNat(last, job.staleAt.Add(r.options.StaleGraceSeconds))
			}
		}
		add(last)
	}
	return next
}

func (r *workflowRuntime) wait(ticks <-chan time.Time) error {
	deadline := r.nextDeadline()
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
			if deadline != nil && r.now().Cmp(*deadline) >= 0 {
				return nil
			}
		}
	}
}
