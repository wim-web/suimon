package suimon

import "math/big"

// Executable scheduling policy from Suimon/Scheduler.lean. Worker capacity and
// an announced stall never remove expiry/retry timers from this policy.
type schedulerTimer struct {
	At       Nat    `json:"deadline"`
	Kind     string `json:"kind"`
	Instance string `json:"target"`
	Attempt  string `json:"attempt"`
	Token    string `json:"token"`
}

func (t schedulerTimer) operation(now Nat) Op {
	if t.Kind == "renew" {
		return Op{Kind: "renew", Auth: Credentials{t.Instance, t.Attempt, t.Token, now}}
	}
	return Op{Kind: t.Kind, Inst: t.Instance, Now: now}
}

func schedulerRenewalAt(until, duration Nat) *Nat {
	half := maxNat(N(1), fromBig(new(big.Int).Div(duration.big(), big.NewInt(2))))
	at := maxNat(until.Sub(half), until.Sub(duration).Inc())
	if at.Cmp(until) >= 0 {
		return nil
	}
	return &at
}

func schedulerTimers(s State, owned []string, autoRenew bool) List[schedulerTimer] {
	mandatory, renewals := List[schedulerTimer]{}, List[schedulerTimer]{}
	for _, i := range s.Instances {
		if i.Status == "running" && i.Lease != nil {
			l := i.Lease
			mandatory = append(mandatory, schedulerTimer{At: l.Until, Kind: "expireLease", Instance: i.ID})
			if autoRenew && contains(owned, l.Attempt) {
				if n := s.Node(i.Path, i.Node); n != nil && n.Kind.Type == "leaf" {
					if at := schedulerRenewalAt(l.Until, n.Kind.Retry.LeaseSeconds); at != nil {
						renewals = append(renewals, schedulerTimer{*at, "renew", i.ID, l.Attempt, l.Token})
					}
				}
			}
		}
		if i.Status == "retryWait" && i.RetryAt != nil {
			mandatory = append(mandatory, schedulerTimer{At: *i.RetryAt, Kind: "promoteRetry", Instance: i.ID})
		}
	}
	return append(mandatory, renewals...)
}

func schedulerFirstDue(ts List[schedulerTimer], now Nat) *Op {
	for _, timer := range ts {
		if timer.At.Cmp(now) <= 0 {
			return ptr(timer.operation(now))
		}
	}
	return nil
}

func schedulerEarlier(a, b *Nat) *Nat {
	if a == nil || b != nil && b.Cmp(*a) < 0 {
		return b
	}
	return a
}

func schedulerEarliest(ts List[schedulerTimer]) *Nat {
	var earliest *Nat
	for _, timer := range ts {
		earliest = schedulerEarlier(earliest, ptr(timer.At))
	}
	return earliest
}

func schedulerDue(deadline *Nat, now Nat) bool {
	return deadline != nil && now.Cmp(*deadline) >= 0
}

func schedulerPollEnabled(deadline *Nat) bool { return deadline != nil }

func schedulerWaitDeadline(ts List[schedulerTimer], stale *Nat, announced bool) *Nat {
	if announced {
		stale = nil
	}
	return schedulerEarlier(schedulerEarliest(ts), stale)
}

func schedulerAnnounceStall(ts List[schedulerTimer], stale *Nat, announced bool, now Nat) bool {
	return !schedulerDue(schedulerEarliest(ts), now) && !announced && schedulerDue(stale, now)
}

func schedulerWake(deadline *Nat, now Nat, message bool) bool {
	return message || schedulerDue(deadline, now)
}
