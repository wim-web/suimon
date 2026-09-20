package suimon

import (
	"encoding/json"
	"os"
	"testing"
)

func TestSchedulerAgainstLean(t *testing.T) {
	if os.Getenv("SUIMON_LEAN_ORACLE") == "" {
		t.Skip("run bin/test-go for the Lean scheduler comparison")
	}
	o := newOracle(t)
	w := independentLeaves(t)
	s := Initial(w.Graph)
	s.Started, s.Now = true, N(1000)
	x := Instance{ID: "ix", Node: "x", Status: "running", Lease: &Lease{"ax", "lx", N(1003)}}
	y := Instance{ID: "iy", Node: "y", Status: "retryWait", RetryAt: ptr(N(1004))}
	s.Instances = List[Instance]{x, y}
	states := []State{s}
	other := copyPublicState(s)
	other.Instances[0].Lease.Until = N(1013)
	other.Instances[1].Status, other.Instances[1].RetryAt = "running", nil
	other.Instances[1].Lease = &Lease{"ay", "ly", N(1003)}
	states = append(states, other)
	nested := copyPublicState(s)
	nested.Frames[0].Path = Path{"nested"}
	for n := range nested.Instances {
		nested.Instances[n].Path = Path{"nested"}
	}
	nested.Frames[0].Graph.Nodes[0].Kind.Retry.LeaseSeconds = N(1)
	states = append(states, nested)
	missing := copyPublicState(s)
	missing.Instances[0].Lease, missing.Instances[1].RetryAt = nil, nil
	states = append(states, missing)
	large := copyPublicState(s)
	huge, _ := ParseNat("184467440737095516160000000000000000000")
	large.Instances[0].Lease.Until = huge
	large.Instances[1].RetryAt = ptr(huge.Inc())
	large.Frames[0].Graph.Nodes[0].Kind.Retry.LeaseSeconds = huge.Sub(N(7))
	states = append(states, large)
	compared := 0
	for _, state := range states {
		for _, now := range []Nat{N(0), N(1000), N(1001), N(1002), N(1003), N(1004), N(1010), N(1020), huge, huge.Inc()} {
			for _, owned := range []List[string]{nil, {"ax"}, {"ay", "ax"}} {
				for _, auto := range []bool{false, true} {
					for _, announced := range []bool{false, true} {
						for _, stale := range []*Nat{nil, ptr(N(0)), ptr(N(1005))} {
							for _, message := range []bool{false, true} {
								ts := schedulerTimers(state, owned, auto)
								deadline := schedulerWaitDeadline(ts, stale, announced)
								got := map[string]any{"timers": ts, "maintenance": schedulerFirstDue(ts, now), "deadline": deadline,
									"enabled":  schedulerPollEnabled(deadline),
									"announce": schedulerAnnounceStall(ts, stale, announced, now), "wake": schedulerWake(deadline, now, message)}
								var want json.RawMessage
								o.ask(map[string]any{"action": "scheduler", "state": state, "owned": owned, "autoRenew": auto, "now": now, "stale": stale, "announced": announced, "message": message}, &want)
								assertJSON(t, "Lean scheduling policy", got, want)
								compared++
							}
						}
					}
				}
			}
		}
	}
	t.Logf("compared %d scheduler decisions with Lean", compared)
}

func TestWorkflowSchedulerPriority(t *testing.T) {
	w := independentLeaves(t)
	s := Initial(w.Graph)
	s.Instances = List[Instance]{
		{ID: "x", Node: "x", Status: "running", Lease: &Lease{"ax", "lx", N(1013)}},
		{ID: "y", Node: "y", Status: "running", Lease: &Lease{"ay", "ly", N(1003)}},
	}
	ts := schedulerTimers(s, []string{"ax"}, true)
	op := schedulerFirstDue(ts, N(1012))
	if op == nil || op.Kind != "expireLease" || op.Inst != "y" {
		t.Fatal("optional renewal took priority over overdue maintenance:", op)
	}
	for _, announced := range []bool{false, true} {
		deadline := schedulerWaitDeadline(ts, ptr(N(1001)), announced)
		if !schedulerWake(deadline, N(1012), false) || schedulerAnnounceStall(ts, ptr(N(1001)), announced, N(1012)) {
			t.Fatal("overdue maintenance was hidden by stall notification")
		}
	}
}
