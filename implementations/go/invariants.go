package suimon

func channelOK(c Channel) bool {
	if c.Consumed.Cmp(natLen(c.Placed)) > 0 {
		return false
	}
	before := 0
	for _, t := range c.Placed {
		if t.EOS {
			break
		}
		before++
	}
	if c.Closed() {
		before++
	}
	return before == len(c.Placed) && unique(c.Items()) && (c.Kind != "plain" || len(c.Items()) <= 1)
}

// Invariants mirrors the commit checks in Suimon/Invariants.lean.
func Invariants(s State) bool {
	if !all(s.Channels, channelOK) || !unique(mapped(s.Channels, func(c Channel) string { return c.ID })) || !unique(mapped(s.Instances, func(i Instance) string { return i.ID })) || !unique(mapped(s.Instances, instanceKey)) {
		return false
	}
	for _, i := range s.Instances {
		if i.Status == "running" {
			if i.Lease == nil || !anyOf(s.Attempts, func(a Attempt) bool {
				return a.ID == i.Lease.Attempt && a.Instance == i.ID && a.Token == i.Lease.Token && a.Status == "running"
			}) {
				return false
			}
		} else if i.Lease != nil {
			return false
		}
	}
	if !unique(mapped(s.Attempts, func(a Attempt) string { return a.ID })) || !unique(mapped(s.Attempts, func(a Attempt) string { return a.Token })) {
		return false
	}
	for _, a := range s.Attempts {
		i := s.Instance(a.Instance)
		if i == nil {
			return false
		}
		if a.Status == "running" && (i.Status != "running" || i.Lease == nil || i.Lease.Attempt != a.ID) {
			return false
		}
	}
	for _, i := range s.Instances {
		if len(filter(s.Attempts, func(a Attempt) bool { return a.Instance == i.ID && a.Status == "running" })) > 1 {
			return false
		}
	}
	if !unique(mapped(s.Consumed, func(c Consumption) string { return compact([]any{c.Channel, c.Index}) })) {
		return false
	}
	for _, c := range s.Channels {
		for idx, t := range c.Placed[:c.Consumed.index(len(c.Placed))] {
			if !t.EOS && !anyOf(s.Consumed, func(a Consumption) bool { return a.Channel == c.ID && a.Index == N(uint64(idx)) && a.Item == t.Item }) {
				return false
			}
		}
	}
	for _, a := range s.Consumed {
		if s.Instance(a.ByInstance) == nil || !anyOf(s.Channels, func(c Channel) bool {
			idx := a.Index.index(len(c.Placed))
			return c.ID == a.Channel && a.Index.Cmp(c.Consumed) < 0 && idx < len(c.Placed) && c.Placed[idx] == (Token{Item: a.Item})
		}) {
			return false
		}
	}
	for _, i := range s.Instances {
		n := s.Node(i.Path, i.Node)
		if n == nil {
			return false
		}
		if n.Kind.Type == "loop" {
			frames := filter(s.Frames, func(f Frame) bool { return f.Owner != nil && *f.Owner == i.ID })
			if i.Iteration.Cmp(n.Kind.MaxIterations.Add(i.ExtraIterations)) > 0 || natLen(frames) != i.Iteration {
				return false
			}
		}
	}
	return true
}
func allowedStatus(a, b string) bool {
	if a == b {
		return true
	}
	switch a {
	case "waitingInputs":
		return b == "succeeded" || b == "failed" || b == "cancelled"
	case "ready":
		return b == "running" || b == "cancelled"
	case "running":
		return b == "succeeded" || b == "failed" || b == "retryWait" || b == "cancelled"
	case "retryWait":
		return b == "ready" || b == "cancelled"
	case "failed":
		return b == "retryWait" || b == "waitingInputs" || b == "cancelled"
	}
	return false
}
func historyOK(a, b State) bool {
	if a.Now.Cmp(b.Now) > 0 {
		return false
	}
	for _, i := range a.Instances {
		j := b.Instance(i.ID)
		if j == nil || instanceKey(i) != instanceKey(*j) || !allowedStatus(i.Status, j.Status) || i.AttemptCount.Cmp(j.AttemptCount) > 0 {
			return false
		}
	}
	for _, c := range a.Channels {
		d := find(b.Channels, func(d Channel) bool { return c.ID == d.ID })
		if d == nil || c.Consumed.Cmp(d.Consumed) > 0 || len(c.Placed) > len(d.Placed) {
			return false
		}
		for j, t := range c.Placed {
			if t != d.Placed[j] {
				return false
			}
		}
	}
	return true
}
