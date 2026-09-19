package suimon

import "slices"

func (s State) plainChannelReady(c Channel) bool {
	p := c.Pending()
	i := s.NodeInstance(c.Path, c.Edge.Src.Node)
	return c.Kind == "plain" && c.Closed() && len(p) > 0 && !p[0].EOS && (c.Entry || (i != nil && i.Status == "succeeded"))
}
func (s State) preconditions(o Op) bool {
	switch o.Kind {
	case "activate", "fireWaitAll", "fireBranch":
		return all(s.Incoming(o.Path, o.Node), s.plainChannelReady)
	case "spawn":
		cs := s.Incoming(o.Path, o.Node)
		if len(cs) == 0 {
			return false
		}
		ts := cs[0].Pending()
		return len(ts) > 0 && ts[0] == (Token{Item: o.Item})
	case "fireCoalesce":
		c := find(s.Incoming(o.Path, o.Node), func(c Channel) bool { return c.ID == o.Edge })
		return c != nil && s.plainChannelReady(*c) && c.Pending()[0] == (Token{Item: o.Item})
	}
	return true
}
func (s *State) transition(o Op) *Reject {
	switch o.Kind {
	case "start":
		if s.Started || len(s.Instances) > 0 {
			return reject("ALREADY_STARTED")
		}
		f := s.Frame(nil)
		if f == nil {
			return reject("NO_ROOT", "missing root graph")
		}
		if !unique(mapped(o.Inputs, func(i Input) PortRef { return i.Entry })) || len(o.Inputs) != len(f.Graph.Entries) || !all(o.Inputs, func(i Input) bool { return contains(f.Graph.Entries, i.Entry) }) {
			return reject("ENTRY_MISMATCH")
		}
		for _, in := range o.Inputs {
			cs := filter(s.Channels, func(c Channel) bool { return len(c.Path) == 0 && c.Entry && c.Edge.Dst == in.Entry })
			if !unique(in.Items) || !all(cs, func(c Channel) bool { return c.Kind != "plain" || len(in.Items) == 1 }) {
				return reject("INVALID_INPUT")
			}
			ids := mapped(cs, func(c Channel) string { return c.ID })
			for _, item := range in.Items {
				if r := s.place(ids, Token{Item: item}); r != nil {
					return r
				}
			}
			if r := s.place(ids, Token{EOS: true}); r != nil {
				return r
			}
		}
		s.Started = true
	case "activate":
		if !s.Started {
			return reject("NOT_STARTED")
		}
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		inputs, r := s.plainInputs(o.Path, n)
		if r != nil {
			return r
		}
		switch n.Kind.Type {
		case "leaf":
			i := makeInstance(o.Path, n, "ready", inputs, nil)
			if r := s.freshInstance(i); r != nil {
				return r
			}
			return s.consumeInputs(o.Path, o.Node, i.ID)
		case "subworkflow", "loop":
			i := makeInstance(o.Path, n, "waitingInputs", inputs, nil)
			if n.Kind.Type == "loop" {
				i.Iteration = N(1)
			}
			if r := s.freshInstance(i); r != nil {
				return r
			}
			if r := s.consumeInputs(o.Path, o.Node, i.ID); r != nil {
				return r
			}
			return s.addFrame(i, *n.Kind.Body, mapped(inputs, func(p [2]string) string { return p[1] }))
		default:
			return reject("NOT_ACTIVATABLE", o.Node)
		}
	case "spawn":
		if !s.Started {
			return reject("NOT_STARTED")
		}
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "forEach" {
			return reject("NOT_FOREACH", o.Node)
		}
		cs := s.Incoming(o.Path, o.Node)
		if len(cs) == 0 {
			return reject("MISSING_INPUT", o.Node)
		}
		i := makeInstance(o.Path, n, "waitingInputs", List[[2]string]{{"item", o.Item}}, ptr(o.Item))
		if r := s.freshInstance(i); r != nil {
			return r
		}
		if r := s.consume(cs[0].ID, i.ID, &o.Item); r != nil {
			return r
		}
		return s.addFrame(i, *n.Kind.Body, []string{o.Item})
	case "claim":
		a := o.Auth
		i, r := s.getInstance(a.Instance)
		if r != nil {
			return r
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		policy, concurrency, r := leafPolicy(n)
		if r != nil {
			return r
		}
		if a.Now.Cmp(s.Now) < 0 {
			return reject("CLOCK_REGRESSION")
		}
		if i.Status != "ready" || i.Lease != nil || i.RetryAt != nil {
			return reject("NOT_READY")
		}
		if i.AttemptCount.Cmp(policy.MaxAttempts.Add(i.ExtraAttempts)) >= 0 {
			return reject("ATTEMPTS_EXHAUSTED")
		}
		if a.Attempt == "" || a.Token == "" || o.Worker == "" || anyOf(s.Attempts, func(x Attempt) bool { return x.ID == a.Attempt || x.Token == a.Token }) {
			return reject("DUPLICATE_ATTEMPT_OR_TOKEN")
		}
		if anyOf(s.Instances, func(j Instance) bool {
			return j.Status == "running" && j.Lease != nil && j.Lease.Until.Cmp(a.Now) <= 0 || j.Status == "retryWait" && j.RetryAt != nil && j.RetryAt.Cmp(a.Now) <= 0
		}) {
			return reject("MAINTENANCE_REQUIRED")
		}
		definition := func(path Path) *List[string] {
			f := s.Frame(path)
			if f == nil {
				return nil
			}
			return &f.Definition
		}
		d := definition(i.Path)
		active := filter(s.Instances, func(j Instance) bool {
			return j.Node == i.Node && equal(definition(j.Path), d) && j.Status == "running"
		})
		if natLen(active).Cmp(concurrency) >= 0 {
			return reject("CONCURRENCY_LIMIT")
		}
		i.Lease = &Lease{a.Attempt, a.Token, a.Now.Add(policy.LeaseSeconds)}
		i.Status = "running"
		i.AttemptCount = i.AttemptCount.Inc()
		s.setInstance(i)
		s.Attempts = append(s.Attempts, Attempt{a.Attempt, i.ID, i.AttemptCount, "running", a.Token, o.Worker})
		s.Now = a.Now
	case "renew":
		i, r := s.getInstance(o.Auth.Instance)
		if r != nil {
			return r
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		p, _, r := leafPolicy(n)
		if r != nil {
			return r
		}
		if i.Lease != nil {
			l := *i.Lease
			l.Until = o.Auth.Now.Add(p.LeaseSeconds)
			i.Lease = &l
		}
		s.setInstance(i)
		s.Now = o.Auth.Now
	case "expireLease":
		i, r := s.getInstance(o.Inst)
		if r != nil {
			return r
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		if o.Now.Cmp(s.Now) < 0 || i.Status != "running" || i.Lease == nil || i.Lease.Until.Cmp(o.Now) > 0 {
			return reject("LEASE_NOT_EXPIRED")
		}
		return s.expireOrFail(i, n, o.Now, "abandoned", true, "LEASE_EXPIRED")
	case "promoteRetry":
		i, r := s.getInstance(o.Inst)
		if r != nil {
			return r
		}
		if o.Now.Cmp(s.Now) < 0 || i.Status != "retryWait" || i.RetryAt == nil || i.RetryAt.Cmp(o.Now) > 0 {
			return reject("RETRY_NOT_DUE")
		}
		i.Status = "ready"
		i.RetryAt = nil
		s.setInstance(i)
		s.Now = o.Now
	case "emit":
		i, r := s.getInstance(o.Auth.Instance)
		if r != nil {
			return r
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		if _, _, r := leafPolicy(n); r != nil {
			return r
		}
		if !anyOf(n.Outputs, func(p Port) bool { return p.Name == o.Port && p.Kind == "stream" }) {
			return reject("NOT_STREAM_OUTPUT")
		}
		if r := s.putOutput(i.Path, i.Node, o.Port, Token{Item: o.Item}); r != nil {
			return r
		}
		s.Now = o.Auth.Now
	case "complete":
		i, r := s.getInstance(o.Auth.Instance)
		if r != nil {
			return r
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		if _, _, r := leafPolicy(n); r != nil {
			return r
		}
		ps := filter(n.Outputs, func(p Port) bool { return p.Kind == "plain" })
		if !unique(mapped(o.Outputs, func(out Output) string { return out.Port })) || len(o.Outputs) != len(ps) || !all(o.Outputs, func(out Output) bool {
			return len(out.Items) == 1 && anyOf(ps, func(p Port) bool { return p.Name == out.Port })
		}) {
			return reject("OUTPUT_MISMATCH")
		}
		if r := s.decision(Identity([]string{"leaf", i.ID}), compact(o.Outputs)); r != nil {
			return r
		}
		for _, out := range o.Outputs {
			for _, item := range out.Items {
				if r := s.putOutput(i.Path, i.Node, out.Port, Token{Item: item}); r != nil {
					return r
				}
			}
		}
		if r := s.closeOutputs(i.Path, n); r != nil {
			return r
		}
		s.setAttempt(o.Auth.Attempt, "succeeded")
		i.Status = "succeeded"
		i.Lease = nil
		s.setInstance(i)
		s.Now = o.Auth.Now
		s.Receipts = append(s.Receipts, Receipt{o.Auth.Instance, o.Auth.Attempt, o.Auth.Token, cloneOutputs(o.Outputs)})
	case "fail":
		i, r := s.getInstance(o.Auth.Instance)
		if r != nil {
			return r
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		return s.expireOrFail(i, n, o.Auth.Now, "failed", o.Retryable, o.Code)
	case "fireWaitAll":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "waitAll" {
			return reject("NOT_WAIT_ALL", o.Node)
		}
		inputs, r := s.plainInputs(o.Path, n)
		if r != nil {
			return r
		}
		item := DerivedItem("record", o.Path, o.Node, mapped(inputs, func(p [2]string) string { return Identity(p[:]) }))
		return s.finishControl(o.Path, n, inputs, &item, nil)
	case "fireBranch":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "branch" {
			return reject("NOT_BRANCH", o.Node)
		}
		if !contains(n.Kind.Arms, o.Arm) {
			return reject("UNKNOWN_ARM")
		}
		inputs, r := s.plainInputs(o.Path, n)
		if r != nil {
			return r
		}
		if len(inputs) == 0 {
			return reject("MISSING_INPUT", o.Node)
		}
		item := inputs[0][1]
		if r := s.decision(Identity([]string{"branch", InstanceID(o.Path, o.Node, nil), item}), o.Arm); r != nil {
			return r
		}
		return s.finishControl(o.Path, n, inputs, &item, &o.Arm)
	case "fireCollect":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "collect" {
			return reject("NOT_COLLECT", o.Node)
		}
		cs := s.Incoming(o.Path, o.Node)
		if len(cs) == 0 {
			return reject("MISSING_INPUT", o.Node)
		}
		c := cs[0]
		if !c.Closed() || !c.Consumed.IsZero() {
			return reject("COLLECT_NOT_READY")
		}
		items := c.Items()
		slices.Sort(items)
		result := DerivedItem("list", o.Path, o.Node, items)
		return s.finishControl(o.Path, n, mapped(items, func(item string) [2]string { return [2]string{"item", item} }), &result, nil)
	case "fireCoalesce":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "coalesce" {
			return reject("NOT_COALESCE", o.Node)
		}
		c := find(s.Incoming(o.Path, o.Node), func(c Channel) bool { return c.ID == o.Edge })
		if c == nil {
			return reject("WRONG_INPUT_EDGE", o.Edge)
		}
		i := makeInstance(o.Path, n, "succeeded", List[[2]string]{{c.Edge.Dst.Port, o.Item}}, nil)
		if r := s.freshInstance(i); r != nil {
			return r
		}
		if r := s.consume(c.ID, i.ID, &o.Item); r != nil {
			return r
		}
		if len(n.Outputs) == 0 {
			return reject("MISSING_OUTPUT", o.Node)
		}
		if r := s.putOutput(o.Path, o.Node, n.Outputs[0].Name, Token{Item: o.Item}); r != nil {
			return r
		}
		return s.closeOutputs(o.Path, n)
	case "fireFilter":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "filter" {
			return reject("NOT_FILTER", o.Node)
		}
		cs := s.Incoming(o.Path, o.Node)
		if len(cs) == 0 {
			return reject("MISSING_INPUT", o.Node)
		}
		who := InstanceID(o.Path, o.Node, nil)
		if r := s.streamController(o.Path, n); r != nil {
			return r
		}
		if r := s.decision(Identity([]string{"filter", who, o.Item}), compact(o.Keep)); r != nil {
			return r
		}
		if r := s.consume(cs[0].ID, who, &o.Item); r != nil {
			return r
		}
		if o.Keep {
			if len(n.Outputs) == 0 {
				return reject("MISSING_OUTPUT", o.Node)
			}
			return s.putOutput(o.Path, o.Node, n.Outputs[0].Name, Token{Item: o.Item})
		}
	case "fireMerge":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "merge" {
			return reject("NOT_MERGE", o.Node)
		}
		if !anyOf(s.Incoming(o.Path, o.Node), func(c Channel) bool { return c.ID == o.Edge }) {
			return reject("WRONG_INPUT_EDGE")
		}
		if r := s.streamController(o.Path, n); r != nil {
			return r
		}
		if r := s.consume(o.Edge, InstanceID(o.Path, o.Node, nil), &o.Item); r != nil {
			return r
		}
		if len(n.Outputs) == 0 {
			return reject("MISSING_OUTPUT", o.Node)
		}
		return s.putOutput(o.Path, o.Node, n.Outputs[0].Name, Token{Item: DerivedItem("merge", o.Path, o.Node, []string{o.Edge, o.Item})})
	case "propagateEos":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "filter" && n.Kind.Type != "merge" && n.Kind.Type != "forEach" {
			return reject("NOT_STREAM_CONTROL")
		}
		cs := s.Incoming(o.Path, o.Node)
		if !all(cs, func(c Channel) bool { return c.Closed() && len(c.PendingItems()) == 0 }) {
			return reject("INPUT_NOT_DRAINED")
		}
		if !all(filter(s.Instances, func(i Instance) bool { return slices.Equal(i.Path, o.Path) && i.Node == o.Node && i.Trigger != nil }), func(i Instance) bool { return i.Status == "succeeded" }) {
			return reject("CHILDREN_NOT_FINISHED")
		}
		i := makeInstance(o.Path, n, "succeeded", nil, nil)
		old := s.NodeInstance(o.Path, o.Node)
		if old == nil {
			if r := s.freshInstance(i); r != nil {
				return r
			}
		} else {
			if old.Status != "waitingInputs" {
				return reject("CONTROL_FINISHED")
			}
			old.Status = "succeeded"
			s.setInstance(*old)
		}
		if r := s.consumeChannels(cs, i.ID); r != nil {
			return r
		}
		return s.closeOutputs(o.Path, n)
	case "finishSubworkflow":
		i, r := s.getInstance(o.Inst)
		if r != nil {
			return r
		}
		if i.Status != "waitingInputs" {
			return reject("NOT_WAITING_BODY")
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "subworkflow" && n.Kind.Type != "forEach" {
			return reject("NOT_SUBWORKFLOW")
		}
		f, r := s.CurrentFrame(i)
		if r != nil {
			return r
		}
		items, r := s.bodyResults(f)
		if r != nil {
			return r
		}
		if len(n.Outputs) != len(items) {
			return reject("BODY_OUTPUT_ARITY")
		}
		if r := s.closeFrame(f, i.ID); r != nil {
			return r
		}
		for j, p := range n.Outputs {
			if r := s.putOutput(i.Path, n.ID, p.Name, Token{Item: items[j]}); r != nil {
				return r
			}
		}
		i.Status = "succeeded"
		s.setInstance(i)
		if n.Kind.Type == "subworkflow" {
			return s.closeOutputs(i.Path, n)
		}
	case "loopIterate":
		i, r := s.getInstance(o.Inst)
		if r != nil {
			return r
		}
		if i.Status != "waitingInputs" {
			return reject("NOT_WAITING_BODY")
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		if n.Kind.Type != "loop" {
			return reject("NOT_LOOP", o.Inst)
		}
		f, r := s.CurrentFrame(i)
		if r != nil {
			return r
		}
		items, r := s.bodyResults(f)
		if r != nil {
			return r
		}
		if len(items) == 0 {
			return reject("MISSING_BODY_RESULT", o.Inst)
		}
		item := items[0]
		if r := s.decision(Identity([]string{"loop", o.Inst, i.Iteration.String(), item}), compact(o.Done)); r != nil {
			return r
		}
		if r := s.closeFrame(f, i.ID); r != nil {
			return r
		}
		if o.Done {
			if len(n.Outputs) == 0 {
				return reject("MISSING_OUTPUT", o.Inst)
			}
			if r := s.putOutput(i.Path, n.ID, n.Outputs[0].Name, Token{Item: item}); r != nil {
				return r
			}
			if r := s.closeOutputs(i.Path, n); r != nil {
				return r
			}
			i.Status = "succeeded"
			s.setInstance(i)
		} else if i.Iteration.Cmp(n.Kind.MaxIterations.Add(i.ExtraIterations)) >= 0 {
			i.Status = "failed"
			s.setInstance(i)
			s.Status = "blocked"
			s.Reason = ptr("LOOP_LIMIT")
		} else {
			i.Iteration = i.Iteration.Inc()
			s.setInstance(i)
			return s.addFrame(i, *n.Kind.Body, []string{item})
		}
	case "skip":
		n, r := s.getNode(o.Path, o.Node)
		if r != nil {
			return r
		}
		inputs := s.Incoming(o.Path, o.Node)
		empty := func(c Channel) bool { return c.Closed() && len(c.Items()) == 0 }
		absent := anyOf(inputs, empty)
		if n.Kind.Type == "coalesce" {
			absent = len(inputs) > 0 && all(inputs, empty)
		}
		if !allKind(n.Inputs, "plain") || !absent {
			return reject("NOT_SKIPPABLE")
		}
		if !all(inputs, func(c Channel) bool { return c.Closed() }) {
			return reject("INPUT_NOT_FINISHED")
		}
		if anyOf(s.Instances, func(i Instance) bool { return slices.Equal(i.Path, o.Path) && i.Node == o.Node }) {
			return reject("NODE_ALREADY_STARTED")
		}
		i := makeInstance(o.Path, n, "cancelled", nil, nil)
		if r := s.freshInstance(i); r != nil {
			return r
		}
		if r := s.consumeInputs(o.Path, o.Node, i.ID); r != nil {
			return r
		}
		return s.closeOutputs(o.Path, n)
	case "idle":
		return nil
	case "cancel":
		s.Status = "cancelled"
		for j := range s.Instances {
			i := &s.Instances[j]
			if !terminal(i.Status) {
				i.Status = "cancelled"
				i.Lease = nil
				i.RetryAt = nil
			}
		}
		for j := range s.Attempts {
			if s.Attempts[j].Status == "running" {
				s.Attempts[j].Status = "cancelled"
			}
		}
		s.Reason = ptr("CANCELLED")
	case "manualRetry":
		i, r := s.getInstance(o.Inst)
		if r != nil {
			return r
		}
		n, r := s.getNode(i.Path, i.Node)
		if r != nil {
			return r
		}
		if i.Status != "failed" {
			return reject("NOT_FAILED")
		}
		switch n.Kind.Type {
		case "leaf":
			i.Status = "retryWait"
			i.ExtraAttempts = i.ExtraAttempts.Inc()
			i.RetryAt = ptr(s.Now)
			s.setInstance(i)
			s.Status = "running"
			s.Reason = nil
		case "loop":
			f, r := s.CurrentFrame(i)
			if r != nil {
				return r
			}
			if !f.Closed {
				return reject("BODY_NOT_FINISHED")
			}
			items, r := s.frameOutputItems(f)
			if r != nil {
				return r
			}
			i.Status = "waitingInputs"
			i.ExtraIterations = i.ExtraIterations.Inc()
			i.Iteration = i.Iteration.Inc()
			s.setInstance(i)
			if r := s.addFrame(i, *n.Kind.Body, items); r != nil {
				return r
			}
			s.Status = "running"
			s.Reason = nil
		default:
			return reject("NOT_RETRYABLE_NODE", i.Node)
		}
	default:
		return reject("UNKNOWN_OPERATION", o.Kind)
	}
	return nil
}
func cloneOutputs(xs List[Output]) List[Output] {
	return mapped(xs, func(o Output) Output { o.Items = slices.Clone(o.Items); return o })
}
func (o Op) countsAsWork() bool {
	return o.Kind != "idle" && o.Kind != "cancel" && o.Kind != "manualRetry"
}
func (s State) authorized(o Op) bool {
	switch o.Kind {
	case "emit", "complete", "fail", "renew":
		return s.validLease(o.Auth)
	}
	return true
}
func (s State) duplicateComplete(o Op) bool {
	return o.Kind == "complete" && anyOf(s.Receipts, func(r Receipt) bool {
		return r.Instance == o.Auth.Instance && r.Attempt == o.Auth.Attempt && r.Token == o.Auth.Token && equal(r.Outputs, o.Outputs)
	})
}

// Step applies one operation atomically. Neither accepted nor rejected
// operations mutate their input state. A rejection returns the original state.
func Step(s State, o Op) (State, *Reject) { return step(s, o, true) }
func step(s State, o Op, idle bool) (State, *Reject) {
	if s.duplicateComplete(o) || terminal(s.Status) && s.authorized(o) {
		return s, nil
	}
	if !s.authorized(o) {
		return s, reject("INVALID_LEASE", "stale, mismatched or expired lease")
	}
	if !s.Started && o.Kind != "start" && o.Kind != "cancel" {
		return s, reject("NOT_STARTED")
	}
	if !s.preconditions(o) {
		return s, reject("PRECONDITION")
	}
	next := cloneState(s)
	if idle && o.Kind == "idle" {
		if !s.HasWork() {
			f := s.Frame(nil)
			success := s.Started && f != nil && s.FrameDone(*f)
			if success {
				next.Status = "succeeded"
				next.Reason = nil
			} else {
				next.Status = "blocked"
				if s.Status != "blocked" || s.Reason == nil {
					next.Reason = ptr("DEPENDENCIES_UNRESOLVED")
				}
			}
		}
	} else if r := next.transition(o); r != nil {
		return s, r
	}
	if !Invariants(next) || !historyOK(s, next) {
		return s, reject("INVARIANT", "invalid transaction boundary")
	}
	return next, nil
}
func (s State) HasWork() bool {
	for _, o := range Candidates(DefaultConfig(), s) {
		if o.countsAsWork() {
			next, r := step(s, o, false)
			if r == nil && !equal(next, s) {
				return true
			}
		}
	}
	return false
}

// Transaction replays commands without exposing a partial result on failure.
func Transaction(s State, ops []Op) (State, *Reject) {
	next := s
	for _, o := range ops {
		var r *Reject
		next, r = Step(next, o)
		if r != nil {
			return s, r
		}
	}
	return next, nil
}
