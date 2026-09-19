package suimon

import (
	"slices"
	"strconv"
)

func Identity(parts []string) string { return compact(List[string](parts)) }
func InstanceID(path Path, node string, trigger *string) string {
	return compact([]any{path, []any{node, trigger}})
}
func DerivedItem(tag string, path Path, node string, items []string) string {
	return Identity(append([]string{tag, Identity(path), node}, items...))
}
func terminal(status string) bool {
	return status == "succeeded" || status == "failed" || status == "cancelled"
}
func (c Channel) Items() List[string] {
	out := List[string]{}
	for _, t := range c.Placed {
		if !t.EOS {
			out = append(out, t.Item)
		}
	}
	return out
}
func (c Channel) Closed() bool         { return anyOf(c.Placed, func(t Token) bool { return t.EOS }) }
func (c Channel) Pending() List[Token] { return c.Placed[c.Consumed.index(len(c.Placed)):] }
func (c Channel) PendingItems() List[string] {
	return mapped(filter(c.Pending(), func(t Token) bool { return !t.EOS }), func(t Token) string { return t.Item })
}
func (s State) Instance(id string) *Instance {
	return find(s.Instances, func(i Instance) bool { return i.ID == id })
}
func (s State) NodeInstance(path Path, node string) *Instance {
	return find(s.Instances, func(i Instance) bool { return slices.Equal(i.Path, path) && i.Node == node && i.Trigger == nil })
}
func (s State) Frame(path Path) *Frame {
	return find(s.Frames, func(f Frame) bool { return slices.Equal(f.Path, path) })
}
func (s State) Node(path Path, node string) *Node {
	f := s.Frame(path)
	if f == nil {
		return nil
	}
	return f.Graph.Node(node)
}
func (s State) Incoming(path Path, node string) List[Channel] {
	return filter(s.Channels, func(c Channel) bool { return slices.Equal(c.Path, path) && !c.Exit && c.Edge.Dst.Node == node })
}
func (s State) Outgoing(path Path, node, port string) List[Channel] {
	return filter(s.Channels, func(c Channel) bool {
		return slices.Equal(c.Path, path) && !c.Entry && c.Edge.Src == (PortRef{node, port})
	})
}
func (f Frame) channels() List[Channel] {
	cs := List[Channel]{}
	id := func(tag string, i int) string {
		return Identity(append(append([]string{}, f.Path...), tag, strconv.Itoa(i)))
	}
	for i, e := range f.Graph.Edges {
		kind := "plain"
		if p := f.Graph.output(e.Src); p != nil {
			kind = p.Kind
		}
		cs = append(cs, Channel{ID: id("edge", i), Edge: e, Path: f.Path, Kind: kind})
	}
	for i, r := range f.Graph.Entries {
		kind := "plain"
		if p := f.Graph.input(r); p != nil {
			kind = p.Kind
		}
		cs = append(cs, Channel{ID: id("entry", i), Edge: Edge{PortRef{"$input", strconv.Itoa(i)}, r}, Path: f.Path, Kind: kind, Entry: true})
	}
	for i, r := range f.Graph.Exits {
		kind := "plain"
		if p := f.Graph.output(r); p != nil {
			kind = p.Kind
		}
		cs = append(cs, Channel{ID: id("exit", i), Edge: Edge{r, PortRef{"$output", strconv.Itoa(i)}}, Path: f.Path, Kind: kind, Exit: true})
	}
	return cs
}

// Initial constructs the initial state. Validate the graph before executing it.
func Initial(g Graph) State {
	f := Frame{Graph: cloneGraph(g)}
	return State{Status: "running", Frames: List[Frame]{f}, Channels: f.channels()}
}
func cloneGraph(g Graph) Graph {
	g.Nodes = slices.Clone(g.Nodes)
	g.Edges = slices.Clone(g.Edges)
	g.Entries = slices.Clone(g.Entries)
	g.Exits = slices.Clone(g.Exits)
	for j := range g.Nodes {
		n := &g.Nodes[j]
		n.Inputs = slices.Clone(n.Inputs)
		n.Outputs = slices.Clone(n.Outputs)
		n.Kind.Arms = slices.Clone(n.Kind.Arms)
		if n.Kind.Body != nil {
			n.Kind.Body = ptr(cloneGraph(*n.Kind.Body))
		}
	}
	return g
}
func cloneState(s State) State {
	s.Channels = slices.Clone(s.Channels)
	for j := range s.Channels {
		s.Channels[j].Placed = slices.Clone(s.Channels[j].Placed)
	}
	s.Instances = slices.Clone(s.Instances)
	s.Attempts = slices.Clone(s.Attempts)
	s.Frames = slices.Clone(s.Frames)
	s.Consumed = slices.Clone(s.Consumed)
	s.Receipts = slices.Clone(s.Receipts)
	s.Decisions = slices.Clone(s.Decisions)
	return s
}
func (s *State) setInstance(i Instance) {
	for j := range s.Instances {
		if s.Instances[j].ID == i.ID {
			s.Instances[j] = i
		}
	}
}
func (s *State) setAttempt(id, status string) {
	for j := range s.Attempts {
		if s.Attempts[j].ID == id {
			s.Attempts[j].Status = status
		}
	}
}
func (s State) validLease(c Credentials) bool {
	i := s.Instance(c.Instance)
	return !terminal(s.Status) && c.Now.Cmp(s.Now) >= 0 && i != nil && i.Status == "running" && i.Lease != nil && i.Lease.Attempt == c.Attempt && i.Lease.Token == c.Token && c.Now.Cmp(i.Lease.Until) < 0
}
func (s State) getInstance(id string) (Instance, *Reject) {
	i := s.Instance(id)
	if i == nil {
		return Instance{}, reject("UNKNOWN_INSTANCE", id)
	}
	return *i, nil
}
func (s State) getNode(path Path, id string) (Node, *Reject) {
	f := s.Frame(path)
	if f == nil {
		return Node{}, reject("UNKNOWN_FRAME", Identity(path))
	}
	if f.Closed {
		return Node{}, reject("CLOSED_FRAME")
	}
	n := f.Graph.Node(id)
	if n == nil {
		return Node{}, reject("UNKNOWN_NODE", id)
	}
	return *n, nil
}
func (s *State) freshInstance(i Instance) *Reject {
	if anyOf(s.Instances, func(j Instance) bool { return j.ID == i.ID || instanceKey(j) == instanceKey(i) }) {
		return reject("DUPLICATE_INSTANCE")
	}
	s.Instances = append(s.Instances, i)
	return nil
}
func instanceKey(i Instance) string { return compact([]any{i.Node, i.Trigger, i.Path}) }
func makeInstance(path Path, n Node, status string, inputs List[[2]string], trigger *string) Instance {
	return Instance{ID: InstanceID(path, n.ID, trigger), Node: n.ID, Path: slices.Clone(path), Status: status, Inputs: slices.Clone(inputs), Trigger: trigger}
}
func (s *State) putOutput(path Path, node, port string, t Token) *Reject {
	ids := mapped(s.Outgoing(path, node, port), func(c Channel) string { return c.ID })
	return s.place(ids, t)
}
func (s *State) place(ids []string, t Token) *Reject {
	for j := range s.Channels {
		c := &s.Channels[j]
		if !contains(ids, c.ID) {
			continue
		}
		if c.Closed() {
			return reject("AFTER_EOS", c.ID)
		}
		if contains(c.Placed, t) {
			continue
		}
		if c.Kind == "plain" && !t.EOS && len(c.Items()) > 0 {
			return reject("PLAIN_CARDINALITY")
		}
		c.Placed = append(c.Placed, t)
	}
	return nil
}
func (s *State) closeOutputs(path Path, n Node) *Reject {
	for _, p := range n.Outputs {
		if r := s.putOutput(path, n.ID, p.Name, Token{EOS: true}); r != nil {
			return r
		}
	}
	return nil
}
func (s *State) consume(channel, who string, expected *string) *Reject {
	for j := range s.Channels {
		c := &s.Channels[j]
		if c.ID != channel {
			continue
		}
		pending := c.Pending()
		if len(pending) == 0 {
			return reject("NO_TOKEN", channel)
		}
		t := pending[0]
		if expected != nil {
			if t.EOS {
				return reject("EXPECTED_ITEM")
			}
			if t.Item != *expected {
				return reject("WRONG_ITEM")
			}
		}
		if !t.EOS {
			s.Consumed = append(s.Consumed, Consumption{channel, c.Consumed, t.Item, who})
		}
		c.Consumed = c.Consumed.Inc()
		return nil
	}
	return reject("UNKNOWN_CHANNEL", channel)
}
func (s *State) consumeChannels(cs []Channel, who string) *Reject {
	for _, c := range cs {
		for range c.Pending() {
			if r := s.consume(c.ID, who, nil); r != nil {
				return r
			}
		}
	}
	return nil
}
func (s *State) consumeInputs(path Path, node, who string) *Reject {
	return s.consumeChannels(s.Incoming(path, node), who)
}
func (s *State) decision(key, val string) *Reject {
	d := find(s.Decisions, func(d Decision) bool { return d.Key == key })
	if d != nil {
		if d.Value != val {
			return reject("NONDETERMINISTIC_ORACLE")
		}
		return nil
	}
	s.Decisions = append(s.Decisions, Decision{key, val})
	return nil
}
func leafPolicy(n Node) (RetryPolicy, Nat, *Reject) {
	if n.Kind.Type != "leaf" {
		return RetryPolicy{}, Nat{}, reject("NOT_LEAF", n.ID)
	}
	return n.Kind.Retry, n.Kind.Concurrency, nil
}
func (s State) plainInputs(path Path, n Node) (List[[2]string], *Reject) {
	if !allKind(n.Inputs, "plain") {
		return nil, reject("NOT_PLAIN")
	}
	inputs := List[[2]string]{}
	for _, p := range n.Inputs {
		c := find(s.Incoming(path, n.ID), func(c Channel) bool { return c.Edge.Dst.Port == p.Name })
		if c == nil {
			return nil, reject("MISSING_INPUT", p.Name)
		}
		if !c.Closed() {
			return nil, reject("UPSTREAM_NOT_FINISHED")
		}
		producer := s.NodeInstance(path, c.Edge.Src.Node)
		if !c.Entry && (producer == nil || producer.Status != "succeeded") {
			return nil, reject("UPSTREAM_NOT_SUCCEEDED")
		}
		ts := c.Pending()
		if len(ts) == 0 || ts[0].EOS {
			return nil, reject("INPUT_NOT_READY", c.ID)
		}
		inputs = append(inputs, [2]string{p.Name, ts[0].Item})
	}
	return inputs, nil
}
func (s *State) streamController(path Path, n Node) *Reject {
	i := s.NodeInstance(path, n.ID)
	if i != nil {
		if i.Status != "waitingInputs" {
			return reject("CONTROL_FINISHED")
		}
		return nil
	}
	return s.freshInstance(makeInstance(path, n, "waitingInputs", nil, nil))
}
func (s *State) addFrame(owner Instance, body Graph, items []string) *Reject {
	path := append(slices.Clone(owner.Path), Identity([]string{owner.ID, owner.Iteration.String()}))
	if s.Frame(path) != nil {
		return reject("DUPLICATE_FRAME")
	}
	if len(items) != len(body.Entries) {
		return reject("BODY_INPUT_ARITY")
	}
	definition := List[string]{}
	if f := s.Frame(owner.Path); f != nil {
		definition = slices.Clone(f.Definition)
	}
	definition = append(definition, owner.Node)
	f := Frame{Path: path, Graph: body, Definition: definition, Owner: ptr(owner.ID)}
	s.Frames = append(s.Frames, f)
	s.Channels = append(s.Channels, f.channels()...)
	for i, p := range body.Entries {
		ids := mapped(filter(s.Incoming(path, p.Node), func(c Channel) bool { return c.Entry && c.Edge.Dst == p }), func(c Channel) string { return c.ID })
		if r := s.place(ids, Token{Item: items[i]}); r != nil {
			return r
		}
		if r := s.place(ids, Token{EOS: true}); r != nil {
			return r
		}
	}
	return nil
}
func (s State) CurrentFrame(i Instance) (Frame, *Reject) {
	f := s.Frame(append(slices.Clone(i.Path), Identity([]string{i.ID, i.Iteration.String()})))
	if f == nil {
		return Frame{}, reject("MISSING_BODY", i.ID)
	}
	return *f, nil
}
func (s State) FrameDone(f Frame) bool {
	return !f.Closed && all(filter(s.Channels, func(c Channel) bool { return slices.Equal(c.Path, f.Path) && c.Exit }), func(c Channel) bool { return c.Closed() }) && all(filter(s.Channels, func(c Channel) bool { return slices.Equal(c.Path, f.Path) && !c.Exit }), func(c Channel) bool { return c.Closed() && len(c.PendingItems()) == 0 }) && all(filter(s.Instances, func(i Instance) bool { return slices.Equal(i.Path, f.Path) }), func(i Instance) bool { return i.Status == "succeeded" || i.Status == "cancelled" }) && all(f.Graph.Nodes, func(n Node) bool {
		i := s.NodeInstance(f.Path, n.ID)
		return i != nil && (i.Status == "succeeded" || i.Status == "cancelled")
	})
}
func (s State) frameOutputItems(f Frame) (List[string], *Reject) {
	items := List[string]{}
	for _, p := range f.Graph.Exits {
		c := find(s.Channels, func(c Channel) bool { return slices.Equal(c.Path, f.Path) && c.Exit && c.Edge.Src == p })
		if c == nil {
			return nil, reject("MISSING_EXIT", p.Port)
		}
		xs := c.Items()
		if len(xs) != 1 {
			return nil, reject("BODY_RESULT_ARITY", p.Port)
		}
		items = append(items, xs[0])
	}
	return items, nil
}
func (s State) bodyResults(f Frame) (List[string], *Reject) {
	if !s.FrameDone(f) {
		return nil, reject("BODY_NOT_FINISHED")
	}
	return s.frameOutputItems(f)
}
func (s *State) closeFrame(f Frame, who string) *Reject {
	if r := s.consumeChannels(filter(s.Channels, func(c Channel) bool { return slices.Equal(c.Path, f.Path) && c.Exit }), who); r != nil {
		return r
	}
	for j := range s.Frames {
		if slices.Equal(s.Frames[j].Path, f.Path) {
			s.Frames[j].Closed = true
		}
	}
	return nil
}
func (s *State) finishControl(path Path, n Node, inputs List[[2]string], output, arm *string) *Reject {
	i := makeInstance(path, n, "succeeded", inputs, nil)
	if r := s.freshInstance(i); r != nil {
		return r
	}
	if r := s.consumeInputs(path, n.ID, i.ID); r != nil {
		return r
	}
	for _, p := range n.Outputs {
		if output != nil && (arm == nil || *arm == p.Name) {
			if r := s.putOutput(path, n.ID, p.Name, Token{Item: *output}); r != nil {
				return r
			}
		}
	}
	return s.closeOutputs(path, n)
}
func (s *State) expireOrFail(i Instance, n Node, now Nat, outcome string, retryable bool, code string) *Reject {
	policy, _, r := leafPolicy(n)
	if r != nil {
		return r
	}
	if i.Lease == nil {
		return reject("NO_LEASE", i.ID)
	}
	retry := retryable && i.AttemptCount.Cmp(policy.MaxAttempts.Add(i.ExtraAttempts)) < 0
	s.setAttempt(i.Lease.Attempt, outcome)
	i.Lease = nil
	i.RetryAt = nil
	i.Status = "failed"
	if retry {
		i.Status = "retryWait"
		i.RetryAt = ptr(now.Add(policy.RetrySeconds))
	} else {
		s.Status = "blocked"
		s.Reason = ptr(code)
	}
	s.setInstance(i)
	s.Now = now
	return nil
}
