package suimon

import "unicode/utf8"

type Config struct {
	Depth     Nat `json:"depth"`
	Workers   Nat `json:"workers"`
	Tick      Nat `json:"tick"`
	MaxItems  Nat `json:"maxItems"`
	MaxStates Nat `json:"maxStates"`
}

func DefaultConfig() Config { return Config{N(8), N(1), N(1), N(2), N(100000)} }
func InputValues(g Graph) List[Input] {
	return mapped(g.Entries, func(p PortRef) Input { return Input{p, List[string]{Identity([]string{"input", p.Node, p.Port})}} })
}
func Outputs(i Instance, n Node) List[Output] {
	return mapped(filter(n.Outputs, func(p Port) bool { return p.Kind == "plain" }), func(p Port) Output {
		items := append([]string{p.Name}, mapped(i.Inputs, func(p [2]string) string { return p[1] })...)
		return Output{p.Name, List[string]{DerivedItem("leaf", i.Path, i.Node, items)}}
	})
}
func freshID(tag string, used []string) string {
	longest := ""
	for _, id := range used {
		if utf8.RuneCountInString(id) >= utf8.RuneCountInString(longest) {
			longest = id
		}
	}
	return tag + ":" + longest
}
func ClaimCredentials(s State, i Instance) Credentials {
	return Credentials{i.ID, freshID("attempt", mapped(s.Attempts, func(a Attempt) string { return a.ID })), freshID("lease", mapped(s.Attempts, func(a Attempt) string { return a.Token })), s.Now}
}
func pendingCandidates(path Path, n Node, c Channel) List[Op] {
	ts := c.Pending()
	if len(ts) == 0 || ts[0].EOS {
		return nil
	}
	o := Op{Path: path, Node: n.ID, Item: ts[0].Item, Edge: c.ID}
	switch n.Kind.Type {
	case "coalesce":
		o.Kind = "fireCoalesce"
	case "merge":
		o.Kind = "fireMerge"
	case "forEach":
		o.Kind = "spawn"
	case "filter":
		o.Kind = "fireFilter"
		o.Keep = true
		other := o
		other.Keep = false
		return List[Op]{o, other}
	default:
		return nil
	}
	return List[Op]{o}
}
func nodeCandidates(s State, path Path, n Node) List[Op] {
	ops := List[Op]{{Kind: "skip", Path: path, Node: n.ID}}
	o := Op{Path: path, Node: n.ID}
	switch n.Kind.Type {
	case "leaf", "subworkflow", "loop":
		o.Kind = "activate"
		ops = append(ops, o)
	case "waitAll":
		o.Kind = "fireWaitAll"
		ops = append(ops, o)
	case "branch":
		for _, arm := range n.Kind.Arms {
			o.Kind = "fireBranch"
			o.Arm = arm
			ops = append(ops, o)
		}
	case "collect":
		o.Kind = "fireCollect"
		ops = append(ops, o)
	case "coalesce", "filter", "merge", "forEach":
		if n.Kind.Type != "coalesce" {
			o.Kind = "propagateEos"
			ops = append(ops, o)
		}
		for _, c := range s.Incoming(path, n.ID) {
			ops = append(ops, pendingCandidates(path, n, c)...)
		}
	}
	return ops
}
func instanceCandidates(cfg Config, s State, i Instance) List[Op] {
	switch i.Status {
	case "ready":
		ops := List[Op]{}
		for w := (Nat{}); w.Cmp(cfg.Workers) < 0; w = w.Inc() {
			ops = append(ops, Op{Kind: "claim", Auth: ClaimCredentials(s, i), Worker: w.String()})
		}
		return ops
	case "running":
		if i.Lease == nil {
			return nil
		}
		auth := Credentials{i.ID, i.Lease.Attempt, i.Lease.Token, s.Now}
		renew := auth
		renew.Now = s.Now.Add(cfg.Tick)
		ops := List[Op]{{Kind: "fail", Auth: auth, Code: "TRANSIENT", Retryable: true}, {Kind: "fail", Auth: auth, Code: "PERMANENT"}, {Kind: "expireLease", Inst: i.ID, Now: maxNat(s.Now.Add(cfg.Tick), i.Lease.Until)}, {Kind: "renew", Auth: renew}}
		n := s.Node(i.Path, i.Node)
		if n == nil {
			return ops
		}
		ops = append(ops, Op{Kind: "complete", Auth: auth, Outputs: Outputs(i, *n)})
		for _, p := range n.Outputs {
			if p.Kind == "stream" {
				for idx := (Nat{}); idx.Cmp(cfg.MaxItems) < 0; idx = idx.Inc() {
					ops = append(ops, Op{Kind: "emit", Auth: auth, Port: p.Name, Item: DerivedItem("emit", i.Path, i.Node, []string{p.Name, idx.String()})})
				}
			}
		}
		return ops
	case "retryWait":
		return List[Op]{{Kind: "promoteRetry", Inst: i.ID, Now: maxNat(s.Now, value(i.RetryAt, s.Now.Add(cfg.Tick)))}}
	case "failed":
		return List[Op]{{Kind: "manualRetry", Inst: i.ID}}
	case "waitingInputs":
		return List[Op]{{Kind: "finishSubworkflow", Inst: i.ID}, {Kind: "loopIterate", Inst: i.ID, Done: true}, {Kind: "loopIterate", Inst: i.ID}}
	}
	return nil
}

// Candidates returns the same finite operation domain and order as Lean.
func Candidates(cfg Config, s State) List[Op] {
	if terminal(s.Status) {
		return nil
	}
	if !s.Started {
		f := s.Frame(nil)
		if f == nil {
			return nil
		}
		return List[Op]{{Kind: "start", Inputs: InputValues(f.Graph)}, {Kind: "cancel"}}
	}
	ops := List[Op]{{Kind: "idle"}, {Kind: "cancel"}}
	for _, f := range s.Frames {
		if !f.Closed {
			for _, n := range f.Graph.Nodes {
				ops = append(ops, nodeCandidates(s, f.Path, n)...)
			}
		}
	}
	for _, i := range s.Instances {
		ops = append(ops, instanceCandidates(cfg, s, i)...)
	}
	return ops
}

type Failure struct {
	Reason string   `json:"reason"`
	Trace  List[Op] `json:"trace"`
	State  State    `json:"state"`
}
type Report struct {
	States      Nat      `json:"states"`
	Transitions Nat      `json:"transitions"`
	Depth       Nat      `json:"depth"`
	Complete    bool     `json:"complete"`
	Failure     *Failure `json:"failure"`
}

func Search(g Graph, cfg Config) Report {
	type entry struct {
		s   State
		ops List[Op]
	}
	initial := Initial(g)
	visited := map[string]bool{compact(initial): true}
	frontier := []entry{{initial, nil}}
	transitions := Nat{}
	for depth := (Nat{}); depth.Cmp(cfg.Depth) < 0; depth = depth.Inc() {
		nextFrontier := []entry{}
		for _, current := range frontier {
			for _, o := range Candidates(cfg, current.s) {
				next, r := Step(current.s, o)
				if r != nil {
					if r.Code == "INVARIANT" {
						trace := append(append(List[Op]{}, current.ops...), o)
						return Report{N(uint64(len(visited))), transitions, depth, false, &Failure{r.Message, trace, current.s}}
					}
					continue
				}
				transitions = transitions.Inc()
				key := compact(next)
				if !visited[key] {
					if N(uint64(len(visited))).Cmp(cfg.MaxStates) >= 0 {
						return Report{N(uint64(len(visited))), transitions, depth, false, nil}
					}
					visited[key] = true
					nextFrontier = append(nextFrontier, entry{next, append(append(List[Op]{}, current.ops...), o)})
				}
			}
		}
		frontier = nextFrontier
	}
	return Report{N(uint64(len(visited))), transitions, cfg.Depth, true, nil}
}
func NextSeed(seed Nat) Nat { return seed.Mul(N(1664525)).Add(N(1013904223)).mod(N(4294967296)) }
func Generate(g Graph, cfg Config, seed, count Nat) (State, List[Event], *Reject) {
	s := Initial(g)
	events := List[Event]{}
	for idx := (Nat{}); idx.Cmp(count) < 0; idx = idx.Inc() {
		choices := List[Op]{}
		for _, o := range Candidates(cfg, s) {
			next, r := Step(s, o)
			if r != nil {
				if r.Code == "INVARIANT" {
					return s, nil, r
				}
				continue
			}
			if !equal(s, next) {
				choices = append(choices, o)
			}
		}
		if len(choices) == 0 {
			break
		}
		seed = NextSeed(seed)
		o := choices[seed.mod(natLen(choices)).index(len(choices))]
		next, records, r := RecordTransaction(s, []Op{o}, natLen(events).Inc(), "txn-"+idx.Inc().String(), s.Now)
		if r != nil {
			return s, nil, r
		}
		s = next
		events = append(events, records...)
	}
	return s, events, nil
}
