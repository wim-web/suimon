package suimon

import "strconv"

// Exploration of Suimon/Explore.lean: the operations that might be accepted in a state, and a
// reproducible random walk over them. The candidate order and the choices are those of Lean, so a
// seed produces the same operations in both.

// Config bounds an exploration. The zero value is not the Lean default; use DefaultConfig.
type Config struct {
	// MaxYields is the number of elements a Stream function yields at most.
	MaxYields int
	// Failures includes failures, timeouts and lost calls among the reports of user processes.
	Failures bool
	// Cancel includes cancellation by the caller.
	Cancel bool
	// Disruption: a random walk picks a disruptive operation once in this many choices, when one
	// is accepted.
	Disruption uint64
}

// DefaultConfig is Lean's Explore.Config default.
func DefaultConfig() Config {
	return Config{MaxYields: 2, Failures: true, Cancel: true, Disruption: 40}
}

// ExploreValue derives a value from where it comes from, so a run is reproducible.
func ExploreValue(parts ...string) string {
	return Identity(append([]string{"value"}, parts...)...)
}

func armsOf(p *Definition, v view, c *Call) []string {
	i, ok := v.invocation(c.Owner)
	if !ok {
		return nil
	}
	w, ok := v.workflow(p, i.Run)
	if !ok {
		return nil
	}
	pl, ok := w.placement(i.Placement)
	if !ok {
		return nil
	}
	if branch, ok := pl.Control.(BranchControl); ok {
		return branch.Arms
	}
	return nil
}

func callCandidates(p *Definition, cfg Config, s *State, c *Call) []Op {
	failures := func(fetching bool) []Op {
		if !cfg.Failures {
			return nil
		}
		ops := []Op{OpFailed{c.ID}, OpTimedOut{c.ID, false}, OpLost{c.ID}}
		if fetching {
			ops = append(ops, OpTimedOut{c.ID, true})
		}
		return ops
	}
	var ops []Op
	switch c.Status {
	case CallRunning:
		if c.Target.Judge {
			for _, arm := range armsOf(p, s.view(), c) {
				ops = append(ops, OpJudged{c.ID, arm})
			}
		} else if c.Stream {
			ops = append(ops, OpFetch{c.ID})
		} else {
			ops = append(ops, OpReturned{c.ID, ExploreValue("return", c.ID)})
		}
		return append(ops, failures(false)...)
	case CallFetching:
		if c.Yields < cfg.MaxYields {
			ops = append(ops, OpYielded{c.ID, ExploreValue("yield", c.ID, strconv.Itoa(c.Yields))})
		}
		return append(append(ops, OpEnded{c.ID}), failures(true)...)
	case CallCancelling:
		return []Op{OpTerminated{c.ID}, OpLost{c.ID}}
	}
	return nil
}

// invokeCandidates are the invocations of the placement name of w, whose kinds are k.
func invokeCandidates(s *State, path Path, w *Workflow, k kindTable, name string) []Op {
	sh, ok := w.shape(k, name)
	if !ok {
		return nil
	}
	switch sh.kind {
	case shapeNone, shapeEntry:
		return []Op{OpInvoke{Run: path, Placement: name}}
	case shapeSingle:
		if r := s.view().resolveSingle(path, sh.index, sh.connection); r.kind == resolutionValue {
			return []Op{OpInvoke{Run: path, Placement: name, Trigger: ptr(r.source)}}
		}
	case shapeStream:
		var ops []Op
		for d := range s.view().deliveriesOn(path, sh.index) {
			if d.Outcome.Kind != DeliveredFailed {
				ops = append(ops, OpInvoke{Run: path, Placement: name, Trigger: ptr(d.Source)})
			}
		}
		return ops
	}
	return nil
}

func deliveryCandidates(p *Definition, cfg Config, s *State, r *Result) []Op {
	w, ok := s.workflow(p, r.Run)
	if !ok {
		return nil
	}
	var ops []Op
	for i, c := range w.Connections {
		if c.Source != r.Placement || (c.Arm != nil && !equalPtr(c.Arm, r.Arm)) {
			continue
		}
		if _, delivered := s.view().delivery(r.Run, i, r.ID); delivered {
			continue
		}
		if c.Transform.Discard {
			ops = append(ops, OpDeliver{Run: r.Run, Connection: i, Source: r.ID})
			continue
		}
		ops = append(ops, OpDeliver{Run: r.Run, Connection: i, Source: r.ID,
			Value: ptr(ExploreValue("transform", strconv.Itoa(i), r.ID))})
		if cfg.Failures {
			ops = append(ops, OpTransformFailed{Run: r.Run, Connection: i, Source: r.ID})
		}
	}
	return ops
}

func taskCandidates(p *Definition, cfg Config, s *State, e *Execution) []Op {
	ops := []Op{OpCloseExecution{e.ID}}
	for _, t := range e.Tasks {
		spec, err := s.view().taskSpec(p, e, t.Name)
		if err != nil {
			continue
		}
		switch t.Status {
		case TaskPending:
			switch {
			case spec.Input == nil:
			case spec.Input.Discard:
				ops = append(ops, OpTaskInput{Execution: e.ID, Task: t.Name})
			default:
				ops = append(ops, OpTaskInput{Execution: e.ID, Task: t.Name, Value: ptr(ExploreValue("input", e.ID, t.Name))})
				if cfg.Failures {
					ops = append(ops, OpTaskInputFailed{e.ID, t.Name})
				}
			}
		case TaskReady:
			ops = append(ops, OpBeginTask{e.ID, t.Name})
		}
	}
	for _, r := range s.TaskResults {
		if r.Execution != e.ID || r.Output.Kind != TaskOutputPending {
			continue
		}
		ops = append(ops, OpTaskOutput{Execution: e.ID, Task: r.Task, Index: r.Index,
			Value: ExploreValue("output", e.ID, r.Task, strconv.Itoa(r.Index))})
		if cfg.Failures {
			ops = append(ops, OpTaskOutputFailed{Execution: e.ID, Task: r.Task, Index: r.Index})
		}
	}
	return ops
}

// Candidates are every operation that might be accepted; Step decides which ones are.
func Candidates(p *Definition, cfg Config, s *State) []Op {
	return candidatesWith(p, p.derive(), cfg, s)
}

// candidatesWith is Candidates with d, a derivation of p.
func candidatesWith(p *Definition, d *derivation, cfg Config, s *State) []Op {
	if !s.Started {
		var input *string
		if w, ok := p.workflow(p.Main); ok && w.Input != nil {
			input = ptr(ExploreValue("input"))
		}
		return []Op{OpStart{Input: input}}
	}
	switch s.Status {
	case StatusRunning:
		ops := []Op{OpConclude{}}
		if cfg.Cancel {
			ops = append(ops, OpCancel{})
		}
		for _, r := range s.Runs {
			if r.Complete {
				continue
			}
			w, ok := p.workflow(r.Workflow)
			if !ok {
				continue
			}
			if len(r.Path) != 0 {
				ops = append(ops, OpCloseRun{Run: r.Path})
			}
			kinds := d.kinds(w)
			for _, pl := range w.Placements {
				ops = append(ops, OpSettle{Run: r.Path, Placement: pl.Name})
				ops = append(ops, invokeCandidates(s, r.Path, w, kinds, pl.Name)...)
			}
		}
		for i := range s.Results {
			ops = append(ops, deliveryCandidates(p, cfg, s, &s.Results[i])...)
		}
		for i := range s.Calls {
			ops = append(ops, callCandidates(p, cfg, s, &s.Calls[i])...)
		}
		for i := range s.Executions {
			if !s.Executions[i].Complete {
				ops = append(ops, taskCandidates(p, cfg, s, &s.Executions[i])...)
			}
		}
		return ops
	case StatusStopping:
		ops := []Op{OpConclude{}}
		if cfg.Cancel && !s.Cancelled {
			ops = append(ops, OpCancel{})
		}
		for _, c := range s.Calls {
			if c.Status == CallCancelling {
				ops = append(ops, OpTerminated{c.ID}, OpLost{c.ID})
			}
		}
		return ops
	}
	return nil
}

// Choice is an accepted operation and the state it leads to.
type Choice struct {
	Op   Op
	Next *State
}

// Accepted are the candidates that Step accepts and that change the state.
func Accepted(p *Definition, cfg Config, s *State) []Choice {
	return acceptedWith(p, p.derive(), cfg, s)
}

// acceptedWith is Accepted with d, a derivation of p.
func acceptedWith(p *Definition, d *derivation, cfg Config, s *State) []Choice {
	var choices []Choice
	for _, op := range candidatesWith(p, d, cfg, s) {
		next, err := stepWith(p, d, s, op)
		if err == nil && !next.Equal(s) {
			choices = append(choices, Choice{op, next})
		}
	}
	return choices
}

// NextSeed is a portable generator, so that a failing seed reproduces anywhere.
func NextSeed(seed uint64) uint64 {
	return (1664525*(seed%4294967296) + 1013904223) % 4294967296
}

// disruptive: failures, cancellation and short streams end work early, so a walk picks them rarely.
func disruptive(cfg Config, s *State, op Op) bool {
	switch op := op.(type) {
	case OpFailed, OpTimedOut, OpLost, OpTransformFailed, OpTaskInputFailed, OpTaskOutputFailed, OpCancel:
		return true
	case OpEnded:
		c, ok := s.call(op.Call)
		return ok && c.Yields < cfg.MaxYields
	}
	return false
}

// Lean's natural number division and remainder, where n / 0 = 0 and n % 0 = n.
func natDiv(a, b uint64) uint64 {
	if b == 0 {
		return 0
	}
	return a / b
}

func natMod(a, b uint64) uint64 {
	if b == 0 {
		return a
	}
	return a % b
}

// Pick chooses among the accepted operations with the seed: usually a non-disruptive one.
func Pick(cfg Config, s *State, seed uint64, choices []Choice) (Choice, bool) {
	var bad, good []Choice
	for _, c := range choices {
		if disruptive(cfg, s, c.Op) {
			bad = append(bad, c)
		} else {
			good = append(good, c)
		}
	}
	pool := good
	if len(good) == 0 || (len(bad) > 0 && natMod(seed, cfg.Disruption) == 0) {
		pool = bad
	}
	if len(pool) == 0 {
		return Choice{}, false
	}
	return pool[natMod(natDiv(seed, cfg.Disruption), uint64(len(pool)))], true
}

// Walk is a random walk from the state before the start until no operation is accepted, or limit
// operations were taken. It returns the final state and the operations.
func Walk(p *Definition, cfg Config, seed uint64, limit int) (*State, []Op) {
	d := p.derive()
	state := &State{}
	var trace []Op
	for range limit {
		choices := acceptedWith(p, d, cfg, state)
		if len(choices) == 0 {
			break
		}
		seed = NextSeed(seed)
		choice, ok := Pick(cfg, state, seed, choices)
		if !ok {
			break
		}
		trace = append(trace, choice.Op)
		state = choice.Next
	}
	return state, trace
}
