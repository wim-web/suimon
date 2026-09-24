package suimon

// Derivations of Suimon/Derive.lean. An Option (Option T) of Lean is returned as a pointer that is
// nil for "no input" together with a flag that is false for "unknown".

// bodyInput is the input of one call: known is false for an unknown body, input is nil for a body
// without input.
func (p *Definition) bodyInput(b Body) (input *ValueType, known bool) {
	if !b.Workflow {
		f, ok := p.function(b.ID)
		if !ok {
			return nil, false
		}
		return copyPtr(f.Input), true
	}
	w, ok := p.workflow(b.ID)
	if !ok {
		return nil, false
	}
	if w.Input == nil {
		return nil, true
	}
	return ptr(w.Input.Type), true
}

func (p *Definition) bodyKind(b Body) (Kind, bool) {
	if !b.Workflow {
		f, ok := p.function(b.ID)
		if !ok {
			return 0, false
		}
		return f.Output.Kind, true
	}
	if _, ok := p.workflow(b.ID); !ok {
		return 0, false
	}
	return KindSingle, true
}

// localResult is the result element type of the controls other than calls.
func (p *Definition) localResult(c Control) (ValueType, bool) {
	switch c := c.(type) {
	case BranchControl:
		j, ok := p.judge(c.Judge)
		if !ok {
			return ValueType{}, false
		}
		return j.Input, true
	case WaitStreamControl:
		return ListOf(c.Element), true
	case MergeControl:
		return ListOf(c.Element), true
	case ConcurrencyControl:
		if c.Spec.Output == CollectList {
			return ListOf(c.Spec.Element), true
		}
		return c.Spec.Element, true
	}
	return ValueType{}, false
}

// bodyElement is the element type of a body's results. The fuel bounds nested workflow references.
func (p *Definition) bodyElement(fuel int, b Body) (ValueType, bool) {
	if fuel == 0 {
		return ValueType{}, false
	}
	if !b.Workflow {
		f, ok := p.function(b.ID)
		if !ok {
			return ValueType{}, false
		}
		return f.Output.Element(), true
	}
	w, ok := p.workflow(b.ID)
	if !ok {
		return ValueType{}, false
	}
	pl, ok := w.placement(b.Output)
	if !ok {
		return ValueType{}, false
	}
	if call, isCall := pl.Control.(CallControl); isCall {
		return p.bodyElement(fuel-1, call.Body)
	}
	return p.localResult(pl.Control)
}

// depth is enough fuel for an acyclic call graph, where each nested reference names another workflow.
func (p *Definition) depth() int { return len(p.Workflows) + 1 }

// resultType is the element type of the results of one placement.
func (p *Definition) resultType(c Control) (ValueType, bool) {
	if call, ok := c.(CallControl); ok {
		return p.bodyElement(p.depth(), call.Body)
	}
	return p.localResult(c)
}

// inputType is what an input connection's transform returns: input is nil when the control takes
// no input, known is false for an unknown reference.
func (p *Definition) inputType(c Control) (input *ValueType, known bool) {
	switch c := c.(type) {
	case CallControl:
		return p.bodyInput(c.Body)
	case BranchControl:
		j, ok := p.judge(c.Judge)
		if !ok {
			return nil, false
		}
		return ptr(j.Input), true
	case WaitStreamControl:
		return ptr(c.Element), true
	case MergeControl:
		return ptr(c.Element), true
	case ConcurrencyControl:
		return copyPtr(c.Spec.Input), true
	}
	return nil, false
}

// outputKind is the output kind of one placement from its input kind, nil for no input (§5.2, §8.4).
func (p *Definition) outputKind(control Control, input *Kind) (Kind, bool) {
	switch c := control.(type) {
	case CallControl:
		if input == nil || *input == KindSingle {
			return p.bodyKind(c.Body)
		}
		return KindStream, true
	case BranchControl:
		if input != nil {
			return *input, true
		}
	case WaitStreamControl:
		if input != nil && *input == KindStream {
			return KindSingle, true
		}
	case MergeControl:
		if input != nil && *input == KindSingle {
			return KindSingle, true
		}
	case ConcurrencyControl:
		if input == nil || *input == KindSingle {
			if c.Spec.Output == CollectList {
				return KindSingle, true
			}
			return KindStream, true
		}
		return KindStream, true
	}
	return 0, false
}

// combineInput: an entry supplies one Single input; otherwise every source must agree.
func (w *Workflow) combineInput(name string, sources []Kind) (input *Kind, ok bool) {
	if w.isEntry(name) {
		if len(sources) == 0 {
			return ptr(KindSingle), true
		}
		return nil, false
	}
	if len(sources) == 0 {
		return nil, true
	}
	for _, k := range sources[1:] {
		if k != sources[0] {
			return nil, false
		}
	}
	return ptr(sources[0]), true
}

// kind is the output kind of a placement; the fuel bounds the length of connection paths.
func (w *Workflow) kind(p *Definition, fuel int, name string) (Kind, bool) {
	if fuel == 0 {
		return 0, false
	}
	pl, ok := w.placement(name)
	if !ok {
		return 0, false
	}
	sources, ok := w.sourceKinds(p, fuel-1, name)
	if !ok {
		return 0, false
	}
	input, ok := w.combineInput(name, sources)
	if !ok {
		return 0, false
	}
	return p.outputKind(pl.Control, input)
}

// sourceKinds is Lean's (w.incoming name).mapM fun c => w.kind? p fuel c.source.
func (w *Workflow) sourceKinds(p *Definition, fuel int, name string) ([]Kind, bool) {
	var sources []Kind
	for _, c := range w.incoming(name) {
		k, ok := w.kind(p, fuel, c.Source)
		if !ok {
			return nil, false
		}
		sources = append(sources, k)
	}
	return sources, true
}

func (w *Workflow) depth() int { return len(w.Placements) + 1 }

// inputKind is the derived input kind of a placement, nil when it takes no input.
func (w *Workflow) inputKind(p *Definition, name string) (input *Kind, ok bool) {
	sources, ok := w.sourceKinds(p, w.depth(), name)
	if !ok {
		return nil, false
	}
	return w.combineInput(name, sources)
}

// outputKind is the derived output kind of a placement.
func (w *Workflow) outputKind(p *Definition, name string) (Kind, bool) {
	return w.kind(p, w.depth(), name)
}

// OutputKind is the derived Single/Stream kind of a placement of workflow; ok is false when it
// cannot be derived.
func (p *Definition) OutputKind(workflow, placement string) (kind Kind, ok bool) {
	w, found := p.workflow(workflow)
	if !found {
		return 0, false
	}
	return w.outputKind(p, placement)
}

func copyPtr[T any](v *T) *T {
	if v == nil {
		return nil
	}
	c := *v
	return &c
}
