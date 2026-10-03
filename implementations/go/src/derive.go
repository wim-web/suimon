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

// kindTable holds the output kinds of the placements of one workflow at one fuel, by name: what
// Lean's w.kind? p fuel name derives. A placement whose kind cannot be derived, like a name that is
// not a placement, has no entry.
type kindTable map[string]Kind

// kindRow is what kind? reads of one placement name: the placement it names, which is the first of
// that name, and its input connections.
type kindRow struct {
	placement *Placement
	incoming  []Connection
}

// kindsAt resolves each placement once, when every source kind is available.
// A derived kind never changes with more fuel: only an unknown kind can become
// known. The longest source path records the first fuel at which it is known.
// Cycles and missing sources remain unresolved, exactly as in kind?.
func (w *Workflow) kindsAt(p *Definition, fuel int) kindTable {
	table := kindTable{}
	if fuel <= 0 {
		return table
	}
	rows := make(map[string]kindRow, len(w.Placements))
	pending := make(map[string]int, len(w.Placements))
	outgoing := make(map[string][]string, len(w.Placements))
	level := make(map[string]int, len(w.Placements))
	for i := range w.Placements {
		pl := &w.Placements[i]
		if _, exists := rows[pl.Name]; !exists {
			rows[pl.Name] = kindRow{placement: pl}
			level[pl.Name] = 1
		}
	}
	for _, c := range w.Connections {
		if row, exists := rows[c.Target]; exists {
			row.incoming = append(row.incoming, c)
			rows[c.Target] = row
			pending[c.Target]++
			outgoing[c.Source] = append(outgoing[c.Source], c.Target)
		}
	}
	functions := make(map[string]Kind, len(p.Functions))
	workflows := make(map[string]bool, len(p.Workflows))
	for _, f := range p.Functions {
		if _, exists := functions[f.ID]; !exists {
			functions[f.ID] = f.Output.Kind
		}
	}
	for _, w := range p.Workflows {
		workflows[w.ID] = true
	}
	queue := make([]string, 0, len(rows))
	for name := range rows {
		if pending[name] == 0 {
			queue = append(queue, name)
		}
	}
	for head := 0; head < len(queue); head++ {
		name := queue[head]
		if level[name] > fuel {
			continue
		}
		row := rows[name]
		sources, ok := table.sourceKinds(row.incoming)
		if !ok {
			continue
		}
		input, ok := w.combineInput(name, sources)
		if !ok {
			continue
		}
		var k Kind
		if call, isCall := row.placement.Control.(CallControl); isCall && (input == nil || *input == KindSingle) {
			if call.Body.Workflow {
				k, ok = KindSingle, workflows[call.Body.ID]
			} else {
				k, ok = functions[call.Body.ID]
			}
		} else {
			k, ok = p.outputKind(row.placement.Control, input)
		}
		if !ok {
			continue
		}
		table[name] = k
		for _, dst := range outgoing[name] {
			pending[dst]--
			level[dst] = max(level[dst], level[name]+1)
			if pending[dst] == 0 {
				queue = append(queue, dst)
			}
		}
	}
	return table
}

// sourceKinds is Lean's incoming.mapM fun c => prev c.source.
func (t kindTable) sourceKinds(incoming []Connection) ([]Kind, bool) {
	sources := make([]Kind, 0, len(incoming))
	for _, c := range incoming {
		k, ok := t[c.Source]
		if !ok {
			return nil, false
		}
		sources = append(sources, k)
	}
	return sources, true
}

func (w *Workflow) depth() int { return len(w.Placements) + 1 }

// deriveKinds derives the table of w at the fuel of Lean's outputKind? and inputKind?, which
// suffices for an acyclic workflow.
func (w *Workflow) deriveKinds(p *Definition) kindTable { return w.kindsAt(p, w.depth()) }

// outputKind is Lean's outputKind? of the workflow of the table, derived by deriveKinds.
func (t kindTable) outputKind(name string) (Kind, bool) {
	k, ok := t[name]
	return k, ok
}

// inputKind is Lean's inputKind? of the workflow w of the table, derived by deriveKinds: the input
// kind of a placement, nil when it takes no input.
func (t kindTable) inputKind(w *Workflow, name string) (input *Kind, ok bool) {
	sources, ok := t.sourceKinds(w.incoming(name))
	if !ok {
		return nil, false
	}
	return w.combineInput(name, sources)
}

// derivation holds the kind tables of the workflows of a definition, derived once, which the
// validator and the engine share. The definition must not change while its derivation is in use. A
// derivation is only read after derive returns, so goroutines may share it.
type derivation struct {
	p      *Definition
	tables map[*Workflow]kindTable
}

func (p *Definition) derive() *derivation {
	d := &derivation{p: p, tables: make(map[*Workflow]kindTable, len(p.Workflows))}
	for i := range p.Workflows {
		w := &p.Workflows[i]
		d.tables[w] = w.deriveKinds(p)
	}
	return d
}

// kinds is the table of w, a workflow of the definition, as deriveKinds derives it.
func (d *derivation) kinds(w *Workflow) kindTable {
	if t, ok := d.tables[w]; ok {
		return t
	}
	return w.deriveKinds(d.p)
}

// OutputKind is the derived Single/Stream kind of a placement of workflow; ok is false when it
// cannot be derived or the definition exceeds resource limits.
func (p *Definition) OutputKind(workflow, placement string) (kind Kind, ok bool) {
	if p.checkResources() != nil {
		return 0, false
	}
	w, found := p.workflow(workflow)
	if !found {
		return 0, false
	}
	return w.deriveKinds(p).outputKind(placement)
}

func copyPtr[T any](v *T) *T {
	if v == nil {
		return nil
	}
	c := *v
	return &c
}
