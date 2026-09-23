package suimon

import (
	"errors"
	"fmt"
	"slices"
)

// Validate performs the structural checks of §14 and returns the first failed check, with the
// message and in the order of Suimon/Validate.lean. run executes only programs accepted here.
func (p *Program) Validate() error {
	if !unique(ids(p.Functions, func(f FunctionDecl) string { return f.ID })) {
		return errors.New("duplicate function id")
	}
	if !unique(ids(p.Judges, func(j JudgeDecl) string { return j.ID })) {
		return errors.New("duplicate judge id")
	}
	if !unique(ids(p.Transforms, func(t TransformDecl) string { return t.ID })) {
		return errors.New("duplicate transform id")
	}
	for _, t := range p.Transforms {
		if t.ID == DiscardName {
			return fmt.Errorf("%s is provided by the library and cannot be declared", DiscardName)
		}
	}
	if !unique(ids(p.Workflows, func(w Workflow) string { return w.ID })) {
		return errors.New("duplicate workflow id")
	}
	if _, ok := p.workflow(p.Main); !ok {
		return fmt.Errorf("unknown main workflow %s", p.Main)
	}
	if !p.callsAcyclic() {
		return errors.New("workflows call each other in a cycle")
	}
	for i := range p.Workflows {
		if err := p.validateWorkflow(&p.Workflows[i]); err != nil {
			return err
		}
	}
	return nil
}

func ids[T any](xs []T, id func(T) string) []string {
	out := make([]string, len(xs))
	for i, x := range xs {
		out[i] = id(x)
	}
	return out
}

func unique(xs []string) bool {
	seen := make(map[string]bool, len(xs))
	for _, x := range xs {
		if seen[x] {
			return false
		}
		seen[x] = true
	}
	return true
}

type edge struct{ src, dst string }

// acyclic is Kahn elimination, bounded by the number of vertices.
func acyclic(edges []edge, fuel int, vertices []string) bool {
	for ; fuel > 0; fuel-- {
		if len(vertices) == 0 {
			return true
		}
		var roots, rest []string
		for _, v := range vertices {
			isRoot := true
			for _, e := range edges {
				if e.dst == v && slices.Contains(vertices, e.src) {
					isRoot = false
					break
				}
			}
			if isRoot {
				roots = append(roots, v)
			}
		}
		if len(roots) == 0 {
			return false
		}
		for _, v := range vertices {
			if !slices.Contains(roots, v) {
				rest = append(rest, v)
			}
		}
		vertices = rest
	}
	return len(vertices) == 0
}

func (b Body) workflowRef() (string, bool) { return b.ID, b.Workflow }

func workflowRefs(c Control) []string {
	switch c := c.(type) {
	case CallControl:
		if id, ok := c.Body.workflowRef(); ok {
			return []string{id}
		}
	case ConcurrencyControl:
		var refs []string
		for _, t := range c.Spec.Tasks {
			if id, ok := t.Body.workflowRef(); ok {
				refs = append(refs, id)
			}
		}
		return refs
	}
	return nil
}

// callsAcyclic: a workflow may not call itself, directly or through other workflows (§13.1).
func (p *Program) callsAcyclic() bool {
	var edges []edge
	for _, w := range p.Workflows {
		for _, pl := range w.Placements {
			for _, ref := range workflowRefs(pl.Control) {
				edges = append(edges, edge{w.ID, ref})
			}
		}
	}
	return acyclic(edges, len(p.Workflows), ids(p.Workflows, func(w Workflow) string { return w.ID }))
}

func (w *Workflow) acyclic() bool {
	edges := make([]edge, len(w.Connections))
	for i, c := range w.Connections {
		edges[i] = edge{c.Source, c.Target}
	}
	return acyclic(edges, len(w.Placements), ids(w.Placements, func(pl Placement) string { return pl.Name }))
}

func (p *Program) validateBody(at string, b Body) error {
	if !b.Workflow {
		if _, ok := p.function(b.ID); !ok {
			return fmt.Errorf("%s: unknown function %s", at, b.ID)
		}
		return nil
	}
	w, ok := p.workflow(b.ID)
	if !ok {
		return fmt.Errorf("%s: unknown workflow %s", at, b.ID)
	}
	if _, ok := w.placement(b.Output); !ok {
		return fmt.Errorf("%s: workflow %s has no placement %s", at, b.ID, b.Output)
	}
	if !w.isEndpoint(b.Output) {
		return fmt.Errorf("%s: %s is not an endpoint of workflow %s", at, b.Output, b.ID)
	}
	return nil
}

// validateTimeout: timeouts are for function calls and branch judges; element timeouts only for
// Stream functions. function is the contract of the called function, nil for other placements.
func validateTimeout(at string, timeout Timeout, function *Contract, judge bool) error {
	if timeout.IsEmpty() {
		return nil
	}
	if function == nil && !judge {
		return fmt.Errorf("%s: a timeout is only for a function call or a branch judge", at)
	}
	if (timeout.CallMs != nil && *timeout.CallMs == 0) || (timeout.ElementMs != nil && *timeout.ElementMs == 0) {
		return fmt.Errorf("%s: a timeout must be positive", at)
	}
	if timeout.ElementMs != nil && (function == nil || function.Kind != KindStream) {
		return fmt.Errorf("%s: an element timeout is only for a Stream function", at)
	}
	return nil
}

func (p *Program) validateTask(at string, c *Concurrency, task *TaskSpec) error {
	at = fmt.Sprintf("%s task %s", at, task.Name)
	if task.Name == "" {
		return fmt.Errorf("%s: empty task name", at)
	}
	if err := p.validateBody(at, task.Body); err != nil {
		return err
	}
	input, known := p.bodyInput(task.Body)
	if !known {
		return fmt.Errorf("%s: unknown body", at)
	}
	switch {
	case input == nil && task.Input == nil:
		if c.Input != nil {
			return fmt.Errorf("%s: the body takes no input, so the input transform must be discard", at)
		}
	case input == nil && task.Input.Discard:
		if c.Input == nil {
			return fmt.Errorf("%s: the concurrency has no input to discard", at)
		}
	case input == nil:
		return fmt.Errorf("%s: the body takes no input, so the input transform must be discard", at)
	case task.Input == nil:
		return fmt.Errorf("%s: an input transform is required", at)
	case task.Input.Discard:
		return fmt.Errorf("%s: discard passes no value, but the body takes %s", at, *input)
	default:
		id := task.Input.ID
		t, ok := p.transform(id)
		if !ok {
			return fmt.Errorf("%s: unknown transform %s", at, id)
		}
		if c.Input == nil {
			return fmt.Errorf("%s: the concurrency has no input for the task", at)
		}
		if t.Input != *c.Input {
			return fmt.Errorf("%s: transform %s takes %s, but the concurrency input is %s", at, id, t.Input, *c.Input)
		}
		if t.Output != *input {
			return fmt.Errorf("%s: transform %s returns %s, but the body takes %s", at, id, t.Output, *input)
		}
	}
	if task.Output != nil {
		id := *task.Output
		t, ok := p.transform(id)
		if !ok {
			return fmt.Errorf("%s: unknown transform %s", at, id)
		}
		element, ok := p.bodyElement(p.depth(), task.Body)
		if !ok {
			return fmt.Errorf("%s: the result type cannot be derived", at)
		}
		if t.Input != element {
			return fmt.Errorf("%s: transform %s takes %s, but the body produces %s", at, id, t.Input, element)
		}
		if t.Output != c.Element {
			return fmt.Errorf("%s: transform %s returns %s, but the output element is %s", at, id, t.Output, c.Element)
		}
	}
	var function *Contract
	if !task.Body.Workflow {
		if f, ok := p.function(task.Body.ID); ok {
			function = &f.Output
		}
	}
	return validateTimeout(at, task.Timeout, function, false)
}

func (p *Program) validateConnection(w *Workflow, c *Connection) error {
	at := fmt.Sprintf("%s: connection %s -> %s", w.ID, c.Source, c.Target)
	source, ok := w.placement(c.Source)
	if !ok {
		return fmt.Errorf("%s: unknown source", at)
	}
	target, ok := w.placement(c.Target)
	if !ok {
		return fmt.Errorf("%s: unknown target", at)
	}
	branch, isBranch := source.Control.(BranchControl)
	switch {
	case isBranch && c.Arm != nil:
		if !slices.Contains(branch.Arms, *c.Arm) {
			return fmt.Errorf("%s: unknown arm %s", at, *c.Arm)
		}
	case isBranch:
		return fmt.Errorf("%s: a connection from a branch needs an arm", at)
	case c.Arm != nil:
		return fmt.Errorf("%s: only a connection from a branch has an arm", at)
	}
	produced, ok := p.resultType(source.Control)
	if !ok {
		return fmt.Errorf("%s: the result type of %s cannot be derived", at, c.Source)
	}
	expected, known := p.inputType(target.Control)
	if !known {
		return fmt.Errorf("%s: %s has an unknown reference", at, c.Target)
	}
	switch {
	case c.Transform.Discard && expected == nil:
		return nil
	case c.Transform.Discard:
		return fmt.Errorf("%s: discard passes no value, but %s takes %s", at, c.Target, *expected)
	case expected == nil:
		return fmt.Errorf("%s: %s takes no input, so the transform must be discard", at, c.Target)
	}
	id := c.Transform.ID
	t, ok := p.transform(id)
	if !ok {
		return fmt.Errorf("%s: unknown transform %s", at, id)
	}
	if t.Input != produced {
		return fmt.Errorf("%s: transform %s takes %s, but %s produces %s", at, id, t.Input, c.Source, produced)
	}
	if t.Output != *expected {
		return fmt.Errorf("%s: transform %s returns %s, but %s takes %s", at, id, t.Output, c.Target, *expected)
	}
	return nil
}

func (p *Program) validateEntry(w *Workflow, e *Entry) error {
	at := fmt.Sprintf("%s: entry %s", w.ID, e.Placement)
	pl, ok := w.placement(e.Placement)
	if !ok {
		return fmt.Errorf("%s: unknown placement", at)
	}
	if _, isMerge := pl.Control.(MergeControl); isMerge {
		return fmt.Errorf("%s: Merge cannot be the entry", at)
	}
	expected, known := p.inputType(pl.Control)
	if !known {
		return fmt.Errorf("%s: unknown reference", at)
	}
	if expected == nil || *expected != e.Type {
		return fmt.Errorf("%s: the input type %s does not match the placement", at, e.Type)
	}
	if len(w.incoming(e.Placement)) != 0 {
		return fmt.Errorf("%s: the entry cannot have an input connection", at)
	}
	return nil
}

func (p *Program) validatePlacement(w *Workflow, pl *Placement) error {
	at := fmt.Sprintf("%s.%s", w.ID, pl.Name)
	incoming := w.incoming(pl.Name)
	switch c := pl.Control.(type) {
	case CallControl:
		if err := p.validateBody(at, c.Body); err != nil {
			return err
		}
	case BranchControl:
		if _, ok := p.judge(c.Judge); !ok {
			return fmt.Errorf("%s: unknown judge %s", at, c.Judge)
		}
		if len(c.Arms) == 0 || !unique(c.Arms) || slices.Contains(c.Arms, "") {
			return fmt.Errorf("%s: arms must be distinct non-empty names", at)
		}
		connected := false
		for _, arm := range c.Arms {
			for _, o := range w.outgoing(pl.Name) {
				if o.Arm != nil && *o.Arm == arm {
					connected = true
				}
			}
		}
		if !connected {
			return fmt.Errorf("%s: at least one arm needs a connection", at)
		}
	case WaitStreamControl:
	case MergeControl:
		if len(incoming) == 0 {
			return fmt.Errorf("%s: Merge needs input connections", at)
		}
	case ConcurrencyControl:
		spec := &c.Spec
		if spec.Limit == 0 {
			return fmt.Errorf("%s: limit must be positive", at)
		}
		if len(spec.Tasks) == 0 {
			return fmt.Errorf("%s: concurrency needs tasks", at)
		}
		if !unique(ids(spec.Tasks, func(t TaskSpec) string { return t.Name })) {
			return fmt.Errorf("%s: duplicate task name", at)
		}
		if !slices.ContainsFunc(spec.Tasks, func(t TaskSpec) bool { return t.Output != nil }) {
			return fmt.Errorf("%s: at least one task must be in the output", at)
		}
		for i := range spec.Tasks {
			if err := p.validateTask(at, spec, &spec.Tasks[i]); err != nil {
				return err
			}
		}
	}
	expected, known := p.inputType(pl.Control)
	if !known {
		return fmt.Errorf("%s: unknown reference", at)
	}
	_, isMerge := pl.Control.(MergeControl)
	if !isMerge {
		count := len(incoming)
		if w.isEntry(pl.Name) {
			count++
		}
		if expected != nil && count != 1 {
			return fmt.Errorf("%s: needs exactly one input", at)
		}
		if expected == nil && count > 1 {
			return fmt.Errorf("%s: accepts at most one connection", at)
		}
	}
	switch pl.Control.(type) {
	case WaitStreamControl:
		if input, ok := w.inputKind(p, pl.Name); !ok || input == nil || *input != KindStream {
			return fmt.Errorf("%s: waitStream needs a Stream input", at)
		}
	case MergeControl:
		for _, c := range incoming {
			if k, ok := w.outputKind(p, c.Source); !ok || k != KindSingle {
				return fmt.Errorf("%s: Merge accepts only Single inputs (%s)", at, c.Source)
			}
		}
	}
	if _, ok := w.outputKind(p, pl.Name); !ok {
		return fmt.Errorf("%s: Single/Stream cannot be derived", at)
	}
	var function *Contract
	if call, ok := pl.Control.(CallControl); ok && !call.Body.Workflow {
		if f, ok := p.function(call.Body.ID); ok {
			function = &f.Output
		}
	}
	_, isBranch := pl.Control.(BranchControl)
	return validateTimeout(at, pl.Timeout, function, isBranch)
}

func (p *Program) validateWorkflow(w *Workflow) error {
	at := fmt.Sprintf("workflow %s", w.ID)
	if w.ID == "" {
		return errors.New("empty workflow id")
	}
	if len(w.Placements) == 0 {
		return fmt.Errorf("%s: no placements", at)
	}
	for _, pl := range w.Placements {
		if pl.Name == "" {
			return fmt.Errorf("%s: empty placement name", at)
		}
	}
	if !unique(ids(w.Placements, func(pl Placement) string { return pl.Name })) {
		return fmt.Errorf("%s: duplicate placement name", at)
	}
	for i := range w.Connections {
		if err := p.validateConnection(w, &w.Connections[i]); err != nil {
			return err
		}
	}
	if !w.acyclic() {
		return fmt.Errorf("%s: connections contain a cycle", at)
	}
	if w.Input != nil {
		if err := p.validateEntry(w, w.Input); err != nil {
			return err
		}
	}
	for i := range w.Placements {
		if err := p.validatePlacement(w, &w.Placements[i]); err != nil {
			return err
		}
	}
	for _, pl := range w.Placements {
		if w.isEndpoint(pl.Name) {
			if k, ok := w.outputKind(p, pl.Name); !ok || k != KindSingle {
				return fmt.Errorf("%s: endpoint %s must be Single", at, pl.Name)
			}
		}
	}
	return nil
}
