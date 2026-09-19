package suimon

import "fmt"

func (g Graph) Node(id string) *Node { return find(g.Nodes, func(n Node) bool { return n.ID == id }) }
func (g Graph) input(r PortRef) *Port {
	n := g.Node(r.Node)
	if n == nil {
		return nil
	}
	return find(n.Inputs, func(p Port) bool { return p.Name == r.Port })
}
func (g Graph) output(r PortRef) *Port {
	n := g.Node(r.Node)
	if n == nil {
		return nil
	}
	return find(n.Outputs, func(p Port) bool { return p.Name == r.Port })
}
func allKind(ps []Port, kind string) bool {
	return all(ps, func(p Port) bool { return p.Kind == kind })
}
func (n Node) shapeOK() bool {
	pi, po, si, so := allKind(n.Inputs, "plain"), allKind(n.Outputs, "plain"), allKind(n.Inputs, "stream"), allKind(n.Outputs, "stream")
	k := n.Kind
	b := k.Body
	bodyPlain := func() bool {
		return b != nil && all(b.Entries, func(r PortRef) bool { p := b.input(r); return p != nil && p.Kind == "plain" }) && all(b.Exits, func(r PortRef) bool { p := b.output(r); return p != nil && p.Kind == "plain" })
	}
	switch k.Type {
	case "leaf":
		return pi && !k.Retry.MaxAttempts.IsZero() && !k.Retry.LeaseSeconds.IsZero() && !k.Concurrency.IsZero()
	case "waitAll":
		return pi && po && len(n.Outputs) == 1
	case "coalesce":
		return pi && po && len(n.Inputs) > 0 && len(n.Outputs) == 1
	case "branch":
		return pi && po && len(n.Inputs) == 1 && len(k.Arms) > 0 && unique(k.Arms) && equal(k.Arms, mapped(n.Outputs, func(p Port) string { return p.Name }))
	case "loop":
		return pi && po && len(n.Inputs) == 1 && len(n.Outputs) == 1 && !k.MaxIterations.IsZero() && b != nil && len(b.Entries) == 1 && len(b.Exits) == 1 && bodyPlain()
	case "subworkflow":
		return pi && po && b != nil && len(n.Inputs) == len(b.Entries) && len(n.Outputs) == len(b.Exits) && bodyPlain()
	case "forEach":
		return si && so && len(n.Inputs) == 1 && len(n.Outputs) == 1 && b != nil && len(b.Entries) == 1 && len(b.Exits) == 1 && bodyPlain()
	case "collect":
		return si && po && len(n.Inputs) == 1 && len(n.Outputs) == 1
	case "filter":
		return si && so && len(n.Inputs) == 1 && len(n.Outputs) == 1
	case "merge":
		return si && so && len(n.Inputs) > 0 && len(n.Outputs) == 1
	}
	return false
}
func (g Graph) acyclic() bool {
	ns := mapped(g.Nodes, func(n Node) string { return n.ID })
	for fuel := len(ns); len(ns) > 0 && fuel > 0; fuel-- {
		roots := filter(ns, func(n string) bool {
			return !anyOf(g.Edges, func(e Edge) bool { return e.Dst.Node == n && contains(ns, e.Src.Node) })
		})
		if len(roots) == 0 {
			return false
		}
		ns = filter(ns, func(n string) bool { return !contains(roots, n) })
	}
	return len(ns) == 0
}
func (g Graph) rejoinsAt(target string, fuel int, src PortRef) bool {
	if fuel == 0 {
		return false
	}
	edges := filter(g.Edges, func(e Edge) bool { return e.Src == src })
	return !contains(g.Exits, src) && len(edges) > 0 && all(edges, func(e Edge) bool {
		if e.Dst.Node == target {
			return true
		}
		n := g.Node(e.Dst.Node)
		return n != nil && len(n.Outputs) > 0 && all(n.Outputs, func(p Port) bool { return g.rejoinsAt(target, fuel-1, PortRef{n.ID, p.Name}) })
	})
}
func (g Graph) branchesCoalesced() bool {
	return all(g.Nodes, func(n Node) bool {
		if n.Kind.Type != "branch" {
			return true
		}
		return anyOf(g.Nodes, func(join Node) bool {
			return join.Kind.Type == "coalesce" && all(n.Outputs, func(p Port) bool { return g.rejoinsAt(join.ID, len(g.Nodes), PortRef{n.ID, p.Name}) })
		})
	})
}

type condition = [2]string

func combineConditions(a, b []condition) ([]condition, bool) {
	c := append(append([]condition{}, a...), b...)
	out := []condition{}
	for _, x := range c {
		if !contains(out, x) {
			out = append(out, x)
		}
	}
	return out, all(out, func(x condition) bool {
		return all(out, func(y condition) bool { return x[0] != y[0] || x[1] == y[1] })
	})
}
func (g Graph) outputConditions(fuel int, src PortRef) ([]condition, bool) {
	if fuel == 0 {
		return nil, false
	}
	p := g.output(src)
	if p == nil || p.Kind != "plain" {
		return nil, false
	}
	n := g.Node(src.Node)
	if n == nil {
		return nil, false
	}
	input := func(node Node, p Port) ([]condition, bool) {
		r := PortRef{node.ID, p.Name}
		if contains(g.Entries, r) {
			return []condition{}, true
		}
		e := find(g.Edges, func(e Edge) bool { return e.Dst == r })
		if e == nil {
			return nil, false
		}
		return g.outputConditions(fuel-1, e.Src)
	}
	allInputs := func(node Node) ([]condition, bool) {
		required := []condition{}
		for _, p := range node.Inputs {
			c, ok := input(node, p)
			if !ok {
				return nil, false
			}
			required, ok = combineConditions(required, c)
			if !ok {
				return nil, false
			}
		}
		return required, true
	}
	switch n.Kind.Type {
	case "leaf", "waitAll", "loop", "subworkflow":
		return allInputs(*n)
	case "branch":
		if !contains(n.Kind.Arms, src.Port) {
			return nil, false
		}
		base, ok := allInputs(*n)
		if !ok {
			return nil, false
		}
		return combineConditions(base, []condition{{n.ID, src.Port}})
	case "collect":
		return []condition{}, true
	case "coalesce":
		if len(n.Inputs) == 0 {
			return nil, false
		}
		actual := [][]condition{}
		for _, p := range n.Inputs {
			c, ok := input(*n, p)
			if !ok {
				return nil, false
			}
			actual = append(actual, c)
		}
		for _, source := range g.Nodes {
			if source.Kind.Type != "branch" {
				continue
			}
			if !all(actual, func(c []condition) bool { return anyOf(c, func(x condition) bool { return x[0] == source.ID }) }) {
				continue
			}
			base, ok := allInputs(source)
			if !ok {
				continue
			}
			origins := []string{}
			valid := true
			for _, c := range actual {
				matches := []string{}
				for _, arm := range source.Kind.Arms {
					expected, _ := combineConditions(base, []condition{{source.ID, arm}})
					if len(c) == len(expected) && all(c, func(x condition) bool { return contains(expected, x) }) {
						matches = append(matches, arm)
					}
				}
				if len(matches) != 1 {
					valid = false
					break
				}
				origins = append(origins, matches[0])
			}
			if valid && unique(origins) && len(origins) == len(source.Kind.Arms) {
				return base, true
			}
		}
	}
	return nil, false
}

// Validate is the translation of Graph.validate, including the restrictions
// on exclusive Coalesce inputs and branches inside nested workflow bodies.
func (g Graph) Validate() error { return g.validate(false) }
func (g Graph) validate(body bool) error {
	if !unique(mapped(g.Nodes, func(n Node) string { return n.ID })) {
		return fmt.Errorf("duplicate node id")
	}
	if !unique(g.Entries) || !unique(g.Exits) {
		return fmt.Errorf("duplicate graph boundary")
	}
	if !g.acyclic() {
		return fmt.Errorf("graph contains a cycle")
	}
	if body && !g.branchesCoalesced() {
		return fmt.Errorf("body Branch must rejoin through Coalesce")
	}
	for _, n := range g.Nodes {
		if n.ID == "" || !unique(mapped(n.Inputs, func(p Port) string { return p.Name })) || !unique(mapped(n.Outputs, func(p Port) string { return p.Name })) || !all(append(append([]Port{}, n.Inputs...), n.Outputs...), func(p Port) bool { return p.Name != "" && (p.Kind == "plain" || p.Kind == "stream") }) {
			return fmt.Errorf("invalid port or node name")
		}
		if !n.shapeOK() {
			return fmt.Errorf("invalid port shape: %s", n.ID)
		}
		if n.Kind.Type == "coalesce" {
			if _, ok := g.outputConditions(len(g.Nodes)+1, PortRef{n.ID, n.Outputs[0].Name}); !ok {
				return fmt.Errorf("Coalesce inputs must correspond to distinct arms of one Branch: %s", n.ID)
			}
		}
		for _, p := range n.Inputs {
			r := PortRef{n.ID, p.Name}
			count := len(filter(g.Edges, func(e Edge) bool { return e.Dst == r }))
			if contains(g.Entries, r) {
				count++
			}
			if count != 1 {
				return fmt.Errorf("input must have exactly one source: %s.%s", n.ID, p.Name)
			}
		}
		if n.Kind.Body != nil {
			if err := n.Kind.Body.validate(true); err != nil {
				return err
			}
		}
	}
	for _, e := range g.Edges {
		a, b := g.output(e.Src), g.input(e.Dst)
		if a == nil || b == nil {
			return fmt.Errorf("edge references an unknown port")
		}
		if a.Kind != b.Kind {
			return fmt.Errorf("edge port kinds differ")
		}
	}
	for _, r := range g.Entries {
		if g.input(r) == nil {
			return fmt.Errorf("unknown entry port")
		}
	}
	for _, r := range g.Exits {
		if g.output(r) == nil {
			return fmt.Errorf("unknown exit port")
		}
	}
	return nil
}

// ParseGraph rejects missing and additional fields before validating the graph.
func ParseGraph(data []byte) (Graph, error) {
	var g Graph
	if err := decodeCanonical(data, &g); err != nil {
		return g, err
	}
	return g, g.Validate()
}
