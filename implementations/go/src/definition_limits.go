package suimon

import "fmt"

// Resource limits are shared with Suimon/Limits.lean. They apply before semantic
// validation, including to definitions constructed in code. Work is a conservative
// estimate of the reference validator's list scans, independent of semantic fuel.
const (
	MaxDefinitionBytes               = 1 << 20
	MaxDefinitionJSONDepth           = 64
	MaxDefinitionTypeDepth           = 32
	MaxDefinitionNameBytes           = 256
	MaxDefinitionWorkflows           = 128
	MaxDefinitionDeclarations        = 1024
	MaxDefinitionPlacements          = 1024
	MaxDefinitionConnections         = 4096
	MaxDefinitionTasks               = 1024
	MaxDefinitionArms                = 1024
	MaxValidationWork         uint64 = 1_000_000_000
)

func resourceLimit(name string, count, limit uint64) error {
	if count > limit {
		return fmt.Errorf("definition: %s limit exceeded (max %d)", name, limit)
	}
	return nil
}

// checkDefinitionText runs before recursive JSON parsing. Brackets in strings,
// including escaped quotes and backslashes, do not count toward nesting.
func checkDefinitionText(data []byte) error {
	return checkDefinitionTextWithin(data, MaxDefinitionBytes, MaxDefinitionJSONDepth)
}

func checkDefinitionTextWithin(data []byte, bytes, nesting uint64) error {
	if err := resourceLimit("byte", uint64(len(data)), bytes); err != nil {
		return err
	}
	depth := 0
	quoted, escaped := false, false
	for _, c := range data {
		if quoted {
			if escaped {
				escaped = false
			} else if c == '\\' {
				escaped = true
			} else if c == '"' {
				quoted = false
			}
		} else {
			switch c {
			case '"':
				quoted = true
			case '{', '[':
				depth++
				if err := resourceLimit("JSON depth", uint64(depth), nesting); err != nil {
					return err
				}
			case '}', ']':
				if depth > 0 {
					depth--
				}
			}
		}
	}
	return nil
}

func (p *Definition) checkResources() error {
	var bad error
	check := func(name string, n, max uint64) {
		if bad == nil {
			bad = resourceLimit(name, n, max)
		}
	}
	text := func(s string) { check("name byte", uint64(len(s)), MaxDefinitionNameBytes) }
	typ := func(t ValueType) {
		if t.Lists > MaxDefinitionTypeDepth {
			check("type depth", uint64(t.Lists), MaxDefinitionTypeDepth)
		}
		text(t.Name)
	}
	optType := func(t *ValueType) {
		if t != nil {
			typ(*t)
		}
	}
	body := func(b Body) {
		text(b.ID)
		text(b.Output)
	}
	ref := func(r TransformRef) {
		text(r.ID)
	}
	wc := uint64(len(p.Workflows))
	decls := uint64(len(p.Functions)) + uint64(len(p.Judges)) + uint64(len(p.Transforms))
	check("workflow", wc, MaxDefinitionWorkflows)
	check("declaration", decls, MaxDefinitionDeclarations)
	if bad != nil {
		return bad
	}
	text(p.Main)
	for _, f := range p.Functions {
		text(f.ID)
		optType(f.Input)
		typ(f.Output.Type)
	}
	for _, j := range p.Judges {
		text(j.ID)
		typ(j.Input)
	}
	for _, t := range p.Transforms {
		text(t.ID)
		typ(t.Input)
		typ(t.Output)
	}
	if bad != nil {
		return bad
	}
	var placements, connections, tasks, arms uint64
	for _, w := range p.Workflows {
		placements += uint64(len(w.Placements))
		connections += uint64(len(w.Connections))
		check("placement", placements, MaxDefinitionPlacements)
		check("connection", connections, MaxDefinitionConnections)
		if bad != nil {
			return bad
		}
		text(w.ID)
		if w.Input != nil {
			typ(w.Input.Type)
			text(w.Input.Placement)
		}
		for _, pl := range w.Placements {
			text(pl.Name)
			switch c := pl.Control.(type) {
			case CallControl:
				body(c.Body)
			case BranchControl:
				text(c.Judge)
				arms += uint64(len(c.Arms))
				check("arm", arms, MaxDefinitionArms)
				if bad != nil {
					return bad
				}
				for _, a := range c.Arms {
					text(a)
				}
			case WaitStreamControl:
				typ(c.Element)
			case MergeControl:
				typ(c.Element)
			case ConcurrencyControl:
				optType(c.Spec.Input)
				typ(c.Spec.Element)
				tasks += uint64(len(c.Spec.Tasks))
				check("task", tasks, MaxDefinitionTasks)
				if bad != nil {
					return bad
				}
				for _, t := range c.Spec.Tasks {
					text(t.Name)
					body(t.Body)
					if t.Input != nil {
						ref(*t.Input)
					}
					if t.Output != nil {
						text(*t.Output)
					}
				}
			}
			if bad != nil {
				return bad
			}
		}
		for _, c := range w.Connections {
			text(c.Source)
			text(c.Target)
			ref(c.Transform)
			if c.Arm != nil {
				text(*c.Arm)
			}
		}
		if bad != nil {
			return bad
		}
	}
	// All operands have been capped above; these products fit in uint64 even
	// on a 32-bit host. Include repeated kind queries, Kahn scans, nested body
	// lookups, duplicate checks and branch scans in the Lean reference.
	d := decls + wc
	n := d + placements + connections + tasks + arms + 1
	work := n*n + wc*wc*wc*(placements+tasks+1)
	for _, w := range p.Workflows {
		v, e := uint64(len(w.Placements)), uint64(len(w.Connections))
		work += (2*v + 2*e + 1) * (v + 1) * (v*(v+e+d+1) + e)
		work += v * v * (v*e + v)
		work += (e + tasks + v + 1) * (wc + 1) * (wc + placements + d + 1)
	}
	work += arms * connections
	return resourceLimit("validation work", work, MaxValidationWork)
}
