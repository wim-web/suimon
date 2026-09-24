package suimon

import (
	"math"
	"reflect"
	"testing"
)

// Ported from Test/Validate.lean.

func accepted(t *testing.T, label string, p *Definition) {
	t.Helper()
	if err := p.Validate(); err != nil {
		t.Errorf("%s: expected a valid definition, got: %v", label, err)
	}
}

func rejected(t *testing.T, label, fragment string, p *Definition) {
	t.Helper()
	err := p.Validate()
	if err == nil {
		t.Errorf("%s: accepted, expected an error with %q", label, fragment)
	} else if !hasFragment(err.Error(), fragment) {
		t.Errorf("%s: expected %q, got: %v", label, fragment, err)
	}
}

func decodeRejected(t *testing.T, label, fragment, text string) {
	t.Helper()
	_, err := ParseDefinition([]byte(text))
	if err == nil {
		t.Errorf("%s: decoded, expected an error with %q", label, fragment)
	} else if !hasFragment(err.Error(), fragment) {
		t.Errorf("%s: expected %q, got: %v", label, fragment, err)
	}
}

type placementKind struct {
	name string
	kind string
}

// kinds lists the derived kind of each placement, "none" where it cannot be derived.
func kinds(p *Definition, id string) []placementKind {
	w, ok := p.workflow(id)
	if !ok {
		return nil
	}
	var out []placementKind
	table := w.deriveKinds(p)
	for _, pl := range w.Placements {
		kind := "none"
		if k, ok := table.outputKind(pl.Name); ok {
			kind = k.String()
		}
		out = append(out, placementKind{pl.Name, kind})
	}
	return out
}

func cycleDefinition() *Definition {
	return &Definition{
		Main:       "loop",
		Functions:  []FunctionDecl{{ID: "step", Input: ptr(Named("A")), Output: Contract{KindSingle, Named("A")}}},
		Transforms: []TransformDecl{{ID: "a", Input: Named("A"), Output: Named("A")}},
		Workflows: []Workflow{{
			ID: "loop",
			Placements: []Placement{
				{Name: "x", Control: CallControl{FunctionBody("step")}, Policy: PolicyStop},
				{Name: "y", Control: CallControl{FunctionBody("step")}, Policy: PolicyStop},
			},
			Connections: []Connection{
				{Source: "x", Target: "y", Transform: Declared("a")},
				{Source: "y", Target: "x", Transform: Declared("a")},
			},
		}},
	}
}

// standalone is a concurrency without input, whose only task takes no input either.
func standalone(input *TransformRef) *Definition {
	return &Definition{
		Main:       "w",
		Functions:  []FunctionDecl{{ID: "loadConfig", Output: Contract{KindSingle, Named("Config")}}},
		Transforms: []TransformDecl{{ID: "config", Input: Named("Config"), Output: Named("Config")}},
		Workflows: []Workflow{{
			ID: "w",
			Placements: []Placement{{
				Name:   "c",
				Policy: PolicyStop,
				Control: ConcurrencyControl{Concurrency{
					Limit:   1,
					Output:  CollectList,
					Element: Named("Config"),
					Tasks: []TaskSpec{{Name: "config", Body: FunctionBody("loadConfig"), Input: input,
						Output: ptr("config"), Policy: PolicyStop}},
				}},
			}},
		}},
	}
}

func TestValidateDefinitions(t *testing.T) {
	for _, name := range append(definitionNames, extraDefinitions...) {
		p := load(t, name)
		accepted(t, name, p)
		data, err := p.MarshalJSON()
		if err != nil {
			t.Fatal(err)
		}
		q, err := ParseDefinition(data)
		if err != nil {
			t.Fatalf("%s: JSON round trip failed: %v", name, err)
		}
		if !reflect.DeepEqual(p, q) {
			t.Errorf("%s: JSON round trip changed the definition", name)
		}
	}
}

func TestDerivedKinds(t *testing.T) {
	check := func(label string, got, want []placementKind) {
		t.Helper()
		if !reflect.DeepEqual(got, want) {
			t.Errorf("%s: got %v, want %v", label, got, want)
		}
	}
	check("users: Stream input to a List concurrency is a Stream of lists", kinds(load(t, "users"), "users"),
		[]placementKind{{"fetchAllUsers", "stream"}, {"perUser", "stream"}, {"all", "single"}})
	check("branch: a branch keeps its input kind", kinds(load(t, "branch"), "shipping"),
		[]placementKind{{"list", "stream"}, {"paid", "stream"}, {"ship", "stream"}, {"receipts", "single"}})
	check("merge: Merge of Singles is Single, and a discard connection from a Single is Single",
		kinds(load(t, "merge"), "dashboard"),
		[]placementKind{{"sales", "single"}, {"stock", "single"}, {"widgets", "single"}, {"page", "single"},
			{"archive", "single"}, {"notify", "single"}})
	users := load(t, "users")
	got, ok := users.resultType(ConcurrencyControl{Concurrency{Limit: 1, Output: CollectList, Element: Named("T")}})
	if !ok || got != ListOf(Named("T")) {
		t.Errorf("a List concurrency produces List<T>, got %v", got)
	}
}

func TestValidateNamesAndReferences(t *testing.T) {
	rejected(t, "duplicate placement", "duplicate placement name", mapWorkflow(load(t, "merge"), "dashboard",
		func(w *Workflow) { w.Placements = append(w.Placements, w.Placements[0]) }))
	merge := load(t, "merge")
	merge.Main = "nope"
	rejected(t, "unknown main", "unknown main workflow nope", merge)
	rejected(t, "unknown transform", "unknown transform nope", mapWorkflow(load(t, "merge"), "dashboard",
		mapConnection("sales", "archive", func(c *Connection) { c.Transform = Declared("nope") })))
	rejected(t, "unknown output endpoint", "fetch is not an endpoint of workflow profileFlow",
		mapWorkflow(load(t, "users"), "users", mapPlacement("perUser", mapConcurrency(mapTask("profile",
			func(task *TaskSpec) { task.Body = WorkflowBody("profileFlow", "fetch") })))))
}

func TestValidateRepresentable(t *testing.T) {
	// What a Go definition can hold but a Lean one cannot is rejected before any shared check.
	merge := load(t, "merge")
	merge.Main = "d\xffashboard"
	rejected(t, "invalid UTF-8", `the name "d\xffashboard" is not valid UTF-8`, merge)
	merge = load(t, "merge")
	merge.Transforms[0].Output.Lists = -1
	rejected(t, "negative list depth", "has a negative number of List wrappers", merge)
}

func TestValidateTypes(t *testing.T) {
	rejected(t, "transform input", "takes Stock, but sales produces Sales", mapWorkflow(load(t, "merge"), "dashboard",
		mapConnection("sales", "archive", func(c *Connection) { c.Transform = Declared("stockWidget") })))
	rejected(t, "transform output", "returns Widget, but archive takes Sales", mapWorkflow(load(t, "merge"), "dashboard",
		mapConnection("sales", "archive", func(c *Connection) { c.Transform = Declared("salesWidget") })))
	rejected(t, "entry type", "the input type Org does not match", mapWorkflow(load(t, "users"), "users",
		func(w *Workflow) { w.Input = &Entry{Type: Named("Org"), Placement: "fetchAllUsers"} }))
	rejected(t, "task input transform", "an input transform is required", mapWorkflow(load(t, "users"), "users",
		mapPlacement("perUser", mapConcurrency(mapTask("orders", func(task *TaskSpec) { task.Input = nil })))))
	rejected(t, "task output transform", "takes Profile, but the body produces Orders",
		mapWorkflow(load(t, "users"), "users", mapPlacement("perUser", mapConcurrency(mapTask("orders",
			func(task *TaskSpec) { task.Output = ptr("profileSummary") })))))
}

func TestValidateInputs(t *testing.T) {
	rejected(t, "two inputs", "archive: needs exactly one input", mapWorkflow(load(t, "merge"), "dashboard",
		func(w *Workflow) {
			for _, c := range w.Connections {
				if c.Target == "archive" {
					w.Connections = append(w.Connections, c)
				}
			}
		}))
	rejected(t, "missing input", "archive: needs exactly one input", mapWorkflow(load(t, "merge"), "dashboard",
		func(w *Workflow) { dropConnection(w, "sales", "archive") }))
	rejected(t, "input to a node without input", "stock takes no input", mapWorkflow(load(t, "merge"), "dashboard",
		func(w *Workflow) {
			w.Connections = append(w.Connections, Connection{Source: "sales", Target: "stock", Transform: Declared("sales")})
		}))
	rejected(t, "Merge entry", "Merge cannot be the entry", mapWorkflow(load(t, "merge"), "dashboard",
		func(w *Workflow) { w.Input = &Entry{Type: Named("Widget"), Placement: "widgets"} }))
}

// discard: a target without input runs once per value it receives, without the value.
func TestValidateDiscard(t *testing.T) {
	ticks := mapWorkflow(load(t, "branch"), "shipping", func(w *Workflow) {
		w.Placements = append(w.Placements,
			Placement{Name: "tick", Control: CallControl{FunctionBody("tick")}, Policy: PolicyContinue},
			Placement{Name: "ticks", Control: WaitStreamControl{Named("Tick")}, Policy: PolicyStop})
		w.Connections = append(w.Connections,
			Connection{Source: "ship", Target: "tick", Transform: Discard},
			Connection{Source: "tick", Target: "ticks", Transform: Declared("tick")})
	})
	ticks.Functions = append(ticks.Functions, FunctionDecl{ID: "tick", Output: Contract{KindSingle, Named("Tick")}})
	ticks.Transforms = append(ticks.Transforms, TransformDecl{ID: "tick", Input: Named("Tick"), Output: Named("Tick")})
	accepted(t, "discard from a Stream", ticks)
	if k, ok := ticks.OutputKind("shipping", "tick"); !ok || k != KindStream {
		t.Error("discard keeps the Stream kind")
	}
	rejected(t, "discard to a node with input", "discard passes no value, but archive takes Sales",
		mapWorkflow(load(t, "merge"), "dashboard",
			mapConnection("sales", "archive", func(c *Connection) { c.Transform = Discard })))
	rejected(t, "two discard connections", "notify: accepts at most one connection",
		mapWorkflow(load(t, "merge"), "dashboard", func(w *Workflow) {
			w.Connections = append(w.Connections, Connection{Source: "stock", Target: "notify", Transform: Discard})
		}))
	configTask := func(input *TransformRef) *Definition {
		p := mapWorkflow(load(t, "users"), "users", mapPlacement("perUser", mapConcurrency(func(c *Concurrency) {
			c.Tasks = append(c.Tasks, TaskSpec{Name: "config", Body: FunctionBody("loadConfig"), Input: input,
				Policy: PolicyContinue})
		})))
		p.Functions = append(p.Functions, FunctionDecl{ID: "loadConfig", Output: Contract{KindSingle, Named("Config")}})
		return p
	}
	accepted(t, "task without input discards the concurrency input", configTask(&Discard))
	rejected(t, "task without input and without discard", "the input transform must be discard", configTask(nil))
	accepted(t, "task without input in a concurrency without input", standalone(nil))
	rejected(t, "discard without concurrency input", "the concurrency has no input to discard", standalone(&Discard))
	merge := load(t, "merge")
	merge.Transforms = append(merge.Transforms, TransformDecl{ID: "discard", Input: Named("A"), Output: Named("A")})
	rejected(t, "declared discard", "discard is provided by the library and cannot be declared", merge)
}

func TestValidateGraph(t *testing.T) {
	rejected(t, "cycle", "connections contain a cycle", cycleDefinition())
	rejected(t, "recursive call", "workflows call each other in a cycle", mapWorkflow(load(t, "users"), "profileFlow",
		mapPlacement("format", func(pl *Placement) { pl.Control = CallControl{WorkflowBody("profileFlow", "format")} })))
	rejected(t, "waitStream on Single", "waitStream needs a Stream input", mapWorkflow(load(t, "merge"), "dashboard",
		mapPlacement("page", func(pl *Placement) { pl.Control = WaitStreamControl{ListOf(Named("Widget"))} })))
	rejected(t, "Merge of Stream", "Merge accepts only Single inputs (ship)", mapWorkflow(load(t, "branch"), "shipping",
		mapPlacement("receipts", func(pl *Placement) { pl.Control = MergeControl{Named("Receipt")} })))
	rejected(t, "Stream endpoint", "endpoint ship must be Single", mapWorkflow(load(t, "branch"), "shipping",
		func(w *Workflow) {
			dropConnection(w, "ship", "receipts")
			var kept []Placement
			for _, pl := range w.Placements {
				if pl.Name != "receipts" {
					kept = append(kept, pl)
				}
			}
			w.Placements = kept
		}))
}

func TestValidateBranchArms(t *testing.T) {
	rejected(t, "no connected arm", "at least one arm needs a connection", mapWorkflow(load(t, "branch"), "shipping",
		func(w *Workflow) { dropConnection(w, "paid", "ship") }))
	rejected(t, "unknown arm", "unknown arm refunded", mapWorkflow(load(t, "branch"), "shipping",
		mapConnection("paid", "ship", func(c *Connection) { c.Arm = ptr("refunded") })))
	rejected(t, "missing arm", "a connection from a branch needs an arm", mapWorkflow(load(t, "branch"), "shipping",
		mapConnection("paid", "ship", func(c *Connection) { c.Arm = nil })))
	rejected(t, "arm outside a branch", "only a connection from a branch has an arm",
		mapWorkflow(load(t, "merge"), "dashboard",
			mapConnection("sales", "archive", func(c *Connection) { c.Arm = ptr("x") })))
	// A branch without connections, which is not the entry, reaches the check of its placement.
	rejected(t, "unknown judge", "shipping.orphan: unknown judge nope",
		mapWorkflow(load(t, "branch"), "shipping", func(w *Workflow) {
			w.Placements = append(w.Placements, Placement{Name: "orphan", Control: BranchControl{Judge: "nope", Arms: []string{"a"}},
				Policy: PolicyStop})
		}))
}

func TestValidateSettings(t *testing.T) {
	rejected(t, "zero limit", "limit must be positive", mapWorkflow(load(t, "users"), "users",
		mapPlacement("perUser", mapConcurrency(func(c *Concurrency) { c.Limit = 0 }))))
	rejected(t, "no task in the output", "at least one task must be in the output",
		mapWorkflow(load(t, "users"), "users", mapPlacement("perUser", mapConcurrency(func(c *Concurrency) {
			for i := range c.Tasks {
				c.Tasks[i].Output = nil
			}
		}))))
	accepted(t, "Merge with one input", mapWorkflow(load(t, "merge"), "dashboard", func(w *Workflow) {
		var placements []Placement
		for _, pl := range w.Placements {
			if pl.Name != "stock" {
				placements = append(placements, pl)
			}
		}
		var connections []Connection
		for _, c := range w.Connections {
			if c.Source != "stock" {
				connections = append(connections, c)
			}
		}
		w.Placements, w.Connections = placements, connections
	}))
	rejected(t, "timeout on waitStream", "a timeout is only for a function call or a branch judge",
		mapWorkflow(load(t, "users"), "users",
			mapPlacement("all", func(pl *Placement) { pl.Timeout = Timeout{CallMs: ptr[uint64](10)} })))
	rejected(t, "element timeout on Single", "an element timeout is only for a Stream function",
		mapWorkflow(load(t, "merge"), "dashboard",
			mapPlacement("sales", func(pl *Placement) { pl.Timeout = Timeout{ElementMs: ptr[uint64](10)} })))
	rejected(t, "zero timeout", "a timeout must be positive", mapWorkflow(load(t, "branch"), "shipping",
		mapPlacement("paid", func(pl *Placement) { pl.Timeout = Timeout{CallMs: ptr[uint64](0)} })))
}

// What the definition file can express, for a definition built in code: identifiers and type names are
// not empty. Validation rejects the others with the messages of the Lean tests, and their canonical
// form does not decode. Placements without connections reach the checks of their placement. The Lean
// tests also reject a limit or a timeout above 2^64-1, which a uint64 cannot hold.
func TestValidateUnexpressible(t *testing.T) {
	orphan := func(p *Definition, control Control) *Definition {
		return mapWorkflow(p, p.Main, func(w *Workflow) {
			w.Placements = append(w.Placements, Placement{Name: "orphan", Control: control, Policy: PolicyStop})
		})
	}
	with := func(p *Definition, f func(*Definition)) *Definition { f(p); return p }
	// loadConfig is a concurrency whose task runs loadConfig of standalone, changed by f.
	loadConfig := func(f func(*Concurrency)) Control {
		c := Concurrency{Limit: 1, Output: CollectList, Element: Named("Config"),
			Tasks: []TaskSpec{{Name: "config", Body: FunctionBody("loadConfig"), Output: ptr("config"), Policy: PolicyStop}}}
		f(&c)
		return ConcurrencyControl{c}
	}
	cases := []struct {
		label, want string
		p           *Definition
	}{
		{"empty function id", "empty function id", with(load(t, "merge"), func(p *Definition) {
			p.Functions = append(p.Functions, FunctionDecl{Output: Contract{KindSingle, Named("T")}})
		})},
		{"empty judge id", "empty judge id", with(load(t, "branch"), func(p *Definition) {
			p.Judges = append(p.Judges, JudgeDecl{Input: Named("T")})
		})},
		{"empty transform id", "empty transform id", with(load(t, "merge"), func(p *Definition) {
			p.Transforms = append(p.Transforms, TransformDecl{Input: Named("T"), Output: Named("T")})
		})},
		{"function type", "function f: empty type name", with(load(t, "merge"), func(p *Definition) {
			p.Functions = append(p.Functions, FunctionDecl{ID: "f", Input: ptr(Named("")), Output: Contract{KindSingle, Named("T")}})
		})},
		{"function output type", "function f: empty type name", with(load(t, "merge"), func(p *Definition) {
			p.Functions = append(p.Functions, FunctionDecl{ID: "f", Output: Contract{KindStream, ListOf(Named(""))}})
		})},
		{"judge type", "judge j: empty type name", with(load(t, "branch"), func(p *Definition) {
			p.Judges = append(p.Judges, JudgeDecl{ID: "j", Input: ListOf(Named(""))})
		})},
		{"transform type", "transform t: empty type name", with(load(t, "merge"), func(p *Definition) {
			p.Transforms = append(p.Transforms, TransformDecl{ID: "t", Input: Named("T"), Output: Named("")})
		})},
		{"entry type", "users: entry fetchAllUsers: empty type name", mapWorkflow(load(t, "users"), "users",
			func(w *Workflow) { w.Input = &Entry{Type: Named(""), Placement: "fetchAllUsers"} })},
		{"waitStream element", "shipping.orphan: empty type name", orphan(load(t, "branch"), WaitStreamControl{Named("")})},
		{"Merge element", "shipping.orphan: empty type name", orphan(load(t, "branch"), MergeControl{ListOf(Named(""))})},
		{"concurrency element", "w.orphan: empty type name", orphan(standalone(nil),
			loadConfig(func(c *Concurrency) { c.Element = Named("") }))},
		{"concurrency input", "w.orphan: empty type name", orphan(standalone(nil),
			loadConfig(func(c *Concurrency) { c.Input = ptr(Named("")) }))},
	}
	for _, c := range cases {
		if err := c.p.Validate(); err == nil || err.Error() != c.want {
			t.Errorf("%s: got %v, want %q", c.label, err, c.want)
		}
		data, err := c.p.MarshalJSON()
		if err != nil {
			t.Fatal(err)
		}
		if _, err := ParseDefinition(data); err == nil {
			t.Errorf("%s: the canonical form decoded", c.label)
		}
	}
	recordable := func(label string, p *Definition) {
		t.Helper()
		accepted(t, label, p)
		data, err := p.MarshalJSON()
		if err != nil {
			t.Fatal(err)
		}
		if q, err := ParseDefinition(data); err != nil || !reflect.DeepEqual(p, q) {
			t.Errorf("%s: the canonical form reads back as %+v, %v", label, q, err)
		}
	}
	recordable("largest numbers", mapWorkflow(load(t, "users"), "users", mapPlacement("perUser", mapConcurrency(
		func(c *Concurrency) {
			c.Limit = math.MaxUint64
			mapTask("orders", func(task *TaskSpec) { task.Timeout = Timeout{CallMs: ptr[uint64](math.MaxUint64)} })(c)
		}))))
	// A function or judge may be named discard; only a transform may not.
	discardFunction := standalone(nil)
	discardFunction.Functions = []FunctionDecl{{ID: DiscardName, Output: Contract{KindSingle, Named("Config")}}}
	recordable("discard as a function", mapWorkflow(discardFunction, "w", mapPlacement("c", mapConcurrency(
		mapTask("config", func(task *TaskSpec) { task.Body = FunctionBody(DiscardName) })))))
}

func TestDecodeRejections(t *testing.T) {
	base := `{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"merge","element":"T"}`
	decodeRejected(t, "unknown field", "unknown field retries", base+`,"policy":"stop","retries":1}]}]}`)
	decodeRejected(t, "missing policy", "missing field policy", base+`}]}]}`)
	decodeRejected(t, "unknown policy", "policy is stop or continue", base+`,"policy":"retry"}]}]}`)
}

// Exact messages, where the Lean tests above only look for a fragment.
func TestValidateMessages(t *testing.T) {
	cases := []struct {
		label, want string
		p           *Definition
	}{
		{"two inputs", "dashboard.archive: needs exactly one input", mapWorkflow(load(t, "merge"), "dashboard",
			func(w *Workflow) { dropConnection(w, "sales", "archive") })},
		{"unknown arm", "shipping: connection paid -> ship: unknown arm refunded", mapWorkflow(load(t, "branch"), "shipping",
			mapConnection("paid", "ship", func(c *Connection) { c.Arm = ptr("refunded") }))},
		{"task output", "users.perUser task orders: transform profileSummary takes Profile, but the body produces Orders",
			mapWorkflow(load(t, "users"), "users", mapPlacement("perUser", mapConcurrency(mapTask("orders",
				func(task *TaskSpec) { task.Output = ptr("profileSummary") }))))},
		{"list type", "dashboard.page: waitStream needs a Stream input", mapWorkflow(load(t, "merge"), "dashboard",
			mapPlacement("page", func(pl *Placement) { pl.Control = WaitStreamControl{ListOf(Named("Widget"))} }))},
		{"entry", "users: entry fetchAllUsers: the input type List<List<Org>> does not match the placement",
			mapWorkflow(load(t, "users"), "users", func(w *Workflow) {
				w.Input = &Entry{Type: ListOf(ListOf(Named("Org"))), Placement: "fetchAllUsers"}
			})},
	}
	for _, c := range cases {
		err := c.p.Validate()
		if err == nil || err.Error() != c.want {
			t.Errorf("%s: got %v, want %q", c.label, err, c.want)
		}
	}
}

func TestDecodeMessages(t *testing.T) {
	cases := []struct{ text, want string }{
		{``, "offset 0: unexpected end of input"},
		{`[1,]`, "offset 3: unexpected input"},
		{`{"a":1,}`, `offset 7: expected "`},
		{`"\x"`, `offset 3: illegal \u escape`},
		{`tru`, "offset 0: expected: true"},
		{`-a`, "offset 1: expected 1-9"},
		{`01`, "offset 1: expected end of input"},
		{`1.`, "offset 2: unexpected end of input"},
		{`[1 2]`, "offset 4: unexpected character in array"},
		{`{"a" 1}`, "offset 5: expected :"},
		{`"é\u00zz"`, "offset 8: invalid hex character"},
		{"\"a\u0001\"", "offset 3: unexpected character in string"},
		{`1e99999999999999999999`, "offset 22: exp too large"},
		{`[]`, "definition: expected an object"},
		{`{"main":"w","workflows":[],"b":1,"a":2}`, "definition: unknown field a"},
		{`{"main":""}`, "definition.main: empty string"},
		{`{"main":"w","workflows":{}}`, "definition.workflows: expected an array"},
		{`{"main":"w","functions":[{"id":"f","output":{"single":"A","stream":"B"}}]}`,
			"functions.f.output: an output contract is either single or stream"},
		{`{"main":"w","functions":[{"id":"f","output":{"single":{"list":{"lst":"A"}}}}]}`,
			"functions.f.output.single: unknown field lst"},
		{`{"main":"w","functions":[{"id":"f","output":{"single":7}}]}`,
			`functions.f.output.single: a type is a name or {"list": type}`},
		{`{"main":"w","judges":[{"id":"j"}]}`, "judges: missing field input"},
		{`{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":5}]}]}`,
			"workflows.w.placements.a.node: missing field type"},
		{`{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","node":{"type":"loop"}}]}]}`,
			"workflows.w.placements.a.node: unknown node type loop"},
		{`{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","policy":"stop","node":{"type":"concurrency","limit":2.5}}]}]}`,
			"workflows.w.placements.a.node.limit: expected a natural number"},
		{`{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","policy":"stop","node":{"type":"concurrency","tasks":[]}}]}]}`,
			"workflows.w.placements.a.node: missing field limit"},
		{`{"main":"w","workflows":[{"id":"w","placements":[{"name":"a","policy":"stop","timeout":{"callMs":-1},"node":{"type":"merge","element":"T"}}]}]}`,
			"workflows.w.placements.a.timeout.callMs: expected a natural number"},
		{`{"main":"w","workflows":[{"id":"w","input":{"type":"T"},"placements":[]}]}`,
			"workflows.w.input: missing field placement"},
		{`{"main":"w","workflows":[{"id":"w","connections":[{"source":"a","target":"b","transform":"t","arm":null}]}]}`,
			"workflows.w.connections.arm: expected a string"},
	}
	for _, c := range cases {
		_, err := ParseDefinition([]byte(c.text))
		if err == nil || err.Error() != c.want {
			t.Errorf("%s: got %v, want %q", c.text, err, c.want)
		}
	}
}

func TestDecodeNumbers(t *testing.T) {
	// A natural number is read by its value, whatever the notation. Above 2^64-1 it is large, also
	// when the value is only reached after the trailing zeros are stripped.
	cases := map[string]uint64{"2": 2, "2e0": 2, "-0": 0, "0.2e1": 2, "1E+1": 10, "0e999": 0,
		"2.0": 2, "20e-1": 2, "1.50e1": 15, "100e-2": 1, "0.0": 0, "-0.0": 0, "0e-99999999999999999999": 0,
		"1.00000000000000000000e1": 10, "20000000000000000000000e-20": 200,
		"18446744073709551615": ^uint64(0), "1.8446744073709551615e19": ^uint64(0)}
	for text, want := range cases {
		v, err := parseLeanJSON(text)
		if err != nil {
			t.Fatalf("%s: %v", text, err)
		}
		if n, ok, large := v.num.nat(); !ok || large || n != want {
			t.Errorf("%s: got %d %v %v, want %d", text, n, ok, large, want)
		}
	}
	for _, text := range []string{"1e20", "18446744073709551616", "18446744073709551616.0", "7e100", "1e1000000000"} {
		v, err := parseLeanJSON(text)
		if err != nil {
			t.Fatalf("%s: %v", text, err)
		}
		if _, ok, large := v.num.nat(); !ok || !large {
			t.Errorf("%s: got ok %v large %v, want a large natural number", text, ok, large)
		}
	}
	for _, text := range []string{"2.5", "-1", "-10e-1", "1e-1", "0.5", "1e-1000000000", "1e-99999999999999999999"} {
		v, err := parseLeanJSON(text)
		if err != nil {
			t.Fatalf("%s: %v", text, err)
		}
		if _, ok, _ := v.num.nat(); ok {
			t.Errorf("%s: accepted as a natural number", text)
		}
	}
	// 0.0 is 0, which validation rejects.
	p, err := ParseDefinition([]byte(`{"main":"w","workflows":[{"id":"w","placements":[{"name":"c","policy":"stop",` +
		`"node":{"type":"concurrency","limit":0.0,"tasks":[],"output":"list","element":"T"}}]}]}`))
	if err != nil {
		t.Fatal(err)
	}
	if err := p.Validate(); err == nil || err.Error() != "w.c: limit must be positive" {
		t.Errorf("limit 0.0: %v", err)
	}
}

func TestLeanJSONStrings(t *testing.T) {
	cases := map[string]string{
		`"\ud83d\ude00"`: "\U0001F600",
		`"\ud83dx"`:      "\uFFFDx",
		`"\ude00"`:       "\uFFFD",
		`"\ud83d\u0041"`: "\uFFFDA",
		`"a\/b\n"`:       "a/b\n",
	}
	for text, want := range cases {
		v, err := parseLeanJSON(text)
		if err != nil || v.str != want {
			t.Errorf("%s: got %q %v, want %q", text, v.str, err, want)
		}
	}
	// Objects keep their fields in key order.
	v, err := parseLeanJSON(`{"b":1,"a":"x"}`)
	if err != nil || len(v.fields) != 2 || v.fields[0].key != "a" || v.fields[0].value.str != "x" || v.fields[1].key != "b" {
		t.Errorf("tree map: %+v %v", v.fields, err)
	}
	// An object may not repeat a key, compared after its escapes are decoded; the error is right after
	// the repeated key, at a byte offset, with the key quoted as Lean's String.quote does.
	for text, want := range map[string]string{
		`{"b":1,"a":2,"b":"x"}`:                     `offset 16: duplicate key "b"`,
		`{"é":1,"\u00e9":2}`:                        `offset 16: duplicate key "é"`,
		`{"a":[{"b":{"c":1,"c":2}}]}`:               `offset 21: duplicate key "c"`,
		`{"\u0001":1,"\u0001":2}`:                   `offset 20: duplicate key "\x01"`,
		`{"'":1,"'":2}`:                             `offset 10: duplicate key "'"`,
		`{"a":1,"a":2,}`:                            `offset 10: duplicate key "a"`,
		`{"a":{"a":1},"b":[{"a":1},{"a":2}],"a":3}`: `offset 38: duplicate key "a"`,
	} {
		if _, err := parseLeanJSON(text); err == nil || err.Error() != want {
			t.Errorf("%s: got %v, want %q", text, err, want)
		}
	}
	if _, err := parseLeanJSON(`{"a":{"a":1},"b":[{"a":1},{"a":2}]}`); err != nil {
		t.Errorf("the same key in other objects: %v", err)
	}
}
