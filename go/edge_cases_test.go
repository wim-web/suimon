package suimon

import (
	"encoding/json"
	"path/filepath"
	"strings"
	"testing"
)

func TestLeanGraphValidation(t *testing.T) {
	o := newOracle(t)
	paths, err := filepath.Glob("../Test/graphs/*.json")
	if err != nil {
		t.Fatal(err)
	}
	checked := 0
	for _, path := range paths {
		g := readGraph(t, strings.TrimSuffix(filepath.Base(path), ".json"))
		cases := []Graph{g}
		duplicate := cloneGraph(g)
		duplicate.Nodes = append(duplicate.Nodes, duplicate.Nodes[0])
		cases = append(cases, duplicate)
		missing := cloneGraph(g)
		missing.Entries = nil
		cases = append(cases, missing)
		badExit := cloneGraph(g)
		badExit.Exits = List[PortRef]{{"unknown", "out"}}
		cases = append(cases, badExit)
		name := cloneGraph(g)
		name.Nodes[0].ID = ""
		cases = append(cases, name)
		shape := cloneGraph(g)
		shape.Nodes[0].Outputs = nil
		cases = append(cases, shape)
		if len(g.Edges) > 0 {
			cycle := cloneGraph(g)
			cycle.Edges[0].Dst.Node = cycle.Edges[0].Src.Node
			cases = append(cases, cycle)
			port := cloneGraph(g)
			port.Edges[0].Src.Port = "unknown"
			cases = append(cases, port)
		}
		// Duplicate Branch origins must be rejected by Coalesce validation.
		crossed := cloneGraph(g)
		for i := range crossed.Edges {
			e := &crossed.Edges[i]
			if e.Src.Port == "right" {
				e.Src.Port = "left"
			}
		}
		cases = append(cases, crossed)
		for _, candidate := range cases {
			for _, body := range []bool{false, true} {
				var want struct {
					Error *string `json:"error"`
				}
				o.ask(map[string]any{"action": "validate", "graph": candidate, "body": body}, &want)
				got := candidate.validate(body)
				if got == nil && want.Error != nil || got != nil && (want.Error == nil || got.Error() != *want.Error) {
					t.Fatalf("%s body=%v: Go=%v Lean=%v", path, body, got, want.Error)
				}
				checked++
			}
		}
	}
	t.Logf("compared %d valid and invalid graph checks", checked)
}

func TestLeanLargeNumbersAndUnicode(t *testing.T) {
	o := newOracle(t)
	g := readGraph(t, "minimal")
	name := "仕事<>&\u2028\t\r\n\x00😀"
	g.Nodes[0].ID = name
	g.Entries[0].Node = name
	g.Exits[0].Node = name
	large, err := ParseNat("184467440737095516160000")
	if err != nil {
		t.Fatal(err)
	}
	g.Nodes[0].Kind.Retry.LeaseSeconds = large
	var reset struct {
		State State `json:"state"`
	}
	o.ask(map[string]any{"action": "reset", "graph": g}, &reset)
	s := Initial(g)
	assertJSON(t, "Unicode initial state", s, reset.State)
	auth := Credentials{Instance: InstanceID(nil, name, nil), Attempt: "試行😀", Token: "資格\t\x00", Now: large}
	ops := []Op{
		{Kind: "start", Inputs: InputValues(g)},
		{Kind: "activate", Node: name},
		{Kind: "claim", Auth: auth, Worker: "作業員"},
		{Kind: "renew", Auth: Credentials{auth.Instance, auth.Attempt, auth.Token, large.Inc()}},
		{Kind: "complete", Auth: Credentials{auth.Instance, auth.Attempt, auth.Token, large.Inc()}, Outputs: List[Output]{{"out", List[string]{"値<>&\t😀"}}}},
		{Kind: "idle"},
	}
	for _, op := range ops {
		var want stepResult
		o.ask(map[string]any{"action": "step", "op": op}, &want)
		var r *Reject
		s, r = checkStep(t, s, op, want)
		if r != nil {
			t.Fatal(r)
		}
	}
	// Multi-command transactions use one durable boundary, and rollback is atomic.
	next, events, r := RecordTransaction(Initial(g), ops, N(1), "取引😀", Nat{})
	if r != nil {
		t.Fatal(r)
	}
	assertJSON(t, "multi-command result", next, s)
	for cut := 0; cut < len(events); cut++ {
		recovered, d := Recover(g, events[:cut])
		if d != nil {
			t.Fatal(d)
		}
		assertJSON(t, "uncommitted multi-command prefix", recovered, Initial(g))
	}
	var checked struct {
		State      State       `json:"state"`
		Diagnostic *Diagnostic `json:"diagnostic"`
	}
	o.ask(map[string]any{"action": "check", "graph": g, "lines": mapped(events, EncodeEvent)}, &checked)
	if checked.Diagnostic != nil {
		t.Fatal(checked.Diagnostic)
	}
	assertJSON(t, "multi-command Lean replay", s, checked.State)
	forged := append([]Op{}, ops[:3]...)
	forged = append(forged, Op{Kind: "renew", Auth: Credentials{auth.Instance, auth.Attempt, "wrong", large}})
	rolledBack, r := Transaction(Initial(g), forged)
	if r == nil || r.Code != "INVALID_LEASE" {
		t.Fatalf("missing rejection: %v", r)
	}
	assertJSON(t, "transaction rollback", rolledBack, Initial(g))
}

func TestStrictFactNumberScale(t *testing.T) {
	o := newOracle(t)
	g := readGraph(t, "minimal")
	_, events, r := RecordTransaction(Initial(g), []Op{{Kind: "start", Inputs: InputValues(g)}, {Kind: "activate", Node: "work"}}, N(1), "txn", Nat{})
	if r != nil {
		t.Fatal(r)
	}
	for i, e := range events {
		if e.Type == "token.consumed" {
			var data map[string]json.RawMessage
			if err := json.Unmarshal(e.Data, &data); err != nil {
				t.Fatal(err)
			}
			data["index"] = json.RawMessage("0.0")
			events[i].Data = raw(data)
		}
	}
	_, got := Check(g, events)
	var want struct {
		Diagnostic *Diagnostic `json:"diagnostic"`
	}
	o.ask(map[string]any{"action": "check", "graph": g, "lines": mapped(events, EncodeEvent)}, &want)
	if got == nil || want.Diagnostic == nil || got.Reason.Code != want.Diagnostic.Reason.Code {
		t.Fatalf("scale mismatch: Go=%v Lean=%v", got, want.Diagnostic)
	}
}
