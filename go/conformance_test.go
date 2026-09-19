package suimon

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

func readGraph(t *testing.T, name string) Graph {
	t.Helper()
	b, err := os.ReadFile(filepath.Join("..", "Test", "graphs", name+".json"))
	if err != nil {
		t.Fatal(err)
	}
	g, err := ParseGraph(b)
	if err != nil {
		t.Fatal(err)
	}
	return g
}
func assertJSON(t *testing.T, label string, a, b any) {
	t.Helper()
	if !sameValues(a, b) {
		t.Fatalf("%s mismatch\nGo:   %s\nLean: %s", label, compact(a), compact(b))
	}
}

type oracle struct {
	t   *testing.T
	enc *json.Encoder
	dec *json.Decoder
}

func newOracle(t *testing.T) *oracle {
	t.Helper()
	path := os.Getenv("SUIMON_LEAN_ORACLE")
	if path == "" {
		t.Skip("run bin/test-go for the Lean differential suite")
	}
	cmd := exec.Command(path)
	input, err := cmd.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}
	output, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	cmd.Stderr = os.Stderr
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		input.Close()
		if err := cmd.Wait(); err != nil {
			t.Errorf("Lean oracle: %v", err)
		}
	})
	return &oracle{t, json.NewEncoder(input), json.NewDecoder(output)}
}
func (o *oracle) ask(v any, out any) {
	o.t.Helper()
	if err := o.enc.Encode(v); err != nil {
		o.t.Fatal(err)
	}
	var raw json.RawMessage
	if err := o.dec.Decode(&raw); err != nil {
		o.t.Fatal(err)
	}
	var failure struct {
		Error string `json:"oracle_error"`
	}
	_ = json.Unmarshal(raw, &failure)
	if failure.Error != "" {
		o.t.Fatal(failure.Error)
	}
	if err := json.Unmarshal(raw, out); err != nil {
		o.t.Fatalf("oracle response: %v\n%s", err, raw)
	}
}

type stepResult struct {
	State  State      `json:"state"`
	Reject *Reject    `json:"reject"`
	Facts  List[Fact] `json:"facts"`
}

func checkStep(t *testing.T, s State, op Op, want stepResult) (State, *Reject) {
	t.Helper()
	before := compact(s)
	next, r := Step(s, op)
	assertJSON(t, "rejection for "+compact(op), r, want.Reject)
	if r == nil {
		assertJSON(t, "state for "+compact(op), next, want.State)
		assertJSON(t, "facts for "+compact(op), Effects(s, next, op), want.Facts)
	}
	if compact(s) != before {
		t.Fatal("Step mutated input state")
	}
	return next, r
}

func TestLeanRegressionCorpus(t *testing.T) {
	path := os.Getenv("SUIMON_GO_CORPUS")
	if path == "" {
		t.Skip("run bin/test-go to replay the existing Lean regression cases")
	}
	f, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	d := json.NewDecoder(f)
	count := 0
	accepted := map[string]int{}
	rejected := 0
	for {
		var c struct {
			Before State      `json:"before"`
			Op     Op         `json:"op"`
			After  State      `json:"after"`
			Reject *Reject    `json:"reject"`
			Facts  List[Fact] `json:"facts"`
		}
		err := d.Decode(&c)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		count++
		_, r := checkStep(t, c.Before, c.Op, stepResult{c.After, c.Reject, c.Facts})
		if r == nil {
			accepted[c.Op.Kind]++
		} else {
			rejected++
		}
	}
	if count < 100 {
		t.Fatalf("incomplete corpus: %d cases", count)
	}
	t.Logf("replayed %d original Lean regression cases (%d rejected); accepted operations: %v", count, rejected, accepted)
}

func TestLeanCandidatesAndWalks(t *testing.T) {
	o := newOracle(t)
	paths, err := filepath.Glob("../Test/graphs/*.json")
	if err != nil {
		t.Fatal(err)
	}
	cfg := DefaultConfig()
	cfg.Workers = N(2)
	accepted := map[string]int{}
	probes := 0
	for _, path := range paths {
		g := readGraph(t, strings.TrimSuffix(filepath.Base(path), ".json"))
		for run := 0; run < 3; run++ {
			var reset struct {
				State State `json:"state"`
			}
			o.ask(map[string]any{"action": "reset", "graph": g}, &reset)
			s := Initial(g)
			assertJSON(t, "initial", s, reset.State)
			for turn := 0; turn < 55 && !terminal(s.Status); turn++ {
				var inspect struct {
					State      State    `json:"state"`
					Candidates List[Op] `json:"candidates"`
					HasWork    bool     `json:"hasWork"`
				}
				o.ask(map[string]any{"action": "inspect", "config": cfg}, &inspect)
				ops := Candidates(cfg, s)
				assertJSON(t, "candidate enumeration", ops, inspect.Candidates)
				if s.HasWork() != inspect.HasWork {
					t.Fatal("hasWork mismatch")
				}
				variants := append(List[Op]{}, ops...)
				for _, op := range ops {
					switch op.Kind {
					case "claim", "renew", "complete", "fail", "emit":
						bad := op
						bad.Auth.Token = "wrong-token"
						variants = append(variants, bad)
						bad = op
						bad.Auth.Now = s.Now.Add(N(999))
						variants = append(variants, bad)
					case "spawn", "fireCoalesce", "fireFilter", "fireMerge":
						bad := op
						bad.Item = "wrong-item"
						variants = append(variants, bad)
					}
				}
				var results []stepResult
				o.ask(map[string]any{"action": "probe", "ops": variants}, &results)
				if len(results) != len(variants) {
					t.Fatal("incomplete probe response")
				}
				for i, op := range variants {
					checkStep(t, s, op, results[i])
					probes++
				}
				// Cover successful operations without immediately cancelling the run.
				choice := -1
				best := int(^uint(0) >> 1)
				for i, op := range ops {
					if results[i].Reject != nil || equal(results[i].State, s) || op.Kind == "cancel" {
						continue
					}
					score := accepted[op.Kind]*10 + (i+run+turn)%7
					if op.Kind == "idle" {
						score += 10000
					}
					if score < best {
						choice = i
						best = score
					}
				}
				if choice < 0 {
					break
				}
				op := ops[choice]
				var result stepResult
				o.ask(map[string]any{"action": "step", "op": op}, &result)
				s, _ = checkStep(t, s, op, result)
				accepted[op.Kind]++
			}
		}
	}
	t.Logf("compared %d candidate and adversarial operations; selected operations: %v", probes, accepted)
}

func TestLeanGenerationAndSearch(t *testing.T) {
	o := newOracle(t)
	paths, _ := filepath.Glob("../Test/graphs/*.json")
	cfg := DefaultConfig()
	for _, path := range paths {
		g := readGraph(t, strings.TrimSuffix(filepath.Base(path), ".json"))
		for _, seed := range []uint64{1, 3, 17, 71} {
			var want struct {
				State  State       `json:"state"`
				Events List[Event] `json:"events"`
				Reject *Reject     `json:"reject"`
			}
			o.ask(map[string]any{"action": "generate", "graph": g, "config": cfg, "seed": N(seed), "count": N(40)}, &want)
			s, events, r := Generate(g, cfg, N(seed), N(40))
			assertJSON(t, "generate rejection", r, want.Reject)
			assertJSON(t, "generated state", s, want.State)
			assertJSON(t, "generated events", events, want.Events)
			checked, d := Check(g, events)
			if d != nil {
				t.Fatal(d)
			}
			assertJSON(t, "generated replay", s, checked)
			lines := mapped(events, EncodeEvent)
			var checkedLean struct {
				State      State       `json:"state"`
				Diagnostic *Diagnostic `json:"diagnostic"`
			}
			o.ask(map[string]any{"action": "check", "graph": g, "lines": lines}, &checkedLean)
			if checkedLean.Diagnostic != nil {
				t.Fatal(checkedLean.Diagnostic)
			}
			assertJSON(t, "Lean acceptance of Go JSONL", s, checkedLean.State)
		}
		for _, limit := range []uint64{1, 10000} {
			c := cfg
			c.Depth = N(5)
			c.Workers = N(2)
			c.MaxStates = N(limit)
			var want Report
			o.ask(map[string]any{"action": "search", "graph": g, "config": c}, &want)
			assertJSON(t, "bounded search "+path, Search(g, c), want)
		}
	}
}

func TestFixturesAndTornTransactions(t *testing.T) {
	for _, tc := range []struct {
		trace, graph string
		invalid      bool
	}{{"minimal", "minimal", false}, {"coalesce", "coalesce", false}, {"loop-retry", "loop", false}, {"missing-attempt", "minimal", true}, {"after-eos", "minimal", true}} {
		t.Run(tc.trace, func(t *testing.T) {
			g := readGraph(t, tc.graph)
			b, err := os.ReadFile("../Test/traces/" + tc.trace + ".jsonl")
			if err != nil {
				t.Fatal(err)
			}
			c := NewCursor(g)
			events := List[Event]{}
			var diagnostic *Diagnostic
			for _, line := range strings.Split(strings.TrimSuffix(string(b), "\n"), "\n") {
				e, err := ParseEvent([]byte(line))
				if err != nil {
					t.Fatal(err)
				}
				events = append(events, e)
				next, d := CheckTextLine(c, line)
				if d != nil {
					diagnostic = d
					break
				}
				c = next
			}
			if tc.invalid {
				if diagnostic == nil {
					t.Fatal("corrupt trace accepted")
				}
				t.Logf("rejection: %s", diagnostic.Reason.Code)
				return
			}
			if diagnostic != nil {
				t.Fatal(diagnostic)
			}
			s, d := Finish(c)
			if d != nil || s.Status != "succeeded" {
				t.Fatalf("fixture: %v/%s", d, s.Status)
			}
			boundary := Initial(g)
			for cut := 0; cut <= len(events); cut++ {
				if cut > 0 && events[cut-1].Type == "transaction.committed" {
					var d *Diagnostic
					boundary, d = Check(g, events[:cut])
					if d != nil {
						t.Fatal(d)
					}
				}
				recovered, d := Recover(g, events[:cut])
				if d != nil {
					t.Fatal(d)
				}
				assertJSON(t, fmt.Sprintf("recovery at %d", cut), recovered, boundary)
			}
		})
	}
}

func TestLeanMalformedTraces(t *testing.T) {
	o := newOracle(t)
	g := readGraph(t, "minimal")
	b, err := os.ReadFile("../Test/traces/minimal.jsonl")
	if err != nil {
		t.Fatal(err)
	}
	lines := strings.Split(strings.TrimSuffix(string(b), "\n"), "\n")
	variants := [][]string{lines[:len(lines)-1], {"{broken"}}
	for _, edit := range []func(map[string]any){func(m map[string]any) { m["sequence"] = json.Number("2") }, func(m map[string]any) { m["schema_version"] = json.Number("1") }, func(m map[string]any) { delete(m, "op") }, func(m map[string]any) { m["extra"] = true }, func(m map[string]any) { m["type"] = "wrong" }, func(m map[string]any) { m["sequence"] = json.Number("1.0") }, func(m map[string]any) { m["data"] = nil }} {
		copy := slices.Clone(lines)
		v, _ := jsonValue([]byte(copy[0]))
		m := v.(map[string]any)
		edit(m)
		copy[0] = compactValue(m)
		variants = append(variants, copy)
	}
	for _, input := range variants {
		var want struct {
			Diagnostic *Diagnostic `json:"diagnostic"`
		}
		o.ask(map[string]any{"action": "check", "graph": g, "lines": List[string](input)}, &want)
		c := NewCursor(g)
		var got *Diagnostic
		for _, line := range input {
			c, got = CheckTextLine(c, line)
			if got != nil {
				break
			}
		}
		if got == nil {
			_, got = Finish(c)
		}
		if got == nil || want.Diagnostic == nil || got.Reason.Code != want.Diagnostic.Reason.Code {
			t.Fatalf("diagnostic mismatch: Go=%v Lean=%v", got, want.Diagnostic)
		}
		assertJSON(t, "diagnostic boundary", got.Boundary, want.Diagnostic.Boundary)
	}
}

func TestNaturalNumbersAndIDs(t *testing.T) {
	large, err := ParseNat("184467440737095516160000")
	if err != nil {
		t.Fatal(err)
	}
	if large.Inc().String() != "184467440737095516160001" || !N(1).Sub(N(2)).IsZero() {
		t.Fatal("natural arithmetic mismatch")
	}
	for _, number := range []string{"1.0", "-1", "null", "true", "\"1\""} {
		var n Nat
		if json.Unmarshal([]byte(number), &n) == nil {
			t.Fatalf("accepted %s", number)
		}
	}
	for _, number := range []string{"1", "1e-0", "10e-0", "1.0e1"} {
		var n Nat
		if err := json.Unmarshal([]byte(number), &n); err != nil {
			t.Fatal(err)
		}
	}
	if got := Identity([]string{"<>&\u2028\n\r\t\x00日本語"}); got != "[\"<>&\u2028\\n\\r\\u0009\\u0000日本語\"]" {
		t.Fatalf("Lean ID spelling: %q", got)
	}
}

func TestJSONContracts(t *testing.T) {
	g := readGraph(t, "minimal")
	b := raw(g)
	v, _ := jsonValue(b)
	m := v.(map[string]any)
	m["extra"] = true
	if _, err := ParseGraph([]byte(compactValue(m))); err == nil {
		t.Fatal("unknown graph field accepted")
	}
	delete(m, "extra")
	delete(m, "edges")
	if _, err := ParseGraph([]byte(compactValue(m))); err == nil {
		t.Fatal("missing graph field accepted")
	}
	for _, text := range []string{`{"start":{"inputs":[],"extra":true}}`, `{"claim":{"auth":null,"worker":"a"}}`, `{"idle":{}}`, `"unknown"`} {
		if _, err := ParseOp([]byte(text)); err == nil {
			t.Fatalf("accepted malformed op %s", text)
		}
	}
}
