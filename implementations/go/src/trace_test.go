package suimon

import (
	"fmt"
	"slices"
	"strings"
	"testing"
	"unicode/utf8"
)

// Ported from Test/Trace.lean.

// genPayloads are the payloads gen writes for op: each value's identity repeated.
func genPayloads(t *testing.T, recorder *Recorder, op Op) []Payload {
	t.Helper()
	needs, err := recorder.Needs(op)
	if err != nil {
		t.Fatal(err)
	}
	var values []Payload
	for _, v := range needs {
		values = append(values, Payload{Value: v, Payload: v})
	}
	return values
}

// header is the header line of a record of p whose execution was started with validation, with its
// newline.
func header(p *Definition) string { return EncodeHeader(p, true) + "\n" }

// recorded is the record of a random walk, with a header that says the execution was started with
// validation: its transitions with the payloads gen writes, the text (the header, then the records),
// and the state before the first transition and after each committed one.
func recorded(t *testing.T, p *Definition, seed uint64) ([]Transition, string, []*State) {
	t.Helper()
	return recordedAs(t, p, seed, true)
}

// recordedAs is recorded with the header of an execution started with validation or without it.
func recordedAs(t *testing.T, p *Definition, seed uint64, validated bool) ([]Transition, string, []*State) {
	t.Helper()
	_, ops := Walk(p, DefaultConfig(), seed, 10000)
	recorder := NewRecorder(p)
	states := []*State{recorder.State()}
	var steps []Transition
	var text strings.Builder
	text.WriteString(EncodeHeader(p, validated) + "\n")
	for _, op := range ops {
		values := genPayloads(t, recorder, op)
		records, err := recorder.Record(op, values)
		if err != nil {
			t.Fatal(err)
		}
		steps = append(steps, Transition{op, values})
		text.WriteString(RecordsText(records))
		states = append(states, recorder.State())
	}
	return steps, text.String(), states
}

// written is the text of records for steps, which the recorder need not accept.
func written(steps []Transition) string {
	var records []Record
	for i, step := range steps {
		records = append(records, Record{Seq: 2*i + 1, Op: step.Op, Values: step.Values}, Record{Seq: 2*i + 2, Commit: true})
	}
	return RecordsText(records)
}

// isList reports a list the engine built, for a waitStream, a Merge or a concurrency List output.
func isList(v string) bool {
	parts, ok := DecodeIdentity(v)
	return ok && len(parts) > 0 && parts[0] == "list"
}

func splitPayloads(values []Payload, keep func(Payload) bool) (kept, dropped []Payload) {
	for _, v := range values {
		if keep(v) {
			kept = append(kept, v)
		} else {
			dropped = append(dropped, v)
		}
	}
	return kept, dropped
}

func checkedText(t *testing.T, label, text string) Checked {
	t.Helper()
	c, err := Check(text, LoadHeader)
	if err != nil {
		t.Fatalf("%s: %v", label, err)
	}
	return c
}

func rejectedText(t *testing.T, label, fragment, text string) {
	t.Helper()
	_, err := Check(text, LoadHeader)
	if err == nil {
		t.Errorf("%s: accepted, expected %q", label, fragment)
	} else if !hasFragment(err.Error(), fragment) {
		t.Errorf("%s: expected %q, got %v", label, fragment, err)
	}
}

// checked checks a record of p whose lines after the header are text.
func checked(t *testing.T, label string, p *Definition, text string) Checked {
	t.Helper()
	return checkedText(t, label, header(p)+text)
}

func rejectedTrace(t *testing.T, label, fragment string, p *Definition, text string) {
	t.Helper()
	rejectedText(t, label, fragment, header(p)+text)
}

// withoutInputs is p without the connections into its placement target.
func withoutInputs(p *Definition, target string) *Definition {
	for i := range p.Workflows {
		w := &p.Workflows[i]
		w.Connections = slices.DeleteFunc(slices.Clone(w.Connections), func(c Connection) bool { return c.Target == target })
	}
	return p
}

// withoutOutputs is p without a task of any concurrency in the output.
func withoutOutputs(p *Definition) *Definition {
	for i := range p.Workflows {
		for j := range p.Workflows[i].Placements {
			mapConcurrency(func(c *Concurrency) {
				for k := range c.Tasks {
					c.Tasks[k].Output = nil
				}
			})(&p.Workflows[i].Placements[j])
		}
	}
	return p
}

// invalidDefinition is a definition that validation rejects, with the error, and that an execution
// started without validation can run.
type invalidDefinition struct {
	name  string
	p     *Definition
	error string
}

// invalidDefinitions, as in Test/Trace.lean: a Merge without input connections, which the model
// gives no kind, so that it never settles and the run concludes only after a stop or a
// cancellation; and a concurrency without a task in the output, which runs its tasks but has no
// result.
func invalidDefinitions(t *testing.T) []invalidDefinition {
	t.Helper()
	return []invalidDefinition{
		{"merge without inputs", withoutInputs(load(t, "merge"), "widgets"), "dashboard.widgets: Merge needs input connections"},
		{"users without outputs", withoutOutputs(load(t, "users")), "users.perUser: at least one task must be in the output"},
	}
}

// half is the first half of a line in characters, like Lean's line.take (line.length / 2).
func half(line string) string {
	runes := []rune(line)
	return string(runes[:len(runes)/2])
}

func TestTraceReplay(t *testing.T) {
	for _, name := range append(definitionNames, extraDefinitions...) {
		p := load(t, name)
		if replayWalks(t, name, p, true, 20) == 0 {
			t.Errorf("%s: no walk built a list", name)
		}
		replayWalks(t, name, p, false, 5)
	}
	// An execution started without validation may run a definition that validation rejects: its record
	// checks without validation, cut anywhere, and the same record marked as validated is refused at
	// line 1 with the error of validation.
	for _, x := range invalidDefinitions(t) {
		if err := x.p.Validate(); err == nil || err.Error() != x.error {
			t.Fatalf("%s: validation gives %v, want %q", x.name, err, x.error)
		}
		replayWalks(t, x.name, x.p, false, 10)
		for seed := uint64(1); seed <= 10; seed++ {
			_, text, _ := recordedAs(t, x.p, seed, true)
			if _, err := Check(text, LoadHeader); err == nil || err.Error() != "line 1: "+x.error {
				t.Errorf("%s seed %d validated: %v", x.name, seed, err)
			}
		}
	}
}

// replayWalks checks the records of random walks of p whose header says whether the execution was
// started with validation: whole, cut anywhere and corrupted. It returns how many walks built a list.
func replayWalks(t *testing.T, name string, p *Definition, validated bool, seeds uint64) int {
	t.Helper()
	listCases := 0
	for seed := uint64(1); seed <= seeds; seed++ {
		label := fmt.Sprintf("%s seed %d validated %t", name, seed, validated)
		steps, text, states := recordedAs(t, p, seed, validated)
		final := states[len(states)-1]
		// Replaying a whole record reproduces the state of the run that wrote it, with its definition.
		whole := checkedText(t, label, text)
		if !whole.State.Equal(final) || whole.Committed+1 != len(states) || whole.Uncommitted {
			t.Fatalf("%s: replay differs from the run", label)
		}
		if whole.Definition == nil || EncodeHeader(whole.Definition, validated) != EncodeHeader(p, validated) ||
			whole.Validated != validated {
			t.Fatalf("%s: another header", label)
		}
		for _, v := range whole.State.Values() {
			if !hasPayload(whole.Values, v) {
				t.Fatalf("%s: a value without payload: %s", label, v)
			}
		}
		// A commit needs the payload of each value its transition introduces, lists the engine
		// builds included, and an op record carries payloads only for the values its transition
		// introduces: neither an earlier record nor a later one may hold it. The header is line 1.
		for i, step := range steps {
			kept, lists := splitPayloads(step.Values, func(v Payload) bool { return !isList(v.Value) })
			if len(lists) == 0 {
				continue
			}
			with := func(j int, values []Payload) []Transition {
				out := slices.Clone(steps)
				out[i] = Transition{step.Op, kept}
				out[j] = Transition{out[j].Op, append(slices.Clone(out[j].Values), values...)}
				return out
			}
			stripped := with(i, nil)
			head := EncodeHeader(p, validated) + "\n"
			rejectedText(t, label+" list payload", fmt.Sprintf("line %d: missing payloads", 2*i+3), head+written(stripped))
			if _, _, err := RecordTransitions(p, &State{}, stripped, nil, 1); err == nil || !hasFragment(err.Error(), "missing payloads") {
				t.Fatalf("%s: recorder without a list payload: %v", label, err)
			}
			var listValues []string
			for _, v := range lists {
				listValues = append(listValues, v.Value)
			}
			early := with(0, lists)
			rejectedText(t, label+" early payload",
				fmt.Sprintf("line 3: payloads for %s, which the transition does not introduce", leanList(listValues)),
				head+written(early))
			if _, _, err := RecordTransitions(p, &State{}, early, nil, 1); err == nil ||
				!hasFragment(err.Error(), "which the transition does not introduce") {
				t.Fatalf("%s: recorder with an early payload: %v", label, err)
			}
			if i+1 < len(steps) {
				rejectedText(t, label+" later payload", fmt.Sprintf("line %d: missing payloads", 2*i+3), head+written(with(i+1, lists)))
			}
			listCases++
			break
		}
		// Every op survives its encoding, and every line is canonical.
		for i, line := range strings.Split(text, "\n") {
			if line == "" || i == 0 {
				continue
			}
			r, err := DecodeRecord(line)
			if err != nil {
				t.Fatalf("%s: %v", label, err)
			}
			if EncodeRecord(r) != line || strings.ContainsRune(line, '\n') {
				t.Fatalf("%s: record codec changed %s", label, line)
			}
			if !r.Commit {
				op, err := DecodeOp(EncodeOp(r.Op))
				if err != nil || EncodeOp(op) != EncodeOp(r.Op) {
					t.Fatalf("%s: op codec: %v", label, err)
				}
			}
		}
		// A crash may cut the record anywhere, the header included; recovery keeps exactly the
		// committed transitions, and knows the definition once the header is complete.
		lines := strings.Split(text, "\n")
		lines = lines[:len(lines)-1]
		for cut := 0; cut <= len(lines); cut++ {
			prefix := strings.Join(lines[:cut], "\n")
			if cut > 0 {
				prefix += "\n"
			}
			torn := prefix
			if cut < len(lines) {
				torn += half(lines[cut])
			}
			committed := max(cut-1, 0) / 2
			for _, text := range []string{prefix, torn} {
				c := checkedText(t, fmt.Sprintf("%s cut %d", label, cut), text)
				if c.Committed != committed || !c.State.Equal(states[committed]) {
					t.Fatalf("%s cut %d: wrong recovered state", label, cut)
				}
				if (c.Definition == nil) != (cut == 0) || c.Validated != (cut > 0 && validated) {
					t.Fatalf("%s cut %d: definition %v, validated %t", label, cut, c.Definition, c.Validated)
				}
				if c.Uncommitted != ((cut > 0 && (cut-1)%2 == 1) || len(text) > len(prefix)) {
					t.Fatalf("%s cut %d: uncommitted flag", label, cut)
				}
				if recovered, err := Recover(text, LoadHeader); err != nil || !recovered.Equal(states[committed]) {
					t.Fatalf("%s cut %d: recover", label, cut)
				}
			}
		}
		// Corruption before the last commit is an error, not a torn tail.
		if len(lines) >= 5 {
			corrupt := append([]string(nil), lines...)
			corrupt[2] = `{"seq":2`
			rejectedText(t, label+" corrupt", "line 3", strings.Join(corrupt, "\n")+"\n")
			reordered := append([]string{lines[0], lines[2], lines[1]}, lines[3:]...)
			rejectedText(t, label+" reordered", "line 2: expected sequence 1", strings.Join(reordered, "\n")+"\n")
		}
	}
	return listCases
}

func TestTraceRejections(t *testing.T) {
	merge := load(t, "merge")
	start := "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
	rejectedTrace(t, "commit twice", "a commit without an op", merge, start+"{\"seq\":3,\"commit\":true}\n")
	again := strings.ReplaceAll(strings.ReplaceAll(start, `"seq":1`, `"seq":3`), `"seq":2`, `"seq":4`)
	rejectedTrace(t, "rejected op", "line 5: rejected", merge, start+again)
	users := load(t, "users")
	rejectedTrace(t, "missing payload", "missing payloads", users,
		"{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}}\n{\"seq\":2,\"commit\":true}\n")
	// The payloads are checked at the commit, so an op without its commit is only uncommitted.
	if c := checked(t, "pending op", users, "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}}\n"); c.Committed != 0 || !c.Uncommitted {
		t.Errorf("pending op: %+v", c)
	}

	rejectedTrace(t, "op twice", "an op before the previous commit", merge,
		"{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"op\":{\"type\":\"cancel\"}}\n")
	rejectedTrace(t, "unknown op field", "unknown field trigger", merge, "{\"seq\":1,\"op\":{\"type\":\"start\",\"trigger\":\"x\"}}\n")
	rejectedTrace(t, "unknown record field", "unknown field extra", merge, "{\"seq\":1,\"op\":{\"type\":\"start\"},\"extra\":1}\n")
	rejectedTrace(t, "op and commit", "either an op or a commit", merge, "{\"seq\":1,\"op\":{\"type\":\"start\"},\"commit\":true}\n")
	rejectedTrace(t, "unknown op", "unknown op type", merge, "{\"seq\":1,\"op\":{\"type\":\"retry\"}}\n")
	rejectedTrace(t, "empty line", "line 2", merge, "\n")
	torn := checked(t, "torn start", merge, "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"com")
	if torn.Committed != 0 || !torn.Uncommitted || !torn.State.Equal(&State{}) {
		t.Errorf("torn start: %+v", torn)
	}
	// The header comes first and only there, and its definition must load.
	for _, validated := range []bool{true, false} {
		text := EncodeHeader(merge, validated) + "\n"
		if c := checkedText(t, "header only", text); c.Definition == nil || c.Validated != validated || c.Committed != 0 ||
			c.Uncommitted || !c.State.Equal(&State{}) || c.Length != len(text) {
			t.Errorf("header only: %+v", c)
		}
	}
	if c := checkedText(t, "torn header", header(merge)[:30]); c.Definition != nil || c.Committed != 0 || !c.Uncommitted ||
		!c.State.Equal(&State{}) || c.Length != 0 {
		t.Errorf("torn header: %+v", c)
	}
	if c := checkedText(t, "empty", ""); c.Definition != nil || c.Committed != 0 || c.Uncommitted || !c.State.Equal(&State{}) {
		t.Errorf("empty: %+v", c)
	}
	rejectedText(t, "no header", "line 1: header: unknown field seq", start)
	rejectedTrace(t, "header twice", "line 2: record: missing field seq", merge, header(merge))
	rejectedTrace(t, "header after records", "line 4: record: missing field seq", merge, start+header(merge))
	// A record replays against the definition of its header: users records are rejected under merge.
	rejectedText(t, "another definition", "line 3: rejected", header(merge)+
		"{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n")
	startInput := "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}"
	rejectedTrace(t, "payload not a string", "expected a string", users, startInput+",\"values\":{\"t\":1}}\n")
	withPayload := checked(t, "payload", users, startInput+",\"values\":{\"t\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n")
	if withPayload.Committed != 1 || withPayload.Uncommitted || len(withPayload.Values) != 1 ||
		withPayload.Values[0] != (Payload{"t", "x"}) {
		t.Errorf("payload: %+v", withPayload)
	}

	exact := []struct {
		label, text, want string
	}{
		{"missing payload", "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}}\n{\"seq\":2,\"commit\":true}\n",
			"line 3: missing payloads for [t]"},
		{"rejected op", start + again, `line 5: rejected {"type":"start"}: ALREADY_STARTED`},
		{"an op before the commit", "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"op\":{\"type\":\"start\"}}\n",
			"line 3: an op before the previous commit"},
		{"parse error", "{\"seq\":1,\n", "line 2: unterminated object at offset 9"},
		{"not an object", "[]\n", "line 2: record: expected an object"},
		{"neither", "{\"seq\":1}\n", "line 2: record: either an op or a commit"},
		{"commit false", "{\"seq\":1,\"commit\":false}\n", "line 2: record: either an op or a commit"},
		{"unknown field", "{\"seq\":1,\"commit\":true,\"at\":0}\n", "line 2: record: unknown field at"},
		{"values", "{\"seq\":1,\"op\":{\"type\":\"start\"},\"values\":[]}\n", "line 2: record.values: expected an object"},
		{"payload", "{\"seq\":1,\"op\":{\"type\":\"start\"},\"values\":{\"v\":1}}\n", "line 2: record.values.v: expected a string"},
		{"op field", "{\"seq\":1,\"op\":{\"type\":\"fetch\",\"call\":\"c\",\"x\":1}}\n", "line 2: op fetch: unknown field x"},
		{"op type", "{\"seq\":1,\"op\":{\"type\":\"jump\"}}\n", "line 2: unknown op type jump"},
		{"null", "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":null}}\n", "line 2: op.input: expected a string"},
		{"path", "{\"seq\":1,\"op\":{\"type\":\"closeRun\",\"run\":[1]}}\n", "line 2: op.run: expected an array of strings"},
		{"negative", "{\"seq\":-1,\"commit\":true}\n", "line 2: unexpected character '-' at offset 7"},
		{"seq", "{\"seq\":2,\"commit\":true}\n", "line 2: expected sequence 1, got 2"},
		{"huge", "{\"seq\":99999999999999999999,\"commit\":true}\n", "line 2: expected sequence 1, got 99999999999999999999"},
		{"huge index", "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n" +
			"{\"seq\":3,\"op\":{\"type\":\"taskOutputFailed\",\"execution\":\"e\",\"task\":\"t\",\"index\":99999999999999999999}}\n{\"seq\":4,\"commit\":true}\n",
			"line 5: rejected {\"type\":\"taskOutputFailed\",\"execution\":\"e\",\"task\":\"t\",\"index\":9223372036854775807}: UNKNOWN_EXECUTION"},
		{"invalid UTF-8", "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"\xff\"}}\n", "line 2: invalid UTF-8"},
		{"repeated op key", "{\"seq\":1,\"op\":{\"type\":\"start\",\"type\":\"cancel\"}}\n{\"seq\":2,\"commit\":true}\n",
			`line 2: duplicate key "type" at offset 36`},
		{"repeated payload key", startInput + ",\"values\":{\"t\":\"x\",\"t\":\"y\"}}\n{\"seq\":2,\"commit\":true}\n",
			`line 2: duplicate key "t" at offset 64`},
		// An op record carries payloads only for values its transition introduces, so a committed
		// payload is never given again, the same or another.
		{"known payload", startInput + ",\"values\":{\"t\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n" +
			"{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"fetchAllUsers\"},\"values\":{\"t\":\"y\"}}\n" +
			"{\"seq\":4,\"commit\":true}\n",
			"line 5: payloads for [t], which the transition does not introduce"},
		{"stray payloads", startInput + ",\"values\":{\"z\":\"w\",\"t\":\"x\",\"y\":\"v\"}}\n{\"seq\":2,\"commit\":true}\n",
			"line 3: payloads for [z, y], which the transition does not introduce"},
		{"stray and missing payloads", startInput + ",\"values\":{\"u\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n",
			"line 3: payloads for [u], which the transition does not introduce"},
	}
	for _, c := range exact {
		p := users
		if c.label == "rejected op" || c.label == "an op before the commit" {
			p = merge
		}
		if _, err := Check(header(p)+c.text, LoadHeader); err == nil || err.Error() != c.want {
			t.Errorf("%s: got %v, want %q", c.label, err, c.want)
		}
	}
	// The header is line 1: it needs the definition, then the flag, a boolean. The definition of a
	// header marked as validated is read like a definition file; that of a header marked as unchecked
	// is only decoded, which still rejects what the definition file cannot express.
	headers := []struct {
		label, text, want string
	}{
		{"empty first line", "\n", "line 1: unexpected end of input at offset 0"},
		{"not an object", "[]\n", "line 1: header: expected an object"},
		{"without definition", "{}\n", "line 1: header: missing field definition"},
		{"without definition, with the flag", "{\"validated\":true}\n", "line 1: header: missing field definition"},
		{"without the flag", "{\"definition\":{}}\n", "line 1: header: missing field validated"},
		{"flag string", "{\"definition\":{},\"validated\":\"true\"}\n", "line 1: header.validated: expected a boolean"},
		{"flag null", "{\"definition\":{},\"validated\":null}\n", "line 1: header.validated: expected a boolean"},
		{"flag number", "{\"definition\":{},\"validated\":1}\n", "line 1: header.validated: expected a boolean"},
		{"unknown field", "{\"definition\":{},\"validated\":true,\"seq\":0}\n", "line 1: header: unknown field seq"},
		{"undecodable definition", "{\"definition\":{},\"validated\":true}\n", "line 1: definition: missing field main"},
		{"undecodable unchecked definition", "{\"definition\":{},\"validated\":false}\n", "line 1: definition: missing field main"},
		{"invalid definition", "{\"definition\":{\"main\":\"w\",\"workflows\":[]},\"validated\":true}\n",
			"line 1: unknown main workflow w"},
		{"empty name", "{\"definition\":{\"main\":\"w\",\"workflows\":[{\"id\":\"w\",\"placements\":[{\"name\":\"\"}]}]},\"validated\":false}\n",
			"line 1: workflows.w.placements.name: empty string"},
		{"invalid UTF-8", "{\"definition\":\"\xff\"}\n", "line 1: invalid UTF-8"},
		{"repeated definition key", "{\"definition\":{\"main\":\"x\",\"main\":\"w\",\"workflows\":[]}}\n",
			`line 1: duplicate key "main" at offset 32`},
	}
	for _, c := range headers {
		if _, err := Check(c.text, LoadHeader); err == nil || err.Error() != c.want {
			t.Errorf("header %s: got %v, want %q", c.label, err, c.want)
		}
	}
	unchecked := checkedText(t, "unchecked invalid definition", "{\"definition\":{\"main\":\"w\",\"workflows\":[]},\"validated\":false}\n")
	if unchecked.Definition == nil || unchecked.Definition.Main != "w" || unchecked.Validated || unchecked.Committed != 0 {
		t.Errorf("unchecked invalid definition: %+v", unchecked)
	}
	// Check gives the definition of the header to load as its canonical JSON, whatever the formatting,
	// with the flag, and whatever the order of the fields.
	var given string
	var flag bool
	if _, err := Check("{ \"validated\" : false, \"definition\" : {\"workflows\":[], \"main\":\"w\", \"limit\":123456789012345678901234567890} }\n",
		func(definition []byte, validated bool) (*Definition, error) {
			given, flag = string(definition), validated
			return merge, nil
		}); err != nil || given != `{"workflows":[],"main":"w","limit":123456789012345678901234567890}` || flag {
		t.Errorf("the definition given to load: %v %s %t", err, given, flag)
	}
}

func TestTornTail(t *testing.T) {
	merge := load(t, "merge")
	start := "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
	// A crash inside a multi-byte character leaves invalid UTF-8 in the partial last line only.
	c, err := Check(header(merge)+start+"{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"\xe3\x81", LoadHeader)
	if err != nil || c.Committed != 1 || !c.Uncommitted {
		t.Errorf("torn tail: %+v %v", c, err)
	}
	c, err = Check("{\"definition\":{\"main\":\"\xe3\x81", LoadHeader)
	if err != nil || c.Definition != nil || !c.Uncommitted {
		t.Errorf("torn header: %+v %v", c, err)
	}
	// No object of a line may repeat a key, at any depth, the definition of the header included.
	_, err = Check(header(merge)+"{\"seq\":1,\"seq\":7,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n", LoadHeader)
	if err == nil || err.Error() != `line 2: duplicate key "seq" at offset 14` {
		t.Errorf("duplicate field: %v", err)
	}
	_, err = Check("{\"definition\":{\"main\":\"x\"},\"definition\":{}}\n", func([]byte, bool) (*Definition, error) { return merge, nil })
	if err == nil || err.Error() != `line 1: duplicate key "definition" at offset 39` {
		t.Errorf("duplicate header field: %v", err)
	}
}

func TestRecordEncoding(t *testing.T) {
	op := OpDeliver{Run: Path{"a"}, Connection: 3, Source: "s\"\\\n\x01\x7f<é>", Value: ptr("v")}
	r := Record{Seq: 5, Op: op, Values: []Payload{{Value: "v", Payload: "p\t"}}}
	want := `{"seq":5,"op":{"type":"deliver","run":["a"],"connection":3,"source":"s\"\\\u000a\u0001` + "\x7f<é>" +
		`","value":"v"},"values":{"v":"p\u0009"}}`
	if got := EncodeRecord(r); got != want {
		t.Errorf("got  %s\nwant %s", got, want)
	}
	if got := EncodeRecord(Record{Seq: 6, Commit: true}); got != `{"seq":6,"commit":true}` {
		t.Errorf("commit: %s", got)
	}
	if got := EncodeRecord(Record{Seq: 1, Op: OpStart{}}); got != `{"seq":1,"op":{"type":"start"}}` {
		t.Errorf("empty values are left out: %s", got)
	}
	// Parsing accepts any JSON formatting of a record.
	decoded, err := DecodeRecord(" {\"values\" : {\"v\":\"p\\t\"}, \"op\": {\"value\":\"v\",\"source\":\"s\\\"\\\\\\n\\u0001\\u007f\\u003c\\u00e9>\"," +
		"\"connection\":3,\"run\":[\"a\"],\"type\":\"deliver\"},\"seq\":5}\r\n")
	if err != nil || EncodeRecord(decoded) != want {
		t.Errorf("formatted record: %v %s", err, EncodeRecord(decoded))
	}
	decoded, err = DecodeRecord(`{"seq":1,"op":{"type":"returned","call":"c","value":"\ud83d\ude00\/"}}`)
	if err != nil || decoded.Op.(OpReturned).Value != "\U0001F600/" {
		t.Errorf("escapes: %v %+v", err, decoded)
	}
}

// Fields have a fixed order, and empty values are left out.
func TestRecordFieldOrder(t *testing.T) {
	keys := func(w wire) string {
		var out []string
		for _, f := range w.fields {
			out = append(out, f.key)
		}
		return strings.Join(out, ",")
	}
	cases := map[string]wire{
		"seq,op,values":                    recordWire(Record{Seq: 1, Op: OpStart{Input: ptr("v")}, Values: []Payload{{"v", "payload"}}}),
		"seq,op":                           recordWire(Record{Seq: 1, Op: OpStart{}}),
		"seq,commit":                       recordWire(Record{Seq: 2, Commit: true}),
		"type,run,placement":               opWire(OpInvoke{Placement: "a"}),
		"type,run,placement,trigger":       opWire(OpInvoke{Placement: "a", Trigger: ptr("t")}),
		"type,run,connection,source,value": opWire(OpDeliver{Source: "s", Value: ptr("v")}),
		"type,execution,task,index,value":  opWire(OpTaskOutput{Execution: "e", Task: "t", Value: "v"}),
	}
	for want, w := range cases {
		if got := keys(w); got != want {
			t.Errorf("fields %s, want %s", got, want)
		}
	}
}

func TestWireParseErrors(t *testing.T) {
	cases := map[string]string{
		``:               "unexpected end of input at offset 0",
		`{"a":1} x`:      "unexpected trailing character 'x' at offset 8",
		`{"a"`:           "unterminated object at offset 4",
		`[1,2`:           "unterminated array at offset 4",
		`"ab`:            "unterminated string at offset 3",
		`"a\`:            "unterminated escape at offset 3",
		`"\u12"`:         `truncated \u escape at offset 3`,
		`"\u12zz"`:       `invalid \u escape at offset 7`,
		`"\ud83d"`:       "unpaired high surrogate at offset 7",
		`"\ud83dabcdef"`: "unpaired high surrogate at offset 13",
		`"\ud83d\u0041"`: "invalid low surrogate at offset 13",
		`"\ude00"`:       "unpaired low surrogate at offset 7",
		`"\q"`:           "invalid escape 'q' at offset 3",
		"\"\x01\"":       "control character in string at offset 1",
		`tru`:            "invalid literal at offset 1",
		`01`:             "leading zero in number at offset 1",
		`1.5`:            "unexpected trailing character '.' at offset 1",
		`[1 2]`:          "expected ',' or ']' at offset 3",
		`{"a":1 "b"}`:    "expected ',' or '}' at offset 7",
		`{"a" 1}`:        "expected ':' at offset 5",
		`{1:2}`:          "expected a string key at offset 1",
		"é\n":            "unexpected character 'é' at offset 0",
		"\t":             "unexpected end of input at offset 1",
		"'":              `unexpected character '\'' at offset 0`,
	}
	for text, want := range cases {
		_, err := parseWire(text)
		if err == nil || err.Error() != want {
			t.Errorf("%q: got %v, want %q", text, err, want)
		}
	}
}

func TestRecorder(t *testing.T) {
	users := load(t, "users")
	recorder := NewRecorder(users)
	if _, err := recorder.Record(OpStart{Input: ptr("t")}, nil); err == nil || err.Error() != "missing payloads for [t]" {
		t.Errorf("missing payload: %v", err)
	}
	if _, err := recorder.Record(OpStart{Input: ptr("t")}, []Payload{{"t", "\xff"}}); err == nil {
		t.Error("a payload must be valid UTF-8")
	}
	// A line may not repeat a key, so a value has one payload.
	if _, err := recorder.Record(OpStart{Input: ptr("t")}, []Payload{{"t", "x"}, {"u", "y"}, {"t", "z"}, {"u", "w"}, {"t", "v"}}); err == nil ||
		err.Error() != "duplicate payloads for [t, u]" {
		t.Errorf("repeated payload: %v", err)
	}
	if _, _, err := Transaction(users, &State{}, OpStart{Input: ptr("t")}, []Payload{{"t", "x"}, {"t", "x"}}, nil, 1); err == nil ||
		err.Error() != "duplicate payloads for [t]" {
		t.Errorf("repeated payload in a transaction: %v", err)
	}
	// An op record carries payloads only for values its transition introduces.
	if _, err := recorder.Record(OpStart{Input: ptr("t")}, []Payload{{"t", "x"}, {"z", "w"}}); err == nil ||
		err.Error() != "payloads for [z], which the transition does not introduce" {
		t.Errorf("stray payload: %v", err)
	}
	if _, _, err := Transaction(users, &State{}, OpStart{Input: ptr("t")}, []Payload{{"z", "w"}, {"t", "x"}}, nil, 1); err == nil ||
		err.Error() != "payloads for [z], which the transition does not introduce" {
		t.Errorf("stray payload in a transaction: %v", err)
	}
	records, err := recorder.Record(OpStart{Input: ptr("t")}, []Payload{{"t", `{"tenant":1}`}})
	if err != nil || len(records) != 2 || records[0].Seq != 1 || !records[1].Commit || records[1].Seq != 2 {
		t.Fatalf("start: %+v %v", records, err)
	}
	// A value already known gets no second payload, the same or another.
	for _, payload := range []string{`{"tenant":1}`, `{"tenant":2}`} {
		if _, err := recorder.Record(OpInvoke{Run: Path{}, Placement: "fetchAllUsers"}, []Payload{{"t", payload}}); err == nil ||
			err.Error() != "payloads for [t], which the transition does not introduce" {
			t.Errorf("payload for a known value: %v", err)
		}
	}
	if _, _, err := RecordTransitions(users, &State{}, []Transition{
		{OpStart{Input: ptr("t")}, []Payload{{"t", "before"}}},
		{OpInvoke{Run: Path{}, Placement: "fetchAllUsers"}, []Payload{{"t", "after"}}},
	}, nil, 1); err == nil || err.Error() != "payloads for [t], which the transition does not introduce" {
		t.Errorf("a later payload for a known value: %v", err)
	}
	if _, err := recorder.Record(OpStart{}, nil); err == nil || err.Error() != "ALREADY_STARTED" {
		t.Errorf("rejected op: %v", err)
	}
	records, err = recorder.Record(OpInvoke{Run: Path{}, Placement: "fetchAllUsers"}, nil)
	if err != nil || records[0].Seq != 3 {
		t.Fatalf("invoke: %+v %v", records, err)
	}
	final, all, err := RecordTransitions(users, &State{}, []Transition{
		{OpStart{Input: ptr("t")}, []Payload{{"t", `{"tenant":1}`}}},
		{OpInvoke{Run: Path{}, Placement: "fetchAllUsers"}, nil},
	}, nil, 1)
	if err != nil || len(all) != 4 || !final.Equal(recorder.State()) {
		t.Fatalf("RecordTransitions: %v", err)
	}
	c := checked(t, "recorder", users, RecordsText(all))
	if c.Definition == nil || EncodeHeader(c.Definition, true) != EncodeHeader(users, true) || !c.Validated {
		t.Errorf("check: definition %v", c.Definition)
	}
	if c.Committed != 2 || len(c.Values) != 1 || c.Values[0].Payload != `{"tenant":1}` {
		t.Errorf("check: %+v", c)
	}
	if !utf8.ValidString(RecordsText(all)) {
		t.Error("records are UTF-8")
	}
}

// A transition introduces the values its state newly mentions, including the lists the engine
// builds; a value that is already there needs no payload again.
func TestIntroduced(t *testing.T) {
	merge := load(t, "merge")
	recorder := NewRecorder(merge)
	var settled []string
	for _, op := range func() []Op { _, ops := Walk(merge, DefaultConfig(), 3, 10000); return ops }() {
		needs, err := recorder.Needs(op)
		if err != nil {
			t.Fatal(err)
		}
		before := recorder.State()
		if _, err := recorder.Record(op, genPayloads(t, recorder, op)); err != nil {
			t.Fatal(err)
		}
		if got := Introduced(before, recorder.State()); strings.Join(got, ",") != strings.Join(needs, ",") {
			t.Errorf("%s: needs %v, introduced %v", EncodeOp(op), needs, got)
		}
		switch op := op.(type) {
		case OpSettle:
			if op.Placement == "widgets" {
				settled = needs
			} else if len(needs) != 0 {
				t.Errorf("%s introduces %v", EncodeOp(op), needs)
			}
		case OpInvoke, OpCloseRun, OpConclude:
			if len(needs) != 0 {
				t.Errorf("%s introduces %v", EncodeOp(op), needs)
			}
		}
	}
	if len(settled) != 1 || !strings.HasPrefix(settled[0], Identity("list")) {
		t.Errorf("the Merge list is introduced when widgets settles: %v", settled)
	}
	// A transform value equal to one the state has already needs no payload.
	s := mustStep(t, merge, &State{}, OpStart{})
	s = mustStep(t, merge, s, OpInvoke{Placement: "sales"})
	call := s.Calls[0].ID
	s = mustStep(t, merge, s, OpReturned{Call: call, Value: "v"})
	next := mustStep(t, merge, s, OpDeliver{Connection: 1, Source: s.Results[0].ID, Value: ptr("v")})
	if got := Introduced(s, next); len(got) != 0 {
		t.Errorf("a repeated value is introduced again: %v", got)
	}
}

// A recorder continues a record after its committed transitions, wherever a crash cut it; the
// continued record replays to the state of the uncut one.
func TestRecorderFrom(t *testing.T) {
	for _, name := range append(definitionNames, extraDefinitions...) {
		p := load(t, name)
		// The longest of a few walks.
		var steps []Transition
		var text string
		var states []*State
		for seed := uint64(1); seed <= 6; seed++ {
			if s, x, st := recorded(t, p, seed); len(x) > len(text) {
				steps, text, states = s, x, st
			}
		}
		// The first line is the header; a cut inside it keeps nothing, and the header is written again.
		lines := strings.SplitAfter(text, "\n")
		lines = lines[:len(lines)-1]
		offset := 0
		for i, line := range lines {
			for _, cut := range []int{offset, offset + len(line)/2} {
				c := checkedText(t, name, text[:cut])
				committed, length := 0, 0
				if i > 0 {
					committed = (i - 1) / 2
					length = len(strings.Join(lines[:2*committed+1], ""))
				}
				if c.Committed != committed || c.Length != length || (c.Definition == nil) != (i == 0) {
					t.Fatalf("%s cut %d: committed %d, length %d", name, cut, c.Committed, c.Length)
				}
				recorder := NewRecorderFrom(p, c)
				continued := text[:c.Length]
				if c.Definition == nil {
					continued = header(p)
				}
				for _, step := range steps[c.Committed:] {
					records, err := recorder.RecordWith(step.Op, func(v string) (string, error) { return v, nil })
					if err != nil {
						t.Fatalf("%s cut %d: %s: %v", name, cut, EncodeOp(step.Op), err)
					}
					continued += RecordsText(records)
				}
				if continued != text || !recorder.State().Equal(states[len(states)-1]) {
					t.Fatalf("%s cut %d: the continued record differs", name, cut)
				}
			}
			offset += len(line)
		}
	}
	// RecordWith asks for no payload when the op is rejected, and fails without one.
	merge := load(t, "merge")
	recorder := NewRecorder(merge)
	asked := false
	if _, err := recorder.RecordWith(OpConclude{}, func(string) (string, error) { asked = true; return "", nil }); err == nil || asked {
		t.Errorf("rejected op: %v, asked %v", err, asked)
	}
	users := load(t, "users")
	if _, err := NewRecorder(users).RecordWith(OpStart{Input: ptr("t")}, func(string) (string, error) {
		return "", fmt.Errorf("no payload")
	}); err == nil || err.Error() != "no payload" {
		t.Errorf("missing payload: %v", err)
	}
	if _, err := NewRecorder(users).RecordWith(OpStart{Input: ptr("t")}, func(string) (string, error) { return "\xff", nil }); err == nil {
		t.Error("a payload must be valid UTF-8")
	}
}
