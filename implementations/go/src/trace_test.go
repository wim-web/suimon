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

// recorded is the record of a random walk: its transitions with the payloads gen writes, the text,
// and the state before the first transition and after each committed one.
func recorded(t *testing.T, p *Program, seed uint64) ([]Transition, string, []*State) {
	t.Helper()
	_, ops := Walk(p, DefaultConfig(), seed, 10000)
	recorder := NewRecorder(p)
	states := []*State{recorder.State()}
	var steps []Transition
	var text strings.Builder
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

func checked(t *testing.T, label string, p *Program, text string) Checked {
	t.Helper()
	c, err := Check(p, text)
	if err != nil {
		t.Fatalf("%s: %v", label, err)
	}
	return c
}

func rejectedTrace(t *testing.T, label, fragment string, p *Program, text string) {
	t.Helper()
	_, err := Check(p, text)
	if err == nil {
		t.Errorf("%s: accepted, expected %q", label, fragment)
	} else if !hasFragment(err.Error(), fragment) {
		t.Errorf("%s: expected %q, got %v", label, fragment, err)
	}
}

// half is the first half of a line in characters, like Lean's line.take (line.length / 2).
func half(line string) string {
	runes := []rune(line)
	return string(runes[:len(runes)/2])
}

func TestTraceReplay(t *testing.T) {
	for _, name := range append(programNames, extraPrograms...) {
		p := load(t, name)
		listCases := 0
		for seed := uint64(1); seed <= 20; seed++ {
			label := fmt.Sprintf("%s seed %d", name, seed)
			steps, text, states := recorded(t, p, seed)
			final := states[len(states)-1]
			// Replaying a whole record reproduces the state of the run that wrote it.
			whole := checked(t, label, p, text)
			if !whole.State.Equal(final) || whole.Committed+1 != len(states) || whole.Uncommitted {
				t.Fatalf("%s: replay differs from the run", label)
			}
			for _, v := range whole.State.Values() {
				if !hasPayload(whole.Values, v) {
					t.Fatalf("%s: a value without payload: %s", label, v)
				}
			}
			// A commit needs the payload of each value its transition introduces, lists the engine
			// builds included; an earlier committed record may hold it, a later one may not.
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
				rejectedTrace(t, label+" list payload", fmt.Sprintf("line %d: missing payloads", 2*i+2), p, written(stripped))
				if _, _, err := RecordTransitions(p, &State{}, stripped, nil, 1); err == nil || !hasFragment(err.Error(), "missing payloads") {
					t.Fatalf("%s: recorder without a list payload: %v", label, err)
				}
				early := with(0, lists)
				if c := checked(t, label+" early payload", p, written(early)); !c.State.Equal(final) || c.Uncommitted {
					t.Fatalf("%s: early payload", label)
				}
				if got, _, err := RecordTransitions(p, &State{}, early, nil, 1); err != nil || !got.Equal(final) {
					t.Fatalf("%s: recorder with an early payload: %v", label, err)
				}
				if i+1 < len(steps) {
					rejectedTrace(t, label+" later payload", fmt.Sprintf("line %d: missing payloads", 2*i+2), p, written(with(i+1, lists)))
				}
				listCases++
				break
			}
			// Every op survives its encoding, and every line is canonical.
			for _, line := range strings.Split(text, "\n") {
				if line == "" {
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
			// A crash may cut the record anywhere; recovery keeps exactly the committed transitions.
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
				for _, text := range []string{prefix, torn} {
					c := checked(t, fmt.Sprintf("%s cut %d", label, cut), p, text)
					if c.Committed != cut/2 || !c.State.Equal(states[cut/2]) {
						t.Fatalf("%s cut %d: wrong recovered state", label, cut)
					}
					if c.Uncommitted != (cut%2 == 1 || len(text) > len(prefix)) {
						t.Fatalf("%s cut %d: uncommitted flag", label, cut)
					}
					if recovered, err := Recover(p, text); err != nil || !recovered.Equal(states[cut/2]) {
						t.Fatalf("%s cut %d: recover", label, cut)
					}
				}
			}
			// Corruption before the last commit is an error, not a torn tail.
			if len(lines) >= 4 {
				corrupt := append([]string(nil), lines...)
				corrupt[1] = `{"seq":2`
				rejectedTrace(t, label+" corrupt", "line 2", p, strings.Join(corrupt, "\n")+"\n")
				reordered := append([]string{lines[1], lines[0]}, lines[2:]...)
				rejectedTrace(t, label+" reordered", "expected sequence 1", p, strings.Join(reordered, "\n")+"\n")
			}
		}
		if listCases == 0 {
			t.Errorf("%s: no walk built a list", name)
		}
	}
}

func TestTraceRejections(t *testing.T) {
	merge := load(t, "merge")
	start := "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
	rejectedTrace(t, "commit twice", "a commit without an op", merge, start+"{\"seq\":3,\"commit\":true}\n")
	again := strings.ReplaceAll(strings.ReplaceAll(start, `"seq":1`, `"seq":3`), `"seq":2`, `"seq":4`)
	rejectedTrace(t, "rejected op", "rejected", merge, start+again)
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
	rejectedTrace(t, "empty line", "line 1", merge, "\n")
	torn := checked(t, "torn start", merge, "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"com")
	if torn.Committed != 0 || !torn.Uncommitted || !torn.State.Equal(&State{}) {
		t.Errorf("torn start: %+v", torn)
	}
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
			"line 2: missing payloads for [t]"},
		{"rejected op", start + again, `line 4: rejected {"type":"start"}: ALREADY_STARTED`},
		{"an op before the commit", "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"op\":{\"type\":\"start\"}}\n",
			"line 2: an op before the previous commit"},
		{"parse error", "{\"seq\":1,\n", "line 1: unterminated object at offset 9"},
		{"not an object", "[]\n", "line 1: record: expected an object"},
		{"neither", "{\"seq\":1}\n", "line 1: record: either an op or a commit"},
		{"commit false", "{\"seq\":1,\"commit\":false}\n", "line 1: record: either an op or a commit"},
		{"unknown field", "{\"seq\":1,\"commit\":true,\"at\":0}\n", "line 1: record: unknown field at"},
		{"values", "{\"seq\":1,\"op\":{\"type\":\"start\"},\"values\":[]}\n", "line 1: record.values: expected an object"},
		{"payload", "{\"seq\":1,\"op\":{\"type\":\"start\"},\"values\":{\"v\":1}}\n", "line 1: record.values.v: expected a string"},
		{"op field", "{\"seq\":1,\"op\":{\"type\":\"fetch\",\"call\":\"c\",\"x\":1}}\n", "line 1: op fetch: unknown field x"},
		{"op type", "{\"seq\":1,\"op\":{\"type\":\"jump\"}}\n", "line 1: unknown op type jump"},
		{"null", "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":null}}\n", "line 1: op.input: expected a string"},
		{"path", "{\"seq\":1,\"op\":{\"type\":\"closeRun\",\"run\":[1]}}\n", "line 1: op.run: expected an array of strings"},
		{"negative", "{\"seq\":-1,\"commit\":true}\n", "line 1: unexpected character '-' at offset 7"},
		{"seq", "{\"seq\":2,\"commit\":true}\n", "line 1: expected sequence 1, got 2"},
		{"huge", "{\"seq\":99999999999999999999,\"commit\":true}\n", "line 1: expected sequence 1, got 99999999999999999999"},
		{"huge index", "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":\"x\"}}\n{\"seq\":2,\"commit\":true}\n" +
			"{\"seq\":3,\"op\":{\"type\":\"taskOutputFailed\",\"execution\":\"e\",\"task\":\"t\",\"index\":99999999999999999999}}\n{\"seq\":4,\"commit\":true}\n",
			"line 4: rejected {\"type\":\"taskOutputFailed\",\"execution\":\"e\",\"task\":\"t\",\"index\":9223372036854775807}: UNKNOWN_EXECUTION"},
		{"invalid UTF-8", "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"\xff\"}}\n", "line 1: invalid UTF-8"},
	}
	for _, c := range exact {
		_, err := Check(users, c.text)
		if c.label == "rejected op" || c.label == "an op before the commit" {
			_, err = Check(merge, c.text)
		}
		if err == nil || err.Error() != c.want {
			t.Errorf("%s: got %v, want %q", c.label, err, c.want)
		}
	}
}

func TestTornTail(t *testing.T) {
	merge := load(t, "merge")
	start := "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
	// A crash inside a multi-byte character leaves invalid UTF-8 in the partial last line only.
	c, err := Check(merge, start+"{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"\xe3\x81")
	if err != nil || c.Committed != 1 || !c.Uncommitted {
		t.Errorf("torn tail: %+v %v", c, err)
	}
	// The first field of a name counts; every field must be known.
	c, err = Check(merge, "{\"seq\":1,\"seq\":7,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n")
	if err != nil || c.Committed != 1 {
		t.Errorf("duplicate field: %+v %v", c, err)
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
	records, err := recorder.Record(OpStart{Input: ptr("t")}, []Payload{{"t", `{"tenant":1}`}})
	if err != nil || len(records) != 2 || records[0].Seq != 1 || !records[1].Commit || records[1].Seq != 2 {
		t.Fatalf("start: %+v %v", records, err)
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
	for _, name := range append(programNames, extraPrograms...) {
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
		lines := strings.SplitAfter(text, "\n")
		lines = lines[:len(lines)-1]
		offset := 0
		for i, line := range lines {
			for _, cut := range []int{offset, offset + len(line)/2} {
				c := checked(t, name, p, text[:cut])
				if c.Committed != i/2 || c.Length != len(strings.Join(lines[:2*c.Committed], "")) {
					t.Fatalf("%s cut %d: committed %d, length %d", name, cut, c.Committed, c.Length)
				}
				recorder := NewRecorderFrom(p, c)
				continued := text[:c.Length]
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
