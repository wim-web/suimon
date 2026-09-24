package suimon

import (
	"errors"
	"fmt"
	"slices"
	"strings"
	"unicode/utf8"
)

// The execution record of Suimon/Trace.lean (schema/trace.schema.json): one line per record. The
// first line is the header, which holds the definition of the execution and whether the execution
// was started with validation of it. Each accepted transition is then an op record followed by a
// commit record; only committed transitions are part of the record (§12.1).

// Payload is the serialized payload of a value, keyed by the value's identity.
type Payload struct {
	Value   string
	Payload string
}

// Record is one line of an execution record: an op record, or a commit record.
type Record struct {
	Seq int
	// Commit marks a commit record, which has no Op and no Values.
	Commit bool
	Op     Op
	// Values are the payloads of the values the transition introduces, in record order.
	Values []Payload
	// seqText is the sequence number as it was read, for messages.
	seqText string
}

// Introduced are the values the transition from before to after introduces: those after mentions
// and before does not, each once, including the lists the engine builds. Their payloads are stored
// by the commit of the transition, so a recovered state never names a lost value (§12.1).
func Introduced(before, after *State) []string {
	seen := map[string]bool{}
	for _, v := range before.Values() {
		seen[v] = true
	}
	var introduced []string
	for _, v := range after.Values() {
		if !seen[v] {
			introduced = append(introduced, v)
			seen[v] = true
		}
	}
	return introduced
}

func pathWire(path Path) wire {
	items := make([]wire, len(path))
	for i, segment := range path {
		items[i] = wireStr(segment)
	}
	return wireArr(items...)
}

// optional is the field when the value is present; an absent optional field is left out.
func optional(key string, value *string) []wireField {
	if value == nil {
		return nil
	}
	return []wireField{field(key, wireStr(*value))}
}

func typed(kind string, fields ...wireField) wire {
	return wireObj(append([]wireField{field("type", wireStr(kind))}, fields...)...)
}

// opWire is the wire form of an op: the type first, then the fields in the order of Lean's opWire.
func opWire(op Op) wire {
	switch op := op.(type) {
	case OpStart:
		return typed("start", optional("input", op.Input)...)
	case OpInvoke:
		return typed("invoke", append([]wireField{field("run", pathWire(op.Run)),
			field("placement", wireStr(op.Placement))}, optional("trigger", op.Trigger)...)...)
	case OpFetch:
		return typed("fetch", field("call", wireStr(op.Call)))
	case OpReturned:
		return typed("returned", field("call", wireStr(op.Call)), field("value", wireStr(op.Value)))
	case OpJudged:
		return typed("judged", field("call", wireStr(op.Call)), field("arm", wireStr(op.Arm)))
	case OpYielded:
		return typed("yielded", field("call", wireStr(op.Call)), field("value", wireStr(op.Value)))
	case OpEnded:
		return typed("ended", field("call", wireStr(op.Call)))
	case OpFailed:
		return typed("failed", field("call", wireStr(op.Call)))
	case OpTimedOut:
		return typed("timedOut", field("call", wireStr(op.Call)), field("element", wireBool(op.Element)))
	case OpLost:
		return typed("lost", field("call", wireStr(op.Call)))
	case OpTerminated:
		return typed("terminated", field("call", wireStr(op.Call)))
	case OpDeliver:
		return typed("deliver", append([]wireField{field("run", pathWire(op.Run)),
			field("connection", wireInt(op.Connection)), field("source", wireStr(op.Source))},
			optional("value", op.Value)...)...)
	case OpTransformFailed:
		return typed("transformFailed", field("run", pathWire(op.Run)), field("connection", wireInt(op.Connection)),
			field("source", wireStr(op.Source)))
	case OpTaskInput:
		return typed("taskInput", append([]wireField{field("execution", wireStr(op.Execution)),
			field("task", wireStr(op.Task))}, optional("value", op.Value)...)...)
	case OpTaskInputFailed:
		return typed("taskInputFailed", field("execution", wireStr(op.Execution)), field("task", wireStr(op.Task)))
	case OpBeginTask:
		return typed("beginTask", field("execution", wireStr(op.Execution)), field("task", wireStr(op.Task)))
	case OpTaskOutput:
		return typed("taskOutput", field("execution", wireStr(op.Execution)), field("task", wireStr(op.Task)),
			field("index", wireInt(op.Index)), field("value", wireStr(op.Value)))
	case OpTaskOutputFailed:
		return typed("taskOutputFailed", field("execution", wireStr(op.Execution)), field("task", wireStr(op.Task)),
			field("index", wireInt(op.Index)))
	case OpSettle:
		return typed("settle", field("run", pathWire(op.Run)), field("placement", wireStr(op.Placement)))
	case OpCloseExecution:
		return typed("closeExecution", field("execution", wireStr(op.Execution)))
	case OpCloseRun:
		return typed("closeRun", field("run", pathWire(op.Run)))
	case OpCancel:
		return typed("cancel")
	case OpConclude:
		return typed("conclude")
	}
	return wireNull()
}

// EncodeOp is the canonical JSON text of an op.
func EncodeOp(op Op) string { return opWire(op).render() }

// recordWire keeps the fields in a fixed order: seq, op, values and seq, commit. Empty values
// are left out.
func recordWire(r Record) wire {
	if r.Commit {
		return wireObj(field("seq", wireInt(r.Seq)), field("commit", wireBool(true)))
	}
	fields := []wireField{field("seq", wireInt(r.Seq)), field("op", opWire(r.Op))}
	if len(r.Values) > 0 {
		values := make([]wireField, len(r.Values))
		for i, v := range r.Values {
			values[i] = field(v.Value, wireStr(v.Payload))
		}
		fields = append(fields, field("values", wireObj(values...)))
	}
	return wireObj(fields...)
}

// EncodeRecord is the canonical line of a record, without the newline.
func EncodeRecord(r Record) string { return recordWire(r).render() }

// RecordsText is the text of records, each line ended by a newline.
func RecordsText(records []Record) string {
	var b strings.Builder
	for _, r := range records {
		b.WriteString(EncodeRecord(r))
		b.WriteByte('\n')
	}
	return b.String()
}

// Decoding looks fields up by name. The parser rejects a repeated key, so a name has at most one
// field.

func strictFields(w wire, allowed []string, at string) error {
	for _, f := range w.fields {
		if !slices.Contains(allowed, f.key) {
			return fmt.Errorf("%s: unknown field %s", at, f.key)
		}
	}
	return nil
}

func getText(w wire, key, at string) (string, error) {
	v, ok := w.lookup(key)
	if !ok {
		return "", fmt.Errorf("%s: missing field %s", at, key)
	}
	if v.kind != wireStrKind {
		return "", fmt.Errorf("%s.%s: expected a string", at, key)
	}
	return v.s, nil
}

// getOptionalText: an absent key is the only way to omit an optional field; null is rejected.
func getOptionalText(w wire, key, at string) (*string, error) {
	v, ok := w.lookup(key)
	if !ok {
		return nil, nil
	}
	if v.kind != wireStrKind {
		return nil, fmt.Errorf("%s.%s: expected a string", at, key)
	}
	return ptr(v.s), nil
}

// getNat reads a natural number. Lean's numbers have no bound; one beyond the int range is read as
// maxInt, which no sequence number, connection or result index reaches, so the record is rejected,
// or discarded as uncommitted, as in Lean. Only an error message can then show another number.
func getNat(w wire, key, at string) (int, error) {
	v, ok := w.lookup(key)
	if !ok {
		return 0, fmt.Errorf("%s: missing field %s", at, key)
	}
	if v.kind != wireNatKind {
		return 0, fmt.Errorf("%s.%s: expected a natural number", at, key)
	}
	if v.overflow || v.n > uint64(maxInt) {
		return maxInt, nil
	}
	return int(v.n), nil
}

const maxInt = int(^uint(0) >> 1)

func getBool(w wire, key, at string) (bool, error) {
	v, ok := w.lookup(key)
	if !ok {
		return false, fmt.Errorf("%s: missing field %s", at, key)
	}
	if v.kind != wireBoolKind {
		return false, fmt.Errorf("%s.%s: expected a boolean", at, key)
	}
	return v.b, nil
}

func getPath(w wire, key, at string) (Path, error) {
	v, ok := w.lookup(key)
	if !ok {
		return nil, fmt.Errorf("%s: missing field %s", at, key)
	}
	if v.kind != wireArrKind {
		return nil, fmt.Errorf("%s.%s: expected an array of strings", at, key)
	}
	path := make(Path, len(v.items))
	for i, item := range v.items {
		if item.kind != wireStrKind {
			return nil, fmt.Errorf("%s.%s: expected an array of strings", at, key)
		}
		path[i] = item.s
	}
	return path, nil
}

// fieldReader reads fields in order and keeps the first error, so that an op reads like its
// Lean decoder: the fields are read left to right and the first failure is reported.
type fieldReader struct {
	w   wire
	at  string
	err error
}

func (r *fieldReader) text(key string) string {
	if r.err != nil {
		return ""
	}
	s, err := getText(r.w, key, r.at)
	r.err = err
	return s
}

func (r *fieldReader) optionalText(key string) *string {
	if r.err != nil {
		return nil
	}
	s, err := getOptionalText(r.w, key, r.at)
	r.err = err
	return s
}

func (r *fieldReader) nat(key string) int {
	if r.err != nil {
		return 0
	}
	n, err := getNat(r.w, key, r.at)
	r.err = err
	return n
}

func (r *fieldReader) boolean(key string) bool {
	if r.err != nil {
		return false
	}
	b, err := getBool(r.w, key, r.at)
	r.err = err
	return b
}

func (r *fieldReader) path(key string) Path {
	if r.err != nil {
		return nil
	}
	p, err := getPath(r.w, key, r.at)
	r.err = err
	return p
}

func opOfWire(w wire) (Op, error) {
	if w.kind != wireObjKind {
		return nil, errors.New("op: expected an object")
	}
	const at = "op"
	kind, err := getText(w, "type", at)
	if err != nil {
		return nil, err
	}
	keys := func(names ...string) error {
		return strictFields(w, append([]string{"type"}, names...), at+" "+kind)
	}
	r := &fieldReader{w: w, at: at}
	var op Op
	switch kind {
	case "start":
		r.err = keys("input")
		op = OpStart{Input: r.optionalText("input")}
	case "invoke":
		r.err = keys("run", "placement", "trigger")
		op = OpInvoke{Run: r.path("run"), Placement: r.text("placement"), Trigger: r.optionalText("trigger")}
	case "fetch":
		r.err = keys("call")
		op = OpFetch{Call: r.text("call")}
	case "returned":
		r.err = keys("call", "value")
		op = OpReturned{Call: r.text("call"), Value: r.text("value")}
	case "judged":
		r.err = keys("call", "arm")
		op = OpJudged{Call: r.text("call"), Arm: r.text("arm")}
	case "yielded":
		r.err = keys("call", "value")
		op = OpYielded{Call: r.text("call"), Value: r.text("value")}
	case "ended":
		r.err = keys("call")
		op = OpEnded{Call: r.text("call")}
	case "failed":
		r.err = keys("call")
		op = OpFailed{Call: r.text("call")}
	case "timedOut":
		r.err = keys("call", "element")
		op = OpTimedOut{Call: r.text("call"), Element: r.boolean("element")}
	case "lost":
		r.err = keys("call")
		op = OpLost{Call: r.text("call")}
	case "terminated":
		r.err = keys("call")
		op = OpTerminated{Call: r.text("call")}
	case "deliver":
		r.err = keys("run", "connection", "source", "value")
		op = OpDeliver{Run: r.path("run"), Connection: r.nat("connection"), Source: r.text("source"),
			Value: r.optionalText("value")}
	case "transformFailed":
		r.err = keys("run", "connection", "source")
		op = OpTransformFailed{Run: r.path("run"), Connection: r.nat("connection"), Source: r.text("source")}
	case "taskInput":
		r.err = keys("execution", "task", "value")
		op = OpTaskInput{Execution: r.text("execution"), Task: r.text("task"), Value: r.optionalText("value")}
	case "taskInputFailed":
		r.err = keys("execution", "task")
		op = OpTaskInputFailed{Execution: r.text("execution"), Task: r.text("task")}
	case "beginTask":
		r.err = keys("execution", "task")
		op = OpBeginTask{Execution: r.text("execution"), Task: r.text("task")}
	case "taskOutput":
		r.err = keys("execution", "task", "index", "value")
		op = OpTaskOutput{Execution: r.text("execution"), Task: r.text("task"), Index: r.nat("index"),
			Value: r.text("value")}
	case "taskOutputFailed":
		r.err = keys("execution", "task", "index")
		op = OpTaskOutputFailed{Execution: r.text("execution"), Task: r.text("task"), Index: r.nat("index")}
	case "settle":
		r.err = keys("run", "placement")
		op = OpSettle{Run: r.path("run"), Placement: r.text("placement")}
	case "closeExecution":
		r.err = keys("execution")
		op = OpCloseExecution{Execution: r.text("execution")}
	case "closeRun":
		r.err = keys("run")
		op = OpCloseRun{Run: r.path("run")}
	case "cancel":
		r.err = keys()
		op = OpCancel{}
	case "conclude":
		r.err = keys()
		op = OpConclude{}
	default:
		return nil, fmt.Errorf("unknown op type %s", kind)
	}
	if r.err != nil {
		return nil, r.err
	}
	return op, nil
}

// DecodeOp reads an op from JSON text.
func DecodeOp(text string) (Op, error) {
	w, err := parseWire(text)
	if err != nil {
		return nil, err
	}
	return opOfWire(w)
}

func payloads(entries []wireField) ([]Payload, error) {
	out := make([]Payload, 0, len(entries))
	for _, e := range entries {
		if e.value.kind != wireStrKind {
			return nil, fmt.Errorf("record.values.%s: expected a string", e.key)
		}
		out = append(out, Payload{Value: e.key, Payload: e.value.s})
	}
	return out, nil
}

func recordOfWire(w wire) (Record, error) {
	if w.kind != wireObjKind {
		return Record{}, errors.New("record: expected an object")
	}
	seq, err := getNat(w, "seq", "record")
	if err != nil {
		return Record{}, err
	}
	seqWire, _ := w.lookup("seq")
	seqText := natText(seqWire)
	commit, hasCommit := w.lookup("commit")
	op, hasOp := w.lookup("op")
	switch {
	case hasCommit && commit.kind == wireBoolKind && commit.b && !hasOp:
		if err := strictFields(w, []string{"seq", "commit"}, "record"); err != nil {
			return Record{}, err
		}
		return Record{Seq: seq, Commit: true, seqText: seqText}, nil
	case !hasCommit && hasOp:
		if err := strictFields(w, []string{"seq", "op", "values"}, "record"); err != nil {
			return Record{}, err
		}
		var values []Payload
		if v, ok := w.lookup("values"); ok {
			if v.kind != wireObjKind {
				return Record{}, errors.New("record.values: expected an object")
			}
			if values, err = payloads(v.fields); err != nil {
				return Record{}, err
			}
		}
		o, err := opOfWire(op)
		if err != nil {
			return Record{}, err
		}
		return Record{Seq: seq, Op: o, Values: values, seqText: seqText}, nil
	}
	return Record{}, errors.New("record: either an op or a commit")
}

// DecodeRecord reads one line of an execution record, without its newline.
func DecodeRecord(line string) (Record, error) {
	w, err := parseWire(line)
	if err != nil {
		return Record{}, err
	}
	return recordOfWire(w)
}

// The header holds the definition in its canonical form (definitionWire), and whether the execution
// was started with validation of it: by NewEngine (run), or by NewUncheckedEngine (runUnchecked,
// §14). It has no seq, so no other line reads as a header, and it reads as no other line.

// headerWire keeps the fields in a fixed order: definition, validated.
func headerWire(definition wire, validated bool) wire {
	return wireObj(field("definition", definition), field("validated", wireBool(validated)))
}

func headerOfWire(w wire) (definition wire, validated bool, err error) {
	if w.kind != wireObjKind {
		return wire{}, false, errors.New("header: expected an object")
	}
	if err := strictFields(w, []string{"definition", "validated"}, "header"); err != nil {
		return wire{}, false, err
	}
	definition, ok := w.lookup("definition")
	if !ok {
		return wire{}, false, errors.New("header: missing field definition")
	}
	if validated, err = getBool(w, "validated", "header"); err != nil {
		return wire{}, false, err
	}
	return definition, validated, nil
}

// EncodeHeader is the header of an execution record of p, its first line, without the newline: the
// definition in its canonical form, so that equal definitions are recorded alike, and whether the
// execution was started with validation of p (§12.1).
func EncodeHeader(p *Definition, validated bool) string {
	return headerWire(definitionWire(p), validated).render()
}

// A HeaderLoader reads the definition that the header of a record holds, given as JSON text, with
// the flag of the header: whether the execution was started with validation of the definition. It
// returns the definition to replay the record against, or an error.
type HeaderLoader func(definition []byte, validated bool) (*Definition, error)

// LoadHeader reads the definition of a header by its flag, as suimon check does (Lean
// Trace.Header.load, §12.1). The definition of an execution that was started with validation is
// decoded and validated, like a definition file, so that a record that says so is refused when its
// definition fails validation. The definition of an execution that was started without validation
// is decoded only, so that the record replays against the definition that ran, valid or not;
// ParseDefinition still rejects what the definition file cannot express.
func LoadHeader(definition []byte, validated bool) (*Definition, error) {
	p, err := ParseDefinition(definition)
	if err != nil {
		return nil, err
	}
	if validated {
		if err := p.Validate(); err != nil {
			return nil, err
		}
	}
	return p, nil
}

// readHeader reads the header line and has load read its definition; it returns the flag too.
func readHeader(line string, load HeaderLoader) (*Definition, bool, error) {
	if !utf8.ValidString(line) {
		return nil, false, errors.New("invalid UTF-8")
	}
	w, err := parseWire(line)
	if err != nil {
		return nil, false, err
	}
	definition, validated, err := headerOfWire(w)
	if err != nil {
		return nil, false, err
	}
	p, err := load([]byte(definition.render()), validated)
	return p, validated, err
}

// sameDefinition is a HeaderLoader for Check that accepts only a record of p: the definition of the
// header must read back to the canonical form of p, and the record replays against p itself. When
// the header says that the execution was started with validation, p must pass validation too, or
// the error wraps ErrInvalidDefinition and the validation error (§12.1). Lean's Trace.resume replays
// against the definition of the header, which is p itself when the definition file can express p
// (resume_eq_ok_of_expressible), so the two replay alike.
func sameDefinition(p *Definition) HeaderLoader {
	canonical := definitionWire(p).render()
	return func(definition []byte, validated bool) (*Definition, error) {
		q, err := ParseDefinition(definition)
		if err != nil {
			return nil, err
		}
		if definitionWire(q).render() != canonical {
			return nil, ErrDefinitionMismatch
		}
		if validated {
			if err := p.Validate(); err != nil {
				return nil, &invalidDefinitionError{err}
			}
		}
		return p, nil
	}
}

// invalidDefinitionError is the error of Resume for a journal marked validated whose definition fails
// validation: it wraps ErrInvalidDefinition and the validation error.
type invalidDefinitionError struct{ err error }

func (e *invalidDefinitionError) Error() string {
	return ErrInvalidDefinition.Error() + ": " + e.err.Error()
}

func (e *invalidDefinitionError) Unwrap() []error { return []error{ErrInvalidDefinition, e.err} }

// Checked is what the committed transitions of a record establish.
type Checked struct {
	// Definition is the definition load gave for the header, which the record replays against; it is
	// nil when the record has no complete line.
	Definition *Definition
	// Validated is the flag of the header: whether the execution was started with validation of its
	// definition (§12.1). It is false when the record has no complete line.
	Validated bool
	State     *State
	// Committed is the number of committed transitions.
	Committed int
	// Uncommitted reports an operation or a partial line after the last commit, which recovery
	// discards.
	Uncommitted bool
	// Values are the payloads of the committed transitions.
	Values []Payload
	// Length is the length in bytes of the header and the committed lines, which recovery keeps: the
	// text after it is the uncommitted tail. It is not part of the Lean model.
	Length int
}

// replay is what the complete lines read so far establish.
type replay struct {
	// machine holds the state after the committed transitions, which Check owns.
	machine   *machine
	committed int
	values    []Payload
	// known holds the values of the payloads of the committed transitions.
	known map[string]bool
	// pending is the op read since the last commit, with its payloads.
	pending       Op
	pendingValues []Payload
	// next is the sequence number the next record must carry.
	next int
}

// missing are the values the transition from before to after introduces whose payloads are neither
// in the op record (values) nor in an earlier committed record (known).
func missing(before, after *State, values, known []Payload) []string {
	var absent []string
	for _, v := range Introduced(before, after) {
		if !hasPayload(values, v) && !hasPayload(known, v) {
			absent = append(absent, v)
		}
	}
	return absent
}

// unexpected are the values of the payloads that the transition does not introduce, in the order of
// the payloads. An op record may carry a payload only for a value its transition introduces, which the
// state before does not mention, so a committed payload is never repeated or contradicted by a later
// one (§12.1).
func unexpected(introduced []string, values []Payload) []string {
	var extra []string
	for _, v := range values {
		if !slices.Contains(introduced, v.Value) {
			extra = append(extra, v.Value)
		}
	}
	return extra
}

// errUnexpected is the error for payloads of values the transition does not introduce.
func errUnexpected(extra []string) error {
	return fmt.Errorf("payloads for %s, which the transition does not introduce", leanList(extra))
}

// unknown are the introduced values whose payloads are neither in values nor known.
func unknown(introduced []string, values []Payload, known map[string]bool) []string {
	var absent []string
	for _, v := range introduced {
		if !hasPayload(values, v) && !known[v] {
			absent = append(absent, v)
		}
	}
	return absent
}

func hasPayload(values []Payload, v string) bool {
	for _, p := range values {
		if p.Value == v {
			return true
		}
	}
	return false
}

// leanList renders a list of strings as Lean's toString does: [a, b].
func leanList(xs []string) string { return "[" + strings.Join(xs, ", ") + "]" }

// replayLine replays one complete line; the op of a transition is applied at its commit, which
// also checks the payloads: the op record carries payloads only for values the transition
// introduces, and each of them has one.
func replayLine(r *replay, index int, line string) error {
	if err := replayRecord(r, line); err != nil {
		return fmt.Errorf("line %d: %w", index+1, err)
	}
	return nil
}

func replayRecord(r *replay, line string) error {
	if !utf8.ValidString(line) {
		return errors.New("invalid UTF-8")
	}
	record, err := DecodeRecord(line)
	if err != nil {
		return err
	}
	if record.Seq != r.next {
		return fmt.Errorf("expected sequence %d, got %s", r.next, record.seqText)
	}
	switch {
	case !record.Commit && r.pending == nil:
		r.pending, r.pendingValues = record.Op, record.Values
		r.next++
	case record.Commit && r.pending != nil:
		// The machine changes the state in place; after an error, Check drops it.
		introduced, err := r.machine.apply(r.pending)
		if err != nil {
			return fmt.Errorf("rejected %s: %w", EncodeOp(r.pending), err)
		}
		if extra := unexpected(introduced, r.pendingValues); len(extra) > 0 {
			return errUnexpected(extra)
		}
		if absent := unknown(introduced, r.pendingValues, r.known); len(absent) > 0 {
			return fmt.Errorf("missing payloads for %s", leanList(absent))
		}
		r.committed++
		r.values = append(r.values, r.pendingValues...)
		for _, v := range r.pendingValues {
			r.known[v.Value] = true
		}
		r.pending, r.pendingValues = nil, nil
		r.next++
	case !record.Commit:
		return errors.New("an op before the previous commit")
	default:
		return errors.New("a commit without an op")
	}
	return nil
}

// Check replays the committed transitions of a record. The first line is the header: load reads the
// definition it holds, given as JSON text, with the flag of the header, and returns the definition to
// replay the other lines against, or an error, which Check reports for line 1. Line numbers count the
// header. A crash may leave an op without its commit, and a partial last line, which may be the
// header and may end inside a UTF-8 sequence; both are reported as uncommitted and ignored. Anything
// else that is malformed, out of order or rejected by Step is an error.
//
// A reader of a record loads the definition with LoadHeader, as the CLI does; Resume accepts only the
// definition of its engine.
func Check(text string, load HeaderLoader) (Checked, error) {
	lines := strings.Split(text, "\n")
	complete, tail := lines[:len(lines)-1], lines[len(lines)-1]
	if len(complete) == 0 {
		return Checked{State: &State{}, Uncommitted: tail != ""}, nil
	}
	p, validated, err := readHeader(complete[0], load)
	if err != nil {
		return Checked{}, fmt.Errorf("line 1: %w", err)
	}
	r := &replay{machine: newMachine(p, p.derive(), &State{}), known: map[string]bool{}, next: 1}
	offset := len(complete[0]) + 1
	length := offset
	for index, line := range complete[1:] {
		if err := replayLine(r, index+1, line); err != nil {
			return Checked{}, err
		}
		offset += len(line) + 1
		if r.pending == nil {
			length = offset
		}
	}
	return Checked{Definition: p, Validated: validated, State: r.machine.s, Committed: r.committed,
		Uncommitted: r.pending != nil || tail != "", Values: r.values, Length: length}, nil
}

// Recover is the state a crashed run resumes from: the state after the committed transitions. load
// is as for Check.
func Recover(text string, load HeaderLoader) (*State, error) {
	c, err := Check(text, load)
	if err != nil {
		return nil, err
	}
	return c.State, nil
}

// Transaction is the records of one accepted transition, starting at seq, under the rules Check
// applies: the op record holds at most one payload per value and only payloads of values the
// transition introduces, and each value the transition introduces has its payload in values, the
// payloads of the op record, or in known, the payloads of the transitions recorded before. Payloads
// must be UTF-8.
func Transaction(p *Definition, s *State, op Op, values, known []Payload, seq int) (*State, []Record, error) {
	if err := checkPayloads(values); err != nil {
		return nil, nil, err
	}
	next, err := Step(p, s, op)
	if err != nil {
		return nil, nil, err
	}
	if extra := unexpected(Introduced(s, next), values); len(extra) > 0 {
		return nil, nil, errUnexpected(extra)
	}
	if absent := missing(s, next, values, known); len(absent) > 0 {
		return nil, nil, fmt.Errorf("missing payloads for %s", leanList(absent))
	}
	return next, []Record{{Seq: seq, Op: op, Values: values}, {Seq: seq + 1, Commit: true}}, nil
}

// checkPayloads checks the payloads given for an op record: UTF-8, and one per value, since a line
// may not repeat a key.
func checkPayloads(values []Payload) error {
	for _, v := range values {
		if !utf8.ValidString(v.Value) || !utf8.ValidString(v.Payload) {
			return fmt.Errorf("payload of %q is not valid UTF-8", v.Value)
		}
	}
	if repeated := duplicates(values); len(repeated) > 0 {
		return fmt.Errorf("duplicate payloads for %s", leanList(repeated))
	}
	return nil
}

// duplicates are the values that have more than one payload, each once, in the order they first
// occur (Lean duplicates).
func duplicates(values []Payload) []string {
	count := make(map[string]int, len(values))
	for _, v := range values {
		count[v.Value]++
	}
	var repeated []string
	for _, v := range values {
		if count[v.Value] > 1 {
			repeated = append(repeated, v.Value)
			count[v.Value] = 0
		}
	}
	return repeated
}

// Transition is an op with the payloads of the values it introduces.
type Transition struct {
	Op     Op
	Values []Payload
}

// RecordTransitions records consecutive transactions from sequence number seq, after transitions
// whose payloads are known.
func RecordTransitions(p *Definition, s *State, transitions []Transition, known []Payload, seq int) (*State, []Record, error) {
	var records []Record
	for _, t := range transitions {
		next, rs, err := Transaction(p, s, t.Op, t.Values, known, seq)
		if err != nil {
			return nil, nil, err
		}
		s, records, seq = next, append(records, rs...), seq+len(rs)
		known = append(slices.Clip(known), t.Values...)
	}
	return s, records, nil
}

// Recorder writes the records of the transitions of one execution as they are accepted. Like
// Step, it never changes a state it has returned.
type Recorder struct {
	definition *Definition
	state      *State
	// seen holds the values the state mentions, and known the values whose payloads earlier
	// records carry.
	seen  map[string]struct{}
	known map[string]bool
	seq   int
}

// NewRecorder starts recording an execution of p from the state before the start.
func NewRecorder(p *Definition) *Recorder {
	return &Recorder{definition: p, state: &State{}, seen: map[string]struct{}{}, known: map[string]bool{}, seq: 1}
}

// NewRecorderFrom continues recording after the committed transitions of c, the result of Check
// on a record of p: the next records follow them, and their payloads count as known. The text
// after c.Length, if any, must be discarded before appending the new records, which follow the
// header as it was written; a record without a complete line needs the header first (EncodeHeader).
func NewRecorderFrom(p *Definition, c Checked) *Recorder {
	r := &Recorder{definition: p, state: c.State, seen: map[string]struct{}{}, known: map[string]bool{},
		seq: 2*c.Committed + 1}
	for _, v := range c.State.Values() {
		r.seen[v] = struct{}{}
	}
	for _, v := range c.Values {
		r.known[v.Value] = true
	}
	return r
}

// step is Step, with the values op introduces.
func (r *Recorder) step(op Op) (*State, []string, error) {
	t := *r.state
	st := &stepper{view: view{s: &t}, p: r.definition}
	if err := st.apply(op); err != nil {
		return nil, nil, err
	}
	return st.s, st.introduced(r.seen), nil
}

// Needs are the values whose payloads Record needs for op: the values op introduces that no
// earlier record carries.
func (r *Recorder) Needs(op Op) ([]string, error) {
	_, introduced, err := r.step(op)
	if err != nil {
		return nil, err
	}
	return unknown(introduced, nil, r.known), nil
}

// Record applies op and returns its records; a rejected op records nothing. values holds at most
// one payload per value, and only payloads of values op introduces.
func (r *Recorder) Record(op Op, values []Payload) ([]Record, error) {
	if err := checkPayloads(values); err != nil {
		return nil, err
	}
	next, introduced, err := r.step(op)
	if err != nil {
		return nil, err
	}
	if extra := unexpected(introduced, values); len(extra) > 0 {
		return nil, errUnexpected(extra)
	}
	if absent := unknown(introduced, values, r.known); len(absent) > 0 {
		return nil, fmt.Errorf("missing payloads for %s", leanList(absent))
	}
	r.state = next
	return r.commit(op, introduced, values), nil
}

// RecordWith applies op and returns its records like Record, stepping once: it takes the payload
// of each value the transition introduces that no earlier record carries from payload, in the
// order of Introduced. A rejected op records nothing and asks for no payload.
func (r *Recorder) RecordWith(op Op, payload func(value string) (string, error)) ([]Record, error) {
	next, introduced, err := r.step(op)
	if err != nil {
		return nil, err
	}
	values, err := payloadsOf(unknown(introduced, nil, r.known), payload)
	if err != nil {
		return nil, err
	}
	r.state = next
	return r.commit(op, introduced, values), nil
}

// payloadsOf takes the payload of each value from payload.
func payloadsOf(needs []string, payload func(value string) (string, error)) ([]Payload, error) {
	values := make([]Payload, 0, len(needs))
	for _, v := range needs {
		text, err := payload(v)
		if err != nil {
			return nil, err
		}
		if !utf8.ValidString(v) || !utf8.ValidString(text) {
			return nil, fmt.Errorf("payload of %q is not valid UTF-8", v)
		}
		values = append(values, Payload{Value: v, Payload: text})
	}
	return values, nil
}

func (r *Recorder) commit(op Op, introduced []string, values []Payload) []Record {
	records := []Record{{Seq: r.seq, Op: op, Values: values}, {Seq: r.seq + 1, Commit: true}}
	r.seq += len(records)
	for _, v := range introduced {
		r.seen[v] = struct{}{}
	}
	for _, v := range values {
		r.known[v.Value] = true
	}
	return records
}

// State is the state after the recorded transitions.
func (r *Recorder) State() *State { return r.state }

// ownedRecorder records the transitions of the runtime like a Recorder, but owns its state and
// changes it in place (machine), so that a transition costs what it changes. The state it returns
// changes with each transition.
type ownedRecorder struct {
	machine *machine
	known   map[string]bool
	seq     int
}

// newOwnedRecorder continues recording after committed transitions that led to s, with the
// payloads of values; it takes s over. d is a derivation of p.
func newOwnedRecorder(p *Definition, d *derivation, s *State, values []Payload, committed int) *ownedRecorder {
	r := &ownedRecorder{machine: newMachine(p, d, s), known: map[string]bool{}, seq: 2*committed + 1}
	for _, v := range values {
		r.known[v.Value] = true
	}
	return r
}

// recordWith is Recorder.RecordWith. A rejected op changes nothing; after any other error the
// state has changed without records, and the recorder must not be used again.
func (r *ownedRecorder) recordWith(op Op, payload func(value string) (string, error)) ([]Record, error) {
	introduced, err := r.machine.apply(op)
	if err != nil {
		return nil, err
	}
	values, err := payloadsOf(unknown(introduced, nil, r.known), payload)
	if err != nil {
		return nil, err
	}
	records := []Record{{Seq: r.seq, Op: op, Values: values}, {Seq: r.seq + 1, Commit: true}}
	r.seq += len(records)
	for _, v := range values {
		r.known[v.Value] = true
	}
	return records, nil
}
