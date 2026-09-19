package suimon

import (
	"cmp"
	"encoding/json"
	"fmt"
	"slices"
)

type Event struct {
	SchemaVersion Nat             `json:"schema_version"`
	Sequence      Nat             `json:"sequence"`
	Txn           string          `json:"txn"`
	RecordedAt    Nat             `json:"recorded_at"`
	Type          string          `json:"type"`
	Op            *Op             `json:"op"`
	Data          json.RawMessage `json:"data"`
}
type Fact struct {
	Type string          `json:"type"`
	Data json.RawMessage `json:"data"`
}

func raw(v any) json.RawMessage { return json.RawMessage(compact(v)) }
func ParseEvent(data []byte) (Event, error) {
	var e Event
	if err := decodeCanonical(data, &e); err != nil {
		return e, err
	}
	if e.SchemaVersion != N(2) {
		return e, fmt.Errorf("unsupported event schema_version (expected 2)")
	}
	return e, nil
}

// EncodeEvent emits schema v2 JSON. Key order and number spelling are not part
// of the wire contract; Lean's parser also accepts this standard JSON spelling.
func EncodeEvent(e Event) string { return compact(e) }
func CommandType(o Op) string {
	switch o.Kind {
	case "start":
		return "execution.started"
	case "activate", "spawn":
		return "instance.created"
	case "claim":
		return "attempt.started"
	case "renew":
		return "lease.renewed"
	case "complete", "fail", "expireLease":
		return "attempt.finished"
	case "fireBranch":
		return "branch.taken"
	case "loopIterate":
		return "loop.iterated"
	case "fireFilter":
		return "filter.judged"
	case "fireWaitAll", "fireCoalesce", "fireCollect", "fireMerge", "propagateEos", "emit":
		return "token.placed"
	case "finishSubworkflow":
		return "instance.completed"
	case "skip":
		return "instance.skipped"
	case "promoteRetry":
		return "retry.promoted"
	case "manualRetry":
		return "retry.requested"
	case "idle", "cancel":
		return "execution.state_changed"
	}
	return ""
}
func opTime(o Op) *Nat {
	switch o.Kind {
	case "claim", "renew", "emit", "complete", "fail":
		return &o.Auth.Now
	case "expireLease", "promoteRetry":
		return &o.Now
	}
	return nil
}
func opActor(o Op) string {
	switch o.Kind {
	case "activate", "fireWaitAll", "fireBranch", "fireCollect", "fireFilter", "fireCoalesce", "fireMerge", "propagateEos", "skip":
		return InstanceID(o.Path, o.Node, nil)
	case "spawn":
		return InstanceID(o.Path, o.Node, &o.Item)
	case "claim", "renew", "emit", "complete", "fail":
		return o.Auth.Instance
	case "expireLease", "promoteRetry", "finishSubworkflow", "loopIterate", "manualRetry":
		return o.Inst
	}
	return "$execution"
}
func leaseProjection(l Lease) any {
	return map[string]any{"attempt": l.Attempt, "token": l.Token, "lease_until": l.Until}
}
func Effects(before, after State, o Op) List[Fact] {
	facts := List[Fact]{}
	add := func(kind string, v any) { facts = append(facts, Fact{kind, raw(v)}) }
	instances := slices.Clone(after.Instances)
	slices.SortStableFunc(instances, func(a, b Instance) int { return cmp.Compare(a.ID, b.ID) })
	for _, i := range instances {
		if before.Instance(i.ID) == nil {
			add("instance.created", map[string]any{"id": i.ID, "node": i.Node, "path": i.Path, "trigger": i.Trigger})
		}
	}
	attempts := slices.Clone(after.Attempts)
	slices.SortStableFunc(attempts, func(a, b Attempt) int { return cmp.Compare(a.ID, b.ID) })
	for _, a := range attempts {
		b := find(before.Attempts, func(b Attempt) bool { return b.ID == a.ID })
		if b == nil {
			var until *Nat
			if i := after.Instance(a.Instance); i != nil && i.Lease != nil {
				until = &i.Lease.Until
			}
			add("attempt.started", map[string]any{"attempt": a, "lease_until": until})
		} else if a.Status != b.Status {
			add("attempt.finished", a)
		}
	}
	for _, i := range instances {
		b := before.Instance(i.ID)
		if b != nil && i.Lease != nil && b.Lease != nil && *i.Lease != *b.Lease {
			add("lease.renewed", map[string]any{"instance": i.ID, "lease": leaseProjection(*i.Lease)})
		}
	}
	channels := slices.Clone(after.Channels)
	slices.SortStableFunc(channels, func(a, b Channel) int { return cmp.Compare(a.ID, b.ID) })
	for _, c := range channels {
		old := find(before.Channels, func(b Channel) bool { return b.ID == c.ID })
		length := 0
		if old != nil {
			length = len(old.Placed)
		}
		for _, t := range c.Placed[min(length, len(c.Placed)):] {
			add("token.placed", map[string]any{"edge": c.ID, "token": t, "by_instance": opActor(o)})
		}
	}
	consumed := slices.Clone(after.Consumed[min(len(before.Consumed), len(after.Consumed)):])
	slices.SortStableFunc(consumed, func(a, b Consumption) int {
		if c := cmp.Compare(a.Channel, b.Channel); c != 0 {
			return c
		}
		return a.Index.Cmp(b.Index)
	})
	for _, c := range consumed {
		add("token.consumed", map[string]any{"channel": c.Channel, "index": c.Index, "item": c.Item, "by_instance": c.ByInstance})
	}
	if before.Status != after.Status {
		add("execution.state_changed", map[string]any{"status": after.Status, "reason": after.Reason})
	}
	return facts
}
func RecordTransaction(s State, ops []Op, sequence Nat, txn string, time Nat) (State, List[Event], *Reject) {
	if len(ops) == 0 {
		return s, nil, reject("EMPTY_TRANSACTION")
	}
	if txn == "" {
		return s, nil, reject("EMPTY_TRANSACTION_ID")
	}
	state := s
	events := List[Event]{}
	add := func(kind string, op *Op, data json.RawMessage) {
		events = append(events, Event{N(2), sequence.Add(natLen(events)), txn, time, kind, op, data})
	}
	for _, o := range ops {
		clock := value(opTime(o), time)
		if time.Cmp(clock) > 0 {
			return s, nil, reject("CLOCK_REGRESSION")
		}
		time = clock
		next, r := Step(state, o)
		if r != nil {
			return s, nil, r
		}
		add(CommandType(o), ptr(o), raw(map[string]any{}))
		for _, f := range Effects(state, next, o) {
			add(f.Type, nil, f.Data)
		}
		state = next
	}
	add("transaction.committed", nil, raw(map[string]any{}))
	return state, events, nil
}

type Diagnostic struct {
	Sequence Nat             `json:"sequence"`
	Txn      string          `json:"txn"`
	Op       *Op             `json:"op"`
	Reason   Reject          `json:"reason"`
	Boundary json.RawMessage `json:"boundary"`
}

func (d *Diagnostic) Error() string { return d.Reason.Error() }
func summary(s State) json.RawMessage {
	return raw(map[string]any{"status": s.Status, "now": s.Now, "instances": s.Instances, "attempts": s.Attempts, "channels": s.Channels, "reason": s.Reason})
}

type Cursor struct {
	State     State
	Boundary  State
	Sequence  Nat
	Time      Nat
	Txn       *string
	Completed List[string]
	Expected  List[Fact]
	CurrentOp *Op
	Commands  Nat
}

func NewCursor(g Graph) Cursor { s := Initial(g); return Cursor{State: s, Boundary: s, Sequence: N(1)} }
func CheckEvent(c Cursor, e Event) (Cursor, *Diagnostic) {
	original := c
	op := e.Op
	if op == nil {
		op = c.CurrentOp
	}
	fail := func(code, msg string) (Cursor, *Diagnostic) {
		return original, &Diagnostic{e.Sequence, e.Txn, op, Reject{code, msg}, summary(c.Boundary)}
	}
	if e.SchemaVersion != N(2) {
		return fail("SCHEMA_VERSION", "expected event schema_version 2")
	}
	if e.Sequence != c.Sequence {
		return fail("SEQUENCE", "sequence must be contiguous and start at 1")
	}
	if e.Txn == "" || e.RecordedAt.Cmp(c.Time) < 0 {
		return fail("METADATA", "empty transaction or non-monotone clock")
	}
	if c.Txn == nil {
		if contains(c.Completed, e.Txn) {
			return fail("TXN_REUSE", "transaction id was already committed")
		}
		c.Txn = ptr(e.Txn)
	} else if *c.Txn != e.Txn {
		return fail("UNCOMMITTED_TXN", "previous transaction has no commit marker")
	}
	c.Sequence = c.Sequence.Inc()
	c.Time = e.RecordedAt
	if len(c.Expected) > 0 {
		f := c.Expected[0]
		if e.Op != nil || e.Type != f.Type || !sameValues(e.Data, f.Data) {
			return fail("EFFECT_MISMATCH", "expected "+f.Type+": "+compact(f.Data))
		}
		c.Expected = c.Expected[1:]
		return c, nil
	}
	if e.Type == "transaction.committed" {
		if e.Op != nil || !sameValues(e.Data, map[string]any{}) || c.Commands.IsZero() {
			return fail("INVALID_COMMIT", "commit must follow at least one complete operation")
		}
		c.Boundary = c.State
		c.Txn = nil
		c.Completed = append(slices.Clone(c.Completed), e.Txn)
		c.CurrentOp = nil
		c.Commands = Nat{}
		return c, nil
	}
	if e.Op == nil {
		return fail("MISSING_OPERATION", "expected a command with op")
	}
	o := *e.Op
	if e.Type != CommandType(o) || !sameValues(e.Data, map[string]any{}) {
		return fail("COMMAND_MISMATCH", "event type does not match operation")
	}
	if time := opTime(o); time != nil && *time != e.RecordedAt {
		return fail("CLOCK_MISMATCH", "operation time differs from recorded_at")
	}
	next, r := Step(c.State, o)
	if r != nil {
		return fail(r.Code, r.Message)
	}
	c.Expected = Effects(c.State, next, o)
	c.State = next
	c.CurrentOp = e.Op
	c.Commands = c.Commands.Inc()
	return c, nil
}
func CheckTextLine(c Cursor, line string) (Cursor, *Diagnostic) {
	e, err := ParseEvent([]byte(line))
	if err != nil {
		return c, &Diagnostic{c.Sequence, value(c.Txn, ""), c.CurrentOp, Reject{"INVALID_JSON", fmt.Sprintf("line %s: %v", c.Sequence, err)}, summary(c.Boundary)}
	}
	return CheckEvent(c, e)
}
func Finish(c Cursor) (State, *Diagnostic) {
	if c.Txn != nil {
		return c.Boundary, &Diagnostic{c.Sequence, *c.Txn, c.CurrentOp, Reject{"TRUNCATED_TRANSACTION", "missing effects or commit marker"}, summary(c.Boundary)}
	}
	return c.Boundary, nil
}
func Check(g Graph, events []Event) (State, *Diagnostic) {
	c := NewCursor(g)
	for _, e := range events {
		next, d := CheckEvent(c, e)
		if d != nil {
			return c.Boundary, d
		}
		c = next
	}
	return Finish(c)
}

// Recover validates every complete event and discards an uncommitted suffix.
func Recover(g Graph, events []Event) (State, *Diagnostic) {
	c := NewCursor(g)
	for _, e := range events {
		next, d := CheckEvent(c, e)
		if d != nil {
			return c.Boundary, d
		}
		c = next
	}
	return c.Boundary, nil
}
