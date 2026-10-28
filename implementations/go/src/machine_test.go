package suimon

import (
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"reflect"
	"slices"
	"strings"
	"testing"
)

// The machine, which changes its state in place through an index, against Step, which copies:
// along random walks, every candidate operation must be accepted or rejected alike, with the same
// error, state and introduced values, and Step must leave its state unchanged.

// cloneState snapshots every Go field, including nested paths, optional values and task lists.
// Use a distinct type to bypass State.MarshalJSON: that wire representation is production code
// under test, and may omit fields which do not affect the current constructor of a value.
func cloneState(s *State) *State {
	type stateFields State
	data, err := json.Marshal((*stateFields)(s))
	if err != nil {
		panic(fmt.Errorf("snapshot state: %w", err))
	}
	var snapshot stateFields
	if err := json.Unmarshal(data, &snapshot); err != nil {
		panic(fmt.Errorf("restore state snapshot: %w", err))
	}
	return (*State)(&snapshot)
}

func sameError(a, b error) bool {
	if a == nil || b == nil {
		return a == nil && b == nil
	}
	var ra, rb *Rejection
	return errors.As(a, &ra) && errors.As(b, &rb) && ra.Code == rb.Code
}

// checkMachine checks that the index and the values of m are those of its state.
func checkMachine(t *testing.T, label string, m *machine) {
	t.Helper()
	if !reflect.DeepEqual(m.ix, newStateIndex(m.s)) {
		t.Fatalf("%s: the index differs from the index of the state", label)
	}
	seen := map[string]struct{}{}
	for _, v := range m.s.Values() {
		seen[v] = struct{}{}
	}
	if !reflect.DeepEqual(m.seen, seen) {
		t.Fatalf("%s: the values differ from those of the state", label)
	}
}

// agree compares Step and a fresh machine on op in s.
func agree(t *testing.T, label string, p *Definition, s *State, op Op) {
	t.Helper()
	next, err := Step(p, s, op)
	m := newMachine(p, p.derive(), cloneState(s))
	introduced, fastErr := m.apply(op)
	if !sameError(err, fastErr) {
		t.Fatalf("%s: %s: Step %v, machine %v", label, EncodeOp(op), err, fastErr)
	}
	if err != nil {
		if !reflect.DeepEqual(m.s, s) {
			t.Fatalf("%s: %s: the machine changed its state on a rejection", label, EncodeOp(op))
		}
		checkMachine(t, label+" rejected "+EncodeOp(op), m)
		return
	}
	if !m.s.Equal(next) {
		t.Fatalf("%s: %s: the machine reached another state", label, EncodeOp(op))
	}
	if want := Introduced(s, next); !slices.Equal(introduced, want) {
		t.Fatalf("%s: %s: introduced %q, want %q", label, EncodeOp(op), introduced, want)
	}
	checkMachine(t, label+" "+EncodeOp(op), m)
}

func TestMachineAgreesWithStep(t *testing.T) {
	definitions := append(append([]string{}, definitionNames...), extraDefinitions...)
	definitions = append(definitions, "limit")
	for _, name := range definitions {
		p := load(t, name)
		for _, cfg := range []Config{DefaultConfig(), {MaxYields: 3, Disruption: 40}} {
			for seed := range 12 {
				label := fmt.Sprintf("%s seed %d failures %t", name, seed, cfg.Failures)
				s := &State{}
				m := newMachine(p, p.derive(), &State{})
				rng := uint64(seed + 1)
				for step := 0; step < 2000; step++ {
					snapshot := cloneState(s)
					for _, op := range Candidates(p, cfg, s) {
						agree(t, label, p, s, op)
					}
					if !reflect.DeepEqual(s, snapshot) {
						t.Fatalf("%s: Step changed its state", label)
					}
					choices := Accepted(p, cfg, s)
					if len(choices) == 0 {
						break
					}
					rng = NextSeed(rng)
					choice, ok := Pick(cfg, s, rng, choices)
					if !ok {
						break
					}
					if _, err := m.apply(choice.Op); err != nil {
						t.Fatalf("%s: the machine rejected %s: %v", label, EncodeOp(choice.Op), err)
					}
					s = choice.Next
					if !m.s.Equal(s) {
						t.Fatalf("%s: the machine diverged at %s", label, EncodeOp(choice.Op))
					}
				}
				checkMachine(t, label, m)
				if !s.Status.Terminal() {
					t.Fatalf("%s: stuck in %v", label, s.Status)
				}
			}
		}
	}
}

// Rejections that candidate generation avoids. Build the state with explicit accepted operations
// so a change in the walk's choices cannot silently turn one of these into a successful operation.
func TestMachineRejections(t *testing.T) {
	p := load(t, "users")
	call := keyInvocation(nil, "fetchAllUsers", nil)
	result := keyCallResult(call, 0)
	execution := keyInvocation(nil, "perUser", &result)
	s := &State{}
	for _, op := range []Op{
		OpStart{Input: ptr("tenant")}, OpInvoke{Placement: "fetchAllUsers"},
		OpFetch{Call: call}, OpYielded{Call: call, Value: "user"},
		OpDeliver{Connection: 0, Source: result, Value: ptr("input")},
		OpInvoke{Placement: "perUser", Trigger: &result},
		OpTaskInput{Execution: execution, Task: "orders", Value: ptr("user-id")},
	} {
		s = mustStep(t, p, s, op)
	}
	cases := []struct {
		name string
		op   Op
		code string
	}{
		{"started twice", OpStart{}, "ALREADY_STARTED"},
		{"invoke unknown run", OpInvoke{Run: Path{"x"}, Placement: "perUser"}, "UNKNOWN_RUN"},
		{"invoke unknown placement", OpInvoke{Placement: "x"}, "UNKNOWN_PLACEMENT"},
		{"duplicate invocation", OpInvoke{Placement: "fetchAllUsers"}, "DUPLICATE_INVOCATION"},
		{"invoke missing delivery", OpInvoke{Placement: "perUser", Trigger: ptr("x")}, "INPUT_NOT_READY"},
		{"fetch unknown call", OpFetch{Call: "x"}, "UNKNOWN_CALL"},
		{"return from stream", OpReturned{Call: call, Value: "v"}, "NOT_RETURNABLE"},
		{"judge non-judge", OpJudged{Call: call, Arm: "x"}, "NOT_JUDGING"},
		{"yield without fetch", OpYielded{Call: call, Value: "v"}, "NOT_FETCHING"},
		{"end without fetch", OpEnded{Call: call}, "NOT_FETCHING"},
		{"element timeout without fetch", OpTimedOut{Call: call, Element: true}, "NO_TIMEOUT"},
		{"terminate running call", OpTerminated{Call: call}, "NOT_CANCELLING"},
		{"deliver unknown connection", OpDeliver{Connection: 9, Source: "x"}, "UNKNOWN_CONNECTION"},
		{"deliver unknown result", OpDeliver{Connection: 0, Source: "x"}, "UNKNOWN_RESULT"},
		{"transform unknown run", OpTransformFailed{Run: Path{"x"}, Connection: 0, Source: "x"}, "UNKNOWN_RUN"},
		{"input unknown execution", OpTaskInput{Execution: "x", Task: "orders"}, "UNKNOWN_EXECUTION"},
		{"input unknown task", OpTaskInput{Execution: execution, Task: "x"}, "UNKNOWN_TASK"},
		{"input failure after ready", OpTaskInputFailed{Execution: execution, Task: "orders"}, "NOT_PENDING"},
		{"begin unknown task", OpBeginTask{Execution: execution, Task: "x"}, "UNKNOWN_TASK"},
		{"output unknown index", OpTaskOutput{Execution: execution, Task: "orders", Index: 7, Value: "v"}, "UNKNOWN_RESULT"},
		{"output failure unknown task", OpTaskOutputFailed{Execution: execution, Task: "x", Index: 0}, "UNKNOWN_TASK"},
		{"settle before stream ends", OpSettle{Placement: "all"}, "NOT_READY"},
		{"settle unknown run", OpSettle{Run: Path{"x"}, Placement: "all"}, "UNKNOWN_RUN"},
		{"close unknown execution", OpCloseExecution{Execution: "x"}, "UNKNOWN_EXECUTION"},
		{"close unfinished execution", OpCloseExecution{Execution: execution}, "TASKS_RUNNING"},
		{"close root", OpCloseRun{Run: Path{}}, "NOT_CLOSABLE"},
		{"close unknown run", OpCloseRun{Run: Path{"x"}}, "UNKNOWN_RUN"},
		{"conclude before settlement", OpConclude{}, "NOT_SETTLED"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			before := cloneState(s)
			m := newMachine(p, p.derive(), cloneState(s))
			index, seen := newStateIndex(before), maps.Clone(m.seen)
			_, slowErr := Step(p, s, tc.op)
			introduced, fastErr := m.apply(tc.op)
			for _, result := range []struct {
				name string
				err  error
			}{{"Step", slowErr}, {"machine", fastErr}} {
				var rejection *Rejection
				if !errors.As(result.err, &rejection) || rejection.Code != tc.code {
					t.Errorf("%s: got %v, want rejection %s", result.name, result.err, tc.code)
				}
			}
			if !reflect.DeepEqual(s, before) || !reflect.DeepEqual(m.s, before) || len(introduced) != 0 ||
				!reflect.DeepEqual(m.ix, index) || !maps.Equal(m.seen, seen) {
				t.Fatal("rejection changed the input state, machine state, index or introduced values")
			}
		})
	}
}

// The records of Recorder, which copies, and of the runtime's recorder, which changes its state
// in place, are those of Transaction, and Check replays them to the state of the walk.
func TestRecordersAgree(t *testing.T) {
	for _, name := range append(append([]string{}, definitionNames...), extraDefinitions...) {
		p := load(t, name)
		for seed := range 8 {
			label := fmt.Sprintf("%s seed %d", name, seed)
			final, ops := Walk(p, DefaultConfig(), uint64(seed+1), 5000)
			pure, owned := NewRecorder(p), newOwnedRecorder(p, p.derive(), &State{}, nil, 0)
			s, known := &State{}, []Payload(nil)
			var text strings.Builder
			text.WriteString(EncodeHeader(p, true) + "\n")
			for i, op := range ops {
				identity := func(v string) (string, error) { return v, nil }
				records, err := pure.RecordWith(op, identity)
				if err != nil {
					t.Fatalf("%s: %s: %v", label, EncodeOp(op), err)
				}
				// Admission runs before any mutation. Refuse every otherwise valid operation
				// once, then reuse this same recorder to commit it successfully.
				before := cloneState(owned.machine.s)
				index := newStateIndex(before)
				seen, knownBefore := maps.Clone(owned.machine.seen), maps.Clone(owned.known)
				seq := owned.seq
				unchanged := func() {
					t.Helper()
					if !reflect.DeepEqual(owned.machine.s, before) || !reflect.DeepEqual(owned.machine.ix, index) ||
						!maps.Equal(owned.machine.seen, seen) || !maps.Equal(owned.known, knownBefore) || owned.seq != seq {
						t.Fatalf("%s: %s: the recorder changed before admission", label, EncodeOp(op))
					}
				}
				admissions := 0
				rejected, err := owned.recordAdmitted(op, identity, func(proposed []Record) error {
					admissions++
					unchanged()
					if RecordsText(proposed) != RecordsText(records) {
						t.Fatalf("%s: %s: admission saw different records", label, EncodeOp(op))
					}
					return quota("test admission", 0)
				})
				if !errors.Is(err, ErrQuotaExceeded) || len(rejected) != 0 || admissions != 1 {
					t.Fatalf("%s: %s: refused admission returned %v, %d records, %d callbacks",
						label, EncodeOp(op), err, len(rejected), admissions)
				}
				unchanged()
				ownedRecords, err := owned.recordAdmitted(op, identity, func(proposed []Record) error {
					admissions++
					unchanged()
					if RecordsText(proposed) != RecordsText(records) {
						t.Fatalf("%s: %s: retried admission saw different records", label, EncodeOp(op))
					}
					return nil
				})
				if err != nil || admissions != 2 {
					t.Fatalf("%s: %s: retry: %v, %d admissions", label, EncodeOp(op), err, admissions)
				}
				checkMachine(t, label+" "+EncodeOp(op), owned.machine)
				next, want, err := Transaction(p, s, op, records[0].Values, known, 2*i+1)
				if err != nil {
					t.Fatalf("%s: %s: %v", label, EncodeOp(op), err)
				}
				var needed []Payload
				for _, v := range Introduced(s, next) {
					if !hasPayload(known, v) {
						needed = append(needed, Payload{Value: v, Payload: v})
					}
				}
				if !slices.EqualFunc(records[0].Values, needed, func(a, b Payload) bool { return a == b }) {
					t.Fatalf("%s: %s: payloads %v, want %v", label, EncodeOp(op), records[0].Values, needed)
				}
				if got := RecordsText(records); got != RecordsText(want) || RecordsText(ownedRecords) != got {
					t.Fatalf("%s: %s: records differ", label, EncodeOp(op))
				}
				text.WriteString(RecordsText(records))
				s, known = next, append(known, needed...)
			}
			if !pure.State().Equal(final) || !owned.machine.s.Equal(final) {
				t.Fatalf("%s: the recorders reached another state", label)
			}
			c, err := Check(text.String(), sameDefinition(p))
			if err != nil {
				t.Fatalf("%s: %v", label, err)
			}
			if !c.State.Equal(final) || c.Committed != len(ops) {
				t.Fatalf("%s: Check replays to another state", label)
			}
		}
	}
}
