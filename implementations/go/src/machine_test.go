package suimon

import (
	"errors"
	"fmt"
	"reflect"
	"slices"
	"strings"
	"testing"
)

// The machine, which changes its state in place through an index, against Step, which copies:
// along random walks, every candidate operation must be accepted or rejected alike, with the same
// error, state and introduced values, and Step must leave its state unchanged.

// cloneState copies the lists of s, the tasks of its executions included; the rest is never
// changed in place.
func cloneState(s *State) *State {
	t := *s
	t.Runs = slices.Clone(s.Runs)
	t.Invocations = slices.Clone(s.Invocations)
	t.Calls = slices.Clone(s.Calls)
	t.Executions = slices.Clone(s.Executions)
	for i := range t.Executions {
		t.Executions[i].Tasks = slices.Clone(t.Executions[i].Tasks)
	}
	t.Results = slices.Clone(s.Results)
	t.TaskResults = slices.Clone(s.TaskResults)
	t.Deliveries = slices.Clone(s.Deliveries)
	t.Settled = slices.Clone(s.Settled)
	t.Failures = slices.Clone(s.Failures)
	return &t
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
func agree(t *testing.T, label string, p *Program, s *State, op Op) {
	t.Helper()
	next, err := Step(p, s, op)
	m := newMachine(p, cloneState(s))
	introduced, fastErr := m.apply(op)
	if !sameError(err, fastErr) {
		t.Fatalf("%s: %s: Step %v, machine %v", label, EncodeOp(op), err, fastErr)
	}
	if err != nil {
		if !m.s.Equal(s) {
			t.Fatalf("%s: %s: the machine changed its state on a rejection", label, EncodeOp(op))
		}
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
	programs := append(append([]string{}, programNames...), extraPrograms...)
	programs = append(programs, "limit")
	for _, name := range programs {
		p := load(t, name)
		for _, cfg := range []Config{DefaultConfig(), {MaxYields: 3, Disruption: 40}} {
			for seed := range 12 {
				label := fmt.Sprintf("%s seed %d failures %t", name, seed, cfg.Failures)
				s := &State{}
				m := newMachine(p, &State{})
				rng := uint64(seed + 1)
				for step := 0; step < 2000; step++ {
					snapshot := cloneState(s)
					for _, op := range Candidates(p, cfg, s) {
						agree(t, label, p, s, op)
					}
					if !s.Equal(snapshot) {
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

// Rejections that no candidate makes, applied to a machine in the middle of a walk.
func TestMachineRejections(t *testing.T) {
	p := load(t, "users")
	s, _ := Walk(p, DefaultConfig(), 3, 40)
	if !s.Started || len(s.Calls) == 0 || len(s.Executions) == 0 {
		t.Fatal("the walk did not get far enough")
	}
	c, e := s.Calls[0], s.Executions[0]
	ops := []Op{
		OpStart{}, OpInvoke{Run: Path{"x"}, Placement: "perUser"}, OpInvoke{Run: Path{}, Placement: "x"},
		OpInvoke{Run: Path{}, Placement: "fetchAllUsers"}, OpInvoke{Run: Path{}, Placement: "perUser", Trigger: ptr("x")},
		OpFetch{Call: "x"}, OpReturned{Call: c.ID, Value: "v"}, OpJudged{Call: c.ID, Arm: "x"},
		OpYielded{Call: c.ID, Value: "v"}, OpEnded{Call: c.ID}, OpTimedOut{Call: c.ID, Element: true},
		OpTerminated{Call: c.ID}, OpDeliver{Run: Path{}, Connection: 9, Source: "x"},
		OpDeliver{Run: Path{}, Connection: 0, Source: "x"}, OpTransformFailed{Run: Path{"x"}, Connection: 0, Source: "x"},
		OpTaskInput{Execution: "x", Task: "orders"}, OpTaskInput{Execution: e.ID, Task: "x"},
		OpTaskInputFailed{Execution: e.ID, Task: "orders"}, OpBeginTask{Execution: e.ID, Task: "x"},
		OpTaskOutput{Execution: e.ID, Task: "orders", Index: 7, Value: "v"},
		OpTaskOutputFailed{Execution: e.ID, Task: "x", Index: 0}, OpSettle{Run: Path{}, Placement: "all"},
		OpSettle{Run: Path{"x"}, Placement: "all"}, OpCloseExecution{Execution: "x"},
		OpCloseRun{Run: Path{}}, OpCloseRun{Run: Path{"x"}}, OpConclude{},
	}
	for _, op := range ops {
		agree(t, "users", p, s, op)
	}
}

// The records of Recorder, which copies, and of the runtime's recorder, which changes its state
// in place, are those of Transaction, and Check replays them to the state of the walk.
func TestRecordersAgree(t *testing.T) {
	for _, name := range append(append([]string{}, programNames...), extraPrograms...) {
		p := load(t, name)
		for seed := range 8 {
			label := fmt.Sprintf("%s seed %d", name, seed)
			final, ops := Walk(p, DefaultConfig(), uint64(seed+1), 5000)
			pure, owned := NewRecorder(p), newOwnedRecorder(p, &State{}, nil, 0)
			s, known := &State{}, []Payload(nil)
			var text strings.Builder
			for i, op := range ops {
				identity := func(v string) (string, error) { return v, nil }
				records, err := pure.RecordWith(op, identity)
				if err != nil {
					t.Fatalf("%s: %s: %v", label, EncodeOp(op), err)
				}
				ownedRecords, err := owned.recordWith(op, identity)
				if err != nil {
					t.Fatalf("%s: %s: %v", label, EncodeOp(op), err)
				}
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
			c, err := Check(p, text.String())
			if err != nil {
				t.Fatalf("%s: %v", label, err)
			}
			if !c.State.Equal(final) || c.Committed != len(ops) {
				t.Fatalf("%s: Check replays to another state", label)
			}
		}
	}
}
