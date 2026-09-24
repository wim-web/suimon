package suimon

import (
	"fmt"
	"slices"
	"testing"
)

// Ported from Test/Step.lean.

func engineOp(op Op) bool {
	switch op.(type) {
	case OpStart, OpInvoke, OpFetch, OpDeliver, OpTaskInput, OpBeginTask, OpTaskOutput, OpSettle,
		OpCloseExecution, OpCloseRun, OpConclude:
		return true
	}
	return false
}

// acceptedChange is Lean's (step p s op).toOption.filter (· != s).
func acceptedChange(p *Definition, s *State, op Op) (*State, bool) {
	next, err := Step(p, s, op)
	if err != nil || next.Equal(s) {
		return nil, false
	}
	return next, true
}

// drive runs engine operations first; then each running call reports what decide says.
func drive(p *Definition, decide func(*State, *Call) Op) *State {
	s := &State{}
	cfg := DefaultConfig()
	cfg.Failures = false
	for range 10000 {
		progressed := false
		for _, op := range Candidates(p, cfg, s) {
			if !engineOp(op) {
				continue
			}
			if next, ok := acceptedChange(p, s, op); ok {
				s, progressed = next, true
				break
			}
		}
		if progressed {
			continue
		}
		for i := range s.Calls {
			if op := decide(s, &s.Calls[i]); op != nil {
				if next, ok := acceptedChange(p, s, op); ok {
					s, progressed = next, true
					break
				}
			}
		}
		if !progressed {
			break
		}
	}
	return s
}

func functionOf(c *Call) string { return c.Target.ID }

// succeed lets every call succeed; a Stream function yields count elements.
func succeed(count int, arm func(*State, *Call) string) func(*State, *Call) Op {
	return func(s *State, c *Call) Op {
		switch c.Status {
		case CallRunning:
			if c.Target.Judge {
				return OpJudged{c.ID, arm(s, c)}
			}
			if c.Stream {
				return nil
			}
			return OpReturned{c.ID, ExploreValue("return", c.ID)}
		case CallFetching:
			if c.Yields < count {
				return OpYielded{c.ID, ExploreValue("yield", c.ID, fmt.Sprint(c.Yields))}
			}
			return OpEnded{c.ID}
		case CallCancelling:
			return OpTerminated{c.ID}
		}
		return nil
	}
}

func outcome(s *State, path Path, name string) (Outcome, bool) {
	x, ok := s.settledOf(path, name)
	if !ok {
		return 0, false
	}
	return x.Outcome, true
}

func expectOutcome(t *testing.T, label string, s *State, name string, want Outcome) {
	t.Helper()
	if got, ok := outcome(s, nil, name); !ok || got != want {
		t.Errorf("%s: %s settled %v (%v), want %v", label, name, got, ok, want)
	}
}

func expectStatus(t *testing.T, label string, s *State, want Status) {
	t.Helper()
	if s.Status != want {
		t.Errorf("%s: expected %v, got %v with %d failures", label, want, s.Status, len(s.Failures))
	}
}

type deliveryKey struct {
	run        string
	connection int
	source     string
}

// checkTransition checks the invariants of every accepted transition of a random walk.
func checkTransition(t *testing.T, p *Definition, label string, before, after *State, op Op) {
	t.Helper()
	if !unique(ids(after.Results, func(r Result) string { return r.ID })) {
		t.Fatalf("%s: duplicate result after %s", label, EncodeOp(op))
	}
	if !unique(ids(after.Invocations, func(i Invocation) string { return i.ID })) {
		t.Fatalf("%s: duplicate invocation after %s", label, EncodeOp(op))
	}
	deliveries := map[deliveryKey]bool{}
	for _, d := range after.Deliveries {
		key := deliveryKey{Identity(d.Run...), d.Connection, d.Source}
		if deliveries[key] {
			t.Fatalf("%s: duplicate delivery", label)
		}
		deliveries[key] = true
	}
	for i := range after.Executions {
		e := &after.Executions[i]
		if c, err := after.concurrencyOf(p, e); err == nil && uint64(after.slotsHeld(e)) > c.Limit {
			t.Fatalf("%s: limit exceeded after %s", label, EncodeOp(op))
		}
	}
	if before.Status == StatusStopping {
		if !slices.EqualFunc(after.Results, before.Results, Result.equal) ||
			!slices.EqualFunc(after.Deliveries, before.Deliveries, Delivery.equal) ||
			len(after.Invocations) != len(before.Invocations) {
			t.Fatalf("%s: work accepted after the stop: %s", label, EncodeOp(op))
		}
	}
	if len(after.Failures) < len(before.Failures) ||
		!slices.EqualFunc(after.Failures[:len(before.Failures)], before.Failures, Failure.equal) {
		t.Fatalf("%s: failure record removed", label)
	}
	for _, r := range before.Results {
		if !slices.ContainsFunc(after.Results, r.equal) {
			t.Fatalf("%s: accepted result withdrawn by %s", label, EncodeOp(op))
		}
	}
	// A value stays mentioned once it is, so a value a transition introduces is new (§12.1).
	mentioned := map[string]bool{}
	for _, v := range after.Values() {
		mentioned[v] = true
	}
	for _, v := range before.Values() {
		if !mentioned[v] {
			t.Fatalf("%s: value %s withdrawn by %s", label, v, EncodeOp(op))
		}
	}
	// A new result names its producer: the reporting call, the closed execution, the sub-workflow
	// invocation, or the aggregating placement.
	var producer *string
	switch op := op.(type) {
	case OpReturned:
		producer = &op.Call
	case OpJudged:
		producer = &op.Call
	case OpYielded:
		producer = &op.Call
	case OpTaskOutput:
		producer = &op.Execution
	case OpCloseExecution:
		producer = &op.Execution
	case OpCloseRun:
		if r, ok := before.run(op.Run); ok {
			producer = r.Owner
		}
	case OpSettle:
		producer = ptr(keyAggregate(op.Run, op.Placement))
	}
	for _, r := range after.Results {
		if !slices.ContainsFunc(before.Results, r.equal) && (producer == nil || *producer != r.Producer) {
			t.Fatalf("%s: result %s with producer %s after %s", label, r.ID, r.Producer, EncodeOp(op))
		}
	}
}

// nothingRunning: no invocation is active, every task ended and none holds a slot, as in a final state
// reached through a stop (§8.2, §11.3).
func nothingRunning(s *State) bool {
	for _, i := range s.Invocations {
		if i.Status == InvocationActive {
			return false
		}
	}
	v := s.view()
	for i := range s.Executions {
		e := &s.Executions[i]
		for j := range e.Tasks {
			if !e.Tasks[j].Status.ended() || v.holdsSlot(e, &e.Tasks[j]) {
				return false
			}
		}
	}
	return true
}

// rootComplete: the workflow concluded without a stop.
func rootComplete(s *State) bool {
	r, ok := s.run(Path{})
	return ok && r.Complete
}

func randomWalks(t *testing.T, label string, p *Definition, cfg Config, seeds int) {
	for seed := range seeds {
		s := &State{}
		rng := uint64(seed + 1)
		steps := 0
		for steps < 5000 {
			choices := Accepted(p, cfg, s)
			if len(choices) == 0 {
				break
			}
			rng = NextSeed(rng)
			choice, ok := Pick(cfg, s, rng, choices)
			if !ok {
				break
			}
			checkTransition(t, p, fmt.Sprintf("%s seed %d", label, seed), s, choice.Next, choice.Op)
			s = choice.Next
			steps++
		}
		if !s.Status.Terminal() {
			t.Fatalf("%s seed %d: stuck in %v after %d steps", label, seed, s.Status, steps)
		}
		if !rootComplete(s) && !nothingRunning(s) {
			t.Fatalf("%s seed %d: something runs after the conclusion of a stop", label, seed)
		}
		if len(s.Failures) > 0 && s.Status != StatusFailed {
			t.Fatalf("%s seed %d: a recorded failure must fail the workflow", label, seed)
		}
		if len(s.Failures) == 0 && s.Cancelled && s.Status != StatusCancelled {
			t.Fatalf("%s seed %d: cancelled without failures must be cancelled", label, seed)
		}
	}
}

// Every interleaving reaches a final state, with or without failures.
func TestRandomWalks(t *testing.T) {
	for _, name := range append(definitionNames, extraDefinitions...) {
		p := load(t, name)
		randomWalks(t, name, p, DefaultConfig(), 200)
		cfg := DefaultConfig()
		cfg.Failures, cfg.Cancel = false, false
		randomWalks(t, name+" without failures", p, cfg, 50)
	}
}

func none(*State, *Call) string { return "" }

// §8.5: each user gets one list from the profile sub-workflow and the orders call.
func TestUsersScenario(t *testing.T) {
	users := load(t, "users")
	s := drive(users, succeed(2, none))
	expectStatus(t, "users", s, StatusSucceeded)
	if n := len(s.resultsOf(nil, "perUser")); n != 2 {
		t.Errorf("users: one list per user, got %d", n)
	}
	if n := len(s.resultsOf(nil, "all")); n != 1 {
		t.Errorf("users: one list of all users, got %d", n)
	}
	s = drive(users, func(s *State, c *Call) Op {
		if functionOf(c) == "fetchAllUsers" {
			return OpFailed{c.ID}
		}
		return succeed(2, none)(s, c)
	})
	expectStatus(t, "users: stop", s, StatusFailed)
	if len(s.Results) != 0 {
		t.Error("users: nothing is accepted after the stop")
	}
}

// §7.3: every order goes to the other arm, so the arm and its waitStream are skipped.
func TestBranchScenario(t *testing.T) {
	branch := load(t, "branch")
	unpaid := func(*State, *Call) string { return "unpaid" }
	s := drive(branch, succeed(2, unpaid))
	expectStatus(t, "branch: unpaid", s, StatusSkipped)
	expectOutcome(t, "branch: skipped arm", s, "ship", OutcomeSkipped)
	expectOutcome(t, "branch: skipped arm", s, "receipts", OutcomeSkipped)

	s = drive(branch, succeed(2, func(s *State, _ *Call) string {
		if len(s.resultsOf(nil, "paid")) == 0 {
			return "paid"
		}
		return "unpaid"
	}))
	expectStatus(t, "branch: one paid", s, StatusSucceeded)
	var selected []string
	for _, d := range s.deliveriesOn(nil, 2) {
		if d.Outcome.Kind == DeliveredValue {
			selected = append(selected, d.Outcome.Value)
		}
	}
	receipts := s.resultsOf(nil, "receipts")
	if len(receipts) != 1 || receipts[0].Value != listValue(selected) {
		t.Errorf("branch: the receipts of the selected orders, got %v", receipts)
	}

	s = drive(branch, succeed(0, unpaid))
	expectStatus(t, "branch: no orders", s, StatusSucceeded)
	receipts = s.resultsOf(nil, "receipts")
	if len(receipts) != 1 || receipts[0].Value != listValue(nil) {
		t.Errorf("branch: an empty stream is not skipped, got %v", receipts)
	}

	s = drive(branch, func(s *State, c *Call) Op {
		if functionOf(c) == "isPaid" && len(s.Failures) == 0 {
			return OpFailed{c.ID}
		}
		return succeed(2, unpaid)(s, c)
	})
	expectStatus(t, "branch: failed judge", s, StatusFailed)
	expectOutcome(t, "branch: a failed judge is not a non-selection", s, "receipts", OutcomeNormal)
}

// §9.2: Merge keeps the successful inputs; the failed input's other targets are not run.
func TestMergeScenario(t *testing.T) {
	merge := load(t, "merge")
	s := drive(merge, func(s *State, c *Call) Op {
		if functionOf(c) == "fetchSales" {
			return OpFailed{c.ID}
		}
		return succeed(0, none)(s, c)
	})
	expectStatus(t, "merge: failed input", s, StatusFailed)
	if len(s.resultsOf(nil, "widgets")) != 1 {
		t.Error("merge: list of the rest")
	}
	expectOutcome(t, "merge: list of the rest", s, "page", OutcomeNormal)
	expectOutcome(t, "merge: targets of a failed call are not run", s, "archive", OutcomeUpstreamFailed)
	expectOutcome(t, "merge: targets of a failed call are not run", s, "notify", OutcomeUpstreamFailed)
	s = drive(merge, succeed(0, none))
	expectStatus(t, "merge", s, StatusSucceeded)
	if len(s.invocationsOf(nil, "notify")) != 1 {
		t.Error("merge: discard runs its target once")
	}
}

// stoppedText is a concurrency task and a placement whose bodies are sub-workflows, each running one
// call (Test/Step.lean).
const stoppedText = `{"main": "outer", "functions": [{"id": "child", "output": {"single": "T"}}],
  "transforms": [{"id": "pass", "input": "T", "output": "T"}], "workflows": [
  {"id": "outer", "placements": [
    {"name": "fan", "node": {"type": "concurrency", "limit": 1, "output": "list", "element": "T",
      "tasks": [{"name": "sub", "body": {"type": "subworkflow", "workflow": "inner", "output": "leaf"},
        "outputTransform": "pass", "policy": "continue"}]}, "policy": "stop"},
    {"name": "call", "node": {"type": "subworkflow", "workflow": "inner", "output": "leaf"}, "policy": "stop"}]},
  {"id": "inner", "placements": [{"name": "leaf", "node": {"type": "function", "function": "child"}, "policy": "stop"}]}]}`

// §8.2, §11.3: the conclusion after a stop ends the task and the invocation whose sub-workflows were
// still open, without a result, and leaves their runs as they are (Test/Step.lean). Step and a
// machine, which changes its state in place through an index, conclude alike.
func TestConcludeAfterStop(t *testing.T) {
	p, err := ParseDefinition([]byte(stoppedText))
	if err != nil {
		t.Fatal(err)
	}
	if err := p.Validate(); err != nil {
		t.Fatal(err)
	}
	exec := keyInvocation(Path{}, "fan", nil)
	taskRun := keyChild(taskID(exec, "sub"))
	call := keyInvocation(Path{}, "call", nil)
	callRun := keyChild(call)
	ops := []Op{OpStart{}, OpInvoke{Run: Path{}, Placement: "fan"}, OpBeginTask{exec, "sub"},
		OpInvoke{Run: taskRun, Placement: "leaf"}, OpInvoke{Run: Path{}, Placement: "call"},
		OpInvoke{Run: callRun, Placement: "leaf"}, OpCancel{}, OpTerminated{keyInvocation(taskRun, "leaf", nil)},
		OpTerminated{keyInvocation(callRun, "leaf", nil)}}
	s := &State{}
	m := newMachine(p, p.derive(), &State{})
	for _, op := range ops {
		s = mustStep(t, p, s, op)
		if _, err := m.apply(op); err != nil {
			t.Fatalf("machine %s: %v", EncodeOp(op), err)
		}
	}
	task := func(s *State) (*Execution, *TaskState) {
		e, ok := s.view().execution(exec)
		if !ok || len(e.Tasks) != 1 {
			t.Fatal("the execution of fan")
		}
		return e, &e.Tasks[0]
	}
	invocation := func(s *State, id string) InvocationStatus {
		i, ok := s.view().invocation(id)
		if !ok {
			t.Fatalf("no invocation %s", id)
		}
		return i.Status
	}
	if e, ts := task(s); ts.Status != TaskActive || !s.view().holdsSlot(e, ts) {
		t.Fatalf("before the conclusion the task holds its slot: %v", ts.Status)
	}
	if st := invocation(s, call); st != InvocationActive {
		t.Fatalf("before the conclusion the call is active: %v", st)
	}
	concluded := mustStep(t, p, s, OpConclude{})
	if _, err := m.apply(OpConclude{}); err != nil {
		t.Fatalf("machine conclude: %v", err)
	}
	checkMachine(t, "conclude", m)
	if !m.s.Equal(concluded) {
		t.Fatal("the machine concluded to another state")
	}
	if concluded.Status != StatusCancelled {
		t.Fatalf("status %v", concluded.Status)
	}
	if e, ts := task(concluded); ts.Status != TaskCancelled || concluded.view().holdsSlot(e, ts) {
		t.Errorf("the task ended: %v", ts.Status)
	}
	if invocation(concluded, exec) != InvocationCancelled || invocation(concluded, call) != InvocationCancelled {
		t.Error("the invocations ended as cancelled")
	}
	if !nothingRunning(concluded) {
		t.Error("something still runs")
	}
	if !slices.EqualFunc(concluded.Results, s.Results, Result.equal) || len(concluded.Deliveries) != 0 ||
		len(concluded.Settled) != len(s.Settled) || len(concluded.TaskResults) != 0 ||
		len(concluded.Failures) != len(s.Failures) {
		t.Error("the conclusion published something")
	}
	for _, r := range concluded.Runs {
		if r.Complete {
			t.Errorf("run %v completed", r.Path)
		}
	}
	for _, e := range concluded.Executions {
		if e.Complete {
			t.Error("the execution completed")
		}
	}
	if _, err := Step(p, concluded, OpConclude{}); err == nil || err.Error() != "TERMINAL" {
		t.Errorf("a second conclusion: %v", err)
	}
}

// A rejected operation leaves the state unchanged and reports the Lean error code.
func TestStepRejections(t *testing.T) {
	merge := load(t, "merge")
	users := load(t, "users")
	empty := &State{}
	started, err := Step(merge, empty, OpStart{})
	if err != nil {
		t.Fatal(err)
	}
	cases := []struct {
		label string
		p     *Definition
		s     *State
		op    Op
		code  string
	}{
		{"not started", merge, empty, OpInvoke{Placement: "sales"}, "NOT_RUNNING"},
		{"input mismatch", users, empty, OpStart{}, "INPUT_MISMATCH"},
		{"started twice", merge, started, OpStart{}, "ALREADY_STARTED"},
		{"unknown run", merge, started, OpInvoke{Run: Path{"x"}, Placement: "sales"}, "UNKNOWN_RUN"},
		{"unknown placement", merge, started, OpInvoke{Placement: "nope"}, "UNKNOWN_PLACEMENT"},
		{"input not ready", merge, started, OpInvoke{Placement: "archive", Trigger: ptr("r")}, "INPUT_NOT_READY"},
		{"invalid trigger", merge, started, OpInvoke{Placement: "archive"}, "INVALID_TRIGGER"},
		{"merge is settled, not invoked", merge, started, OpInvoke{Placement: "widgets"}, "INVALID_TRIGGER"},
		{"unknown call", merge, started, OpFetch{"c"}, "UNKNOWN_CALL"},
		{"not ready", merge, started, OpSettle{Placement: "sales"}, "NOT_READY"},
		{"not settled", merge, started, OpConclude{}, "NOT_SETTLED"},
		{"root run", merge, started, OpCloseRun{Run: Path{}}, "NOT_CLOSABLE"},
		{"unknown execution", merge, started, OpBeginTask{"e", "t"}, "UNKNOWN_EXECUTION"},
		{"cancel before start", merge, empty, OpCancel{}, "NOT_STARTED"},
	}
	for _, c := range cases {
		_, err := Step(c.p, c.s, c.op)
		if r, ok := err.(*Rejection); !ok || r.Code != c.code {
			t.Errorf("%s: got %v, want %s", c.label, err, c.code)
		}
	}
	invoked, err := Step(merge, started, OpInvoke{Placement: "sales"})
	if err != nil {
		t.Fatal(err)
	}
	call := keyInvocation(nil, "sales", nil)
	if _, err := Step(merge, invoked, OpInvoke{Placement: "sales"}); err == nil || err.Error() != "DUPLICATE_INVOCATION" {
		t.Errorf("duplicate invocation: %v", err)
	}
	if _, err := Step(merge, invoked, OpFetch{call}); err == nil || err.Error() != "NOT_FETCHABLE" {
		t.Errorf("fetch of a Single call: %v", err)
	}
	if _, err := Step(merge, invoked, OpTimedOut{call, false}); err == nil || err.Error() != "NO_TIMEOUT" {
		t.Errorf("timeout without a timeout: %v", err)
	}
	returned, err := Step(merge, invoked, OpReturned{call, "v"})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := Step(merge, returned, OpReturned{call, "v"}); err == nil || err.Error() != "NOT_RETURNABLE" {
		t.Errorf("returned twice: %v", err)
	}
	result := keyCallResult(call, 0)
	if returned.Results[0].ID != result {
		t.Errorf("result identity %q, want %q", returned.Results[0].ID, result)
	}
	if _, err := Step(merge, returned, OpDeliver{Connection: 2, Source: result, Value: ptr("x")}); err == nil ||
		err.Error() != "TRANSFORM_MISMATCH" {
		t.Errorf("value to discard: %v", err)
	}
	if _, err := Step(merge, returned, OpTransformFailed{Connection: 2, Source: result}); err == nil ||
		err.Error() != "DISCARD_CANNOT_FAIL" {
		t.Errorf("failing discard: %v", err)
	}
	if _, err := Step(merge, returned, OpDeliver{Connection: 3, Source: result, Value: ptr("x")}); err == nil ||
		err.Error() != "NOT_ELIGIBLE" {
		t.Errorf("delivery from another source: %v", err)
	}
	if _, err := Step(merge, returned, OpDeliver{Connection: 9, Source: result}); err == nil ||
		err.Error() != "UNKNOWN_CONNECTION" {
		t.Errorf("unknown connection: %v", err)
	}
	// The rejected steps above did not change the states they were given.
	if !invoked.Equal(mustStep(t, merge, started, OpInvoke{Placement: "sales"})) || len(returned.Deliveries) != 0 {
		t.Error("a rejected operation changed the state")
	}
}

func mustStep(t *testing.T, p *Definition, s *State, op Op) *State {
	t.Helper()
	next, err := Step(p, s, op)
	if err != nil {
		t.Fatalf("%s: %v", EncodeOp(op), err)
	}
	return next
}

// Accepted drops an operation that is accepted but changes nothing.
func TestAcceptedDropsNoOps(t *testing.T) {
	merge := load(t, "merge")
	s := mustStep(t, merge, &State{}, OpStart{})
	s = mustStep(t, merge, s, OpCancel{})
	if s.Status != StatusStopping || !s.Cancelled {
		t.Fatalf("cancel: %v %v", s.Status, s.Cancelled)
	}
	again := mustStep(t, merge, s, OpCancel{})
	if !again.Equal(s) {
		t.Fatal("a second cancel changes nothing")
	}
	for _, c := range Accepted(merge, DefaultConfig(), s) {
		if _, isCancel := c.Op.(OpCancel); isCancel {
			t.Fatal("Accepted kept a cancel that changes nothing")
		}
	}
}
