import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## [2] Round3/Enabled.lean — task A1

Forward lemmas: when the guards of one rule of `Step.lean` hold, the operation is accepted and changes
the state. Each is a direct computation of one `Step.*` function; no invariant is involved. -/

section Enabled
variable {p : Definition} {s : State}

/-- The owner record of a call exists: its invocation, or its execution with the task. -/
def OwnerFound (s : State) (c : Call) : Prop :=
  match c.task with
  | none => ∃ i, s.invocation? c.owner = some i
  | some name => ∃ e ts, s.execution? c.owner = some e ∧ e.tasks.find? (·.name == name) = some ts

/-- Index `k` of call `c` is free: no result (no task result, for a task call) carries it yet. -/
def IndexFree (s : State) (c : Call) (k : Nat) : Prop :=
  match c.task with
  | none => s.result? (Key.callResult c.id k) = none
  | some name => (s.taskResults.any fun x => x.execution == c.owner && x.task == name && x.index == k) = false

/-! ### Helpers

Forward computations of the building blocks of `Step.lean`, lookups after an update, and ways to
see that a step changed the state. All private to this file. -/

private theorem ok_bind' {ε α β : Type} {a : α} {f : α → Except ε β} : (Except.ok a >>= f) = f a := rfl
private theorem require_true' {code : String} : require true code = .ok () := rfl

private theorem call?_congr {s t : State} {id : String} (h : t.calls = s.calls) : t.call? id = s.call? id := by
  unfold State.call?; rw [h]

private theorem call?_setCall_self {u : State} {c c' : Call} (hid : c'.id = c.id) (hc : u.call? c.id = some c) :
    (u.setCall c').call? c.id = some c' := by
  rw [State.call?_setCall, hc]; simp [hid]

private theorem execution?_setExecution_self {u : State} {e e' : Execution} (hid : e'.id = e.id)
    (he : u.execution? e.id = some e) : (u.setExecution e').execution? e.id = some e' := by
  rw [State.execution?_setExecution, he]; simp [hid]

private theorem run?_setRun_self {u : State} {r r' : Run} (hpath : r'.path = r.path) (hr : u.run? r.path = some r) :
    (u.setRun r').run? r.path = some r' := by
  rw [State.run?_setRun, hr]; simp [hpath]

/-! Lookups in a record the rule updates only elsewhere; `simp only` rewrites with them. -/

private theorem call?_withInvocations {s : State} {l : List Invocation} {id : String} :
    ({ s with invocations := l } : State).call? id = s.call? id := rfl
private theorem run?_withInvocations {s : State} {l : List Invocation} {path : Path} :
    ({ s with invocations := l } : State).run? path = s.run? path := rfl
private theorem execution?_withInvocations {s : State} {l : List Invocation} {id : String} :
    ({ s with invocations := l } : State).execution? id = s.execution? id := rfl
private theorem result?_withSettled {s : State} {l : List Settled} {id : ResultId} :
    ({ s with settled := l } : State).result? id = s.result? id := rfl
private theorem invocation?_setRun {s : State} {r : Run} {id : String} :
    (s.setRun r).invocation? id = s.invocation? id := rfl
private theorem execution?_setRun {s : State} {r : Run} {id : String} :
    (s.setRun r).execution? id = s.execution? id := rfl
private theorem result?_setRun {s : State} {r : Run} {id : ResultId} :
    (s.setRun r).result? id = s.result? id := rfl

/-- After replacing the elements that satisfy `P` by `y`, with `P y`, the first such element is `y`. -/
private theorem find?_map_replace {α : Type} {l : List α} {P : α → Bool} {y : α} (hy : P y = true) :
    (l.map fun x => if P x then y else x).find? P = (l.find? P).map fun _ => y := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : P a = true
    · simp [ha, hy]
    · simp [ha, ih]

/-! A step changed the state: a record was appended, or a stored record changed its status. -/

private theorem ne_of_failures {s t : State} (h : t.failures.length = s.failures.length + 1) : t ≠ s := by
  intro e; subst e; omega

private theorem ne_of_deliveries {s t : State} {d : Delivery} (h : t.deliveries = s.deliveries ++ [d]) : t ≠ s := by
  intro e; subst e
  have := congrArg List.length h
  simp at this

private theorem ne_of_calls {s t : State} {c : Call} (h : t.calls = s.calls ++ [c]) : t ≠ s := by
  intro e; subst e
  have := congrArg List.length h
  simp at this

private theorem ne_of_runs {s t : State} {r : Run} (h : t.runs = s.runs ++ [r]) : t ≠ s := by
  intro e; subst e
  have := congrArg List.length h
  simp at this

/-- A state whose stored call has another status is not `s`. -/
private theorem ne_of_call? {s t : State} {c c' : Call} (hc : s.call? c.id = some c)
    (ht : t.call? c.id = some c') (hne : c'.status ≠ c.status) : t ≠ s := by
  intro h
  subst h
  rw [hc] at ht
  exact hne (congrArg Call.status (Option.some.inj ht)).symm

/-- Changing the status of a task changes the state. -/
private theorem setTask_ne {s : State} {e : Execution} {ts ts' : TaskState} (he : s.execution? e.id = some e)
    (hts : e.tasks.find? (·.name == ts.name) = some ts) (hname : ts'.name = ts.name)
    (hne : ts'.status ≠ ts.status) : s.setTask e ts' ≠ s := by
  intro h
  have h1 := congrArg (fun u => u.execution? e.id) h
  simp only [State.execution?_setTask, he, ite_true, Option.map_some, Option.some.injEq] at h1
  have h2 := congrArg (fun e' => e'.tasks.find? (·.name == ts.name)) h1
  simp only [State.withTask_tasks] at h2
  rw [← hname] at h2 hts
  rw [find?_map_replace (P := fun x : TaskState => x.name == ts'.name) (by simp), hts] at h2
  exact hne (congrArg TaskState.status (Option.some.inj h2))

/-- Transforming the output of a task result changes the state. -/
private theorem setTaskResult_ne {s : State} {r r' : TaskResult} {eid : String}
    (hr : s.taskResults.find? (fun x => x.execution == eid && x.task == r.task && x.index == r.index) = some r)
    (hexec : r'.execution = r.execution) (htask : r'.task = r.task) (hindex : r'.index = r.index)
    (hne : r'.output ≠ r.output) : s.setTaskResult r' ≠ s := by
  have hre : r.execution = eid := by
    have := List.find?_some hr
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1
  intro h
  have h1 := congrArg (fun u => u.taskResults.find?
    (fun x => x.execution == eid && x.task == r.task && x.index == r.index)) h
  simp only [State.setTaskResult_taskResults, hexec, htask, hindex, hre] at h1
  rw [find?_map_replace (by simp [hexec, htask, hindex, hre]), hr] at h1
  exact hne (congrArg TaskResult.output (Option.some.inj h1))

/-! The owner of a call and a free index make the helpers of the report rules succeed. -/

private theorem OwnerFound.congr {s t : State} {c : Call} (h : OwnerFound s c)
    (hi : t.invocations = s.invocations) (he : t.executions = s.executions) : OwnerFound t c := by
  unfold OwnerFound at h ⊢
  unfold State.invocation? State.execution?
  rw [hi, he]
  exact h

private theorem accept_ok {c : Call} {k : Nat} {v : Value} {arm : Option String}
    (howner : OwnerFound s c) (hfree : IndexFree s c k) : ∃ t, s.accept c k v arm = .ok t := by
  unfold OwnerFound at howner
  unfold IndexFree at hfree
  unfold State.accept
  split
  · rename_i htask
    rw [htask] at howner hfree
    obtain ⟨i, hi⟩ := howner
    simp [hi, hfree]
  · rename_i name htask
    rw [htask] at hfree
    simp [hfree]

private theorem settleOwner_ok {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (howner : OwnerFound s c) : ∃ t, s.settleOwner c inv task = .ok t := by
  unfold OwnerFound at howner
  unfold State.settleOwner
  split
  · rename_i htask
    rw [htask] at howner
    obtain ⟨i, hi⟩ := howner
    simp [hi]
  · rename_i name htask
    rw [htask] at howner
    obtain ⟨e, ts, he, hts⟩ := howner
    simp [he, hts]

private theorem cancelOwner_ok {c : Call} (howner : OwnerFound s c) : ∃ t, s.cancelOwner c = .ok t := by
  unfold OwnerFound at howner
  unfold State.cancelOwner
  split
  · rename_i htask
    rw [htask] at howner
    obtain ⟨i, hi⟩ := howner
    simp [hi]
  · rename_i name htask
    rw [htask] at howner
    obtain ⟨e, ts, he, hts⟩ := howner
    simp [he, hts]

/-- A failing call adds exactly one failure record. -/
private theorem failCall_ok {c : Call} {status : CallStatus} {cause : Cause} (howner : OwnerFound s c) :
    ∃ t, s.failCall c status cause = .ok t ∧ t.failures.length = s.failures.length + 1 := by
  have hf : ∃ f, s.callFailure c cause = .ok f := by
    unfold OwnerFound at howner
    unfold State.callFailure
    split
    · rename_i htask
      rw [htask] at howner
      obtain ⟨i, hi⟩ := howner
      simp [hi]
    · rename_i name htask
      rw [htask] at howner
      obtain ⟨e, ts, he, hts⟩ := howner
      simp [he]
  obtain ⟨f, hf⟩ := hf
  obtain ⟨s', hso⟩ := settleOwner_ok (s := s.setCall { c with status }) (inv := .failed) (task := .failed)
    (howner.congr rfl rfl)
  refine ⟨s'.fail f c.policy, ?_, ?_⟩
  · simp [State.failCall, hf, hso]
  · simp [(State.settleOwner_update hso).failures]

theorem fetch_enabled {c : Call} (started : s.started = true) (running : s.status = .running)
    (hc : s.call? c.id = some c) (hstream : c.stream = true) (hrun : c.status = .running) :
    ∃ t, step p s (.fetch c.id) = .ok t ∧ t ≠ s := by
  refine ⟨s.setCall { c with status := .fetching }, ?_, ?_⟩
  · simp [Step.fetch, started, running, hc, hstream, hrun]
  · exact ne_of_call? hc (call?_setCall_self rfl hc) (by simp [hrun])

theorem yielded_enabled {c : Call} (started : s.started = true) (running : s.status = .running)
    (hc : s.call? c.id = some c) (hstream : c.stream = true) (hfetch : c.status = .fetching)
    (howner : OwnerFound s c) (hfree : IndexFree s c c.yields) (v : Value) :
    ∃ t, step p s (.yielded c.id v) = .ok t ∧ t ≠ s := by
  obtain ⟨s', hacc⟩ := accept_ok (v := v) (arm := none) howner hfree
  obtain ⟨-, -, -, -, -, hcalls, -⟩ := State.accept_frame hacc
  have hc' : s'.call? c.id = some c := by rw [call?_congr hcalls, hc]
  refine ⟨s'.setCall { c with status := .running, yields := c.yields + 1 }, ?_, ?_⟩
  · simp [Step.yielded, started, running, hc, hstream, hfetch, hacc]
  · exact ne_of_call? hc (call?_setCall_self rfl hc') (by simp [hfetch])

theorem returned_enabled {c : Call} (started : s.started = true) (running : s.status = .running)
    (hc : s.call? c.id = some c) (hsingle : c.stream = false) (hrun : c.status = .running)
    (hf : ∃ f, c.target = .function f) (howner : OwnerFound s c) (hfree : IndexFree s c 0) (v : Value) :
    ∃ t, step p s (.returned c.id v) = .ok t ∧ t ≠ s := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨s', hacc⟩ := accept_ok (v := v) (arm := none) howner hfree
  obtain ⟨-, -, -, -, hinvs, hcalls, hexecs, -⟩ := State.accept_frame hacc
  have hc' : s'.call? c.id = some c := by rw [call?_congr hcalls, hc]
  obtain ⟨t, hso⟩ := settleOwner_ok (s := s'.setCall { c with status := .returned }) (inv := .succeeded)
    (task := .succeeded) (howner.congr hinvs hexecs)
  refine ⟨t, ?_, ?_⟩
  · simp only [hsingle, hf] at hso
    simp [Step.returned, started, running, hc, hsingle, hrun, hf, hacc, hso]
  · refine ne_of_call? hc ?_ (c' := { c with status := .returned }) (by simp [hrun])
    rw [call?_congr (State.settleOwner_update hso).calls]
    exact call?_setCall_self rfl hc'

theorem judged_enabled {c : Call} {i : Invocation} {pl : Placement} {j a : String} {arms : List String}
    (started : s.started = true) (running : s.status = .running) (hc : s.call? c.id = some c)
    (hrun : c.status = .running) (hjudge : ∃ j', c.target = .judge j') (htask : c.task = none)
    (hi : s.invocation? c.owner = some i) (hpl : s.placementOf p i.run i.placement = .ok pl)
    (hbranch : pl.control = .branch j arms) (ha : a ∈ arms) (hfree : IndexFree s c 0) :
    ∃ t, step p s (.judged c.id a) = .ok t ∧ t ≠ s := by
  obtain ⟨j', hj'⟩ := hjudge
  have howner : OwnerFound s c := by
    unfold OwnerFound; rw [htask]; exact ⟨i, hi⟩
  obtain ⟨s', hacc⟩ := accept_ok (v := i.input.getD "") (arm := some a) howner hfree
  obtain ⟨-, -, -, -, -, hcalls, -⟩ := State.accept_frame hacc
  have hc' : s'.call? c.id = some c := by rw [call?_congr hcalls, hc]
  refine ⟨(s'.setCall { c with status := .returned }).setInvocation { i with status := .succeeded, arm := some a },
    ?_, ?_⟩
  · obtain ⟨w, hw, hwpl⟩ := State.placementOf_eq_ok.mp hpl
    simp [Step.judged, started, running, hc, hrun, hj', htask, hi, hw, hwpl, hbranch, ha, hacc]
  · refine ne_of_call? hc ?_ (c' := { c with status := .returned }) (by simp [hrun])
    rw [call?_congr State.setInvocation_calls]
    exact call?_setCall_self rfl hc'

theorem ended_enabled {c : Call} (started : s.started = true) (running : s.status = .running)
    (hc : s.call? c.id = some c) (hstream : c.stream = true) (hfetch : c.status = .fetching)
    (howner : OwnerFound s c) :
    ∃ t, step p s (.ended c.id) = .ok t ∧ t ≠ s := by
  obtain ⟨t, hso⟩ := settleOwner_ok (s := s.setCall { c with status := .returned }) (inv := .succeeded)
    (task := .succeeded) (howner.congr rfl rfl)
  refine ⟨t, ?_, ?_⟩
  · simp only [hstream] at hso
    simp [Step.ended, started, running, hc, hstream, hfetch, hso]
  · refine ne_of_call? hc ?_ (c' := { c with status := .returned }) (by simp [hfetch])
    rw [call?_congr (State.settleOwner_update hso).calls]
    exact call?_setCall_self rfl hc

theorem failed_enabled {c : Call} (started : s.started = true) (running : s.status = .running)
    (hc : s.call? c.id = some c) (hrun : c.status = .running ∨ c.status = .fetching) (howner : OwnerFound s c) :
    ∃ t, step p s (.failed c.id) = .ok t ∧ t ≠ s := by
  obtain ⟨t, hf, hlen⟩ := failCall_ok (status := .failed) (cause := .error) howner
  refine ⟨t, ?_, ne_of_failures hlen⟩
  simp [Step.failed, started, running, hc, hrun, hf]

theorem timedOut_enabled {c : Call} {element : Bool} (started : s.started = true) (running : s.status = .running)
    (hc : s.call? c.id = some c) (howner : OwnerFound s c)
    (hguard : if element then c.status = .fetching ∧ c.timeout.elementMs.isSome = true
      else (c.status = .running ∨ c.status = .fetching) ∧ c.timeout.callMs.isSome = true) :
    ∃ t, step p s (.timedOut c.id element) = .ok t ∧ t ≠ s := by
  obtain ⟨t, hf, hlen⟩ := failCall_ok (status := .cancelling) (cause := .timeout) howner
  refine ⟨t, ?_, ne_of_failures hlen⟩
  simp [Step.timedOut, started, running, hc, hguard, hf]

/-- A lost lease is accepted for every call that has not ended, while running or stopping. -/
theorem lost_enabled {c : Call} (started : s.started = true) (live : s.status = .running ∨ s.status = .stopping)
    (hc : s.call? c.id = some c) (hlive : c.status = .running ∨ c.status = .fetching ∨ c.status = .cancelling)
    (howner : OwnerFound s c) :
    ∃ t, step p s (.lost c.id) = .ok t ∧ t ≠ s := by
  have hlive' : (s.status == .running || s.status == .stopping) = true := by
    rcases live with h | h <;> simp [h]
  rcases hlive with h | h | h
  · obtain ⟨t, hf, hlen⟩ := failCall_ok (status := .lost) (cause := .lost) howner
    refine ⟨t, ?_, ne_of_failures hlen⟩
    simp [Step.lost, started, hlive', hc, h, hf]
  · obtain ⟨t, hf, hlen⟩ := failCall_ok (status := .lost) (cause := .lost) howner
    refine ⟨t, ?_, ne_of_failures hlen⟩
    simp [Step.lost, started, hlive', hc, h, hf]
  · obtain ⟨t, ho⟩ := cancelOwner_ok (s := s.setCall { c with status := .cancelled }) (howner.congr rfl rfl)
    refine ⟨t, ?_, ?_⟩
    · simp [Step.lost, started, hlive', hc, h, ho]
    · refine ne_of_call? hc ?_ (c' := { c with status := .cancelled }) (by simp [h])
      rw [call?_congr (State.cancelOwner_update ho).calls]
      exact call?_setCall_self rfl hc

theorem terminated_enabled {c : Call} (started : s.started = true) (live : s.status = .running ∨ s.status = .stopping)
    (hc : s.call? c.id = some c) (hcan : c.status = .cancelling) (howner : OwnerFound s c) :
    ∃ t, step p s (.terminated c.id) = .ok t ∧ t ≠ s := by
  have hlive' : (s.status == .running || s.status == .stopping) = true := by
    rcases live with h | h <;> simp [h]
  obtain ⟨t, ho⟩ := cancelOwner_ok (s := s.setCall { c with status := .cancelled }) (howner.congr rfl rfl)
  refine ⟨t, ?_, ?_⟩
  · simp [Step.terminated, started, hlive', hc, hcan, ho]
  · refine ne_of_call? hc ?_ (c' := { c with status := .cancelled }) (by simp [hcan])
    rw [call?_congr (State.cancelOwner_update ho).calls]
    exact call?_setCall_self rfl hc

/-- Every outcome of an eligible, undelivered transform is accepted: the trigger through `discard`,
    any value or a failure through a declared transform (§4.2). -/
theorem deliver_enabled {path : Path} {j : Nat} {source : ResultId} {w : Workflow} {c : Connection}
    (started : s.started = true) (running : s.status = .running)
    (htarget : Step.deliveryTarget p s path j source = .ok (w, c)) :
    (c.transform = .discard → ∃ t, step p s (.deliver path j source none) = .ok t ∧ t ≠ s) ∧
    (∀ id, c.transform = .declared id →
      (∀ v, ∃ t, step p s (.deliver path j source (some v)) = .ok t ∧ t ≠ s) ∧
      ((w.placement? c.target).isSome → ∃ t, step p s (.transformFailed path j source) = .ok t ∧ t ≠ s)) := by
  refine ⟨fun hd => ?_, fun id hid => ⟨fun v => ?_, fun hpl => ?_⟩⟩
  · refine ⟨{ s with deliveries := s.deliveries ++ [{ run := path, connection := j, source, outcome := .trigger }] },
      ?_, ne_of_deliveries rfl⟩
    simp [Step.deliver, started, running, htarget, hd]
  · refine ⟨{ s with deliveries := s.deliveries ++ [{ run := path, connection := j, source, outcome := .value v }] },
      ?_, ne_of_deliveries rfl⟩
    simp [Step.deliver, started, running, htarget, hid]
  · obtain ⟨target, htg⟩ := Option.isSome_iff_exists.mp hpl
    refine ⟨State.fail
      { s with deliveries := s.deliveries ++ [{ run := path, connection := j, source, outcome := .failed }] }
      { run := path, placement := c.target, cause := .transform } target.policy, ?_,
      ne_of_deliveries (d := { run := path, connection := j, source, outcome := .failed }) (by simp)⟩
    simp [Step.transformFailed, started, running, htarget, hid, htg]

theorem taskInput_enabled {e : Execution} {ts : TaskState} {spec : TaskSpec}
    (started : s.started = true) (running : s.status = .running) (he : s.execution? e.id = some e)
    (hts : e.tasks.find? (·.name == ts.name) = some ts) (hpending : ts.status = .pending)
    (hspec : s.taskSpec p e ts.name = .ok spec) :
    (spec.input = some .discard → ∃ t, step p s (.taskInput e.id ts.name none) = .ok t ∧ t ≠ s) ∧
    (∀ id, spec.input = some (.declared id) →
      (∀ v, ∃ t, step p s (.taskInput e.id ts.name (some v)) = .ok t ∧ t ≠ s) ∧
      ∃ t, step p s (.taskInputFailed e.id ts.name) = .ok t ∧ t ≠ s) := by
  refine ⟨fun hd => ?_, fun id hid => ⟨fun v => ?_, ?_⟩⟩
  · refine ⟨s.setTask e { ts with status := .ready, input := none }, ?_,
      setTask_ne he hts rfl (by simp [hpending])⟩
    simp [Step.taskInput, started, running, he, hts, hpending, hspec, hd]
  · refine ⟨s.setTask e { ts with status := .ready, input := some v }, ?_,
      setTask_ne he hts rfl (by simp [hpending])⟩
    simp [Step.taskInput, started, running, he, hts, hpending, hspec, hid]
  · refine ⟨(s.setTask e { ts with status := .failed }).fail
      { run := e.run, placement := e.placement, task := some ts.name, cause := .transform } spec.policy, ?_,
      ne_of_failures (by simp)⟩
    simp [Step.taskInputFailed, started, running, he, hts, hpending, hspec, hid]

theorem taskOutput_enabled {e : Execution} {cc : Concurrency} {spec : TaskSpec} {r : TaskResult}
    (started : s.started = true) (running : s.status = .running) (he : s.execution? e.id = some e)
    (hcc : s.concurrencyOf p e = .ok cc) (hspec : s.taskSpec p e r.task = .ok spec) (hout : spec.output.isSome = true)
    (hr : s.taskResults.find? (fun x => x.execution == e.id && x.task == r.task && x.index == r.index) = some r)
    (hpending : r.output = .pending)
    (hfree : cc.output = .stream → s.result? (Key.taskOutput e.id r.task r.index) = none) :
    (∀ v, ∃ t, step p s (.taskOutput e.id r.task r.index v) = .ok t ∧ t ≠ s) ∧
    ∃ t, step p s (.taskOutputFailed e.id r.task r.index) = .ok t ∧ t ≠ s := by
  refine ⟨fun v => ?_, ?_⟩
  · cases hcout : cc.output with
    | stream =>
      have hres : (s.setTaskResult { r with output := .value v }).result? (Key.taskOutput e.id r.task r.index) = none :=
        hfree hcout
      refine ⟨{ s.setTaskResult { r with output := .value v } with
        results := s.results ++ [{
          id := Key.taskOutput e.id r.task r.index, run := e.run, placement := e.placement, producer := e.id,
          value := v }] }, ?_, ?_⟩
      · simp [Step.taskOutput, started, running, he, hcc, hspec, hout, hr, hpending, hcout, hres]
      · intro h
        have := congrArg (fun u => u.results.length) h
        simp at this
    | list =>
      refine ⟨s.setTaskResult { r with output := .value v }, ?_,
        setTaskResult_ne hr rfl rfl rfl (by simp [hpending])⟩
      simp [Step.taskOutput, started, running, he, hcc, hspec, hout, hr, hpending, hcout]
  · refine ⟨(s.setTaskResult { r with output := .failed }).fail
      { run := e.run, placement := e.placement, task := some r.task, cause := .transform } spec.policy, ?_,
      ne_of_failures (by simp)⟩
    simp [Step.taskOutputFailed, started, running, he, hspec, hout, hr, hpending]

theorem beginTask_enabled {e : Execution} {cc : Concurrency} {ts : TaskState} {spec : TaskSpec}
    (started : s.started = true) (running : s.status = .running) (he : s.execution? e.id = some e)
    (hopen : e.complete = false) (hcc : s.concurrencyOf p e = .ok cc)
    (hts : e.tasks.find? (·.name == ts.name) = some ts) (hready : ts.status = .ready)
    (hslot : (e.tasks.filter (s.holdsSlot e)).length < cc.limit) (hspec : s.taskSpec p e ts.name = .ok spec)
    (hfun : ∀ f, spec.body = .function f → (p.function? f).isSome ∧ s.call? (Key.task e.id ts.name) = none)
    (hwf : ∀ wf out, spec.body = .workflow wf out → s.run? (Key.child (Key.task e.id ts.name)) = none) :
    ∃ t, step p s (.beginTask e.id ts.name) = .ok t ∧ t ≠ s := by
  cases hbody : spec.body with
  | function f =>
    obtain ⟨hdecl, hcall⟩ := hfun f hbody
    obtain ⟨decl, hdecl⟩ := Option.isSome_iff_exists.mp hdecl
    have hcall' : (s.setTask e { ts with status := .active }).call? (State.taskId e.id ts.name) = none := hcall
    refine ⟨{ s.setTask e { ts with status := .active } with
      calls := s.calls ++ [{
        id := State.taskId e.id ts.name, owner := e.id, task := some ts.name, target := .function f,
        input := ts.input, stream := decl.output.kind == .stream, timeout := spec.timeout, policy := spec.policy }] },
      ?_, ne_of_calls rfl⟩
    simp [Step.beginTask, started, running, he, hopen, hcc, hts, hready, hslot, hspec, hbody, hdecl, hcall']
  | workflow wf out =>
    have hrun : (s.setTask e { ts with status := .active }).run? (Key.child (State.taskId e.id ts.name)) = none :=
      hwf wf out hbody
    refine ⟨{ s.setTask e { ts with status := .active } with
      runs := s.runs ++ [{
        path := Key.child (State.taskId e.id ts.name), workflow := wf, input := ts.input, owner := some e.id,
        task := some ts.name }] },
      ?_, ne_of_runs rfl⟩
    simp [Step.beginTask, started, running, he, hopen, hcc, hts, hready, hslot, hspec, hbody, hrun]

theorem closeExecution_enabled {e : Execution} {cc : Concurrency} {i : Invocation}
    (started : s.started = true) (running : s.status = .running) (he : s.execution? e.id = some e)
    (hopen : e.complete = false) (hcc : s.concurrencyOf p e = .ok cc)
    (hended : ∀ t ∈ e.tasks, s.taskEnded e t = true)
    (houts : ∀ r ∈ s.taskResults, r.execution = e.id →
      ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains r.task = true → r.output ≠ .pending)
    (hi : s.invocation? e.id = some i) (hfree : cc.output = .list → s.result? (Key.list e.id) = none) :
    ∃ t, step p s (.closeExecution e.id) = .ok t ∧ t ≠ s := by
  have h1 : Step.running s = .ok () := by simp [Step.running, started, running]
  have h2 : Step.getExecution s e.id = .ok e := by simp [he]
  have hall : e.tasks.all (s.taskEnded e) = true := List.all_eq_true.mpr hended
  have houts' : (s.taskResults.filter fun x => x.execution == e.id &&
      ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains x.task).all (·.output != .pending) = true := by
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨hr, hkey⟩ := List.mem_filter.mp hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hkey
    simpa using houts r hr hkey.1 hkey.2
  have hi' : (s.setExecution { e with complete := true }).invocation? e.id = some i := hi
  -- Every outcome of the rule stores the completed execution.
  suffices h : ∃ t, step p s (.closeExecution e.id) = .ok t ∧
      t.executions = (s.setExecution { e with complete := true }).executions by
    obtain ⟨t, hstep, hex⟩ := h
    refine ⟨t, hstep, fun heq => ?_⟩
    have hstored : t.execution? e.id = some { e with complete := true } := by
      unfold State.execution?; rw [hex]; exact execution?_setExecution_self rfl he
    rw [heq, he] at hstored
    have := congrArg Execution.complete (Option.some.inj hstored)
    simp [hopen] at this
  by_cases hsk : (e.tasks.filter fun ts => ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains ts.name).all
      (·.status == .skipped) = true
  · refine ⟨(s.setExecution { e with complete := true }).setInvocation { i with status := .skipped }, ?_, rfl⟩
    simp only [step_closeExecution, Step.closeExecution, h1, h2, ok_bind', hopen, Bool.not_false, require_true',
      hcc, hall, houts', hi', need, pure_bind, hsk, ite_true]
    rfl
  · have hsk' := Bool.eq_false_iff.mpr hsk
    cases hcout : cc.output with
    | list =>
      have hres : (s.setExecution { e with complete := true }).result? (Key.list e.id) = none := hfree hcout
      refine ⟨{ (s.setExecution { e with complete := true }).setInvocation { i with status := .succeeded } with
        results := s.results ++ [{
          id := Key.list e.id, run := e.run, placement := e.placement, producer := e.id
          value := listValue ((s.taskResults.filter fun x => x.execution == e.id &&
            ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains x.task).filterMap (·.output.value?)) }] },
        ?_, rfl⟩
      simp only [step_closeExecution, Step.closeExecution, h1, h2, ok_bind', hopen, Bool.not_false, require_true',
        hcc, hall, houts', hi', need, pure_bind, hsk', Bool.false_eq_true, ite_false, hcout, hres, Option.isNone_none]
      rfl
    | stream =>
      refine ⟨(s.setExecution { e with complete := true }).setInvocation { i with status := .succeeded }, ?_, rfl⟩
      simp only [step_closeExecution, Step.closeExecution, h1, h2, ok_bind', hopen, Bool.not_false, require_true',
        hcc, hall, houts', hi', need, pure_bind, hsk', Bool.false_eq_true, ite_false, hcout]
      rfl

/-- The input an invocation takes is available when its trigger fits the input shape (§3.1, §5.3). -/
theorem invocationInput_enabled {r : Run} {w : Workflow} {name : String} {trigger : Option ResultId}
    (h : (w.shape? p name = some .none ∧ trigger = none) ∨ (w.shape? p name = some .entry ∧ trigger = none) ∨
      (∃ j c src input, w.shape? p name = some (.single j c) ∧ trigger = some src ∧
        s.resolveSingle r.path j c = .value src input) ∨
      (∃ j c src d, w.shape? p name = some (.stream j c) ∧ trigger = some src ∧
        s.delivery? r.path j src = some d ∧ d.outcome ≠ .failed)) :
    ∃ input, Step.invocationInput p s r w name trigger = .ok input := by
  rcases h with ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨j, c, src, input, hs, rfl, hres⟩ |
    ⟨j, c, src, d, hs, rfl, hd, hout⟩
  · exact ⟨none, by simp [Step.invocationInput, hs]⟩
  · exact ⟨r.input, by simp [Step.invocationInput, hs]⟩
  · exact ⟨input, by simp [Step.invocationInput, hs, hres]⟩
  · cases hdo : d.outcome with
    | value v => exact ⟨some v, by simp [Step.invocationInput, hs, hd, hdo]⟩
    | trigger => exact ⟨none, by simp [Step.invocationInput, hs, hd, hdo]⟩
    | failed => exact absurd hdo hout

theorem invoke_enabled {path : Path} {name : String} {trigger : Option ResultId} {r : Run} {w : Workflow}
    {pl : Placement} {input : Option Value} (started : s.started = true) (running : s.status = .running)
    (hr : s.run? path = some r) (hopen : r.complete = false) (hw : p.workflow? r.workflow = some w)
    (hpl : w.placement? name = some pl) (hinput : Step.invocationInput p s r w name trigger = .ok input)
    (hnew : ∀ i ∈ s.invocationsOf path name, i.trigger ≠ trigger)
    (hid : s.invocation? (Key.invocation path name trigger) = none)
    (hbody : match pl.control with
      | .call (.function f) => (p.function? f).isSome ∧ s.call? (Key.invocation path name trigger) = none
      | .branch _ _ => s.call? (Key.invocation path name trigger) = none
      | .call (.workflow _ _) => s.run? (Key.child (Key.invocation path name trigger)) = none
      | .concurrency _ => s.execution? (Key.invocation path name trigger) = none
      | _ => False) :
    ∃ t, step p s (.invoke path name trigger) = .ok t ∧ t ≠ s := by
  have h1 : Step.running s = .ok () := by simp [Step.running, started, running]
  have hdup : (!(s.invocationsOf path name).any (·.trigger == trigger) &&
      (s.invocation? (Key.invocation path name trigger)).isNone) = true := by
    have : (s.invocationsOf path name).any (·.trigger == trigger) = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨i, hi, htr⟩ := List.any_eq_true.mp h
      exact hnew i hi (by simpa using htr)
    simp [this, hid]
  -- Each outcome adds the invocation record first.
  suffices h : ∃ t, step p s (.invoke path name trigger) = .ok t ∧ t.invocations = s.invocations ++
      [{ id := Key.invocation path name trigger, run := path, placement := name, trigger, input }] by
    obtain ⟨t, hstep, hinv⟩ := h
    refine ⟨t, hstep, fun e => ?_⟩
    subst e
    have := congrArg List.length hinv
    simp at this
  split at hbody
  · rename_i f hf
    obtain ⟨hdecl, hcall⟩ := hbody
    obtain ⟨decl, hdecl⟩ := Option.isSome_iff_exists.mp hdecl
    refine ⟨{ s with
      invocations := s.invocations ++ [{
        id := Key.invocation path name trigger, run := path, placement := name, trigger, input }]
      calls := s.calls ++ [{
        id := Key.invocation path name trigger, owner := Key.invocation path name trigger, target := .function f,
        input, stream := decl.output.kind == .stream, timeout := pl.timeout, policy := pl.policy }] }, ?_, rfl⟩
    simp only [step_invoke, Step.invoke, h1, ok_bind', hr, need, pure_bind, hopen, Bool.not_false, require_true',
      hw, hpl, hinput, hdup, hf, hdecl, call?_withInvocations, hcall, Option.isNone_none]
    rfl
  · rename_i judge arms hb
    refine ⟨{ s with
      invocations := s.invocations ++ [{
        id := Key.invocation path name trigger, run := path, placement := name, trigger, input }]
      calls := s.calls ++ [{
        id := Key.invocation path name trigger, owner := Key.invocation path name trigger, target := .judge judge,
        input, timeout := pl.timeout, policy := pl.policy }] }, ?_, rfl⟩
    simp only [step_invoke, Step.invoke, h1, ok_bind', hr, need, pure_bind, hopen, Bool.not_false, require_true',
      hw, hpl, hinput, hdup, hb, call?_withInvocations, hbody, Option.isNone_none]
    rfl
  · rename_i wf out hwf
    refine ⟨{ s with
      invocations := s.invocations ++ [{
        id := Key.invocation path name trigger, run := path, placement := name, trigger, input }]
      runs := s.runs ++ [{
        path := Key.child (Key.invocation path name trigger), workflow := wf, input,
        owner := some (Key.invocation path name trigger) }] }, ?_, rfl⟩
    simp only [step_invoke, Step.invoke, h1, ok_bind', hr, need, pure_bind, hopen, Bool.not_false, require_true',
      hw, hpl, hinput, hdup, hwf, run?_withInvocations, hbody, Option.isNone_none]
    rfl
  · rename_i cc hcc
    refine ⟨{ s with
      invocations := s.invocations ++ [{
        id := Key.invocation path name trigger, run := path, placement := name, trigger, input }]
      executions := s.executions ++ [{
        id := Key.invocation path name trigger, run := path, placement := name, input
        tasks := cc.tasks.map fun ts =>
          { name := ts.name, status := if cc.input.isSome then .pending else .ready } }] }, ?_, rfl⟩
    simp only [step_invoke, Step.invoke, h1, ok_bind', hr, need, pure_bind, hopen, Bool.not_false, require_true',
      hw, hpl, hinput, hdup, hcc, execution?_withInvocations, hbody, Option.isNone_none]
    rfl
  · exact hbody.elim

theorem settle_enabled {path : Path} {name : String} {r : Run} {w : Workflow} {pl : Placement}
    {shape : Workflow.Shape} {kind : Kind} {x : Settled} {agg : Option Result}
    (started : s.started = true) (running : s.status = .running) (hr : s.run? path = some r)
    (hopen : r.complete = false) (hw : p.workflow? r.workflow = some w) (hpl : w.placement? name = some pl)
    (hunsettled : s.settled? path name = none) (hshape : w.shape? p name = some shape)
    (hkind : w.outputKind? p name = some kind) (hout : s.settleOutcome path pl shape kind = some (x, agg))
    (hfree : ∀ res, agg = some res → s.result? res.id = none) :
    ∃ t, step p s (.settle path name) = .ok t ∧ t ≠ s := by
  have h1 : Step.running s = .ok () := by simp [Step.running, started, running]
  suffices h : ∃ t, step p s (.settle path name) = .ok t ∧ t.settled = s.settled ++ [x] by
    obtain ⟨t, hstep, hset⟩ := h
    refine ⟨t, hstep, fun e => ?_⟩
    subst e
    have := congrArg List.length hset
    simp at this
  cases agg with
  | none =>
    refine ⟨{ s with settled := s.settled ++ [x] }, ?_, rfl⟩
    simp only [step_settle, Step.settle, h1, ok_bind', hr, need, pure_bind, hopen, Bool.not_false, require_true',
      hw, hpl, hunsettled, Option.isNone_none, hshape, hkind, hout]
    rfl
  | some res =>
    refine ⟨{ s with settled := s.settled ++ [x], results := s.results ++ [res] }, ?_, rfl⟩
    simp only [step_settle, Step.settle, h1, ok_bind', hr, need, pure_bind, hopen, Bool.not_false, require_true',
      hw, hpl, hunsettled, Option.isNone_none, hshape, hkind, hout, result?_withSettled, hfree res rfl]
    rfl

theorem closeRun_enabled {r : Run} {w : Workflow} {output : String} {x : Settled}
    (started : s.started = true) (running : s.status = .running) (hr : s.run? r.path = some r)
    (hopen : r.complete = false) (hroot : r.path ≠ []) (hw : p.workflow? r.workflow = some w)
    (hall : ∀ pl ∈ w.placements, (s.settled? r.path pl.name).isSome)
    (hout : s.designatedOutput p r = .ok output) (hx : s.settled? r.path output = some x)
    (hvalue : x.outcome = .normal → s.resultsOf r.path output ≠ [])
    (howner : match r.task with
      | none => ∃ o i, r.owner = some o ∧ s.invocation? o = some i ∧ s.result? (Key.returned i.id) = none
      | some name => ∃ o e ts, r.owner = some o ∧ s.execution? o = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
          (s.taskResults.any fun y => y.execution == e.id && y.task == name && y.index == 0) = false) :
    ∃ t, step p s (.closeRun r.path) = .ok t ∧ t ≠ s := by
  have h1 : Step.running s = .ok () := by simp [Step.running, started, running]
  have hclosable : (!r.complete && !r.path.isEmpty) = true := by
    simp [hopen, hroot]
  have hall' : w.placements.all (fun pl => (s.settled? r.path pl.name).isSome) = true := List.all_eq_true.mpr hall
  -- Every outcome of the rule stores the completed run.
  suffices h : ∃ t, step p s (.closeRun r.path) = .ok t ∧ t.runs = (s.setRun { r with complete := true }).runs by
    obtain ⟨t, hstep, hruns⟩ := h
    refine ⟨t, hstep, fun heq => ?_⟩
    have hstored : t.run? r.path = some { r with complete := true } := by
      unfold State.run?; rw [hruns]; exact run?_setRun_self rfl hr
    rw [heq, hr] at hstored
    have := congrArg Run.complete (Option.some.inj hstored)
    simp [hopen] at this
  -- The value a normal outcome returns.
  have hval : x.outcome = .normal → ∃ v, ((s.resultsOf r.path output).head?).map (·.value) = some v := by
    intro hn
    obtain ⟨res, rest, hres⟩ := List.exists_cons_of_ne_nil (hvalue hn)
    exact ⟨res.value, by simp [hres]⟩
  split at howner
  · rename_i htask
    obtain ⟨o, i, hown, hi, hret⟩ := howner
    cases hxo : x.outcome with
    | normal =>
      obtain ⟨v, hv⟩ := hval hxo
      refine ⟨{ (s.setRun { r with complete := true }).setInvocation { i with status := .succeeded } with
        results := s.results ++ [{
          id := Key.returned i.id, run := i.run, placement := i.placement, producer := i.id, value := v }] },
        ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, invocation?_setRun, hi, hxo, hv, result?_setRun, hret, Option.isNone_none]
      rfl
    | skipped =>
      refine ⟨(s.setRun { r with complete := true }).setInvocation { i with status := .skipped }, ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, invocation?_setRun, hi, hxo]
      rfl
    | failed =>
      refine ⟨(s.setRun { r with complete := true }).setInvocation { i with status := .failed }, ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, invocation?_setRun, hi, hxo]
      rfl
    | upstreamFailed =>
      refine ⟨(s.setRun { r with complete := true }).setInvocation { i with status := .upstreamFailed }, ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, invocation?_setRun, hi, hxo]
      rfl
  · rename_i name htask
    obtain ⟨o, e, ts, hown, he, hts, hfresh⟩ := howner
    have hget : ∀ r' : Run, Step.getExecution (s.setRun r') o = .ok e := by
      intro r'
      simp [Step.getExecution, execution?_setRun, he]
    have htk : State.task e name = .ok ts := by simp [hts]
    cases hxo : x.outcome with
    | normal =>
      obtain ⟨v, hv⟩ := hval hxo
      refine ⟨{ (s.setRun { r with complete := true }).setTask e { ts with status := .succeeded } with
        taskResults := s.taskResults ++ [{ execution := e.id, task := name, index := 0, value := v }] },
        ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, hget, htk, hxo, hv, State.setRun_taskResults, hfresh, Bool.not_false]
      rfl
    | skipped =>
      refine ⟨(s.setRun { r with complete := true }).setTask e { ts with status := .skipped }, ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, hget, htk, hxo]
      rfl
    | failed =>
      refine ⟨(s.setRun { r with complete := true }).setTask e { ts with status := .failed }, ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, hget, htk, hxo]
      rfl
    | upstreamFailed =>
      refine ⟨(s.setRun { r with complete := true }).setTask e { ts with status := .upstreamFailed }, ?_, rfl⟩
      simp only [step_closeRun, Step.closeRun, h1, ok_bind', hr, need, pure_bind, hclosable, require_true', hw,
        hall', hout, hx, hown, htask, hget, htk, hxo]
      rfl

theorem conclude_running_enabled {r : Run} {w : Workflow} (started : s.started = true) (running : s.status = .running)
    (hr : s.run? [] = some r) (hw : p.workflow? r.workflow = some w)
    (hall : ∀ pl ∈ w.placements, (s.settled? [] pl.name).isSome) :
    ∃ t, step p s .conclude = .ok t ∧ t ≠ s := by
  have hall' : w.placements.all (fun pl => (s.settled? [] pl.name).isSome) = true := List.all_eq_true.mpr hall
  refine ⟨{ s.setRun { r with complete := true } with
    status := if !s.failures.isEmpty then .failed
      else if (w.placements.filter fun pl => w.isEndpoint pl.name).all
          (fun pl => (s.settled? [] pl.name).any (·.outcome == .skipped)) then .skipped
      else .succeeded }, ?_, ?_⟩
  · simp only [step_conclude, Step.conclude, ok_bind', started, require_true', running, hr, need, pure_bind, hw,
      hall']
    rfl
  · intro heq
    have := congrArg State.status heq
    simp only [running] at this
    split at this
    · simp at this
    · split at this <;> simp at this

/-- Stopping: once every call ended, the conclusion is accepted (§11.3). Proven. -/
theorem conclude_stopping_enabled (started : s.started = true) (stopping : s.status = .stopping)
    (hended : ∀ c ∈ s.calls, c.status.ended = true) :
    ∃ t, step p s .conclude = .ok t ∧ t ≠ s := by
  refine ⟨{ s with status := if s.failures.isEmpty then .cancelled else .failed }, ?_, ?_⟩
  · have hall : s.calls.all (·.status.ended) = true := List.all_eq_true.mpr hended
    simp [step, Step.conclude, require, started, stopping, hall, pure, Except.pure, bind, Except.bind]
  · intro heq
    have := congrArg State.status heq
    simp only [stopping] at this
    split at this <;> simp at this

end Enabled

end Suimon.Round3
