import Suimon.Theorems.DeliveryInv

/-! Every record after a step is a record from before with the same fixed fields, or one the step
    created, with what the step checked. -/

namespace Suimon.Delivery
open State

/-! ### Records from before -/

/-- `i` is an invocation of `s` with the same identity, run, placement, trigger and input. --/
def InvOld (s : State) (i : Invocation) : Prop :=
  ∃ i₀ ∈ s.invocations, i₀.id = i.id ∧ i₀.run = i.run ∧ i₀.placement = i.placement ∧ i₀.trigger = i.trigger ∧
    i₀.input = i.input

/-- `c` is a call of `s` with the same fixed fields; if `c` runs or fetches, it already did. --/
def CallOld (s : State) (c : Call) : Prop :=
  ∃ c₀ ∈ s.calls, c₀.id = c.id ∧ c₀.owner = c.owner ∧ c₀.task = c.task ∧ c₀.target = c.target ∧ c₀.stream = c.stream ∧
    ((c.status = .running ∨ c.status = .fetching) → (c₀.status = .running ∨ c₀.status = .fetching))

/-- `r` is a run of `s` with the same fixed fields, complete if it was. --/
def RunOld (s : State) (r : Run) : Prop :=
  ∃ r₀ ∈ s.runs, r₀.path = r.path ∧ r₀.workflow = r.workflow ∧ r₀.input = r.input ∧ r₀.owner = r.owner ∧
    r₀.task = r.task ∧ (r₀.complete = true → r.complete = true)

/-- `e` is an execution of `s` with the same fixed fields and task names, complete if it was. --/
def ExecOld (s : State) (e : Execution) : Prop :=
  ∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.run = e.run ∧ e₀.placement = e.placement ∧
    e₀.tasks.map (·.name) = e.tasks.map (·.name) ∧ (e₀.complete = true → e.complete = true)

/-- `r` is a task result of `s` under the same key, with its transformed output kept. --/
def TaskResultOld (s : State) (r : TaskResult) : Prop :=
  ∃ r₀ ∈ s.taskResults, r₀.execution = r.execution ∧ r₀.task = r.task ∧ r₀.index = r.index ∧
    (r₀.output ≠ .pending → r.output = r₀.output)

/-- A task result a step accepts: from a running task call, or from a closing task run. --/
def NewTaskResult (s : State) (r : TaskResult) : Prop :=
  r.output = .pending ∧
  ((∃ c ∈ s.calls, c.owner = r.execution ∧ c.task = some r.task ∧ (c.status = .running ∨ c.status = .fetching)) ∨
   (∃ R ∈ s.runs, R.owner = some r.execution ∧ R.task = some r.task ∧ R.complete = false))

theorem invOld_self {s : State} {i : Invocation} (h : i ∈ s.invocations) : InvOld s i :=
  ⟨i, h, rfl, rfl, rfl, rfl, rfl⟩
theorem callOld_self {s : State} {c : Call} (h : c ∈ s.calls) : CallOld s c :=
  ⟨c, h, rfl, rfl, rfl, rfl, rfl, id⟩
theorem runOld_self {s : State} {r : Run} (h : r ∈ s.runs) : RunOld s r :=
  ⟨r, h, rfl, rfl, rfl, rfl, rfl, id⟩
theorem execOld_self {s : State} {e : Execution} (h : e ∈ s.executions) : ExecOld s e :=
  ⟨e, h, rfl, rfl, rfl, rfl, id⟩
theorem taskResultOld_self {s : State} {r : TaskResult} (h : r ∈ s.taskResults) : TaskResultOld s r :=
  ⟨r, h, rfl, rfl, rfl, fun _ => rfl⟩

/-! ### Elementary updates -/

theorem invOld_setInvocation {s : State} {i i' x : Invocation} (hi : i ∈ s.invocations)
    (hx : x ∈ (s.setInvocation i').invocations) (hid : i'.id = i.id)
    (hrun : i'.run = i.run) (hpl : i'.placement = i.placement) (htr : i'.trigger = i.trigger) (hin : i'.input = i.input) :
    InvOld s x := by
  rcases State.mem_setInvocation_invocations hx with rfl | hx
  · exact ⟨i, hi, hid.symm, hrun.symm, hpl.symm, htr.symm, hin.symm⟩
  · exact invOld_self hx

theorem callOld_setCall {s : State} {c c' x : Call} (hc : c ∈ s.calls) (hx : x ∈ (s.setCall c').calls)
    (hid : c'.id = c.id) (howner : c'.owner = c.owner)
    (htask : c'.task = c.task) (htarget : c'.target = c.target) (hstream : c'.stream = c.stream)
    (hrun : (c'.status = .running ∨ c'.status = .fetching) → (c.status = .running ∨ c.status = .fetching)) :
    CallOld s x := by
  rcases State.mem_setCall_calls hx with rfl | hx
  · exact ⟨c, hc, hid.symm, howner.symm, htask.symm, htarget.symm, hstream.symm, hrun⟩
  · exact callOld_self hx

theorem callOld_stop {s : State} {x : Call} (hx : x ∈ s.stop.calls) : CallOld s x := by
  obtain ⟨c, hc, rfl⟩ := State.mem_stop_calls.mp hx
  refine ⟨c, hc, by simp, by simp, by simp, ?_, ?_, fun h => absurd h ?_⟩
  · unfold stopCall; split <;> rfl
  · unfold stopCall; split <;> rfl
  · have := stopCall_quiet c
    exact fun h => h.elim this.1 this.2

theorem callOld_fail {s : State} {f : Failure} {policy : Policy} {x : Call} (hx : x ∈ (s.fail f policy).calls) :
    CallOld s x := by
  cases policy
  · exact callOld_stop hx
  · exact callOld_self hx

theorem runOld_setRun {s : State} {r x : Run} (hr : r ∈ s.runs) (hx : x ∈ (s.setRun { r with complete := true }).runs) :
    RunOld s x := by
  rcases State.mem_setRun_runs hx with rfl | hx
  · exact ⟨r, hr, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · exact runOld_self hx

theorem execOld_setExecution {s : State} {e e' x : Execution} (he : e ∈ s.executions)
    (hx : x ∈ (s.setExecution e').executions) (hid : e'.id = e.id)
    (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (hnames : e'.tasks.map (·.name) = e.tasks.map (·.name))
    (hc : e.complete = true → e'.complete = true) : ExecOld s x := by
  rcases State.mem_setExecution_executions hx with rfl | hx
  · exact ⟨e, he, hid.symm, hrun.symm, hpl.symm, hnames.symm, hc⟩
  · exact execOld_self hx

theorem execOld_setTask {s : State} {e : Execution} {ts : TaskState} {x : Execution} (he : e ∈ s.executions)
    (hx : x ∈ (s.setTask e ts).executions) : ExecOld s x :=
  execOld_setExecution (e' := withTask e ts) he hx rfl rfl rfl (Kept.withTask_names e ts) id

theorem execOld_stop {s : State} {x : Execution} (hx : x ∈ s.stop.executions) : ExecOld s x := by
  obtain ⟨e, he, rfl⟩ := State.mem_stop_executions.mp hx
  refine ⟨e, he, rfl, rfl, rfl, ?_, id⟩
  simp only [stopExecution, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  split <;> rfl

theorem execOld_fail {s : State} {f : Failure} {policy : Policy} {x : Execution}
    (hx : x ∈ (s.fail f policy).executions) : ExecOld s x := by
  cases policy
  · exact execOld_stop hx
  · exact execOld_self hx

theorem taskResultOld_setTaskResult {s : State} {r x : TaskResult} {o : TaskOutput} (hr : r ∈ s.taskResults)
    (hp : r.output = .pending) (hx : x ∈ (s.setTaskResult { r with output := o }).taskResults) : TaskResultOld s x := by
  rcases State.mem_setTaskResult_taskResults hx with rfl | hx
  · exact ⟨r, hr, rfl, rfl, rfl, fun h => absurd hp h⟩
  · exact taskResultOld_self hx

/-! ### Owners settled or cancelled -/

section Owners
variable {s t : State}

theorem settleOwner_old {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : s.settleOwner c inv task = .ok t) :
    (∀ x ∈ t.invocations, InvOld s x) ∧ t.calls = s.calls ∧ t.runs = s.runs ∧
      (∀ x ∈ t.executions, ExecOld s x) ∧ t.taskResults = s.taskResults ∧ t.results = s.results ∧
      t.deliveries = s.deliveries ∧ t.settled = s.settled := by
  rcases State.settleOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, e, ts, -, he, -, rfl⟩
  · exact ⟨fun x hx => invOld_setInvocation (State.invocation?_eq_some hi).1 hx rfl rfl rfl rfl rfl, rfl, rfl,
      fun x hx => execOld_self hx, rfl, rfl, rfl, rfl⟩
  · exact ⟨fun x hx => invOld_self hx, rfl, rfl, fun x hx => execOld_setTask (State.execution?_eq_some he).1 hx,
      rfl, rfl, rfl, rfl⟩

theorem cancelOwner_old {c : Call} (h : s.cancelOwner c = .ok t) :
    (∀ x ∈ t.invocations, InvOld s x) ∧ t.calls = s.calls ∧ t.runs = s.runs ∧
      (∀ x ∈ t.executions, ExecOld s x) ∧ t.taskResults = s.taskResults ∧ t.results = s.results ∧
      t.deliveries = s.deliveries ∧ t.settled = s.settled := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, e, ts, -, he, -, rfl⟩ <;> split
  · exact ⟨fun x hx => invOld_setInvocation (State.invocation?_eq_some hi).1 hx rfl rfl rfl rfl rfl, rfl, rfl,
      fun x hx => execOld_self hx, rfl, rfl, rfl, rfl⟩
  · exact ⟨fun x hx => invOld_self hx, rfl, rfl, fun x hx => execOld_self hx, rfl, rfl, rfl, rfl⟩
  · exact ⟨fun x hx => invOld_self hx, rfl, rfl, fun x hx => execOld_setTask (State.execution?_eq_some he).1 hx,
      rfl, rfl, rfl, rfl⟩
  · exact ⟨fun x hx => invOld_self hx, rfl, rfl, fun x hx => execOld_self hx, rfl, rfl, rfl, rfl⟩

/-- Failing a call: only statuses change, and the stop leaves no call running or fetching. --/
theorem failCall_old {c : Call} {status : CallStatus} {cause : Cause} (hc : c ∈ s.calls)
    (hst : status ≠ .running ∧ status ≠ .fetching) (h : s.failCall c status cause = .ok t) :
    (∀ x ∈ t.invocations, InvOld s x) ∧ (∀ x ∈ t.calls, CallOld s x) ∧ t.runs = s.runs ∧
      (∀ x ∈ t.executions, ExecOld s x) ∧ t.taskResults = s.taskResults ∧ t.results = s.results ∧
      t.deliveries = s.deliveries ∧ t.settled = s.settled := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  obtain ⟨hi, hcalls, hr, he, htr, hres, hd, hs⟩ := settleOwner_old hso
  refine ⟨fun x hx => ?_, fun x hx => ?_, by simp [hr], fun x hx => ?_, by simp [htr], by simp [hres], by simp [hd],
    by simp [hs]⟩
  · obtain ⟨x₀, hx₀, h⟩ := hi x (by simpa using hx)
    exact ⟨x₀, by simpa using hx₀, h⟩
  · obtain ⟨y, hy, a1, a2, a3, a4, a5, a6⟩ := callOld_fail hx
    rw [hcalls] at hy
    obtain ⟨z, hz, b1, b2, b3, b4, b5, b6⟩ :=
      callOld_setCall hc hy rfl rfl rfl rfl rfl (fun h => absurd h (by simp [hst]))
    exact ⟨z, hz, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, fun h => b6 (a6 h)⟩
  · obtain ⟨y, hy, a1, a2, a3, a4, a5⟩ := execOld_fail hx
    obtain ⟨z, hz, b1, b2, b3, b4, b5⟩ := he y hy
    exact ⟨z, by simpa using hz, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, fun h => a5 (b5 h)⟩

end Owners

/-! ### Invocations -/

theorem mem_setInvocation_self {s : State} {i : Invocation} (hi : i ∈ s.invocations) (status : InvocationStatus)
    (arm : Option String) : { i with status, arm } ∈ (s.setInvocation { i with status, arm }).invocations := by
  simp only [State.setInvocation_invocations]
  exact List.mem_map.mpr ⟨i, hi, by simp⟩

theorem mem_setTask_self {s : State} {e : Execution} {ts : TaskState} (he : e ∈ s.executions) :
    withTask e ts ∈ (s.setTask e ts).executions := by
  simp only [State.setTask_eq, State.setExecution_executions]
  exact List.mem_map.mpr ⟨e, he, by simp⟩

theorem invocable_of_invoke {pl : Placement} {s t : State} {id : String} {path : Path} {name : String}
    {trigger : Option ResultId} {input : Option Value} {p : Definition}
    (h : (∃ f decl, pl.control = .call (.function f) ∧ p.function? f = some decl ∧ s.call? id = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            calls := s.calls ++ [{
              id, owner := id, target := .function f, input
              stream := decl.output.kind == .stream, timeout := pl.timeout, policy := pl.policy }] }) ∨
       (∃ judge arms, pl.control = .branch judge arms ∧ s.call? id = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            calls := s.calls ++ [{
              id, owner := id, target := .judge judge, input, timeout := pl.timeout, policy := pl.policy }] }) ∨
       (∃ wf out, pl.control = .call (.workflow wf out) ∧ s.run? (path ++ [id]) = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            runs := s.runs ++ [{ path := path ++ [id], workflow := wf, input, owner := some id }] }) ∨
       (∃ c, pl.control = .concurrency c ∧ s.execution? id = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            executions := s.executions ++ [{
              id, run := path, placement := name, input
              tasks := c.tasks.map fun ts =>
                { name := ts.name, status := if c.input.isSome then .pending else .ready } }] })) :
    Invocable pl.control ∧ t.invocations = s.invocations ++ [{ id, run := path, placement := name, trigger, input }] := by
  rcases h with ⟨_, _, hc, -, -, rfl⟩ | ⟨_, _, hc, -, rfl⟩ | ⟨_, _, hc, -, rfl⟩ | ⟨_, hc, -, rfl⟩ <;>
    exact ⟨by simp [hc, Invocable], rfl⟩

open State in
/-- Every invocation after a step is one from before, or the one `invoke` created. --/
theorem step_invocations_back {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ i ∈ t.invocations, InvOld s i ∨ NewInvocation p s i := by
  intro x hx
  have same : t.invocations = s.invocations → InvOld s x ∨ NewInvocation p s x := fun h =>
    Or.inl (invOld_self (h ▸ hx))
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨h1, h2, r, w, pl, input, id, hr, hc, hw, hpl, hinput, rfl, hdup, hid', h⟩ := Step.invoke_inv hs
    obtain ⟨hinv, ht⟩ := invocable_of_invoke h
    rw [ht, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl (invOld_self hx)
    · exact Or.inr ⟨h1, h2, r, w, pl, hr, hc, hw, hpl, hinv, hinput, rfl, rfl, rfl, hdup, hid'⟩
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    obtain ⟨i₀, hi₀, h⟩ := (settleOwner_old hso).1 x hx
    exact Or.inl ⟨i₀, by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1] at hi₀; exact hi₀, h⟩
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', hc, -, -, -, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hi' : i ∈ (s'.setCall { c with status := .returned }).invocations := by
      rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]; exact (invocation?_eq_some hi).1
    obtain ⟨i₀, hi₀, h⟩ := invOld_setInvocation hi' hx rfl rfl rfl rfl rfl
    exact Or.inl ⟨i₀, by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1] at hi₀; exact hi₀, h⟩
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact Or.inl (invOld_self (by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1] at hx; exact hx))
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact Or.inl ((settleOwner_old hso).1 x hx)
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact Or.inl ((failCall_old (call?_eq_some hc).1 (by simp) h).1 x hx)
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact Or.inl ((failCall_old (call?_eq_some hc).1 (by simp) h).1 x hx)
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact Or.inl ((failCall_old (call?_eq_some hc).1 (by simp) h).1 x hx)
    · exact Or.inl ((cancelOwner_old h).1 x hx)
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact Or.inl ((cancelOwner_old h).1 x hx)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact same (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i, -, -, -, -, -, hi, h⟩ := Step.closeExecution_inv hs
    have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (invocation?_eq_some hi).1
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
      exact Or.inl (invOld_setInvocation hi' hx rfl rfl rfl rfl rfl)
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, i, hi, h⟩ | ⟨_, e, ts, -, he, -, h⟩
    · have hi' : i ∈ (s.setRun { r with complete := true }).invocations := (invocation?_eq_some hi).1
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact Or.inl (invOld_setInvocation hi' hx rfl rfl rfl rfl rfl)
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-! ### Calls -/

open State in
/-- Every call after a step is one from before, or the one `invoke` or `beginTask` created. --/
theorem step_calls_back {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ c ∈ t.calls, CallOld s c ∨ NewCall p s t c := by
  intro x hx
  have same : t.calls = s.calls → CallOld s x ∨ NewCall p s t x := fun h => Or.inl (callOld_self (h ▸ hx))
  have setc : ∀ {c : Call} {st : CallStatus}, c ∈ s.calls → (st ≠ .running ∧ st ≠ .fetching) →
      x ∈ (s.setCall { c with status := st }).calls → CallOld s x ∨ NewCall p s t x := fun hc hst hx =>
    Or.inl (callOld_setCall hc hx rfl rfl rfl rfl rfl fun h => absurd h (by simp [hst]))
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨h1, h2, r, w, pl, input, id, hr, hc, hw, hpl, hinput, rfl, hdup, hid', h⟩ := Step.invoke_inv hs
    have hwf : s.workflow? p path = some w := workflow?_iff.mpr ⟨r, hr, hw⟩
    have hpath := (run?_eq_some hr).2
    obtain ⟨hinv, -⟩ := invocable_of_invoke h
    have hnew : NewInvocation p s
        { id := Key.invocation path name trigger, run := path, placement := name, trigger := trigger, input := input } :=
      ⟨h1, h2, r, w, pl, hr, hc, hw, hpl, hinv, hinput, rfl, rfl, rfl, hdup, hid'⟩
    rcases h with ⟨f, decl, hf, hdecl, hcall, rfl⟩ | ⟨judge, arms, hb, hcall, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl (callOld_self hx)
      · exact Or.inr ⟨hcall, rfl, Or.inl ⟨rfl, rfl, _, List.mem_append_right _ (List.mem_singleton_self _), rfl, hnew,
          w, pl, hwf, hpl, Or.inl ⟨f, decl, hf, hdecl, rfl, rfl⟩⟩⟩
    · rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl (callOld_self hx)
      · exact Or.inr ⟨hcall, rfl, Or.inl ⟨rfl, rfl, _, List.mem_append_right _ (List.mem_singleton_self _), rfl, hnew,
          w, pl, hwf, hpl, Or.inr ⟨judge, arms, hb, rfl, rfl⟩⟩⟩
    · exact same rfl
    · exact same rfl
  | fetch id =>
    obtain ⟨-, -, c, hc, -, h4, rfl⟩ := Step.fetch_inv hs
    exact Or.inl (callOld_setCall (call?_eq_some hc).1 hx rfl rfl rfl rfl rfl fun _ => Or.inl h4)
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    rw [(settleOwner_old hso).2.1] at hx
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    obtain ⟨c₀, hc₀, h⟩ := callOld_setCall hc' hx rfl rfl rfl rfl rfl (fun h => absurd h (by simp))
    exact Or.inl ⟨c₀, by rw [(accept_frame hacc).2.2.2.2.2.1] at hc₀; exact hc₀, h⟩
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    obtain ⟨c₀, hc₀, h⟩ := callOld_setCall hc' hx rfl rfl rfl rfl rfl (fun h => absurd h (by simp))
    exact Or.inl ⟨c₀, by rw [(accept_frame hacc).2.2.2.2.2.1] at hc₀; exact hc₀, h⟩
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, h4, hacc, rfl⟩ := Step.yielded_inv hs
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    obtain ⟨c₀, hc₀, h⟩ := callOld_setCall hc' hx rfl rfl rfl rfl rfl (fun _ => Or.inr h4)
    exact Or.inl ⟨c₀, by rw [(accept_frame hacc).2.2.2.2.2.1] at hc₀; exact hc₀, h⟩
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    rw [(settleOwner_old hso).2.1] at hx
    exact setc (call?_eq_some hc).1 (by simp) hx
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact Or.inl ((failCall_old (call?_eq_some hc).1 (by simp) h).2.1 x hx)
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact Or.inl ((failCall_old (call?_eq_some hc).1 (by simp) h).2.1 x hx)
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact Or.inl ((failCall_old (call?_eq_some hc).1 (by simp) h).2.1 x hx)
    · rw [(cancelOwner_old h).2.1] at hx
      exact setc (call?_eq_some hc).1 (by simp) hx
  | terminated id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.terminated_inv hs
    rw [(cancelOwner_old h).2.1] at hx
    exact setc (call?_eq_some hc).1 (by simp) hx
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    have h' := callOld_fail hx
    exact Or.inl h'
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    have h' := callOld_fail hx
    exact Or.inl h'
  | beginTask eid name =>
    obtain ⟨-, h2, e, c, ts, spec, he, h3, -, hts, h4, -, hspec, h⟩ := Step.beginTask_inv hs
    obtain ⟨hmem, rfl⟩ := execution?_eq_some he
    rcases h with ⟨f, decl, hf, -, hcall, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl (callOld_self hx)
      · exact Or.inr ⟨hcall, rfl, Or.inr ⟨name, e, ts, spec, f, rfl, rfl, he, h3, hts, h4, hspec, hf,
          mem_setTask_self hmem, h2⟩⟩
    · exact same rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    have h' := callOld_fail hx
    exact Or.inl h'
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact Or.inl (callOld_stop hx)
    · exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-! ### Runs -/

open State in
/-- Every run after a step is one from before, or the one `start`, `invoke` or `beginTask` created. --/
theorem step_runs_back {p : Definition} {s t : State} {op : Op} (hfresh : s.runs = [] ∨ s.started = true)
    (hs : step p s op = .ok t) : ∀ r ∈ t.runs, RunOld s r ∨ NewRun p s t r := by
  intro x hx
  have same : t.runs = s.runs → RunOld s x ∨ NewRun p s t x := fun h => Or.inl (runOld_self (h ▸ hx))
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    have hnil : s.runs = [] := hfresh.resolve_right (by simp [hst])
    simp only [List.mem_singleton] at hx
    subst hx
    exact Or.inr ⟨by simp [State.run?, hnil], rfl, Or.inl ⟨hst, rfl, rfl, rfl⟩⟩
  | invoke path name trigger =>
    obtain ⟨h1, h2, r, w, pl, input, id, hr, hc, hw, hpl, hinput, rfl, hdup, hid', h⟩ := Step.invoke_inv hs
    have hwf : s.workflow? p path = some w := workflow?_iff.mpr ⟨r, hr, hw⟩
    obtain ⟨hinv, -⟩ := invocable_of_invoke h
    have hnew : NewInvocation p s
        { id := Key.invocation path name trigger, run := path, placement := name, trigger := trigger, input := input } :=
      ⟨h1, h2, r, w, pl, hr, hc, hw, hpl, hinv, hinput, rfl, rfl, rfl, hdup, hid'⟩
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨wf, out, hwf', hrun, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact same rfl
    · exact same rfl
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl (runOld_self hx)
      · exact Or.inr ⟨hrun, rfl, Or.inr (Or.inl ⟨rfl, _, List.mem_append_right _ (List.mem_singleton_self _), rfl, hnew,
          rfl, w, pl, wf, out, hwf, hpl, hwf'⟩)⟩
    · exact same rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact same (by rw [(settleOwner_old hso).2.2.1, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact same (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(settleOwner_old hso).2.2.1, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact same (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact same (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact same (failCall_runs h)
    · exact same (by rw [(cancelOwner_old h).2.2.1, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact same (by rw [(cancelOwner_old h).2.2.1, setCall_runs])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simp)
  | beginTask eid name =>
    obtain ⟨-, h2, e, c, ts, spec, he, h3, -, hts, h4, -, hspec, h⟩ := Step.beginTask_inv hs
    obtain ⟨hmem, rfl⟩ := execution?_eq_some he
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨wf, out, hwf, hrun, rfl⟩
    · exact same rfl
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl (runOld_self hx)
      · exact Or.inr ⟨hrun, rfl, Or.inr (Or.inr ⟨name, e, ts, spec, wf, out, rfl, rfl, he, h3, hts, h4, hspec, hwf, rfl,
          mem_setTask_self hmem, h2⟩)⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact same (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    have hr' := (run?_eq_some hr).1
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact Or.inl (runOld_setRun hr' hx)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact Or.inl (runOld_setRun (run?_eq_some hr).1 hx)
    · exact same rfl

/-! ### Executions -/

open State in
/-- Every execution after a step is one from before, or the one `invoke` created. --/
theorem step_executions_back {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ e ∈ t.executions, ExecOld s e ∨ NewExecution p s t e := by
  intro x hx
  have same : t.executions = s.executions → ExecOld s x ∨ NewExecution p s t x := fun h =>
    Or.inl (execOld_self (h ▸ hx))
  have owners : ∀ {u : State}, (∀ y ∈ u.executions, ExecOld s y) → x ∈ u.executions → ExecOld s x ∨ NewExecution p s t x :=
    fun h hx => Or.inl (h x hx)
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨h1, h2, r, w, pl, input, id, hr, hc, hw, hpl, hinput, rfl, hdup, hid', h⟩ := Step.invoke_inv hs
    have hwf : s.workflow? p path = some w := workflow?_iff.mpr ⟨r, hr, hw⟩
    obtain ⟨hinv, -⟩ := invocable_of_invoke h
    have hnew : NewInvocation p s
        { id := Key.invocation path name trigger, run := path, placement := name, trigger := trigger, input := input } :=
      ⟨h1, h2, r, w, pl, hr, hc, hw, hpl, hinv, hinput, rfl, rfl, rfl, hdup, hid'⟩
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨c, hcc, hexec, rfl⟩
    · exact same rfl
    · exact same rfl
    · exact same rfl
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl (execOld_self hx)
      · refine Or.inr ⟨hexec, rfl, _, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl, hnew,
          w, pl, c, hwf, hpl, hcc, by simp, ?_⟩
        intro tk htk
        simp only [List.mem_map] at htk
        obtain ⟨ts, -, rfl⟩ := htk
        split <;> simp
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    obtain ⟨y, hy, h⟩ := (settleOwner_old hso).2.2.2.1 x hx
    exact Or.inl ⟨y, by rw [setCall_executions, (accept_frame hacc).2.2.2.2.2.2.1] at hy; exact hy, h⟩
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact same (by rw [setInvocation_executions, setCall_executions, (accept_frame hacc).2.2.2.2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by rw [setCall_executions, (accept_frame hacc).2.2.2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact owners (settleOwner_old hso).2.2.2.1 hx
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact owners (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.1 hx
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact owners (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.1 hx
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact owners (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.1 hx
    · exact owners (cancelOwner_old h).2.2.2.1 hx
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact owners (cancelOwner_old h).2.2.2.1 hx
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    have h' := execOld_fail hx
    exact Or.inl h'
  | taskInput eid name value =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Or.inl (execOld_setTask (execution?_eq_some he).1 hx)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    obtain ⟨y, hy, h⟩ := execOld_fail hx
    obtain ⟨z, hz, h'⟩ := execOld_setTask (execution?_eq_some he).1 hy
    exact Or.inl ⟨z, hz, h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
      fun hc => h.2.2.2.2 (h'.2.2.2.2 hc)⟩
  | beginTask eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;>
      exact Or.inl (execOld_setTask (execution?_eq_some he).1 hx)
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    have h' := execOld_fail hx
    exact Or.inl h'
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    have he' := (execution?_eq_some he).1
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
      exact Or.inl (execOld_setExecution he' hx rfl rfl rfl rfl fun _ => rfl)
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, e, _, -, he, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact Or.inl (execOld_setTask (s := s.setRun _) (execution?_eq_some he).1 hx)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact Or.inl (execOld_stop hx)
    · exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-! ### Task results -/

theorem accept_taskResults {s t : State} {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) :
    t.taskResults = s.taskResults ∨
      ∃ name, c.task = some name ∧ t.taskResults = s.taskResults ++ [{ execution := c.owner, task := name, index, value }] := by
  rcases State.accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨name, hn, -, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨name, hn, rfl⟩

open State in
/-- Every task result after a step is one from before, or one a running task call or a closing task
    run produced. --/
theorem step_taskResults_back {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ r ∈ t.taskResults, TaskResultOld s r ∨ NewTaskResult s r := by
  intro x hx
  have same : t.taskResults = s.taskResults → TaskResultOld s x ∨ NewTaskResult s x := fun h =>
    Or.inl (taskResultOld_self (h ▸ hx))
  -- A call that reports a value while running or fetching.
  have accepted : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
      c ∈ s.calls → (c.status = .running ∨ c.status = .fetching) → s.accept c index value arm = .ok s' →
      t.taskResults = s'.taskResults → TaskResultOld s x ∨ NewTaskResult s x := by
    intro c index value arm s' hc hrun hacc ht
    rw [ht] at hx
    rcases accept_taskResults hacc with h | ⟨name, hn, h⟩
    · exact Or.inl (taskResultOld_self (h ▸ hx))
    · rw [h, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl (taskResultOld_self hx)
      · exact Or.inr ⟨rfl, Or.inl ⟨c, hc, rfl, hn, hrun⟩⟩
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, h4, -, hacc, hso⟩ := Step.returned_inv hs
    exact accepted (call?_eq_some hc).1 (Or.inl h4) hacc (by rw [(settleOwner_old hso).2.2.2.2.1, setCall_taskResults])
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, h3, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact accepted (call?_eq_some hc).1 (Or.inl h3) hacc (by rw [setInvocation_taskResults, setCall_taskResults])
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, h4, hacc, rfl⟩ := Step.yielded_inv hs
    exact accepted (call?_eq_some hc).1 (Or.inr h4) hacc (by rw [setCall_taskResults])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(settleOwner_old hso).2.2.2.2.1, setCall_taskResults])
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact same (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact same (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact same (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
    · exact same (by rw [(cancelOwner_old h).2.2.2.2.1, setCall_taskResults])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact same (by rw [(cancelOwner_old h).2.2.2.2.1, setCall_taskResults])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, r, -, -, -, -, hr, h4, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact Or.inl (taskResultOld_setTaskResult (List.mem_of_find?_eq_some hr) h4 hx)
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, hr, h4, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Or.inl (taskResultOld_setTaskResult (List.mem_of_find?_eq_some hr) h4 (by simpa using hx))
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, h3, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨name, e, _, htask, he, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl (taskResultOld_self hx)
        · refine Or.inr ⟨rfl, Or.inr ⟨r, (run?_eq_some hr).1, ?_, htask, h3⟩⟩
          rw [howner, (execution?_eq_some he).2]
      all_goals exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-! ### Deliveries and settlements -/

/-- Only a delivery or a failed transform records a delivery, and only `settle` a settlement. --/
theorem step_deliveries_settled_eq {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    (t.deliveries = s.deliveries ∨ ∃ path j src, (∃ v, op = .deliver path j src v) ∨ op = .transformFailed path j src) ∧
    (t.settled = s.settled ∨ ∃ path name, op = .settle path name) := by
  have g := step_grows hs
  cases op with
  | deliver path index source value => exact ⟨Or.inr ⟨_, _, _, Or.inl ⟨_, rfl⟩⟩, Or.inl (by
      obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs; rfl)⟩
  | transformFailed path index source => exact ⟨Or.inr ⟨_, _, _, Or.inr rfl⟩, Or.inl (by
      obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs; simp)⟩
  | settle path name => refine ⟨Or.inl ?_, Or.inr ⟨_, _, rfl⟩⟩
                        obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
                        rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> rfl
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have u := settleOwner_old hso
    exact ⟨Or.inl (by rw [u.2.2.2.2.2.2.1, State.setCall_deliveries, (accept_frame hacc).2.2.2.2.2.2.2.1]),
      Or.inl (by rw [u.2.2.2.2.2.2.2, State.setCall_settled, (accept_frame hacc).2.2.2.2.2.2.2.2.1])⟩
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact ⟨Or.inl (by simp [(accept_frame hacc).2.2.2.2.2.2.2.1]), Or.inl (by simp [(accept_frame hacc).2.2.2.2.2.2.2.2.1])⟩
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact ⟨Or.inl (by simp [(accept_frame hacc).2.2.2.2.2.2.2.1]), Or.inl (by simp [(accept_frame hacc).2.2.2.2.2.2.2.2.1])⟩
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    have u := settleOwner_old hso
    exact ⟨Or.inl (by rw [u.2.2.2.2.2.2.1, State.setCall_deliveries]), Or.inl (by rw [u.2.2.2.2.2.2.2, State.setCall_settled])⟩
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    have u := failCall_old (State.call?_eq_some hc).1 (by simp) h
    exact ⟨Or.inl u.2.2.2.2.2.2.1, Or.inl u.2.2.2.2.2.2.2⟩
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    have u := failCall_old (State.call?_eq_some hc).1 (by simp) h
    exact ⟨Or.inl u.2.2.2.2.2.2.1, Or.inl u.2.2.2.2.2.2.2⟩
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · have u := failCall_old (State.call?_eq_some hc).1 (by simp) h
      exact ⟨Or.inl u.2.2.2.2.2.2.1, Or.inl u.2.2.2.2.2.2.2⟩
    · have u := cancelOwner_old h
      exact ⟨Or.inl (by rw [u.2.2.2.2.2.2.1, State.setCall_deliveries]), Or.inl (by rw [u.2.2.2.2.2.2.2, State.setCall_settled])⟩
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    have u := cancelOwner_old h
    exact ⟨Or.inl (by rw [u.2.2.2.2.2.2.1, State.setCall_deliveries]), Or.inl (by rw [u.2.2.2.2.2.2.2, State.setCall_settled])⟩
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact ⟨Or.inl (by simp), Or.inl (by simp)⟩
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact ⟨Or.inl rfl, Or.inl rfl⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨Or.inl rfl, Or.inl rfl⟩
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact ⟨Or.inl (by simp), Or.inl (by simp)⟩
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact ⟨Or.inl rfl, Or.inl rfl⟩
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨Or.inl rfl, Or.inl rfl⟩
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact ⟨Or.inl rfl, Or.inl rfl⟩
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact ⟨Or.inl rfl, Or.inl rfl⟩

open State in
/-- Every delivery after a step is one from before, or one checked against the state before it. --/
theorem step_deliveries_back {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ d ∈ t.deliveries, d ∈ s.deliveries ∨ NewDelivery p s d := by
  intro x hx
  rcases (step_deliveries_settled_eq hs).1 with h | ⟨path, j, src, ⟨v, rfl⟩ | rfl⟩
  · exact Or.inl (h ▸ hx)
  · obtain ⟨h1, h2, w, c, _, hdt, -, rfl⟩ := Step.deliver_inv hs
    obtain ⟨hw, hc, ⟨r, hr, hrun, hpl, harm⟩, hd⟩ := Step.deliveryTarget_eq_ok.mp hdt
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr ⟨h1, h2, hd, w, c, r, hw, hc, hr, hrun, hpl, harm⟩
  · obtain ⟨h1, h2, w, c, _, _, hdt, -, -, rfl⟩ := Step.transformFailed_inv hs
    obtain ⟨hw, hc, ⟨r, hr, hrun, hpl, harm⟩, hd⟩ := Step.deliveryTarget_eq_ok.mp hdt
    simp only [fail_deliveries, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr ⟨h1, h2, hd, w, c, r, hw, hc, hr, hrun, hpl, harm⟩

open State in
/-- Every settlement after a step is one from before, or the one `settle` recorded. --/
theorem step_settled_back {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ x ∈ t.settled, x ∈ s.settled ∨ NewSettled p s t x := by
  intro x hx
  rcases (step_deliveries_settled_eq hs).2 with h | ⟨path, name, rfl⟩
  · exact Or.inl (h ▸ hx)
  · obtain ⟨h1, h2, run, w, pl, shape, kind, x', res, hr, h3, hw, hpl, h4, hshape, hkind, hout, h⟩ :=
      Step.settle_inv hs
    obtain ⟨-, hxrun, hxpl, -⟩ := State.settleOutcome_some hout
    have hname := (Workflow.placement?_eq_some hpl).2
    rcases h with ⟨rfl, rfl⟩ | ⟨r, rfl, hres, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · refine Or.inr ⟨h1, h2, run, w, pl, shape, kind, none, ?_, h3, hw, ?_, ?_, ?_, ?_, ?_, rfl, by simp, rfl, rfl,
          rfl, rfl, rfl, rfl, fun r hr => by cases hr⟩
        all_goals simp only [hxrun, hxpl, hname]
        all_goals assumption
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · refine Or.inr ⟨h1, h2, run, w, pl, shape, kind, some r, ?_, h3, hw, ?_, ?_, ?_, ?_, ?_, rfl, by simp, rfl, rfl,
          rfl, rfl, rfl, rfl, fun r' hr' => by cases hr'; exact hres⟩
        all_goals simp only [hxrun, hxpl, hname]
        all_goals assumption

/-! ### Results -/

open State in
/-- Every result after a step is one from before, or one the step accepted, with where it came from. --/
theorem step_results_back {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ r ∈ t.results, r ∈ s.results ∨ NewResult p s t r := by
  intro x hx
  have same : t.results = s.results → x ∈ s.results ∨ NewResult p s t x := fun h => Or.inl (h ▸ hx)
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨h1, h2, c, f, s', hc, h3, h4, hf, hacc, hso⟩ := Step.returned_inv hs
    rw [(settleOwner_old hso).2.2.2.2.2.1, setCall_results] at hx
    rcases State.accept_eq_ok.mp hacc with ⟨htask, i, hi, hres, rfl⟩ | ⟨name, htask, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · have hmem : { i with status := .succeeded } ∈ t.invocations := by
          rcases State.settleOwner_eq_ok.mp hso with ⟨-, i', hi', rfl⟩ | ⟨_, _, _, h, -⟩
          · obtain rfl : i' = i := Option.some.inj (hi'.symm.trans hi)
            exact mem_setInvocation_self (invocation?_eq_some hi).1 _ _
          · rw [htask] at h; cases h
        exact Or.inr ⟨h1, h2, hres, Or.inl ⟨c, (call?_eq_some hc).1, i, (invocation?_eq_some hi).1, htask, h4, h3,
          ⟨f, hf⟩, (invocation?_eq_some hi).2, rfl, rfl, rfl, rfl, hmem⟩⟩
    · exact Or.inl hx
  | judged id arm =>
    obtain ⟨h1, h2, c, j, i, pl, judge, arms, s', hc, h3, hj, h5, hi, hpl, hb, harm, hacc, rfl⟩ := Step.judged_inv hs
    obtain ⟨w, hw, hpl'⟩ := State.placementOf_eq_ok.mp hpl
    rw [setInvocation_results, setCall_results] at hx
    rcases State.accept_eq_ok.mp hacc with ⟨-, i', hi', hres, rfl⟩ | ⟨name, htask, -, rfl⟩
    · obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr ⟨h1, h2, hres, Or.inr (Or.inl ⟨c, (call?_eq_some hc).1, i, (invocation?_eq_some hi).1, arm, judge,
          arms, w, pl, h5, h3, (invocation?_eq_some hi).2, hw, hpl', hb, rfl, rfl, rfl, rfl,
          mem_setInvocation_self (invocation?_eq_some hi).1 _ _⟩)⟩
    · rw [h5] at htask; cases htask
  | yielded id value =>
    obtain ⟨h1, h2, c, s', hc, h3, h4, hacc, rfl⟩ := Step.yielded_inv hs
    rw [setCall_results] at hx
    rcases State.accept_eq_ok.mp hacc with ⟨htask, i, hi, hres, rfl⟩ | ⟨name, htask, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr ⟨h1, h2, hres, Or.inr (Or.inr (Or.inl ⟨c, (call?_eq_some hc).1, i, (invocation?_eq_some hi).1,
          htask, h4, h3, (invocation?_eq_some hi).2, rfl, rfl, rfl, rfl⟩))⟩
    · exact Or.inl hx
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(settleOwner_old hso).2.2.2.2.2.1, setCall_results])
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact same (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.2.1
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact same (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.2.1
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact same (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.2.1
    · exact same (by rw [(cancelOwner_old h).2.2.2.2.2.1, setCall_results])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact same (by rw [(cancelOwner_old h).2.2.2.2.2.1, setCall_results])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same rfl
  | taskOutput eid name index value =>
    obtain ⟨h1, h2, e, c, spec, tr, he, hc, hspec, h3, htr, h4, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨hout, hres, rfl⟩ | ⟨-, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · obtain ⟨he', rfl⟩ := execution?_eq_some he
        have htr' := List.mem_of_find?_eq_some htr
        have htrk : tr.execution = e.id ∧ tr.task = name ∧ tr.index = index := by
          simpa [and_assoc] using List.find?_some htr
        obtain ⟨c', hc', hfind⟩ := State.taskSpec_eq_ok.mp hspec
        rw [hc] at hc'
        cases hc'
        exact Or.inr ⟨h1, h2, hres, Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he', c, tr, hc, hout, htr', htrk.1, h4,
          ⟨spec, List.mem_of_find?_eq_some hfind, by rw [htrk.2.1]; simpa using List.find?_some hfind, h3⟩,
          rfl, rfl, rfl, rfl⟩)))⟩
    · exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact same (by simp)
  | settle path name =>
    obtain ⟨h1, h2, run, w, pl, shape, kind, x', res, hr, h3, hw, hpl, h4, hshape, hkind, hout, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨r, rfl, hres, rfl⟩
    · exact same rfl
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · obtain ⟨-, -, -, -, hrun, hplace, -⟩ := settleOutcome_res hout
        have hname := (Workflow.placement?_eq_some hpl).2
        refine Or.inr ⟨h1, h2, hres, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨run, w, pl, shape, kind, x',
          ?_, hw, ?_, ?_, ?_, ?_, ?_, ?_⟩)))))⟩
        all_goals simp only [hrun, hplace, hname]
        all_goals first | assumption | simp
  | closeExecution eid =>
    obtain ⟨h1, h2, e, c, i, he, h3, hc, -, -, hi, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, hout, hres, rfl⟩ | ⟨-, -, rfl⟩
    · exact same rfl
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · obtain ⟨he', rfl⟩ := execution?_eq_some he
        have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (invocation?_eq_some hi).1
        exact Or.inr ⟨h1, h2, hres, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he', i, (invocation?_eq_some hi).1, c,
          h3, (invocation?_eq_some hi).2, hc, hout, rfl, rfl, rfl, rfl, mem_setInvocation_self hi' _ _⟩))))⟩
    · exact same rfl
  | closeRun path =>
    obtain ⟨h1, h2, r, w, output, x', owner, hr, h3, h4, hw, h5, hout, hx', howner, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨htask, i, hi, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · rcases h with ⟨-, v, -, hres, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl hx
        · have hi' : i ∈ (s.setRun { r with complete := true }).invocations := (invocation?_eq_some hi).1
          refine Or.inr ⟨h1, h2, hres, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, (run?_eq_some hr).1, i,
            (invocation?_eq_some hi).1, h3, htask, ?_, rfl, rfl, rfl, rfl, mem_setInvocation_self hi' _ _⟩)))))⟩
          rw [howner, (invocation?_eq_some hi).2]
      all_goals exact same rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

end Suimon.Delivery
