import Suimon.Theorems.DeliveryOwn

/-! Consequences of ownership: which placement owns calls, runs and executions, and which records
    after a step belong to records from before. -/

namespace Suimon.Delivery
open State

section Placement
variable {p : Definition} {s : State}

/-- The placement of an invocation in the workflow of its run. --/
def PlacementOf (p : Definition) (s : State) (i : Invocation) (pl : Placement) : Prop :=
  ∃ w, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl

theorem PlacementOf.unique {i : Invocation} {pl pl' : Placement} (h : PlacementOf p s i pl) (h' : PlacementOf p s i pl') :
    pl = pl' := by
  obtain ⟨w, hw, hpl⟩ := h
  obtain ⟨w', hw', hpl'⟩ := h'
  rw [hw] at hw'; cases hw'
  rw [hpl] at hpl'; cases hpl'
  rfl

theorem placementOf_of_mem (own : Own p s) {i : Invocation} (hi : i ∈ s.invocations) :
    ∃ pl, PlacementOf p s i pl ∧ Invocable pl.control := by
  obtain ⟨-, w, pl, -, hw, hpl, hinv, -⟩ := own.invocations i hi
  exact ⟨pl, ⟨w, hw, hpl⟩, hinv⟩

/-- A call without a task belongs to the invocation of a function call or a branch. --/
theorem call_placement (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) (htask : c.task = none)
    {i : Invocation} (hi : i ∈ s.invocations) (hid : i.id = c.owner) :
    c.id = c.owner ∧ ∃ pl, PlacementOf p s i pl ∧
      ((∃ f d, pl.control = .call (.function f) ∧ p.function? f = some d ∧ c.target = .function f ∧
          c.stream = (d.output.kind == .stream)) ∨
       (∃ j arms, pl.control = .branch j arms ∧ c.target = .judge j ∧ c.stream = false)) := by
  rcases own.calls c hc with ⟨-, hco, i', hi', hi'o, w, pl, hw, hpl, hk⟩ | ⟨name, ht, -⟩
  · obtain rfl := wk.invocation_eq_of_id hi' hi (hi'o.trans hid.symm)
    exact ⟨hco, pl, ⟨w, hw, hpl⟩, hk⟩
  · rw [htask] at ht; cases ht

/-- A run without a task belongs to the invocation of a sub-workflow call, under a path of its own. --/
theorem run_placement (own : Own p s) (wk : s.WellKeyed) {r : Run} (hr : r ∈ s.runs) (htask : r.task = none)
    {i : Invocation} (hi : i ∈ s.invocations) (howner : r.owner = some i.id) :
    r.path = Key.child i.id ∧ ∃ pl, PlacementOf p s i pl ∧ ∃ wf out, pl.control = .call (.workflow wf out) := by
  rcases own.runs r hr with ⟨ho, -, -⟩ | ⟨-, i', hi', ho, hp, w, pl, wf, out, hw, hpl, hc⟩ | ⟨name, ht, -⟩
  · rw [howner] at ho; cases ho
  · obtain rfl := wk.invocation_eq_of_id hi' hi (Option.some.inj (ho.symm.trans howner))
    exact ⟨hp, pl, ⟨w, hw, hpl⟩, wf, out, hc⟩
  · rw [htask] at ht; cases ht

/-- An execution belongs to the invocation of a concurrency placement. --/
theorem execution_placement (own : Own p s) (wk : s.WellKeyed) {e : Execution} (he : e ∈ s.executions)
    {i : Invocation} (hi : i ∈ s.invocations) (hid : i.id = e.id) :
    i.run = e.run ∧ i.placement = e.placement ∧ ∃ pl c, PlacementOf p s i pl ∧ pl.control = .concurrency c ∧
      s.concurrencyOf p e = .ok c := by
  obtain ⟨i', hi', hi'id, hi'r, hi'p, c, hc⟩ := own.executions e he
  obtain rfl := wk.invocation_eq_of_id hi' hi (hi'id.trans hid.symm)
  obtain ⟨w, pl, hw, hpl, hcc⟩ := concurrencyOf_iff.mp hc
  exact ⟨hi'r, hi'p, pl, c, ⟨w, hi'r ▸ hw, hi'p ▸ hpl⟩, hcc, hc⟩

/-- The owner execution of a task call or task run is unique; its task spec decides the body. --/
theorem task_body_function (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) {name : String}
    (htask : c.task = some name) {e : Execution} (he : e ∈ s.executions) (hid : e.id = c.owner) :
    c.id = Key.task e.id name ∧ (∃ tk ∈ e.tasks, tk.name = name) ∧
      ∃ spec f, s.taskSpec p e name = .ok spec ∧ spec.body = .function f := by
  rcases own.calls c hc with ⟨ht, -⟩ | ⟨name', ht, hkey, e', he', he'o, htk, spec, f, hspec, hbody⟩
  · rw [htask] at ht; cases ht
  · rw [htask] at ht; cases ht
    obtain rfl := wk.execution_eq_of_id he' he (he'o.trans hid.symm)
    exact ⟨by rw [hkey, he'o], htk, spec, f, hspec, hbody⟩

theorem task_body_workflow (own : Own p s) (wk : s.WellKeyed) {r : Run} (hr : r ∈ s.runs) {name : String}
    (htask : r.task = some name) {e : Execution} (he : e ∈ s.executions) (howner : r.owner = some e.id) :
    (∃ tk ∈ e.tasks, tk.name = name) ∧ ∃ spec wf out, s.taskSpec p e name = .ok spec ∧ spec.body = .workflow wf out := by
  rcases own.runs r hr with ⟨-, ht, -⟩ | ⟨ht, -⟩ | ⟨name', ht, e', he', ho, -, htk, spec, wf, out, hspec, hbody⟩
  · rw [htask] at ht; cases ht
  · rw [htask] at ht; cases ht
  · rw [htask] at ht; cases ht
    obtain rfl := wk.execution_eq_of_id he' he (Option.some.inj (ho.symm.trans howner))
    exact ⟨htk, spec, wf, out, hspec, hbody⟩

/-- A task has a call or a run, never both. --/
theorem task_call_run (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) {r : Run} (hr : r ∈ s.runs)
    {name : String} (hct : c.task = some name) (hrt : r.task = some name) (hown : r.owner = some c.owner) : False := by
  obtain ⟨e, he, heid⟩ : ∃ e ∈ s.executions, e.id = c.owner := by
    rcases own.calls c hc with ⟨ht, -⟩ | ⟨_, _, _, e, he, heo, -⟩
    · rw [hct] at ht; cases ht
    · exact ⟨e, he, heo⟩
  obtain ⟨-, -, spec, f, hspec, hbody⟩ := task_body_function own wk hc hct he heid
  obtain ⟨-, spec', wf, out, hspec', hbody'⟩ := task_body_workflow own wk hr hrt he (by rw [hown, heid])
  rw [hspec] at hspec'
  cases hspec'
  rw [hbody] at hbody'
  cases hbody'

/-- A non-branch invocation records no arm. --/
theorem arm_none (own : Own p s) {i : Invocation} (hi : i ∈ s.invocations) {pl : Placement} (hpl : PlacementOf p s i pl)
    (hnb : ∀ j arms, pl.control ≠ .branch j arms) : i.arm = none := by
  obtain ⟨-, w, pl', -, hw, hpl', -, -, -, harm⟩ := own.invocations i hi
  rcases harm with h | ⟨j, arms, hb⟩
  · exact h
  · obtain rfl := hpl.unique ⟨w, hw, hpl'⟩
    exact absurd hb (hnb j arms)

end Placement

/-! ### Records after a step that belong to records from before -/

theorem NewInvocation.fresh {p : Definition} {s : State} {i : Invocation} (h : NewInvocation p s i) :
    s.invocation? i.id = none := by
  obtain ⟨-, -, _, _, _, -, -, -, -, -, -, -, -, -, -, h⟩ := h
  exact h

theorem NewInvocation.active {p : Definition} {s : State} {i : Invocation} (h : NewInvocation p s i) :
    i.status = .active := by
  obtain ⟨-, -, _, _, _, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem NewInvocation.not_mem {p : Definition} {s : State} {i i₀ : Invocation} (h : NewInvocation p s i)
    (hi₀ : i₀ ∈ s.invocations) (hid : i.id = i₀.id) : False := by
  have := h.fresh
  rw [State.invocation?_eq_none_iff] at this
  exact this (List.mem_map.mpr ⟨i₀, hi₀, hid.symm⟩)

section Owned
variable {p : Definition} {s t : State} {op : Op}

/-- A call after a step, without a task, whose owner is an invocation from before, is a call from before. --/
theorem call_of_old_owner (hs : step p s op = .ok t) {c : Call} (hc : c ∈ t.calls) (htask : c.task = none)
    {i₀ : Invocation} (hi₀ : i₀ ∈ s.invocations) (howner : c.owner = i₀.id) : CallOld s c := by
  rcases step_calls_back hs c hc with h | ⟨-, -, hcase⟩
  · exact h
  · rcases hcase with ⟨-, -, i, -, hio, hnew, -⟩ | ⟨name, _, _, _, _, ht, -⟩
    · exact (hnew.not_mem hi₀ (hio.trans howner)).elim
    · rw [htask] at ht; cases ht

theorem run_of_old_owner (hs : step p s op = .ok t) (hfresh : s.runs = [] ∨ s.started = true) {r : Run} (hr : r ∈ t.runs)
    (htask : r.task = none) {i₀ : Invocation} (hi₀ : i₀ ∈ s.invocations) (howner : r.owner = some i₀.id) : RunOld s r := by
  rcases step_runs_back hfresh hs r hr with h | ⟨-, -, hcase⟩
  · exact h
  · rcases hcase with ⟨-, ho, -⟩ | ⟨-, i, -, hio, hnew, -⟩ | ⟨name, _, _, _, _, _, ht, -⟩
    · rw [howner] at ho; cases ho
    · exact (hnew.not_mem hi₀ (Option.some.inj (hio.symm.trans howner))).elim
    · rw [htask] at ht; cases ht

theorem execution_of_old_id (hs : step p s op = .ok t) {e : Execution} (he : e ∈ t.executions)
    {i₀ : Invocation} (hi₀ : i₀ ∈ s.invocations) (hid : e.id = i₀.id) : ExecOld s e := by
  rcases step_executions_back hs e he with h | ⟨-, -, i, -, hio, -, -, hnew, -⟩
  · exact h
  · exact (hnew.not_mem hi₀ (hio.trans hid)).elim

end Owned

/-! ### Completion -/

theorem complete_setTask {s : State} {e₁ e₀ e : Execution} {ts : TaskState} (wk : s.WellKeyed) (he₁ : e₁ ∈ s.executions)
    (he₀ : e₀ ∈ s.executions) (he : e ∈ (s.setTask e₁ ts).executions) (hid : e.id = e₀.id) : e.complete = e₀.complete := by
  rcases mem_map_replace' he with rfl | ⟨he, -⟩
  · obtain rfl := wk.execution_eq_of_id he₁ he₀ hid
    rfl
  · obtain rfl := wk.execution_eq_of_id he he₀ hid
    rfl

theorem complete_fail {u : State} {f : Failure} {policy : Policy} {e₀ e : Execution}
    (h : ∀ e' ∈ u.executions, e'.id = e₀.id → e'.complete = e₀.complete)
    (he : e ∈ (u.fail f policy).executions) (hid : e.id = e₀.id) : e.complete = e₀.complete := by
  cases policy
  · obtain ⟨e', he', rfl⟩ := State.mem_stop_executions.mp (by simpa using he)
    exact h e' he' (by simpa using hid)
  · exact h e (by simpa using he) hid

theorem setTask_executions_congr {s u : State} {e : Execution} {ts : TaskState} (h : u.executions = s.executions) :
    (u.setTask e ts).executions = (s.setTask e ts).executions := by
  simp only [State.setTask_eq, State.setExecution_executions, h]

/-- What `closeExecution` checked before completing an execution. --/
def ExecClosed (p : Definition) (s t : State) (e₀ : Execution) : Prop :=
  ∃ c, s.concurrencyOf p e₀ = .ok c ∧ e₀.tasks.all (s.taskEnded e₀) = true ∧
    (s.taskResults.filter fun x => x.execution == e₀.id &&
      ((c.tasks.filter (·.output.isSome)).map (·.name)).contains x.task).all (·.output != .pending) = true ∧
    t.calls = s.calls ∧ t.runs = s.runs ∧ t.taskResults = s.taskResults

open State in
/-- Only `closeExecution` completes an execution, after checking its tasks and outputs (§8.3). --/
theorem step_execution_completed {p : Definition} {s t : State} {op : Op} (wk : s.WellKeyed) (hs : step p s op = .ok t)
    {e₀ e : Execution} (he₀ : e₀ ∈ s.executions) (he : e ∈ t.executions) (hid : e.id = e₀.id) :
    e.complete = e₀.complete ∨ ExecClosed p s t e₀ := by
  have same : e ∈ s.executions → e.complete = e₀.complete ∨ ExecClosed p s t e₀ := fun h =>
    Or.inl (congrArg Execution.complete (wk.execution_eq_of_id h he₀ hid))
  have setT : ∀ {e₁ : Execution} {ts : TaskState} {u : State}, e₁ ∈ s.executions →
      u.executions = (s.setTask e₁ ts).executions → e ∈ u.executions → e.complete = e₀.complete :=
    fun he₁ hu he => complete_setTask wk he₁ he₀ (hu ▸ he) hid
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same he
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, input, id, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, hexec, rfl⟩
    · exact same he
    · exact same he
    · exact same he
    · simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact same he
      · rw [State.execution?_eq_none_iff] at hexec
        exact absurd (List.mem_map.mpr ⟨e₀, he₀, hid.symm⟩) hexec
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same he
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have hexe : s'.executions = s.executions := (accept_frame hacc).2.2.2.2.2.2.1
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, -, he₁, -, rfl⟩
    · exact same (by simpa [hexe] using he)
    · have he₁' : e₁ ∈ s.executions := by
        have := (execution?_eq_some he₁).1; simpa [hexe] using this
      exact Or.inl (setT he₁' (setTask_executions_congr (by simp [hexe])) he)
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, s', -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact same (by simpa [(accept_frame hacc).2.2.2.2.2.2.1] using he)
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by simpa [(accept_frame hacc).2.2.2.2.2.2.1] using he)
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, -, he₁, -, rfl⟩
    · exact same he
    · exact Or.inl (setT (execution?_eq_some he₁).1 rfl he)
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
    refine Or.inl (complete_fail (fun e' he' hid' => ?_) he hid)
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, -, he₁, -, rfl⟩
    · exact congrArg Execution.complete (wk.execution_eq_of_id he' he₀ hid')
    · exact complete_setTask wk (execution?_eq_some he₁).1 he₀ he' hid'
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
    refine Or.inl (complete_fail (fun e' he' hid' => ?_) he hid)
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, -, he₁, -, rfl⟩
    · exact congrArg Execution.complete (wk.execution_eq_of_id he' he₀ hid')
    · exact complete_setTask wk (execution?_eq_some he₁).1 he₀ he' hid'
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
      refine Or.inl (complete_fail (fun e' he' hid' => ?_) he hid)
      rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, -, he₁, -, rfl⟩
      · exact congrArg Execution.complete (wk.execution_eq_of_id he' he₀ hid')
      · exact complete_setTask wk (execution?_eq_some he₁).1 he₀ he' hid'
    · rcases State.cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, -, he₁, -, rfl⟩ <;> split at he
      · exact same he
      · exact same he
      · exact Or.inl (complete_setTask wk (execution?_eq_some he₁).1 he₀ he hid)
      · exact same he
  | terminated id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.terminated_inv hs
    rcases State.cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, -, he₁, -, rfl⟩ <;> split at he
    · exact same he
    · exact same he
    · exact Or.inl (complete_setTask wk (execution?_eq_some he₁).1 he₀ he hid)
    · exact same he
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same he
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    refine Or.inl (complete_fail ?_ he hid)
    intro e' he' hid'
    exact congrArg Execution.complete (wk.execution_eq_of_id he' he₀ hid')
  | taskInput eid name value =>
    obtain ⟨-, -, e₁, _, _, he₁, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Or.inl (setT (execution?_eq_some he₁).1 rfl he)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e₁, _, _, _, he₁, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact Or.inl (complete_fail (fun e' he' hid' => complete_setTask wk (execution?_eq_some he₁).1 he₀ he' hid') he hid)
  | beginTask eid name =>
    obtain ⟨-, -, e₁, _, _, _, he₁, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact Or.inl (setT (execution?_eq_some he₁).1 rfl he)
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same he
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    refine Or.inl (complete_fail ?_ he hid)
    intro e' he' hid'
    exact congrArg Execution.complete (wk.execution_eq_of_id he' he₀ hid')
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same he
  | closeExecution eid =>
    obtain ⟨-, -, e₁, c, i, he₁, -, hc, h4, h5, -, h⟩ := Step.closeExecution_inv hs
    obtain ⟨he₁m, rfl⟩ := execution?_eq_some he₁
    obtain ⟨hte, htc, htr, httr⟩ : t.executions = (s.setExecution { e₁ with complete := true }).executions ∧
        t.calls = s.calls ∧ t.runs = s.runs ∧ t.taskResults = s.taskResults := by
      rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩
    rw [hte] at he
    rcases mem_map_replace' he with rfl | ⟨he, -⟩
    · obtain rfl := wk.execution_eq_of_id he₁m he₀ hid
      exact Or.inr ⟨c, hc, h4, h5, htc, htr, httr⟩
    · exact same he
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, e₁, _, -, he₁, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same he
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact Or.inl (complete_setTask (s := s.setRun _) (wk.setRun _) (execution?_eq_some he₁).1 he₀ he hid)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · obtain ⟨e', he', rfl⟩ := State.mem_stop_executions.mp he
      refine Or.inl ?_
      simp only [stopExecution_complete]
      exact congrArg Execution.complete (wk.execution_eq_of_id he' he₀ (by simpa using hid))
    · exact same he
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact same he
    · obtain ⟨e', he', rfl⟩ := State.mem_endUnfinished_executions.mp he
      refine Or.inl ?_
      simp only [endExecution_complete]
      exact congrArg Execution.complete (wk.execution_eq_of_id he' he₀ (by simpa using hid))

/-- What completing a run checked: every placement of its workflow settled; and no invocation was
    added. --/
def RunClosed (p : Definition) (s t : State) (r₀ : Run) : Prop :=
  (∃ w, p.workflow? r₀.workflow = some w ∧ w.placements.all (fun pl => (s.settled? r₀.path pl.name).isSome) = true) ∧
  (∀ i ∈ t.invocations, InvOld s i)

open State in
/-- Only `closeRun` and `conclude` complete a run, after every placement settled (§4.5, §13.3). --/
theorem step_run_completed {p : Definition} {s t : State} {op : Op} (wk : s.WellKeyed) (hfresh : s.runs = [] ∨ s.started = true)
    (hs : step p s op = .ok t) {r₀ r : Run} (hr₀ : r₀ ∈ s.runs) (hr : r ∈ t.runs) (hp : r.path = r₀.path) :
    r.complete = r₀.complete ∨ RunClosed p s t r₀ := by
  have same : r ∈ s.runs → r.complete = r₀.complete ∨ RunClosed p s t r₀ := fun h =>
    Or.inl (congrArg Run.complete (wk.run_eq_of_path h hr₀ hp))
  have keep : t.runs = s.runs → r.complete = r₀.complete ∨ RunClosed p s t r₀ := fun h => same (h ▸ hr)
  have fresh : ∀ {x : Run}, s.run? x.path = none → r ∈ s.runs ++ [x] → r.complete = r₀.complete ∨ RunClosed p s t r₀ := by
    intro x hx hr
    rw [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact same hr
    · rw [State.run?_eq_none_iff] at hx
      exact absurd (List.mem_map.mpr ⟨r₀, hr₀, hp.symm⟩) hx
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    rw [hfresh.resolve_right (by simp [hst])] at hr₀
    cases hr₀
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, hrun, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact keep rfl
    · exact keep rfl
    · exact fresh hrun hr
    · exact keep rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact keep rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact keep (by rw [(settleOwner_old hso).2.2.1, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact keep (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact keep (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact keep (by rw [(settleOwner_old hso).2.2.1, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact keep (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact keep (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact keep (failCall_runs h)
    · exact keep (by rw [(cancelOwner_old h).2.2.1, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact keep (by rw [(cancelOwner_old h).2.2.1, setCall_runs])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact keep rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact keep (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact keep rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact keep (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, hrun, rfl⟩
    · exact keep rfl
    · exact fresh hrun hr
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact keep (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact keep rfl
  | closeRun path =>
    obtain ⟨-, -, r₂, w, _, _, _, hr₂, -, -, hw, h5, -, -, -, h⟩ := Step.closeRun_inv hs
    obtain ⟨hr₂m, rfl⟩ := run?_eq_some hr₂
    obtain ⟨htr, hti⟩ : t.runs = (s.setRun { r₂ with complete := true }).runs ∧ ∀ i ∈ t.invocations, InvOld s i := by
      rcases h with ⟨-, i, hi, h⟩ | ⟨_, e, ts, -, -, -, h⟩
      · have hi' := (invocation?_eq_some hi).1
        rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          exact ⟨rfl, fun x hx => invOld_setInvocation (s := s.setRun _) hi' hx rfl rfl rfl rfl rfl⟩
      · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨rfl, fun x hx => invOld_self hx⟩
    rw [htr] at hr
    rcases mem_map_replace' hr with rfl | ⟨hr, -⟩
    · obtain rfl : r₂ = r₀ := wk.run_eq_of_path hr₂m hr₀ hp
      exact Or.inr ⟨⟨w, hw, h5⟩, hti⟩
    · exact same hr
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact keep rfl
  | conclude =>
    obtain ⟨-, ⟨-, r₂, w, hr₂, hw, h3, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · obtain ⟨hr₂m, hp₂⟩ := run?_eq_some hr₂
      simp only at hr
      rcases mem_map_replace' hr with rfl | ⟨hr, -⟩
      · obtain rfl : r₂ = r₀ := wk.run_eq_of_path hr₂m hr₀ hp
        exact Or.inr ⟨⟨w, hw, by rw [hp₂]; exact h3⟩, fun x hx => invOld_self hx⟩
      · exact same hr
    · exact keep rfl

/-! ### Invocations that ended -/

/-- An invocation that is no longer active is left unchanged by a step. --/
theorem frozen {p : Definition} {s t : State} {op : Op} (inv : Inv p s) (hs : step p s op = .ok t) {i₀ i : Invocation}
    (hi₀ : i₀ ∈ s.invocations) (hna : i₀.status ≠ .active) (hi : i ∈ t.invocations) (hid : i.id = i₀.id) : i = i₀ := by
  rcases step_invocation_change inv.wk hs hi₀ hi hid with h | ⟨-, -, -, -, -, hc⟩
  · exact h
  · obtain ⟨hcalls, hruns, hexecs⟩ := inv.dyn.nonActive (step_source_nonterminal hs) i₀ hi₀ hna
    rcases hc with ⟨c, hc, hco, hct, -, hrun, -⟩ | ⟨e, he, heid, hec, -⟩ | ⟨R, hR, hRo, hRt, hRc, -⟩ | ⟨hact, -⟩
    · rcases hrun with hrun | hact
      · have := hcalls c hc hco hct
        rcases hrun with h | h <;> simp [h] at this
      · exact absurd hact hna
    · have := hexecs e he heid
      simp [hec] at this
    · have := hruns R hR hRo hRt
      simp [hRc] at this
    · exact absurd hact hna

/-- An ended invocation stays ended: nothing it owns starts again. --/
theorem ended_kept {p : Definition} {s t : State} {op : Op} (inv : Inv p s) (hs : step p s op = .ok t) {i₀ i : Invocation}
    (hi₀ : i₀ ∈ s.invocations) (hend : s.invocationEnded i₀ = true) (hi : i ∈ t.invocations) (hid : i.id = i₀.id) :
    t.invocationEnded i = true := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  obtain ⟨hna, hcalls, hruns, hexecs⟩ := invocationEnded_iff.mp hend
  have heq := frozen inv hs hi₀ hna hi hid
  subst heq
  refine invocationEnded_iff.mpr ⟨hna, ?_, ?_, ?_⟩
  · intro c hc howner htask
    obtain ⟨c₀, hc₀, cid, cowner, ctask, -⟩ := call_of_old_owner hs hc htask hi₀ howner
    have hend₀ := hcalls c₀ hc₀ (cowner.trans howner) (ctask.trans htask)
    obtain ⟨c', hc', hc'id, -, -, -, -, hsame⟩ := K.call c₀ hc₀
    obtain rfl := hsame hend₀
    obtain rfl := wk'.call_eq_of_id hc hc' (cid.symm.trans hc'id.symm)
    exact hend₀
  · intro r hr howner htask
    obtain ⟨r₀, hr₀, -, -, -, rowner, rtask, hcomp⟩ := run_of_old_owner hs (runs_nil_or_started inv) hr htask hi₀ howner
    exact hcomp (hruns r₀ hr₀ (rowner.trans howner) (rtask.trans htask))
  · intro e he heid
    obtain ⟨e₀, he₀, eid, -, -, -, hcomp⟩ := execution_of_old_id hs he hi₀ heid
    exact hcomp (hexecs e₀ he₀ (eid.trans heid))

end Suimon.Delivery
