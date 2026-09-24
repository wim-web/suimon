import Suimon.Theorems.Round3.Conformance

/-! Helpers for [13] Round3/RunConform.lean — task E1: the root run and unstopped states, identities of
    task calls, whether a task began, and lookups that a step keeps. -/

namespace Suimon.Round3
namespace RunConformAux
open State

variable {p : Definition} {s t : State} {op : Op}

/-! ### Identities -/

theorem task_inj {a b m n : String} (h : Key.task a m = Key.task b n) : a = b ∧ m = n := Key.task_inj h

theorem invocation_ne_task {a : Path} {m b n : String} {tr : Option String} :
    Key.invocation a m tr ≠ Key.task b n :=
  Key.ne_of_kind? (by simp)

/-! ### The root run completes only by the conclusion from a running state -/

theorem run?_of_runs {path : Path} (h : t.runs = s.runs) : t.run? path = s.run? path := by
  unfold State.run?; rw [h]

theorem run?_append_of_ne {path : Path} {x : Run} (hx : x.path ≠ path) (h : t.runs = s.runs ++ [x]) :
    t.run? path = s.run? path := by
  unfold State.run?
  rw [h, List.find?_append]
  have : ([x].find? fun r => r.path == path) = none := by simp [hx]
  rw [this, Option.or_none]

theorem done_of_run? (h : t.run? [] = s.run? []) (hd : Done t) : Done s := by
  unfold Done at hd ⊢; rw [← h]; exact hd

/-- A step keeps the root incomplete, except the conclusion from a running state, which ends the
    workflow. -/
theorem step_done (hs : step p s op = .ok t) (hd : Done t) :
    Done s ∨ (s.status = .running ∧ t.status.terminal = true) := by
  have same : t.runs = s.runs → Done s ∨ (s.status = .running ∧ t.status.terminal = true) :=
    fun h => Or.inl (done_of_run? (run?_of_runs h) hd)
  have app : ∀ {x : Run}, x.path ≠ [] → t.runs = s.runs ++ [x] →
      Done s ∨ (s.status = .running ∧ t.status.terminal = true) :=
    fun hx h => Or.inl (done_of_run? (run?_append_of_ne hx h) hd)
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    simp [Done, State.run?] at hd
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact same rfl
    · exact same rfl
    · exact app (Key.child_ne_nil _) rfl
    · exact same rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact same (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact same (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(settleOwner_update hso).runs, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact same (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact same (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact same (failCall_runs h)
    · exact same (by rw [(cancelOwner_update h).runs, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact same (by rw [(cancelOwner_update h).runs, setCall_runs])
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
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact same rfl
    · exact app (Key.child_ne_nil _) rfl
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
    obtain ⟨-, -, r, _, _, _, _, hr, -, hne, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    have hrp : ({ r with complete := true } : Run).path ≠ [] := by
      show r.path ≠ []
      rw [(run?_eq_some hr).2]
      exact hne
    have key : (s.setRun { r with complete := true }).run? [] = s.run? [] := by
      rw [run?_setRun]; simp only [hrp, ite_false]
    refine Or.inl (done_of_run? ?_ hd)
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact (run?_of_runs (by simp)).trans key
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨hrun, r, w, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · refine Or.inr ⟨hrun, ?_⟩
      simp only
      split
      · rfl
      · split <;> rfl
    · exact same rfl

/-- While running or stopping, the root run is not complete. -/
theorem not_done_of_reachable (h : Reachable p s) : (s.status = .running ∨ s.status = .stopping) → ¬ Done s := by
  induction h with
  | empty => intro _; simp [Done, State.run?]
  | step op hr hs ih =>
    intro live hd
    rcases step_done hs hd with hd' | ⟨-, hterm⟩
    · exact ih (step_source_status hs) hd'
    · rcases live with h | h <;> simp [h, Status.terminal] at hterm

/-- The proof of `unstopped_of_step`: before an unstopped state, the workflow was running, or it was
    stopping and the step kept the root run. -/
theorem unstopped_back (hs : step p s op = .ok t) (ht : Unstopped t) : Unstopped s := by
  by_cases hrun : s.status = .running
  · exact Or.inl hrun
  · have hstop := (step_of_status_ne_running hs hrun).1
    rcases ht with ht | ht
    · exact absurd ht ((step_status hs).1 hstop)
    · rcases step_done hs ht with hd | ⟨h, -⟩
      · exact Or.inr hd
      · exact absurd h hrun

/-- An unstopped state that takes a step is running. -/
theorem running_of_unstopped (h : Reachable p s) (us : Unstopped s) (hs : step p s op = .ok t) :
    s.status = .running := by
  rcases us with h' | hd
  · exact h'
  · exact absurd hd (not_done_of_reachable h (step_source_status hs))

/-- An unstopped state is not stopping. -/
theorem not_stopping_of_unstopped (h : Reachable p s) (us : Unstopped s) : s.status ≠ .stopping := by
  intro hst
  rcases us with h' | hd
  · rw [h'] at hst; cases hst
  · exact not_done_of_reachable h (Or.inr hst) hd

/-! ### Lookups that a step keeps -/

theorem execution?_of_executions {id : String} (h : t.executions = s.executions) :
    t.execution? id = s.execution? id := by
  unfold State.execution?; rw [h]

/-- The workflow of an existing run does not change. -/
theorem workflow?_step (h : Reachable p s) (hs : step p s op = .ok t) {path : Path}
    (hr : (s.run? path).isSome) : t.workflow? p path = s.workflow? p path := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨r', hr', hwf, -⟩ := ((Delivery.Reachable.inv h).kept hs).run? (step_wellKeyed h.wellKeyed hs) hr
  unfold State.workflow?
  rw [hr, hr']
  simp [hwf]

theorem taskSpec_of_workflow? {u : State} {e e' : Execution} {name : String}
    (hw : t.workflow? p e'.run = u.workflow? p e.run) (hpl : e'.placement = e.placement) :
    t.taskSpec p e' name = u.taskSpec p e name := by
  unfold State.taskSpec State.concurrencyOf State.placementOf
  rw [hw, hpl]

theorem concurrencyOf_of_workflow? {u : State} {e e' : Execution}
    (hw : t.workflow? p e'.run = u.workflow? p e.run) (hpl : e'.placement = e.placement) :
    t.concurrencyOf p e' = u.concurrencyOf p e := by
  unfold State.concurrencyOf State.placementOf
  rw [hw, hpl]

/-- The task specs of an existing execution do not change. -/
theorem taskSpec_step (h : Reachable p s) (hs : step p s op = .ok t) {e₀ e : Execution}
    (he₀ : e₀ ∈ s.executions) (hrun : e.run = e₀.run) (hpl : e.placement = e₀.placement) (name : String) :
    t.taskSpec p e name = s.taskSpec p e₀ name :=
  taskSpec_of_workflow? (by rw [hrun]; exact workflow?_step h hs ((Limit.reachable_inv h).execRuns e₀ he₀)) hpl

theorem concurrencyOf_step (h : Reachable p s) (hs : step p s op = .ok t) {e₀ e : Execution}
    (he₀ : e₀ ∈ s.executions) (hrun : e.run = e₀.run) (hpl : e.placement = e₀.placement) :
    t.concurrencyOf p e = s.concurrencyOf p e₀ :=
  concurrencyOf_of_workflow? (by rw [hrun]; exact workflow?_step h hs ((Limit.reachable_inv h).execRuns e₀ he₀)) hpl

/-! ### Whether a task began -/

/-- Neither a call nor a run of the task `name` of execution `eid` exists: `NotBegun` by identity. -/
def notBegun (s : State) (eid name : String) : Prop :=
  s.call? (Key.task eid name) = none ∧ ∀ r ∈ s.runs, ¬ (r.owner = some eid ∧ r.task = some name)

/-- Calls and runs are never removed, so a task that began stays begun. -/
theorem notBegun_back (K : Delivery.Kept s t) {eid name : String} (h : notBegun t eid name) :
    notBegun s eid name := by
  refine ⟨?_, fun r hr hk => ?_⟩
  · cases hc : s.call? (Key.task eid name) with
    | none => rfl
    | some c =>
      have := K.grows.call?_isSome (id := Key.task eid name) (by rw [hc]; rfl)
      rw [h.1] at this
      cases this
  · obtain ⟨r', hr', -, -, -, ho, htk, -⟩ := K.run r hr
    exact h.2 r' hr' ⟨ho.trans hk.1, htk.trans hk.2⟩

theorem not_notBegun_step (h : Reachable p s) (hs : step p s op = .ok t) {eid name : String}
    (hb : ¬ notBegun s eid name) : ¬ notBegun t eid name :=
  fun h' => hb (notBegun_back ((Delivery.Reachable.inv h).kept hs) h')

theorem notBegun_of_eq (hc : t.calls = s.calls) (hr : t.runs = s.runs) {eid name : String}
    (h : notBegun s eid name) : notBegun t eid name := by
  refine ⟨?_, ?_⟩
  · unfold State.call?; rw [hc]; exact h.1
  · rw [hr]; exact h.2

/-- A task call begins its task. -/
theorem not_notBegun_of_call (h : Reachable p s) {c : Call} (hc : c ∈ s.calls) {name : String}
    (htask : c.task = some name) : ¬ notBegun s c.owner name := fun hnb => by
  have hk := (Limit.reachable_inv h).keys c hc name htask
  have := h.wellKeyed.call?_of_mem hc
  rw [hk, hnb.1] at this
  cases this

/-- A task run begins its task. -/
theorem not_notBegun_of_run {r : Run} (hr : r ∈ s.runs) {o name : String} (ho : r.owner = some o)
    (htask : r.task = some name) : ¬ notBegun s o name := fun hnb => hnb.2 r hr ⟨ho, htask⟩

/-- A task that has not begun has neither a call nor a run. -/
theorem notBegun_of_waiting (h : Reachable p s) {e : Execution} (he : e ∈ s.executions) {tk : TaskState}
    (htk : tk ∈ e.tasks) (hnb : ¬ Limit.Begun tk.status) : notBegun s e.id tk.name := by
  have linv := Limit.reachable_inv h
  have keys := Calls.reachable_keys h
  refine ⟨?_, fun r hr hk => linv.no_run he htk hnb r hr hk.2 hk.1⟩
  cases hc : s.call? (Key.task e.id tk.name) with
  | none => rfl
  | some c =>
    obtain ⟨hcm, hcid⟩ := call?_eq_some hc
    exfalso
    cases htask : c.task with
    | none =>
      exact Calls.not_taskKey_of_invocationKey (keys.invocations _ (keys.calls c hcm htask)) ⟨_, _, hcid⟩
    | some n =>
      obtain ⟨ho, hn⟩ := task_inj ((linv.keys c hcm n htask).symm.trans hcid)
      exact linv.no_call he htk hnb c hcm (by rw [htask, hn]) ho

theorem begun_of_not_notBegun (h : Reachable p s) {e : Execution} (he : e ∈ s.executions) {tk : TaskState}
    (htk : tk ∈ e.tasks) (hb : ¬ notBegun s e.id tk.name) : tk.status ≠ .pending ∧ tk.status ≠ .ready :=
  Classical.byContradiction fun hnb => hb (notBegun_of_waiting h he htk hnb)

/-- A task keeps not having begun unless the step began it, which changes its status. -/
theorem notBegun_keep (h : Reachable p s) (hs : step p s op = .ok t) {e₀ e : Execution}
    (he₀ : e₀ ∈ s.executions) (he : e ∈ t.executions) (hid : e.id = e₀.id) {tk₀ tk : TaskState}
    (htk₀ : tk₀ ∈ e₀.tasks) (htk : tk ∈ e.tasks) (hname : tk.name = tk₀.name) (hst : tk.status = tk₀.status)
    (hnb : notBegun s e₀.id tk₀.name) : notBegun t e.id tk.name := by
  have wk := h.wellKeyed
  have wk' := step_wellKeyed wk hs
  have linv := Limit.reachable_inv h
  -- A task that begins in this step was ready and is active afterwards.
  have began : ∀ {e₁ : Execution} {ts : TaskState} {name : String}, s.execution? e₁.id = some e₁ →
      e₁.tasks.find? (·.name == name) = some ts → ts.status = .ready →
      withTask e₁ { ts with status := .active } ∈ t.executions → e₁.id = e.id → name = tk.name → False := by
    intro e₁ ts name he₁ hts hready hmem hid₁ hn
    have he₁m := (execution?_eq_some he₁).1
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    obtain rfl : e₁ = e₀ := wk.execution_eq_of_id he₁m he₀ (hid₁.trans hid)
    have hts₀ : ts = tk₀ := linv.coherent e₁ he₁m ts htsm tk₀ htk₀ (by rw [htsn, hn, hname])
    obtain rfl : e = withTask e₁ { ts with status := .active } := wk'.execution_eq_of_id he hmem hid₁.symm
    rcases Delivery.mem_withTask htk with rfl | ⟨-, hne⟩
    · rw [← hts₀, hready] at hst
      cases hst
    · exact hne (by rw [htsn, hn])
  refine ⟨?_, fun r hr hk => ?_⟩
  · cases hc : t.call? (Key.task e.id tk.name) with
    | none => rfl
    | some c =>
      exfalso
      obtain ⟨hcm, hcid⟩ := call?_eq_some hc
      rcases Delivery.step_calls_back hs c hcm with ⟨c₀, hc₀, hid₀, -⟩ | ⟨-, -, hnew⟩
      · have := wk.call?_of_mem hc₀
        rw [hid₀, hcid, hid, hname, hnb.1] at this
        cases this
      · rcases hnew with ⟨-, hco, i, -, hio, hni, -⟩ |
          ⟨name, e₁, ts, spec, f, -, hkey, he₁, -, hts, hready, -, -, hmem, -⟩
        · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hikey, -⟩ := hni
          rw [hco, ← hio, hikey] at hcid
          exact invocation_ne_task hcid
        · obtain ⟨ho, hn⟩ := task_inj (hkey.symm.trans hcid)
          have he₁' := he₁
          rw [← (execution?_eq_some he₁).2] at he₁'
          exact began he₁' hts hready hmem ((execution?_eq_some he₁).2.trans ho) hn
  · rcases Delivery.step_runs_back (Delivery.runs_nil_or_started (Delivery.Reachable.inv h)) hs r hr with
      ⟨r₀, hr₀, -, -, -, ho, htask, -⟩ | ⟨-, -, hnew⟩
    · exact hnb.2 r₀ hr₀ ⟨by rw [ho, hk.1, hid], by rw [htask, hk.2, hname]⟩
    · rcases hnew with ⟨-, ho, -, -⟩ | ⟨htask, -⟩ |
        ⟨name, e₁, ts, spec, wf, out, htask, ho, he₁, -, hts, hready, -, -, -, hmem, -⟩
      · rw [ho] at hk; cases hk.1
      · rw [htask] at hk; cases hk.2
      · rw [ho] at hk
        rw [htask] at hk
        exact began he₁ hts hready hmem (Option.some.inj hk.1) (Option.some.inj hk.2)

end RunConformAux
end Suimon.Round3
