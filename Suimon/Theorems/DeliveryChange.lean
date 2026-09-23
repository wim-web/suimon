import Suimon.Theorems.DeliveryBack

/-! How a step changes stored records: an invocation changes only through its own call, execution or
    sub-run, which stops in the same step; a task changes only through its own call or run, or by a
    transform of its input, or by the stop. -/

namespace Suimon.Delivery
open State

theorem status_of_setCall {s : State} {c c' : Call} {st : CallStatus} (hx : c' ∈ (s.setCall { c with status := st }).calls)
    (hid : c'.id = c.id) : c'.status = st := by
  rcases mem_map_replace' hx with rfl | ⟨-, hne⟩
  · rfl
  · simp [hid] at hne

theorem status_of_fail_setCall {s u : State} {c c' : Call} {st : CallStatus} {f : Failure} {policy : Policy}
    (hu : u.calls = (s.setCall { c with status := st }).calls) (hst : st ≠ .running ∧ st ≠ .fetching)
    (hx : c' ∈ (u.fail f policy).calls) (hid : c'.id = c.id) : c'.status = st := by
  cases policy
  · obtain ⟨c'', hc'', rfl⟩ := State.mem_stop_calls.mp (by simpa using hx)
    rw [hu] at hc''
    have h := status_of_setCall hc'' (by simpa using hid)
    rw [stopCall_status, h]
    simp [hst]
  · rw [fail_continue] at hx
    exact status_of_setCall (hu ▸ hx) hid

/-- The invocations after a step that updates one invocation `i₁` into `i'`. --/
theorem eq_or_update {s : State} {i₁ i' i₀ i : Invocation} (wk : s.WellKeyed) (hi₁ : i₁ ∈ s.invocations)
    (hi₀ : i₀ ∈ s.invocations) (hid' : i'.id = i₁.id) (hi : i ∈ (s.setInvocation i').invocations) (hid : i.id = i₀.id) :
    i = i₀ ∨ (i = i' ∧ i₁ = i₀) := by
  rcases mem_map_replace' hi with rfl | ⟨hi, -⟩
  · exact Or.inr ⟨rfl, wk.invocation_eq_of_id hi₁ hi₀ (hid'.symm.trans hid)⟩
  · exact Or.inl (wk.invocation_eq_of_id hi hi₀ hid)

/-- How a step can change a stored invocation. --/
def InvChange (p : Program) (s t : State) (i₀ i : Invocation) : Prop :=
  i.id = i₀.id ∧ i.run = i₀.run ∧ i.placement = i₀.placement ∧ i.trigger = i₀.trigger ∧ i.input = i₀.input ∧
  ((∃ c ∈ s.calls, c.owner = i₀.id ∧ c.task = none ∧
      (∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching) ∧
      ((c.status = .running ∨ c.status = .fetching) ∨ i₀.status = .active) ∧
      (i.arm = i₀.arm ∨ ∃ j arms w pl, s.workflow? p i₀.run = some w ∧ w.placement? i₀.placement = some pl ∧
        pl.control = .branch j arms)) ∨
   (∃ e ∈ s.executions, e.id = i₀.id ∧ e.complete = false ∧ i.arm = i₀.arm ∧
      ∀ e' ∈ t.executions, e'.id = e.id → e'.complete = true) ∨
   (∃ R ∈ s.runs, R.owner = some i₀.id ∧ R.task = none ∧ R.complete = false ∧ i.arm = i₀.arm ∧
      ∀ R' ∈ t.runs, R'.path = R.path → R'.complete = true))

open State in
/-- A step leaves a stored invocation unchanged, or changes it through its own call, execution or
    sub-run (§10.2). --/
theorem step_invocation_change {p : Program} {s t : State} {op : Op} (wk : s.WellKeyed) (hs : step p s op = .ok t)
    {i₀ i : Invocation} (hi₀ : i₀ ∈ s.invocations) (hi : i ∈ t.invocations) (hid : i.id = i₀.id) :
    i = i₀ ∨ InvChange p s t i₀ i := by
  have same : i ∈ s.invocations → i = i₀ ∨ InvChange p s t i₀ i := fun h =>
    Or.inl (wk.invocation_eq_of_id h hi₀ hid)
  -- A call of the invocation reported, failed or terminated through `settleOwner` or `cancelOwner`.
  have byCall : ∀ {c : Call} {i₁ : Invocation} {u : State}, c ∈ s.calls → c.task = none → s.invocation? c.owner = some i₁ →
      (∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching) →
      ((c.status = .running ∨ c.status = .fetching) ∨ i₁.status = .active) →
      u.invocations = s.invocations → ∀ {st : InvocationStatus} {arm : Option String},
      (arm = i₁.arm ∨ ∃ j arms w pl, s.workflow? p i₁.run = some w ∧ w.placement? i₁.placement = some pl ∧
        pl.control = .branch j arms) →
      i ∈ (u.setInvocation { i₁ with status := st, arm := arm }).invocations → i = i₀ ∨ InvChange p s t i₀ i := by
    intro c i₁ u hc htask hi₁ hcalls hrun hu st arm harm hi
    obtain ⟨hi₁m, hi₁id⟩ := invocation?_eq_some hi₁
    have hi' : i ∈ (s.setInvocation { i₁ with status := st, arm := arm }).invocations := by
      rw [State.setInvocation_invocations] at hi ⊢; rw [hu] at hi; exact hi
    rcases eq_or_update (i' := { i₁ with status := st, arm := arm }) wk hi₁m hi₀ rfl hi' hid with h | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨c, hc, hi₁id.symm, htask, hcalls, hrun, harm⟩⟩
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same hi
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, input, id, -, -, -, -, -, -, -, hid', h⟩ := Step.invoke_inv hs
    obtain ⟨-, ht⟩ := invocable_of_invoke h
    rw [ht, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact same hi
    · -- The new invocation has a fresh identity.
      rw [State.invocation?_eq_none_iff] at hid'
      exact absurd (List.mem_map.mpr ⟨i₀, hi₀, hid.symm⟩) hid'
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same hi
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, h4, -, hacc, hso⟩ := Step.returned_inv hs
    have hc' := (call?_eq_some hc).1
    have hinv : s'.invocations = s.invocations := (accept_frame hacc).2.2.2.2.1
    have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [(settleOwner_old hso).2.1] at hc''
      rw [status_of_setCall hc'' hid']
      simp
    rcases State.settleOwner_eq_ok.mp hso with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
    · have hi₁' : s.invocation? c.owner = some i₁ := by
        unfold State.invocation? at hi₁ ⊢; rw [State.setCall_invocations, hinv] at hi₁; exact hi₁
      exact byCall hc' htask hi₁' hcalls (Or.inl (Or.inl h4)) (by simp [hinv]) (Or.inl rfl) hi
    · exact same (by simpa [hinv] using hi)
  | judged id arm =>
    obtain ⟨-, -, c, j, i₁, pl, judge, arms, s', hc, h3, -, h5, hi₁, hpl, hb, -, hacc, rfl⟩ := Step.judged_inv hs
    have hinv : s'.invocations = s.invocations := (accept_frame hacc).2.2.2.2.1
    obtain ⟨w, hw, hpl'⟩ := State.placementOf_eq_ok.mp hpl
    have hcalls : ∀ c' ∈ (s'.setCall { c with status := .returned }).calls, c'.id = c.id →
        c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [status_of_setCall hc'' hid']
      simp
    exact byCall (call?_eq_some hc).1 h5 hi₁ hcalls (Or.inl (Or.inl h3)) (by simp [hinv])
      (Or.inr ⟨judge, arms, w, pl, hw, hpl', hb⟩) hi
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by simpa [(accept_frame hacc).2.2.2.2.1] using hi)
  | ended id =>
    obtain ⟨-, -, c, hc, -, h4, hso⟩ := Step.ended_inv hs
    have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [(settleOwner_old hso).2.1] at hc''
      rw [status_of_setCall hc'' hid']
      simp
    rcases State.settleOwner_eq_ok.mp hso with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
    · exact byCall (call?_eq_some hc).1 htask hi₁ hcalls (Or.inl (Or.inr h4)) rfl (Or.inl rfl) hi
    · exact same hi
  | failed id =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.failed_inv hs
    obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
    have hcalls : ∀ c' ∈ (s''.fail f c.policy).calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [status_of_fail_setCall (settleOwner_old hso).2.1 (by simp) hc'' hid']
      simp
    rw [fail_invocations] at hi
    rcases State.settleOwner_eq_ok.mp hso with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
    · exact byCall (call?_eq_some hc).1 htask hi₁ hcalls (Or.inl h3) rfl (Or.inl rfl) hi
    · exact same hi
  | timedOut id element =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.timedOut_inv hs
    obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
    have hcalls : ∀ c' ∈ (s''.fail f c.policy).calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [status_of_fail_setCall (settleOwner_old hso).2.1 (by simp) hc'' hid']
      simp
    have hrun : c.status = .running ∨ c.status = .fetching := by
      rcases h3 with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact Or.inr h
      · exact h
    rw [fail_invocations] at hi
    rcases State.settleOwner_eq_ok.mp hso with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
    · exact byCall (call?_eq_some hc).1 htask hi₁ hcalls (Or.inl hrun) rfl (Or.inl rfl) hi
    · exact same hi
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨h3, h⟩ | ⟨h3, h⟩⟩ := Step.lost_inv hs
    · obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
      have hcalls : ∀ c' ∈ (s''.fail f c.policy).calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
        intro c' hc'' hid'
        rw [status_of_fail_setCall (settleOwner_old hso).2.1 (by simp) hc'' hid']
        simp
      rw [fail_invocations] at hi
      rcases State.settleOwner_eq_ok.mp hso with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
      · exact byCall (call?_eq_some hc).1 htask hi₁ hcalls (Or.inl h3) rfl (Or.inl rfl) hi
      · exact same hi
    · have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
        intro c' hc'' hid'
        rw [(cancelOwner_old h).2.1] at hc''
        rw [status_of_setCall hc'' hid']
        simp
      rcases State.cancelOwner_eq_ok.mp h with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> split at hi
      · rename_i hact
        exact byCall (call?_eq_some hc).1 htask hi₁ hcalls (Or.inr hact) rfl (Or.inl rfl) hi
      all_goals exact same hi
  | terminated id =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.terminated_inv hs
    have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [(cancelOwner_old h).2.1] at hc''
      rw [status_of_setCall hc'' hid']
      simp
    rcases State.cancelOwner_eq_ok.mp h with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> split at hi
    · rename_i hact
      exact byCall (call?_eq_some hc).1 htask hi₁ hcalls (Or.inr hact) rfl (Or.inl rfl) hi
    all_goals exact same hi
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same hi
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simpa using hi)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same hi
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simpa using hi)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same hi
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same hi
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact same (by simpa using hi)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same hi
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i₁, he, h3, -, -, -, hi₁, h⟩ := Step.closeExecution_inv hs
    obtain ⟨he', rfl⟩ := execution?_eq_some he
    obtain ⟨hi₁m, hi₁id⟩ := invocation?_eq_some hi₁
    obtain ⟨st, hte, hti⟩ : ∃ st, t.executions = (s.setExecution { e with complete := true }).executions ∧
        t.invocations = ((s.setExecution { e with complete := true }).setInvocation { i₁ with status := st }).invocations := by
      rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact ⟨_, rfl, rfl⟩
    have hexec : ∀ e' ∈ t.executions, e'.id = e.id → e'.complete = true := by
      intro e' he'' hid'
      rw [hte] at he''
      rcases mem_map_replace' he'' with rfl | ⟨-, hne⟩
      · rfl
      · simp [hid'] at hne
    rw [hti] at hi
    rcases eq_or_update (i' := { i₁ with status := st }) wk hi₁m hi₀ rfl hi hid with h | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨e, he', hi₁id.symm, h3, rfl, hexec⟩)⟩
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, h3, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    have hr' := (run?_eq_some hr).1
    have hruns : ∀ {u : State}, u.runs = (s.setRun { r with complete := true }).runs →
        ∀ R' ∈ u.runs, R'.path = r.path → R'.complete = true := by
      intro u hu R' hR' hp
      rw [hu] at hR'
      rcases mem_map_replace' hR' with rfl | ⟨-, hne⟩
      · rfl
      · simp [hp] at hne
    rcases h with ⟨htask, i₁, hi₁, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · obtain ⟨hi₁m, hi₁id⟩ := invocation?_eq_some hi₁
      obtain ⟨st, htr, hti⟩ : ∃ st, t.runs = (s.setRun { r with complete := true }).runs ∧
          t.invocations = ((s.setRun { r with complete := true }).setInvocation { i₁ with status := st }).invocations := by
        rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl, rfl⟩
      rw [hti] at hi
      rcases eq_or_update (i' := { i₁ with status := st }) wk hi₁m hi₀ rfl hi hid with h | ⟨rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨r, hr', by rw [howner, hi₁id], htask, h3, rfl,
          hruns htr⟩)⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same hi
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same hi
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same hi

/-! ### Tasks -/

/-- How a step can change a task of a stored execution: through the task's call, which stops, or its
    run, which completes; by a transform of the task's input or its start, from pending or ready; or by
    the stop, from pending or ready. --/
def TaskChange (s t : State) (e₀ : Execution) (tk₀ : TaskState) : Prop :=
  (∃ c ∈ s.calls, c.owner = e₀.id ∧ c.task = some tk₀.name ∧
    ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching) ∨
  (∃ R ∈ s.runs, R.owner = some e₀.id ∧ R.task = some tk₀.name ∧ R.complete = false) ∨
  (∃ ts, e₀.tasks.find? (·.name == tk₀.name) = some ts ∧ (ts.status = .pending ∨ ts.status = .ready)) ∨
  (tk₀.status = .pending ∨ tk₀.status = .ready)

/-- The tasks of an execution after `setTask`. --/
theorem mem_withTask {e : Execution} {ts tk : TaskState} (h : tk ∈ (withTask e ts).tasks) :
    tk = ts ∨ (tk ∈ e.tasks ∧ tk.name ≠ ts.name) := by
  rcases mem_map_replace' h with rfl | ⟨h, hne⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨h, by simpa using hne⟩

/-- Tasks of an execution with their counterparts before a step. --/
def TasksFrom (s t : State) (e₀ e : Execution) : Prop :=
  ∀ tk ∈ e.tasks, ∃ tk₀ ∈ e₀.tasks, tk₀.name = tk.name ∧ (tk.status = tk₀.status ∨ TaskChange s t e₀ tk₀)

theorem TasksFrom.refl {s t : State} (e : Execution) : TasksFrom s t e e :=
  fun tk h => ⟨tk, h, rfl, Or.inl rfl⟩

theorem TasksFrom.withTask {s t : State} {e : Execution} {ts ts' : TaskState} (hts : e.tasks.find? (·.name == ts'.name) = some ts)
    (hname : ts'.name = ts.name) (hchange : TaskChange s t e ts) : TasksFrom s t e (withTask e ts') := by
  intro tk h
  rcases mem_withTask h with rfl | ⟨h, -⟩
  · exact ⟨ts, List.mem_of_find?_eq_some hts, hname.symm, Or.inr hchange⟩
  · exact ⟨tk, h, rfl, Or.inl rfl⟩

theorem TasksFrom.stop {s t : State} {e₀ e : Execution} (h : TasksFrom s t e₀ e) : TasksFrom s t e₀ (stopExecution e) := by
  intro tk htk
  simp only [stopExecution, List.mem_map] at htk
  obtain ⟨tk', htk', rfl⟩ := htk
  obtain ⟨tk₀, htk₀, hname, hst⟩ := h tk' htk'
  by_cases hp : tk'.status = .pending ∨ tk'.status = .ready
  · -- The stop leaves a waiting task unstarted.
    have hp' : (tk'.status == .pending || tk'.status == .ready) = true := by simpa using hp
    simp only [hp', ↓reduceIte]
    refine ⟨tk₀, htk₀, hname, Or.inr ?_⟩
    rcases hst with hst | hst
    · exact Or.inr (Or.inr (Or.inr (hst ▸ hp)))
    · exact hst
  · have hp' : (tk'.status == .pending || tk'.status == .ready) = false := by simpa using hp
    simp only [hp', Bool.false_eq_true, ↓reduceIte]
    exact ⟨tk₀, htk₀, hname, hst⟩

theorem TasksFrom.mono {s t t' : State} {e₀ e : Execution} (h : TasksFrom s t e₀ e)
    (hcalls : ∀ c ∈ t'.calls, ∃ c'' ∈ t.calls, c''.id = c.id ∧
      ((c.status = .running ∨ c.status = .fetching) → (c''.status = .running ∨ c''.status = .fetching))) :
    TasksFrom s t' e₀ e := by
  intro tk htk
  obtain ⟨tk₀, htk₀, hname, hst⟩ := h tk htk
  refine ⟨tk₀, htk₀, hname, ?_⟩
  rcases hst with hst | hst
  · exact Or.inl hst
  · refine Or.inr ?_
    rcases hst with ⟨c, hc, h1, h2, h3⟩ | hst
    · refine Or.inl ⟨c, hc, h1, h2, fun c' hc' hid => ?_⟩
      obtain ⟨c'', hc'', hid', himp⟩ := hcalls c' hc'
      have := h3 c'' hc'' (hid'.trans hid)
      exact ⟨fun h => by rcases himp (Or.inl h) with h' | h' <;> simp_all,
        fun h => by rcases himp (Or.inr h) with h' | h' <;> simp_all⟩
    · exact Or.inr hst

theorem tasksFrom_of_mem {s t : State} (wk : s.WellKeyed) {e₀ e : Execution} (he₀ : e₀ ∈ s.executions)
    (he : e ∈ s.executions) (hid : e.id = e₀.id) : TasksFrom s t e₀ e := by
  obtain rfl := wk.execution_eq_of_id he he₀ hid
  exact TasksFrom.refl e

theorem tasksFrom_setTask {s t : State} (wk : s.WellKeyed) {e₀ e e₁ : Execution} {ts ts' : TaskState}
    (he₀ : e₀ ∈ s.executions) (he₁ : e₁ ∈ s.executions) (hts : e₁.tasks.find? (·.name == ts'.name) = some ts)
    (hname : ts'.name = ts.name) (hchange : TaskChange s t e₁ ts) (he : e ∈ (s.setTask e₁ ts').executions)
    (hid : e.id = e₀.id) : TasksFrom s t e₀ e := by
  rcases mem_map_replace' he with rfl | ⟨he, -⟩
  · obtain rfl : e₁ = e₀ := wk.execution_eq_of_id he₁ he₀ hid
    exact TasksFrom.withTask hts hname hchange
  · exact tasksFrom_of_mem wk he₀ he hid

theorem tasksFrom_fail {s u : State} {f : Failure} {policy : Policy} {e₀ e : Execution}
    (h : ∀ e' ∈ u.executions, e'.id = e₀.id → TasksFrom s u e₀ e')
    (he : e ∈ (u.fail f policy).executions) (hid : e.id = e₀.id) : TasksFrom s (u.fail f policy) e₀ e := by
  have hcalls : ∀ c ∈ (u.fail f policy).calls, ∃ c'' ∈ u.calls, c''.id = c.id ∧
      ((c.status = .running ∨ c.status = .fetching) → (c''.status = .running ∨ c''.status = .fetching)) := by
    intro c hc
    obtain ⟨c'', hc'', hid, -, -, -, -, himp⟩ := callOld_fail hc
    exact ⟨c'', hc'', hid, himp⟩
  cases policy
  · obtain ⟨e', he', rfl⟩ := State.mem_stop_executions.mp (by simpa using he)
    exact ((h e' he' (by simpa using hid)).stop).mono hcalls
  · exact (h e (by simpa using he) hid).mono hcalls

theorem find?_name_of_task {e : Execution} {name : String} {ts : TaskState} (h : e.tasks.find? (·.name == name) = some ts) :
    ts.name = name := by
  simpa using List.find?_some h

open State in
/-- The tasks of a stored execution after a step, with their counterparts before it. --/
theorem step_task_change {p : Program} {s t : State} {op : Op} (wk : s.WellKeyed) (hs : step p s op = .ok t)
    {e₀ e : Execution} (he₀ : e₀ ∈ s.executions) (he : e ∈ t.executions) (hid : e.id = e₀.id) :
    TasksFrom s t e₀ e := by
  have same : e ∈ s.executions → TasksFrom s t e₀ e := fun h => tasksFrom_of_mem wk he₀ h hid
  -- A task whose call reported, failed or terminated.
  have byCall : ∀ {t' : State} {e' : Execution} {c : Call} {u : State} {name : String} {e₁ : Execution}
      {ts : TaskState} {st : TaskStatus},
      c ∈ s.calls → c.task = some name → s.execution? c.owner = some e₁ → e₁.tasks.find? (·.name == name) = some ts →
      (∀ c' ∈ t'.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching) →
      u.executions = s.executions → e' ∈ (u.setTask e₁ { ts with status := st }).executions → e'.id = e₀.id →
      TasksFrom s t' e₀ e' := by
    intro t' e' c u name e₁ ts st hc htask he₁ hts hcalls hu he hid
    obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
    have hname := find?_name_of_task hts
    refine tasksFrom_setTask (ts := ts) (ts' := { ts with status := st }) wk he₀ he₁m (by simpa [hname] using hts) rfl
      (Or.inl ⟨c, hc, he₁id.symm, by rw [htask, hname], hcalls⟩) ?_ hid
    rw [State.setTask_eq, State.setExecution_executions] at he ⊢
    rw [hu] at he
    exact he
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same he
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, input, id, -, -, -, -, -, -, -, hid', h⟩ := Step.invoke_inv hs
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
    have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [(settleOwner_old hso).2.1] at hc''
      rw [status_of_setCall hc'' hid']
      simp
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
    · exact same (by simpa [hexe] using he)
    · have he₁' : s.execution? c.owner = some e₁ := by
        unfold State.execution? at he₁ ⊢; rw [State.setCall_executions, hexe] at he₁; exact he₁
      exact byCall (call?_eq_some hc).1 htask he₁' hts hcalls (by simp [hexe]) he hid
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, s', -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact same (by simpa [(accept_frame hacc).2.2.2.2.2.2.1] using he)
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by simpa [(accept_frame hacc).2.2.2.2.2.2.1] using he)
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [(settleOwner_old hso).2.1] at hc''
      rw [status_of_setCall hc'' hid']
      simp
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
    · exact same he
    · exact byCall (call?_eq_some hc).1 htask he₁ hts hcalls rfl he hid
  | failed id =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.failed_inv hs
    obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
    refine tasksFrom_fail (fun e' he' hid' => ?_) he hid
    have hcalls : ∀ c' ∈ s''.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid''
      rw [(settleOwner_old hso).2.1] at hc''
      rw [status_of_setCall hc'' hid'']
      simp
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
    · exact tasksFrom_of_mem wk he₀ he' hid'
    · exact byCall (call?_eq_some hc).1 htask he₁ hts hcalls rfl he' hid'
  | timedOut id element =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.timedOut_inv hs
    obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
    refine tasksFrom_fail (fun e' he' hid' => ?_) he hid
    have hcalls : ∀ c' ∈ s''.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid''
      rw [(settleOwner_old hso).2.1] at hc''
      rw [status_of_setCall hc'' hid'']
      simp
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
    · exact tasksFrom_of_mem wk he₀ he' hid'
    · exact byCall (call?_eq_some hc).1 htask he₁ hts hcalls rfl he' hid'
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨h3, h⟩ | ⟨h3, h⟩⟩ := Step.lost_inv hs
    · obtain ⟨f, s'', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
      refine tasksFrom_fail (fun e' he' hid' => ?_) he hid
      have hcalls : ∀ c' ∈ s''.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
        intro c' hc'' hid''
        rw [(settleOwner_old hso).2.1] at hc''
        rw [status_of_setCall hc'' hid'']
        simp
      rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
      · exact tasksFrom_of_mem wk he₀ he' hid'
      · exact byCall (call?_eq_some hc).1 htask he₁ hts hcalls rfl he' hid'
    · have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
        intro c' hc'' hid'
        rw [(cancelOwner_old h).2.1] at hc''
        rw [status_of_setCall hc'' hid']
        simp
      rcases State.cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩ <;> split at he
      · exact same he
      · exact same he
      · exact byCall (call?_eq_some hc).1 htask he₁ hts hcalls rfl he hid
      · exact same he
  | terminated id =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.terminated_inv hs
    have hcalls : ∀ c' ∈ t.calls, c'.id = c.id → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
      intro c' hc'' hid'
      rw [(cancelOwner_old h).2.1] at hc''
      rw [status_of_setCall hc'' hid']
      simp
    rcases State.cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩ <;> split at he
    · exact same he
    · exact same he
    · exact byCall (call?_eq_some hc).1 htask he₁ hts hcalls rfl he hid
    · exact same he
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same he
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact tasksFrom_fail (fun e' he' hid' => tasksFrom_of_mem wk he₀ he' hid') he hid
  | taskInput eid name value =>
    obtain ⟨-, -, e₁, ts, _, he₁, hts, h3, -, -, rfl⟩ := Step.taskInput_inv hs
    have hname := find?_name_of_task hts
    exact tasksFrom_setTask (ts := ts) (ts' := { ts with status := .ready, input := value }) wk he₀ (execution?_eq_some he₁).1 (by simpa [hname] using hts) rfl
      (Or.inr (Or.inr (Or.inl ⟨ts, by simpa [hname] using hts, Or.inl h3⟩))) he hid
  | taskInputFailed eid name =>
    obtain ⟨-, -, e₁, ts, _, _, he₁, hts, h3, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    have hname := find?_name_of_task hts
    refine tasksFrom_fail (fun e' he' hid' => ?_) he hid
    exact tasksFrom_setTask (ts := ts) (ts' := { ts with status := .failed }) wk he₀ (execution?_eq_some he₁).1 (by simpa [hname] using hts) rfl
      (Or.inr (Or.inr (Or.inl ⟨ts, by simpa [hname] using hts, Or.inl h3⟩))) he' hid'
  | beginTask eid name =>
    obtain ⟨-, -, e₁, _, ts, _, he₁, -, -, hts, h4, -, -, h⟩ := Step.beginTask_inv hs
    have hname := find?_name_of_task hts
    have k : ∀ {u : State}, u.executions = (s.setTask e₁ { ts with status := .active }).executions →
        e ∈ u.executions → TasksFrom s t e₀ e := fun hu he =>
      tasksFrom_setTask (ts := ts) (ts' := { ts with status := .active }) wk he₀ (execution?_eq_some he₁).1 (by simpa [hname] using hts) rfl
        (Or.inr (Or.inr (Or.inl ⟨ts, by simpa [hname] using hts, Or.inr h4⟩))) (hu ▸ he) hid
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact k rfl he
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same he
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact tasksFrom_fail (fun e' he' hid' => tasksFrom_of_mem wk he₀ he' hid') he hid
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same he
  | closeExecution eid =>
    obtain ⟨-, -, e₁, _, _, he₁, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    have k : ∀ {u : State}, u.executions = (s.setExecution { e₁ with complete := true }).executions →
        e ∈ u.executions → TasksFrom s t e₀ e := by
      intro u hu he
      rw [hu] at he
      rcases mem_map_replace' he with rfl | ⟨he, -⟩
      · obtain rfl : e₁ = e₀ := wk.execution_eq_of_id (execution?_eq_some he₁).1 he₀ hid
        exact TasksFrom.refl _
      · exact same he
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact k rfl he
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, h3, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨name, e₁, ts, htask, he₁, hts, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same he
    · obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
      have hname := find?_name_of_task hts
      have k : ∀ {u : State} {st : TaskStatus},
          u.executions = ((s.setRun { r with complete := true }).setTask e₁ { ts with status := st }).executions →
          e ∈ u.executions → TasksFrom s t e₀ e := by
        intro u st hu he
        refine tasksFrom_setTask (ts := ts) (ts' := { ts with status := st }) wk he₀ he₁m (by simpa [hname] using hts) rfl
          (Or.inr (Or.inl ⟨r, (run?_eq_some hr).1, by rw [howner, he₁id], by rw [htask, hname], h3⟩)) ?_ hid
        rw [hu] at he
        exact he
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact k rfl he
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · obtain ⟨e', he', rfl⟩ := State.mem_stop_executions.mp he
      have hcalls : ∀ c ∈ ({ s.stop with cancelled := true } : State).calls, ∃ c'' ∈ s.calls, c''.id = c.id ∧
          ((c.status = .running ∨ c.status = .fetching) → (c''.status = .running ∨ c''.status = .fetching)) := by
        intro c hc
        obtain ⟨c'', hc'', hid, -, -, -, -, himp⟩ := callOld_stop hc
        exact ⟨c'', hc'', hid, himp⟩
      exact ((tasksFrom_of_mem (t := s) wk he₀ he' (by simpa using hid)).stop).mono hcalls
    · exact same he
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same he

end Suimon.Delivery
