import Suimon.Theorems.Round3.Conformance

/-! # Helpers for `Round3/ProgressInv.lean` (task B1)

How one accepted step changes the records that the structural invariants of progress read, one lemma
per kind of record, each by cases on the operation: invocations (`step_invocations`), ended calls
(`step_calls`), runs (`step_runs`), executions and their tasks (`step_executions`), and the root run
(`step_root`). Then the static facts of a valid definition that the invariants need. -/

namespace Suimon.Round3.ProgressInvAux
open State

variable {p : Definition} {s t u : State}

/-! ### Lookups -/

theorem mem_setInvocation_iff {i x : Invocation} (hx : x ∈ (s.setInvocation i).invocations) :
    x = i ∨ (x ∈ s.invocations ∧ x.id ≠ i.id) := by
  rcases Delivery.mem_map_replace' hx with h | ⟨h, hne⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, by simpa using hne⟩

/-- The tasks of `withTask e ts` named like `ts` are `ts`. -/
theorem withTask_named {e : Execution} {ts tk : TaskState} (htk : tk ∈ (withTask e ts).tasks)
    (hname : tk.name = ts.name) : tk = ts := by
  rcases Delivery.mem_withTask htk with h | ⟨-, hne⟩
  · exact h
  · exact absurd hname hne

/-- An execution of `s.setTask e ts` with the identity of `e` is `withTask e ts`. -/
theorem setTask_same_id {e x : Execution} {ts : TaskState} (hx : x ∈ (s.setTask e ts).executions)
    (hid : x.id = e.id) : x = withTask e ts := by
  rcases Limit.mem_setExecution_iff (e := withTask e ts) hx with h | ⟨-, hne⟩
  · exact h
  · exact absurd hid hne

theorem run?_of_runs {path : Path} (h : t.runs = s.runs) : t.run? path = s.run? path := by
  simp only [State.run?, h]

theorem workflow?_of_runs {path : Path} (h : t.runs = s.runs) : t.workflow? p path = s.workflow? p path := by
  simp only [State.workflow?, run?_of_runs h]

theorem concurrencyOf_of_runs {e : Execution} (h : t.runs = s.runs) : t.concurrencyOf p e = s.concurrencyOf p e := by
  simp only [State.concurrencyOf, State.placementOf, workflow?_of_runs h]

theorem run?_append_ne {path : Path} {x : Run} (h : t.runs = s.runs ++ [x]) (hne : x.path ≠ path) :
    t.run? path = s.run? path := by
  simp only [State.run?, h, List.find?_append]
  cases s.runs.find? (·.path == path) with
  | some r => rfl
  | none => simp [hne]

theorem workflow?_append_ne {path : Path} {x : Run} (h : t.runs = s.runs ++ [x]) (hne : x.path ≠ path) :
    t.workflow? p path = s.workflow? p path := by
  simp only [State.workflow?, run?_append_ne h hne]

theorem append_ne_self {α : Type} (l : List α) (a : α) : l ++ [a] ≠ l := by
  intro h
  have := congrArg List.length h
  simp at this

/-- A run of `s` whose workflow is found in `t` has it in `s` already: runs keep their workflow. -/
theorem workflow?_back (hk : Delivery.Kept s t) (wk : t.WellKeyed) {path : Path} (hr : (s.run? path).isSome)
    {w : Workflow} (h : t.workflow? p path = some w) : s.workflow? p path = some w := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨r', hr', hwf, -⟩ := hk.run? wk hr
  obtain ⟨r'', hr'', hw⟩ := Delivery.workflow?_iff.mp h
  rw [hr'] at hr''
  cases hr''
  exact Delivery.workflow?_iff.mpr ⟨r, hr, hwf ▸ hw⟩

theorem stopTask_status (tk : TaskState) :
    (Limit.stopTask tk).status = .notStarted ∨ Limit.stopTask tk = tk := by
  unfold Limit.stopTask
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem stopTask_ended {tk : TaskState} (h : tk.status.ended = true) : (Limit.stopTask tk).status.ended = true := by
  rcases stopTask_status tk with hst | hst
  · rw [hst]; rfl
  · rw [hst]; exact h

/-- A task status that has begun and is not active has ended. -/
theorem ended_of_begun {st : TaskStatus} (hb : Limit.Begun st) (hna : st ≠ .active) : st.ended = true := by
  obtain ⟨h1, h2⟩ := hb
  cases st <;> simp_all [TaskStatus.ended]

/-! ### Invocations -/

/-- The body an invocation's control creates with it in the same step (N2). -/
def InvBody (p : Definition) (s : State) (i : Invocation) : Prop :=
  ∀ w pl, s.workflow? p i.run = some w → w.placement? i.placement = some pl →
    (((∃ f, pl.control = .call (.function f)) ∨ (∃ j arms, pl.control = .branch j arms)) →
        ∃ c ∈ s.calls, c.id = i.id ∧ c.owner = i.id ∧ c.task = none) ∧
    (∀ wf out, pl.control = .call (.workflow wf out) →
        ∃ r ∈ s.runs, r.path = i.run ++ [i.id] ∧ r.owner = some i.id ∧ r.task = none ∧ r.workflow = wf) ∧
    (∀ cc, pl.control = .concurrency cc → ∃ e ∈ s.executions, e.id = i.id)

/-- The invocations of `t` are those of `s`, or updates of them to a status that is not active. -/
def InvKept (s t : State) : Prop :=
  ∀ i ∈ t.invocations, i ∈ s.invocations ∨ (Delivery.InvOld s i ∧ i.status ≠ .active)

namespace InvKept

theorem of_eq (h : t.invocations = s.invocations) : InvKept s t := fun _ hi => Or.inl (h ▸ hi)

theorem trans (h₁ : InvKept s u) (h₂ : InvKept u t) : InvKept s t := by
  intro i hi
  rcases h₂ i hi with hi | ⟨⟨i₀, hi₀, a1, a2, a3, a4, a5⟩, hst⟩
  · exact h₁ i hi
  · refine Or.inr ⟨?_, hst⟩
    rcases h₁ i₀ hi₀ with hi₀ | ⟨⟨i₁, hi₁, b1, b2, b3, b4, b5⟩, -⟩
    · exact ⟨i₀, hi₀, a1, a2, a3, a4, a5⟩
    · exact ⟨i₁, hi₁, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩

theorem pre (h : InvKept u t) (hu : u.invocations = s.invocations) : InvKept s t := (of_eq hu).trans h

theorem setInvocation {i₁ i' : Invocation} (hi₁ : i₁ ∈ s.invocations) (hid : i'.id = i₁.id)
    (hrun : i'.run = i₁.run) (hpl : i'.placement = i₁.placement) (htr : i'.trigger = i₁.trigger)
    (hin : i'.input = i₁.input) (hst : i'.status ≠ .active) : InvKept s (s.setInvocation i') := by
  intro i hi
  rcases mem_setInvocation_iff hi with rfl | ⟨hi, -⟩
  · exact Or.inr ⟨⟨i₁, hi₁, hid.symm, hrun.symm, hpl.symm, htr.symm, hin.symm⟩, hst⟩
  · exact Or.inl hi

theorem settleOwner {c : Call} {inv : InvocationStatus} {task : TaskStatus} (h : s.settleOwner c inv task = .ok t)
    (hinv : inv ≠ .active) : InvKept s t := by
  rcases State.settleOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · exact setInvocation (invocation?_eq_some hi).1 rfl rfl rfl rfl rfl hinv
  · exact of_eq rfl

theorem cancelOwner {c : Call} (h : s.cancelOwner c = .ok t) : InvKept s t := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> split
  · exact setInvocation (invocation?_eq_some hi).1 rfl rfl rfl rfl rfl (by simp)
  · exact of_eq rfl
  · exact of_eq rfl
  · exact of_eq rfl

theorem fail {f : Failure} {policy : Policy} : InvKept s (s.fail f policy) := of_eq (by simp)

theorem failCall {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    InvKept s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  exact ((of_eq rfl).trans (settleOwner hso (by simp))).trans fail

end InvKept

/-- An invocation after a step: stored before, updated to a status that is not active, or the new one
    `invoke` created, with its body. -/
def InvCase (p : Definition) (s t : State) (i : Invocation) : Prop :=
  (i ∈ s.invocations ∨ (Delivery.InvOld s i ∧ i.status ≠ .active)) ∨
  (s.invocation? i.id = none ∧ i.status = .active ∧ InvBody p t i)

/-- Every invocation after a step: only `invoke` adds one, and owners change only to statuses that are
    not active. -/
theorem step_invocations {op : Op} (hs : step p s op = .ok t) : ∀ i ∈ t.invocations, InvCase p s t i := by
  have kept : InvKept s t → ∀ i ∈ t.invocations, InvCase p s t i := fun h i hi => Or.inl (h i hi)
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact kept (.of_eq rfl)
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, rfl, -, hid', h⟩ := Step.invoke_inv hs
    have hwf : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
    have hpath : path ++ [Key.invocation path name trigger] ≠ path := append_ne_self _ _
    -- The new invocation is found with its placement, and its body was stored with it.
    have body : ∀ {t' : State}, t'.workflow? p path = s.workflow? p path →
        ((((∃ f, pl.control = .call (.function f)) ∨ (∃ j arms, pl.control = .branch j arms)) →
          ∃ c ∈ t'.calls, c.id = Key.invocation path name trigger ∧ c.owner = Key.invocation path name trigger ∧
            c.task = none) ∧
        (∀ wf out, pl.control = .call (.workflow wf out) →
          ∃ r ∈ t'.runs, r.path = path ++ [Key.invocation path name trigger] ∧
            r.owner = some (Key.invocation path name trigger) ∧ r.task = none ∧ r.workflow = wf) ∧
        (∀ cc, pl.control = .concurrency cc → ∃ e ∈ t'.executions, e.id = Key.invocation path name trigger)) →
        InvBody p t' { id := Key.invocation path name trigger, run := path, placement := name, trigger, input } := by
      intro t' ht' hb w' pl' hw' hpl'
      rw [ht', hwf] at hw'
      cases hw'
      rw [hpl] at hpl'
      cases hpl'
      exact hb
    intro i hi
    rcases h with ⟨f, decl, hf, -, -, rfl⟩ | ⟨judge, arms, hb, -, rfl⟩ | ⟨wf, out, hwf', -, rfl⟩ |
        ⟨c, hcc, -, rfl⟩ <;>
      simp only [List.mem_append, List.mem_singleton] at hi <;> rcases hi with hi | rfl
    · exact Or.inl (Or.inl hi)
    · refine Or.inr ⟨hid', rfl, body (workflow?_of_runs rfl) ⟨fun _ => ⟨_, List.mem_append_right _
        (List.mem_singleton_self _), rfl, rfl, rfl⟩, fun wf out h => ?_, fun cc h => ?_⟩⟩
      · rw [hf] at h; cases h
      · rw [hf] at h; cases h
    · exact Or.inl (Or.inl hi)
    · refine Or.inr ⟨hid', rfl, body (workflow?_of_runs rfl) ⟨fun _ => ⟨_, List.mem_append_right _
        (List.mem_singleton_self _), rfl, rfl, rfl⟩, fun wf out h => ?_, fun cc h => ?_⟩⟩
      · rw [hb] at h; cases h
      · rw [hb] at h; cases h
    · exact Or.inl (Or.inl hi)
    · refine Or.inr ⟨hid', rfl, body (workflow?_append_ne rfl hpath) ⟨fun h => ?_, fun wf₁ out₁ h => ?_,
        fun cc h => ?_⟩⟩
      · rw [hwf'] at h
        rcases h with ⟨f, h⟩ | ⟨j, arms, h⟩ <;> cases h
      · rw [hwf'] at h
        cases h
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl, rfl⟩
      · rw [hwf'] at h; cases h
    · exact Or.inl (Or.inl hi)
    · refine Or.inr ⟨hid', rfl, body (workflow?_of_runs rfl) ⟨fun h => ?_, fun wf out h => ?_,
        fun cc h => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩⟩⟩
      · rw [hcc] at h
        rcases h with ⟨f, h⟩ | ⟨j, arms, h⟩ <;> cases h
      · rw [hcc] at h; cases h
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact kept (.of_eq rfl)
  | returned id value =>
    obtain ⟨-, -, _, _, s', -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact kept ((InvKept.settleOwner hso (by simp)).pre
      (by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]))
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', hc, -, -, -, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hi' : i ∈ (s'.setCall { c with status := .returned }).invocations := by
      rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]; exact (invocation?_eq_some hi).1
    exact kept ((InvKept.setInvocation (i' := { i with status := .succeeded, arm := some arm }) hi'
      rfl rfl rfl rfl rfl (by simp)).pre (by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]))
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact kept (.of_eq (by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]))
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact kept ((InvKept.settleOwner hso (by simp)).pre rfl)
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact kept (InvKept.failCall h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact kept (InvKept.failCall h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact kept (InvKept.failCall h)
    · exact kept ((InvKept.cancelOwner h).pre rfl)
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact kept ((InvKept.cancelOwner h).pre rfl)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact kept (.of_eq rfl)
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact kept (.of_eq (by simp))
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact kept (.of_eq rfl)
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact kept (.of_eq (by simp))
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact kept (.of_eq rfl)
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact kept (.of_eq rfl)
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact kept (.of_eq (by simp))
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact kept (.of_eq rfl)
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i, -, -, -, -, -, hi, h⟩ := Step.closeExecution_inv hs
    have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (invocation?_eq_some hi).1
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact kept (InvKept.setInvocation hi' rfl rfl rfl rfl rfl (by simp))
    · exact kept (InvKept.setInvocation hi' rfl rfl rfl rfl rfl (by simp))
    · exact kept (InvKept.setInvocation hi' rfl rfl rfl rfl rfl (by simp))
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, i, hi, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · have hi' : i ∈ (s.setRun { r with complete := true }).invocations := (invocation?_eq_some hi).1
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact kept (InvKept.setInvocation hi' rfl rfl rfl rfl rfl (by simp))
      · exact kept (InvKept.setInvocation hi' rfl rfl rfl rfl rfl (by simp))
      · exact kept (InvKept.setInvocation hi' rfl rfl rfl rfl rfl (by simp))
      · exact kept (InvKept.setInvocation hi' rfl rfl rfl rfl rfl (by simp))
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact kept (.of_eq rfl)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact kept (.of_eq rfl)
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact kept (.of_eq rfl)

/-! ### Calls -/

/-- The owner of an ended call no longer runs it: its invocation is not active, or its task ended. -/
def OwnerClosed (t : State) (c : Call) : Prop :=
  (c.task = none → ∀ i ∈ t.invocations, i.id = c.owner → i.status ≠ .active) ∧
  (∀ name, c.task = some name → ∀ e ∈ t.executions, e.id = c.owner → ∀ tk ∈ e.tasks, tk.name = name →
    tk.status.ended = true)

theorem OwnerClosed.congr {c c' : Call} (h : OwnerClosed t c) (howner : c'.owner = c.owner)
    (htask : c'.task = c.task) : OwnerClosed t c' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun hn i hi hid => h1 (htask ▸ hn) i hi (hid.trans howner),
    fun name hn e he hid tk htk hname => h2 name (htask ▸ hn) e he (hid.trans howner) tk htk hname⟩

theorem OwnerClosed.fail {c : Call} {f : Failure} {policy : Policy} (h : OwnerClosed u c) :
    OwnerClosed (u.fail f policy) c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hn i hi hid => h1 hn i (by simpa using hi) hid, fun name hn e he hid tk htk hname => ?_⟩
  cases policy
  · obtain ⟨e', he', rfl⟩ := State.mem_stop_executions.mp (by simpa using he)
    rw [Limit.stopExecution_tasks] at htk
    obtain ⟨tk', htk', rfl⟩ := List.mem_map.mp htk
    exact stopTask_ended (h2 name hn e' he' (by simpa using hid) tk' htk' (by simpa using hname))
  · exact h2 name hn e (by simpa using he) hid tk htk hname

/-- Settling the owner of a call to statuses that are not running closes it. -/
theorem settleOwner_closed {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : u.settleOwner c inv task = .ok t) (hinv : inv ≠ .active) (htask : task.ended = true) :
    OwnerClosed t c := by
  rcases State.settleOwner_eq_ok.mp h with ⟨hn, i, hi, rfl⟩ | ⟨name, e, ts, hn, he, hts, rfl⟩
  · refine ⟨fun _ x hx hid => ?_, fun name h => (by simp [hn] at h)⟩
    rcases mem_setInvocation_iff hx with rfl | ⟨-, hne⟩
    · exact hinv
    · exact absurd (hid.trans (invocation?_eq_some hi).2.symm) hne
  · refine ⟨fun h => (by simp [hn] at h), fun name' h' x hx hid tk htk hname => ?_⟩
    rw [hn] at h'
    cases h'
    have hx := setTask_same_id hx (hid.trans (execution?_eq_some he).2.symm)
    subst hx
    rw [withTask_named htk (hname.trans (Delivery.find?_name_of_task hts).symm)]
    exact htask

/-- A terminated call closes its owner: an active owner is cancelled, and an owner that is no longer
    active has failed, or its task has ended (a task call's task has begun). -/
theorem cancelOwner_closed {c : Call} (h : u.cancelOwner c = .ok t)
    (invIds : (u.invocations.map (·.id)).Nodup) (execIds : (u.executions.map (·.id)).Nodup)
    (coherent : ∀ e ∈ u.executions, ∀ x ∈ e.tasks, ∀ y ∈ e.tasks, x.name = y.name → x = y)
    (begun : ∀ name, c.task = some name → Limit.TaskHas Limit.Begun u c.owner name) : OwnerClosed t c := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨hn, i, hi, rfl⟩ | ⟨name, e, ts, hn, he, hts, rfl⟩
  · obtain ⟨him, hid⟩ := invocation?_eq_some hi
    refine ⟨fun _ x hx hxid => ?_, fun name h => (by simp [hn] at h)⟩
    split at hx
    · rcases mem_setInvocation_iff hx with rfl | ⟨-, hne⟩
      · simp
      · exact absurd (hxid.trans hid.symm) hne
    · rename_i hna
      rw [Limit.eq_of_key invIds hx him (hxid.trans hid.symm)]
      exact hna
  · obtain ⟨hem, hid⟩ := execution?_eq_some he
    have htsn := Delivery.find?_name_of_task hts
    refine ⟨fun h => (by simp [hn] at h), fun name' h' x hx hxid tk htk hname => ?_⟩
    rw [hn] at h'
    cases h'
    split at hx
    · have hx := setTask_same_id hx (hxid.trans hid.symm)
      subst hx
      rw [withTask_named htk (hname.trans htsn.symm)]
      rfl
    · rename_i hna
      obtain rfl := Limit.eq_of_key execIds hx hem (hxid.trans hid.symm)
      obtain ⟨e', he', he'id, y, hy, hyn, hyb⟩ := begun name hn
      obtain rfl := Limit.eq_of_key execIds he' hx (he'id.trans hid.symm)
      have hts' := List.mem_of_find?_eq_some hts
      rw [coherent e' he' tk htk ts hts' (hname.trans htsn.symm)]
      rw [← coherent e' he' ts hts' y hy (htsn.trans hyn.symm)] at hyb
      exact ended_of_begun hyb hna

/-- The calls of `t` that ended were ended calls of `s`, or ended in this step with their owner closed. -/
def CallCase (s t : State) : Prop :=
  ∀ c ∈ t.calls, c.status.ended = true → c ∈ s.calls ∨ OwnerClosed t c

/-- No call ended in the step. -/
def CallKept (s t : State) : Prop :=
  ∀ c ∈ t.calls, c.status.ended = true → c ∈ s.calls

namespace CallKept

theorem of_eq (h : t.calls = s.calls) : CallKept s t := fun _ hc _ => h ▸ hc

theorem trans (h₁ : CallKept s u) (h₂ : CallKept u t) : CallKept s t := fun c hc he => h₁ c (h₂ c hc he) he

theorem pre (h : CallKept u t) (hu : u.calls = s.calls) : CallKept s t := (of_eq hu).trans h

theorem append {x : Call} (h : t.calls = s.calls ++ [x]) (hx : x.status.ended = false) : CallKept s t := by
  intro c hc he
  rw [h, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hc
  · rw [hx] at he; cases he

theorem setCall {c' : Call} (hc' : c'.status.ended = false) : CallKept s (s.setCall c') := by
  intro c hc he
  rcases State.mem_setCall_calls hc with rfl | hc
  · rw [hc'] at he; cases he
  · exact hc

theorem stop : CallKept s s.stop := by
  intro c hc he
  obtain ⟨c', hc', rfl⟩ := State.mem_stop_calls.mp hc
  unfold stopCall at he ⊢
  split
  · rename_i h
    simp only [h, ↓reduceIte] at he
    simp [CallStatus.ended] at he
  · exact hc'

theorem fail {f : Failure} {policy : Policy} : CallKept s (s.fail f policy) := by
  cases policy
  · exact (of_eq (by simp)).trans (stop (s := { s with failures := s.failures ++ [f] }))
  · exact of_eq (by simp)

theorem case (h : CallKept s t) : CallCase s t := fun c hc he => Or.inl (h c hc he)

end CallKept

/-- A call ends in this step, and its owner closes. -/
theorem callCase_end {c c' : Call} (hc : t.calls = (s.setCall c').calls) (hid : c'.owner = c.owner)
    (htask : c'.task = c.task) (hclosed : OwnerClosed t c) : CallCase s t := by
  intro x hx _
  rw [hc] at hx
  rcases State.mem_setCall_calls hx with rfl | hx
  · exact Or.inr (hclosed.congr hid htask)
  · exact Or.inl hx

/-- A failed, timed out or lost call settles its owner as failed. -/
theorem callCase_failCall {c : Call} {status : CallStatus} {cause : Cause}
    (h : s.failCall c status cause = .ok t) : CallCase s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  have hclosed : OwnerClosed (s'.fail f c.policy) c := (settleOwner_closed hso (by simp) rfl).fail
  intro x hx hend
  have hx' : x ∈ s'.calls := CallKept.fail x hx hend
  rw [(State.settleOwner_update hso).calls] at hx'
  rcases State.mem_setCall_calls hx' with rfl | hx'
  · exact Or.inr (hclosed.congr rfl rfl)
  · exact Or.inl hx'

/-- Settling an invocation to a status that is not active closes it for its call (`judged`). -/
theorem setInvocation_closed {c : Call} {i i' : Invocation} (hn : c.task = none) (hi : i.id = c.owner)
    (hid : i'.id = i.id) (hst : i'.status ≠ .active) : OwnerClosed (u.setInvocation i') c := by
  refine ⟨fun _ x hx hxid => ?_, fun name h => (by simp [hn] at h)⟩
  rcases mem_setInvocation_iff hx with rfl | ⟨-, hne⟩
  · exact hst
  · exact absurd (hxid.trans (hi.symm.trans hid.symm)) hne

/-- A call ends only by a report of its own, which settles or cancels its owner in the same step. -/
theorem step_calls {op : Op} (wk : s.WellKeyed) (lim : Limit.Inv s) (hs : step p s op = .ok t) : CallCase s t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact (CallKept.of_eq rfl).case
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact (CallKept.append rfl rfl).case
    · exact (CallKept.append rfl rfl).case
    · exact (CallKept.of_eq rfl).case
    · exact (CallKept.of_eq rfl).case
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact (CallKept.setCall rfl).case
  | returned id value =>
    obtain ⟨-, -, c, _, s', -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact callCase_end (c' := { c with status := .returned })
      (by rw [(State.settleOwner_update hso).calls, setCall_calls, setCall_calls, (accept_frame hacc).2.2.2.2.2.1])
      rfl rfl (settleOwner_closed hso (by simp) rfl)
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', -, -, -, hn, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact callCase_end (c' := { c with status := .returned })
      (by rw [setInvocation_calls, setCall_calls, setCall_calls, (accept_frame hacc).2.2.2.2.2.1]) rfl rfl
      (setInvocation_closed hn (invocation?_eq_some hi).2 rfl (by simp))
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact ((CallKept.setCall rfl).pre (accept_frame hacc).2.2.2.2.2.1).case
  | ended id =>
    obtain ⟨-, -, c, -, -, -, hso⟩ := Step.ended_inv hs
    exact callCase_end (c' := { c with status := .returned }) (State.settleOwner_update hso).calls rfl rfl
      (settleOwner_closed hso (by simp) rfl)
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact callCase_failCall h
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact callCase_failCall h
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact callCase_failCall h
    · exact callCase_end (c' := { c with status := .cancelled }) (State.cancelOwner_update h).calls rfl rfl
        (cancelOwner_closed h wk.invocations wk.executions lim.coherent
          fun name hn => lim.calls c (call?_eq_some hc).1 name hn)
  | terminated id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.terminated_inv hs
    exact callCase_end (c' := { c with status := .cancelled }) (State.cancelOwner_update h).calls rfl rfl
      (cancelOwner_closed h wk.invocations wk.executions lim.coherent
        fun name hn => lim.calls c (call?_eq_some hc).1 name hn)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact (CallKept.of_eq rfl).case
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact (CallKept.fail.pre rfl).case
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact (CallKept.of_eq rfl).case
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (CallKept.fail.pre rfl).case
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact (CallKept.append rfl rfl).case
    · exact (CallKept.of_eq rfl).case
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact (CallKept.of_eq rfl).case
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (CallKept.fail.pre rfl).case
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact (CallKept.of_eq rfl).case
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact (CallKept.of_eq rfl).case
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact (CallKept.of_eq rfl).case
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact (CallKept.stop.pre rfl |>.trans (CallKept.of_eq rfl)).case
    · exact (CallKept.of_eq rfl).case
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact (CallKept.of_eq rfl).case

/-! ### Runs -/

/-- The owner of a completed run no longer waits for it: its invocation is not active, or its task
    ended. -/
def RunOwnerClosed (t : State) (r : Run) : Prop :=
  (r.task = none → ∀ i ∈ t.invocations, r.owner = some i.id → i.status ≠ .active) ∧
  (∀ name, r.task = some name → ∀ e ∈ t.executions, r.owner = some e.id → ∀ tk ∈ e.tasks, tk.name = name →
    tk.status.ended = true)

/-- The workflows a run can have: the main workflow, or one that a placement of a declared workflow
    calls. -/
def Referenced (p : Definition) (wf : String) : Prop :=
  wf = p.main ∨ ∃ w ∈ p.workflows, ∃ pl ∈ w.placements, wf ∈ pl.control.workflowRefs

/-- A run after a step: stored before, completed in this step with its owner closed (the root has no
    owner), or created in this step for a referenced workflow. -/
def RunCase (p : Definition) (s t : State) (r : Run) : Prop :=
  r ∈ s.runs ∨
  (∃ r₀ ∈ s.runs, r₀.path = r.path ∧ r₀.workflow = r.workflow ∧ r₀.owner = r.owner ∧ r₀.task = r.task ∧
    r.complete = true ∧ (r.owner = none ∨ RunOwnerClosed t r)) ∨
  (s.run? r.path = none ∧ r.complete = false ∧ Referenced p r.workflow)

/-- Steps that keep the runs. -/
theorem RunCase.of_eq (h : t.runs = s.runs) : ∀ r ∈ t.runs, RunCase p s t r := fun _ hr => Or.inl (h ▸ hr)

/-- A run created by `invoke` or `beginTask`. -/
theorem RunCase.append {x : Run} (h : t.runs = s.runs ++ [x]) (hfresh : s.run? x.path = none)
    (hc : x.complete = false) (href : Referenced p x.workflow) : ∀ r ∈ t.runs, RunCase p s t r := by
  intro r hr
  rw [h, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · exact Or.inl hr
  · exact Or.inr (Or.inr ⟨hfresh, hc, href⟩)

/-- A run completed by `closeRun` or `conclude`. -/
theorem RunCase.setRun {r₀ : Run} (hr₀ : r₀ ∈ s.runs) (ht : t.runs = (s.setRun { r₀ with complete := true }).runs)
    (hclosed : r₀.owner = none ∨ RunOwnerClosed t { r₀ with complete := true }) : ∀ r ∈ t.runs, RunCase p s t r := by
  intro r hr
  rw [ht] at hr
  rcases State.mem_setRun_runs hr with rfl | hr
  · exact Or.inr (Or.inl ⟨r₀, hr₀, rfl, rfl, rfl, rfl, rfl, hclosed⟩)
  · exact Or.inl hr

/-- `closeRun` of a sub-workflow run settles its invocation. -/
theorem runClosed_setInvocation {r : Run} {i i' : Invocation} {o : String} (hn : r.task = none)
    (ho : r.owner = some o) (hi : i.id = o) (hid : i'.id = i.id) (hst : i'.status ≠ .active) :
    RunOwnerClosed (u.setInvocation i') r := by
  refine ⟨fun _ x hx hxo => ?_, fun name h => (by simp [hn] at h)⟩
  rcases mem_setInvocation_iff hx with rfl | ⟨-, hne⟩
  · exact hst
  · rw [ho, Option.some.injEq] at hxo
    exact absurd (hxo.symm.trans (hi.symm.trans hid.symm)) hne

/-- `closeRun` of a task run settles its task. -/
theorem runClosed_setTask {r : Run} {e : Execution} {ts : TaskState} {name : String} {st : TaskStatus}
    (hn : r.task = some name) (ho : r.owner = some e.id) (hts : e.tasks.find? (·.name == name) = some ts)
    (hst : st.ended = true) : RunOwnerClosed (u.setTask e { ts with status := st }) r := by
  refine ⟨fun h => (by simp [hn] at h), fun name' h' x hx hxo tk htk hname => ?_⟩
  rw [hn] at h'
  cases h'
  rw [ho, Option.some.injEq] at hxo
  have hx := setTask_same_id hx hxo.symm
  subst hx
  rw [withTask_named htk (hname.trans (Delivery.find?_name_of_task hts).symm)]
  exact hst

theorem runClosed_of_eq {r : Run} (h : RunOwnerClosed u r) (hi : t.invocations = u.invocations)
    (he : t.executions = u.executions) : RunOwnerClosed t r := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun hn i hi' ho => h1 hn i (hi ▸ hi') ho, fun name hn e he' ho => h2 name hn e (he ▸ he') ho⟩

/-- Every run after a step: `start`, `invoke` and `beginTask` create runs of referenced workflows,
    `closeRun` completes a run with its owner, and `conclude` completes the root, which has no owner. -/
theorem step_runs {op : Op} (inv : Delivery.Inv p s) (hs : step p s op = .ok t) : ∀ r ∈ t.runs, RunCase p s t r := by
  cases op with
  | start input =>
    obtain ⟨hst, -, w, hw, -, rfl⟩ := Step.start_inv hs
    have hnil : s.runs = [] := by rw [inv.fresh hst]
    exact RunCase.append (x := { path := [], workflow := p.main, input }) (by simp [hnil])
      (by simp [State.run?, hnil]) rfl (Or.inl rfl)
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, _, _, hr, -, hw, hpl, -, rfl, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨wf, out, hwf, hrun, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact RunCase.of_eq rfl
    · exact RunCase.of_eq rfl
    · exact RunCase.append rfl hrun rfl (Or.inr ⟨w, (Definition.workflow?_eq_some hw).1, pl,
        (Workflow.placement?_eq_some hpl).1, by simp [hwf, Control.workflowRefs, Body.workflowRef]⟩)
    · exact RunCase.of_eq rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact RunCase.of_eq rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact RunCase.of_eq (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact RunCase.of_eq (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact RunCase.of_eq (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact RunCase.of_eq (by rw [(settleOwner_update hso).runs, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact RunCase.of_eq (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact RunCase.of_eq (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact RunCase.of_eq (failCall_runs h)
    · exact RunCase.of_eq (by rw [(cancelOwner_update h).runs, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact RunCase.of_eq (by rw [(cancelOwner_update h).runs, setCall_runs])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact RunCase.of_eq rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact RunCase.of_eq (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact RunCase.of_eq rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact RunCase.of_eq (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, e, c, _, spec, -, -, hc, -, -, -, hspec, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨wf, out, hbody, hrun, rfl⟩
    · exact RunCase.of_eq rfl
    · obtain ⟨c', hc', hfind⟩ := State.taskSpec_eq_ok.mp hspec
      obtain ⟨w, pl, hw, hpl, hcc⟩ := Delivery.concurrencyOf_iff.mp hc'
      obtain ⟨r, -, hwf⟩ := Delivery.workflow?_iff.mp hw
      refine RunCase.append rfl hrun rfl (Or.inr ⟨w, (Definition.workflow?_eq_some hwf).1, pl,
        (Workflow.placement?_eq_some hpl).1, ?_⟩)
      rw [hcc]
      exact List.mem_filterMap.mpr ⟨spec, List.mem_of_find?_eq_some hfind, by simp [hbody, Body.workflowRef]⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact RunCase.of_eq rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact RunCase.of_eq (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact RunCase.of_eq rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact RunCase.of_eq rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, -, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    have hr' := (run?_eq_some hr).1
    rcases h with ⟨hn, i, hi, h⟩ | ⟨name, e, ts, hn, he, hts, h⟩
    · have hid := (invocation?_eq_some hi).2
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_of_eq
          (runClosed_setInvocation (u := s.setRun { r with complete := true }) (i' := { i with status := .succeeded })
            hn howner hid rfl (by simp)) rfl rfl))
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_setInvocation hn howner hid rfl (by simp)))
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_setInvocation hn howner hid rfl (by simp)))
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_setInvocation hn howner hid rfl (by simp)))
    · have hid := (execution?_eq_some he).2
      have ho : r.owner = some e.id := by rw [howner, hid]
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_of_eq
          (runClosed_setTask (u := s.setRun { r with complete := true }) (st := .succeeded) hn ho hts rfl) rfl rfl))
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_setTask hn ho hts rfl))
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_setTask hn ho hts rfl))
      · exact RunCase.setRun hr' rfl (Or.inr (runClosed_setTask hn ho hts rfl))
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact RunCase.of_eq rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · obtain ⟨hrm, hrp⟩ := run?_eq_some hr
      refine RunCase.setRun hrm rfl (Or.inl ?_)
      rcases inv.own.runs r hrm with ⟨ho, -, -⟩ | ⟨-, i, -, -, hp, -⟩ | ⟨name, -, e, -, -, hp, -⟩
      · exact ho
      · rw [hrp] at hp; simp at hp
      · rw [hrp] at hp; simp at hp
    · exact RunCase.of_eq rfl

/-! ### Executions and tasks -/

/-- The body of an active task: a call that has not ended, or a run that is open (§8.2). -/
def TaskBody (s : State) (e : Execution) (name : String) : Prop :=
  (∃ c ∈ s.calls, c.id = Key.task e.id name ∧ c.owner = e.id ∧ c.task = some name ∧ c.status.ended = false) ∨
  (∃ r ∈ s.runs, r.path = e.run ++ [Key.task e.id name] ∧ r.owner = some e.id ∧ r.task = some name ∧
    r.complete = false)

/-- How one task may move in one step: it keeps its status, ends, takes its input (pending to ready), or
    begins with its body (ready to active). -/
def Moved (t : State) (e : Execution) (name : String) (a b : TaskStatus) : Prop :=
  b = a ∨ b.ended = true ∨ (a = .pending ∧ b = .ready) ∨ (a = .ready ∧ b = .active ∧ TaskBody t e name)

/-- An execution after a step: a stored one in the same place, completed only together with its
    invocation, whose tasks moved; or the new one `invoke` created, whose tasks wait. -/
def ExecCase (p : Definition) (s t : State) (e : Execution) : Prop :=
  (∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.run = e.run ∧ e₀.placement = e.placement ∧
    (e.complete = true → e₀.complete = true ∨ ∀ i ∈ t.invocations, i.id = e.id → i.status ≠ .active) ∧
    ∀ tk ∈ e.tasks, ∃ tk₀ ∈ e₀.tasks, tk₀.name = tk.name ∧ Moved t e tk.name tk₀.status tk.status) ∨
  (s.execution? e.id = none ∧ e.complete = false ∧ ∀ tk ∈ e.tasks, tk.status ≠ .active ∧
    (tk.status = .pending → ∀ cc, t.concurrencyOf p e = .ok cc → cc.input.isSome = true))

/-- A stored execution that the step keeps. -/
theorem ExecCase.self {e : Execution} (he : e ∈ s.executions) : ExecCase p s t e :=
  Or.inl ⟨e, he, rfl, rfl, rfl, fun hc => Or.inl hc, fun tk htk => ⟨tk, htk, rfl, Or.inl rfl⟩⟩

theorem ExecCase.of_eq (h : t.executions = s.executions) : ∀ e ∈ t.executions, ExecCase p s t e := by
  intro e he
  rw [h] at he
  exact ExecCase.self he

/-- One task of a stored execution moves. -/
theorem ExecCase.setTask {e₁ : Execution} {ts ts' : TaskState} (he₁ : e₁ ∈ s.executions) (hts : ts ∈ e₁.tasks)
    (hname : ts'.name = ts.name) (hmove : Moved t (withTask e₁ ts') ts'.name ts.status ts'.status)
    (ht : t.executions = (s.setTask e₁ ts').executions) : ∀ e ∈ t.executions, ExecCase p s t e := by
  intro e he
  rw [ht] at he
  rcases State.mem_setTask_executions he with rfl | he
  · refine Or.inl ⟨e₁, he₁, rfl, rfl, rfl, fun hc => Or.inl hc, fun tk htk => ?_⟩
    rcases Delivery.mem_withTask htk with rfl | ⟨htk, -⟩
    · exact ⟨ts, hts, hname.symm, hmove⟩
    · exact ⟨tk, htk, rfl, Or.inl rfl⟩
  · exact Or.inl ⟨e, he, rfl, rfl, rfl, fun hc => Or.inl hc, fun tk htk => ⟨tk, htk, rfl, Or.inl rfl⟩⟩

/-- Steps after which nothing an execution's case reads changes, except that the stop may end tasks. -/
structure Post (u t : State) : Prop where
  invocations : t.invocations = u.invocations
  runs : t.runs = u.runs
  calls : ∀ c ∈ u.calls, ∃ c' ∈ t.calls, c'.id = c.id ∧ c'.owner = c.owner ∧ c'.task = c.task ∧
    (c.status.ended = false → c'.status.ended = false)
  executions : t.executions = u.executions ∨ t.executions = u.stop.executions

theorem Post.of_eq (hi : t.invocations = u.invocations) (hr : t.runs = u.runs) (hc : t.calls = u.calls)
    (he : t.executions = u.executions) : Post u t :=
  ⟨hi, hr, fun c h => ⟨c, hc ▸ h, rfl, rfl, rfl, id⟩, Or.inl he⟩

theorem Post.stop (hi : t.invocations = u.invocations) (hr : t.runs = u.runs) (hc : t.calls = u.stop.calls)
    (he : t.executions = u.stop.executions) : Post u t := by
  refine ⟨hi, hr, fun c h => ⟨stopCall c, hc ▸ State.mem_stop_calls.mpr ⟨c, h, rfl⟩, by simp, by simp, by simp,
    fun hne => ?_⟩, Or.inr he⟩
  rw [stopCall_status]
  split
  · rfl
  · exact hne

theorem Post.fail {f : Failure} {policy : Policy} : Post u (u.fail f policy) := by
  cases policy
  · exact Post.stop (u := u) (by simp) (by simp) rfl rfl
  · exact Post.of_eq (by simp) (by simp) rfl rfl

theorem TaskBody.post {e e' : Execution} {name : String} (h : TaskBody u e name) (hp : Post u t)
    (hid : e'.id = e.id) (hrun : e'.run = e.run) : TaskBody t e' name := by
  rcases h with ⟨c, hc, h1, h2, h3, h4⟩ | ⟨r, hr, h1, h2, h3, h4⟩
  · obtain ⟨c', hc', a1, a2, a3, a4⟩ := hp.calls c hc
    exact Or.inl ⟨c', hc', by rw [a1, h1, hid], by rw [a2, h2, hid], by rw [a3, h3], a4 h4⟩
  · exact Or.inr ⟨r, hp.runs ▸ hr, by rw [h1, hid, hrun], by rw [h2, hid], h3, h4⟩

theorem Moved.post {e e' : Execution} {name : String} {a b : TaskStatus} (h : Moved u e name a b) (hp : Post u t)
    (hid : e'.id = e.id) (hrun : e'.run = e.run) : Moved t e' name a b := by
  rcases h with h | h | h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3.post hp hid hrun⟩))

/-- A case of every execution carries over a step that keeps what it reads (`Post`). -/
theorem ExecCase.post (h : ∀ e ∈ u.executions, ExecCase p s u e) (hp : Post u t) :
    ∀ e ∈ t.executions, ExecCase p s t e := by
  have conc : ∀ e, t.concurrencyOf p e = u.concurrencyOf p e := fun e => concurrencyOf_of_runs hp.runs
  intro e he
  rcases hp.executions with he' | he'
  · rw [he'] at he
    rcases h e he with ⟨e₀, he₀, h1, h2, h3, hc, htasks⟩ | ⟨h1, h2, htasks⟩
    · refine Or.inl ⟨e₀, he₀, h1, h2, h3, fun hce => ?_, fun tk htk => ?_⟩
      · rcases hc hce with hc | hc
        · exact Or.inl hc
        · exact Or.inr fun i hi => hc i (hp.invocations ▸ hi)
      · obtain ⟨tk₀, htk₀, hn, hm⟩ := htasks tk htk
        exact ⟨tk₀, htk₀, hn, hm.post hp rfl rfl⟩
    · refine Or.inr ⟨h1, h2, fun tk htk => ⟨(htasks tk htk).1, fun hpend cc hcc => ?_⟩⟩
      rw [conc] at hcc
      exact (htasks tk htk).2 hpend cc hcc
  · rw [he', State.mem_stop_executions] at he
    obtain ⟨e', he', rfl⟩ := he
    rcases h e' he' with ⟨e₀, he₀, h1, h2, h3, hc, htasks⟩ | ⟨h1, h2, htasks⟩
    · refine Or.inl ⟨e₀, he₀, h1, h2, h3, fun hce => ?_, fun tk htk => ?_⟩
      · rcases hc hce with hc | hc
        · exact Or.inl hc
        · exact Or.inr fun i hi => hc i (hp.invocations ▸ hi)
      · rw [Limit.stopExecution_tasks] at htk
        obtain ⟨tk', htk', rfl⟩ := List.mem_map.mp htk
        obtain ⟨tk₀, htk₀, hn, hm⟩ := htasks tk' htk'
        refine ⟨tk₀, htk₀, by rw [hn, Limit.stopTask_name], ?_⟩
        rcases stopTask_status tk' with hst | hst
        · exact Or.inr (Or.inl (by rw [hst]; rfl))
        · rw [hst]
          exact hm.post hp rfl rfl
    · refine Or.inr ⟨h1, h2, fun tk htk => ?_⟩
      rw [Limit.stopExecution_tasks] at htk
      obtain ⟨tk', htk', rfl⟩ := List.mem_map.mp htk
      rcases stopTask_status tk' with hst | hst
      · rw [hst]
        exact ⟨by simp, by simp⟩
      · rw [hst]
        refine ⟨(htasks tk' htk').1, fun hpend cc hcc => ?_⟩
        rw [conc, Delivery.concurrencyOf_congr rfl rfl] at hcc
        exact (htasks tk' htk').2 hpend cc hcc

/-- A report settles the owner of its call: an invocation, or a task to an ended status. -/
theorem ExecCase.settleOwner {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : u.settleOwner c inv task = .ok t) (hu : u.executions = s.executions) (htask : task.ended = true) :
    ∀ e ∈ t.executions, ExecCase p s t e := by
  rcases State.settleOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨name, e, ts, -, he, hts, rfl⟩
  · exact ExecCase.of_eq hu
  · exact ExecCase.setTask (ts' := { ts with status := task }) (hu ▸ (execution?_eq_some he).1)
      (List.mem_of_find?_eq_some hts) rfl (Or.inr (Or.inl htask)) (Delivery.setTask_executions_congr hu)

/-- A terminated call cancels its active owner. -/
theorem ExecCase.cancelOwner {c : Call} (h : u.cancelOwner c = .ok t) (hu : u.executions = s.executions) :
    ∀ e ∈ t.executions, ExecCase p s t e := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨name, e, ts, -, he, hts, rfl⟩ <;> split
  · exact ExecCase.of_eq hu
  · exact ExecCase.of_eq hu
  · exact ExecCase.setTask (ts' := { ts with status := .cancelled }) (hu ▸ (execution?_eq_some he).1)
      (List.mem_of_find?_eq_some hts) rfl (Or.inr (Or.inl rfl)) (Delivery.setTask_executions_congr hu)
  · exact ExecCase.of_eq hu

theorem ExecCase.fail_of_eq {f : Failure} {policy : Policy} (hu : u.executions = s.executions) :
    ∀ e ∈ (u.fail f policy).executions, ExecCase p s (u.fail f policy) e :=
  ExecCase.post (ExecCase.of_eq hu) Post.fail

theorem ExecCase.failCall {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    ∀ e ∈ t.executions, ExecCase p s t e := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  exact ExecCase.post (ExecCase.settleOwner (s := s) hso rfl rfl) Post.fail


/-- `closeExecution` completes an execution together with its invocation. -/
theorem ExecCase.close {e₁ : Execution} {i i' : Invocation} (he₁ : e₁ ∈ s.executions) (hi : i.id = e₁.id)
    (hid : i'.id = i.id) (hst : i'.status ≠ .active)
    (ht : t.executions = (s.setExecution { e₁ with complete := true }).executions)
    (hti : t.invocations = (u.setInvocation i').invocations) : ∀ e ∈ t.executions, ExecCase p s t e := by
  intro e he
  rw [ht] at he
  rcases Limit.mem_setExecution_iff he with rfl | ⟨he, -⟩
  · refine Or.inl ⟨e₁, he₁, rfl, rfl, rfl, fun _ => Or.inr fun x hx hxid => ?_,
      fun tk htk => ⟨tk, htk, rfl, Or.inl rfl⟩⟩
    rw [hti] at hx
    rcases mem_setInvocation_iff hx with rfl | ⟨-, hne⟩
    · exact hst
    · exact absurd (hxid.trans (hi.symm.trans hid.symm)) hne
  · exact Or.inl ⟨e, he, rfl, rfl, rfl, fun hc => Or.inl hc, fun tk htk => ⟨tk, htk, rfl, Or.inl rfl⟩⟩

/-- Every execution after a step: `invoke` creates one whose tasks wait, `closeExecution` completes one
    with its invocation, and tasks move only as `Moved` allows. -/
theorem step_executions {op : Op} (hs : step p s op = .ok t) : ∀ e ∈ t.executions, ExecCase p s t e := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact ExecCase.of_eq rfl
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, rfl, -, -, h⟩ := Step.invoke_inv hs
    have hwf : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨c, hcont, hexec, rfl⟩
    · exact ExecCase.of_eq rfl
    · exact ExecCase.of_eq rfl
    · exact ExecCase.of_eq rfl
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ExecCase.self he
      · refine Or.inr ⟨hexec, rfl, fun tk htk => ?_⟩
        simp only [List.mem_map] at htk
        obtain ⟨ts, -, rfl⟩ := htk
        refine ⟨by split <;> simp, fun hpend cc hcc => ?_⟩
        obtain ⟨w', pl', hw', hpl', hcc'⟩ := Delivery.concurrencyOf_iff.mp hcc
        have hw'' : s.workflow? p path = some w' := hw'
        rw [hwf] at hw''
        cases hw''
        rw [hpl] at hpl'
        cases hpl'
        rw [hcont] at hcc'
        cases hcc'
        revert hpend
        split
        · intro _; assumption
        · simp
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact ExecCase.of_eq rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact ExecCase.settleOwner hso (by rw [setCall_executions, (accept_frame hacc).2.2.2.2.2.2.1]) rfl
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact ExecCase.of_eq (by rw [setInvocation_executions, setCall_executions, (accept_frame hacc).2.2.2.2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact ExecCase.of_eq (by rw [setCall_executions, (accept_frame hacc).2.2.2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact ExecCase.settleOwner hso rfl rfl
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact ExecCase.failCall h
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact ExecCase.failCall h
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact ExecCase.failCall h
    · exact ExecCase.cancelOwner h rfl
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact ExecCase.cancelOwner h rfl
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact ExecCase.of_eq rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact ExecCase.fail_of_eq rfl
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, _, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    exact ExecCase.setTask (ts' := { ts with status := .ready, input := value }) (execution?_eq_some he).1
      (List.mem_of_find?_eq_some hts) rfl (Or.inr (Or.inr (Or.inl ⟨hpend, rfl⟩))) rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, _, _, he, hts, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact ExecCase.post (ExecCase.setTask (ts' := { ts with status := .failed }) (execution?_eq_some he).1
      (List.mem_of_find?_eq_some hts) rfl (Or.inr (Or.inl rfl)) rfl) Post.fail
  | beginTask eid name =>
    obtain ⟨-, -, e, c, ts, spec, he, -, -, hts, hready, -, -, h⟩ := Step.beginTask_inv hs
    have hname := Delivery.find?_name_of_task hts
    rcases h with ⟨f, decl, -, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩
    · refine ExecCase.setTask (ts' := { ts with status := .active }) (execution?_eq_some he).1
        (List.mem_of_find?_eq_some hts) rfl (Or.inr (Or.inr (Or.inr ⟨hready, rfl, Or.inl ⟨_,
          List.mem_append_right _ (List.mem_singleton_self _), ?_, rfl, ?_, rfl⟩⟩))) rfl
      · simp [hname, State.taskId]
      · simp [hname]
    · refine ExecCase.setTask (ts' := { ts with status := .active }) (execution?_eq_some he).1
        (List.mem_of_find?_eq_some hts) rfl (Or.inr (Or.inr (Or.inr ⟨hready, rfl, Or.inr ⟨_,
          List.mem_append_right _ (List.mem_singleton_self _), ?_, rfl, ?_, rfl⟩⟩))) rfl
      · simp [hname, State.taskId]
      · simp [hname]
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact ExecCase.of_eq rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact ExecCase.fail_of_eq rfl
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact ExecCase.of_eq rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i, he, -, -, -, -, hi, h⟩ := Step.closeExecution_inv hs
    have he' := execution?_eq_some he
    have hid : i.id = e.id := (invocation?_eq_some hi).2.trans he'.2.symm
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ExecCase.close (i' := { i with status := .skipped }) he'.1 hid rfl (by simp) rfl rfl
    · exact ExecCase.close (i' := { i with status := .succeeded }) he'.1 hid rfl (by simp) rfl rfl
    · exact ExecCase.close (i' := { i with status := .succeeded }) he'.1 hid rfl (by simp) rfl rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, i, -, h⟩ | ⟨name, e, ts, -, he, hts, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ExecCase.of_eq rfl
    · have he' := (execution?_eq_some he).1
      have hts' := List.mem_of_find?_eq_some hts
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ExecCase.setTask (ts' := { ts with status := .succeeded }) he' hts' rfl (Or.inr (Or.inl rfl))
          (Delivery.setTask_executions_congr rfl)
      · exact ExecCase.setTask (ts' := { ts with status := .skipped }) he' hts' rfl (Or.inr (Or.inl rfl))
          (Delivery.setTask_executions_congr rfl)
      · exact ExecCase.setTask (ts' := { ts with status := .failed }) he' hts' rfl (Or.inr (Or.inl rfl))
          (Delivery.setTask_executions_congr rfl)
      · exact ExecCase.setTask (ts' := { ts with status := .upstreamFailed }) he' hts' rfl (Or.inr (Or.inl rfl))
          (Delivery.setTask_executions_congr rfl)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact ExecCase.post (ExecCase.of_eq (t := s) rfl) (Post.stop rfl rfl rfl rfl)
    · exact ExecCase.of_eq rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact ExecCase.of_eq rfl

/-! ### The root run -/

/-- Only `start` is accepted before the start. -/
theorem step_not_started {op : Op} (hs : step p s op = .ok t) (h : s.started = false) :
    ∃ input, op = .start input ∧ t = { s with started := true, runs := [{ path := [], workflow := p.main, input }] } := by
  have no : s.started = true → False := fun h' => by rw [h] at h'; cases h'
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact ⟨input, rfl, rfl⟩
  | invoke => exact (no (Step.invoke_inv hs).1).elim
  | fetch => exact (no (Step.fetch_inv hs).1).elim
  | returned => exact (no (Step.returned_inv hs).1).elim
  | judged => exact (no (Step.judged_inv hs).1).elim
  | yielded => exact (no (Step.yielded_inv hs).1).elim
  | ended => exact (no (Step.ended_inv hs).1).elim
  | failed => exact (no (Step.failed_inv hs).1).elim
  | timedOut => exact (no (Step.timedOut_inv hs).1).elim
  | lost => exact (no (Step.lost_inv hs).1).elim
  | terminated => exact (no (Step.terminated_inv hs).1).elim
  | deliver => exact (no (Step.deliver_inv hs).1).elim
  | transformFailed => exact (no (Step.transformFailed_inv hs).1).elim
  | taskInput => exact (no (Step.taskInput_inv hs).1).elim
  | taskInputFailed => exact (no (Step.taskInputFailed_inv hs).1).elim
  | beginTask => exact (no (Step.beginTask_inv hs).1).elim
  | taskOutput => exact (no (Step.taskOutput_inv hs).1).elim
  | taskOutputFailed => exact (no (Step.taskOutputFailed_inv hs).1).elim
  | settle => exact (no (Step.settle_inv hs).1).elim
  | closeExecution => exact (no (Step.closeExecution_inv hs).1).elim
  | closeRun => exact (no (Step.closeRun_inv hs).1).elim
  | cancel => exact (no (Step.cancel_inv hs).1).elim
  | conclude => exact (no (Step.conclude_inv hs).1).elim

/-- A started step keeps the root run, or ends the workflow (`conclude`), which keeps a root run. -/
theorem step_root {op : Op} (hs : step p s op = .ok t) (started : s.started = true) {r₀ : Run}
    (hr₀ : s.run? [] = some r₀) :
    t.run? [] = some r₀ ∨ (t.status.terminal = true ∧ ∃ r, t.run? [] = some r) := by
  have keep : t.runs = s.runs → t.run? [] = some r₀ ∨ (t.status.terminal = true ∧ ∃ r, t.run? [] = some r) :=
    fun h => Or.inl (by rw [run?_of_runs h, hr₀])
  cases op with
  | start input =>
    obtain ⟨h1, -⟩ := Step.start_inv hs
    rw [started] at h1; cases h1
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact keep rfl
    · exact keep rfl
    · exact Or.inl (by rw [run?_append_ne rfl (by simp), hr₀])
    · exact keep rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact keep rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact keep (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact keep (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact keep (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact keep (by rw [(settleOwner_update hso).runs, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact keep (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact keep (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact keep (failCall_runs h)
    · exact keep (by rw [(cancelOwner_update h).runs, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact keep (by rw [(cancelOwner_update h).runs, setCall_runs])
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
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact keep rfl
    · exact Or.inl (by rw [run?_append_ne rfl (by simp), hr₀])
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
    obtain ⟨-, -, r, _, _, _, _, hr, -, hne, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    have hroot : (s.setRun { r with complete := true }).run? [] = some r₀ := by
      simp [run?_setRun, (run?_eq_some hr).2, hne, hr₀]
    have kept : t.runs = (s.setRun { r with complete := true }).runs →
        t.run? [] = some r₀ ∨ (t.status.terminal = true ∧ ∃ r, t.run? [] = some r) :=
      fun h => Or.inl (by rw [run?_of_runs h, hroot])
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact kept rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact keep rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · refine Or.inr ⟨?_, { r with complete := true }, ?_⟩
      · simp only
        split
        · rfl
        · split <;> rfl
      · change (s.setRun { r with complete := true }).run? [] = _
        simp [run?_setRun, (run?_eq_some hr).2, hr]
    · exact keep rfl

/-- While started, the root run exists; it completes only when the workflow ends. -/
theorem root_inv {p : Definition} {s : State} (h : Reachable p s) :
    s.started = true → ∃ r, s.run? [] = some r ∧ (r.complete = true → s.status.terminal = true) := by
  induction h with
  | empty => intro h; cases h
  | @step s t op _ hs ih =>
    intro _
    by_cases hst : s.started = true
    · obtain ⟨r₀, hr₀, himp⟩ := ih hst
      have hlive : s.status.terminal = false := by
        rcases step_source_status hs with h | h <;> simp [h, Status.terminal]
      have hc : r₀.complete = false := by
        cases hc : r₀.complete
        · rfl
        · rw [himp hc] at hlive; cases hlive
      rcases step_root hs hst hr₀ with h | ⟨hterm, r, hr⟩
      · exact ⟨r₀, h, fun h' => by rw [hc] at h'; cases h'⟩
      · exact ⟨r, hr, fun _ => hterm⟩
    · obtain ⟨input, rfl, rfl⟩ := step_not_started hs (by simpa using hst)
      exact ⟨{ path := [], workflow := p.main, input }, by simp [State.run?], fun h => by simp at h⟩

/-! ### Static facts -/

/-- Reduces a successful validator computation to its conditions. -/
local macro "vsimp" " at " h:ident : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, exists_const, and_true, true_and, Bool.false_eq_true,
    ↓reduceIte, false_and, and_false, exists_false] at $h:ident)

/-- Validation checks every declared workflow. -/
theorem validateWorkflow_of_validate (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows) :
    p.validateWorkflow w = .ok () := by
  unfold Definition.validate at valid
  vsimp at valid
  obtain ⟨-, -, -, -, -, -, -, u, hloop⟩ := valid
  exact Static.forIn_yield_ok hloop w hw

/-- Validation checks every placement of a declared workflow. -/
theorem validatePlacement_of_validate (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) : p.validatePlacement w pl = .ok () := by
  have h := validateWorkflow_of_validate valid hw
  unfold Definition.validateWorkflow at h
  vsimp at h
  obtain ⟨-, -, -, -, u, -, -, h⟩ := h
  split at h <;> vsimp at h
  case' h_1 => obtain ⟨_, -, h⟩ := h
  all_goals
    obtain ⟨u₁, h1, -⟩ := h
    exact Static.forIn_yield_ok h1 pl hpl

/-- The body of a call placement is checked. -/
theorem body_of_call (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) {body : Body} (hc : pl.control = .call body) :
    ∃ at_ input, p.validateBody at_ body = .ok input := by
  have h := validatePlacement_of_validate valid hw hpl
  rcases pl with ⟨name, control, policy, timeout⟩
  simp only at hc
  subst hc
  unfold Definition.validatePlacement at h
  vsimp at h
  obtain ⟨input, hb, -⟩ := h
  exact ⟨_, input, hb⟩

/-- A checked workflow body names a declared workflow. -/
theorem workflow_of_validateBody {at_ id output : String} {input : Option ValueType}
    (h : p.validateBody at_ (.workflow id output) = .ok input) : (p.workflow? id).isSome := by
  unfold Definition.validateBody at h
  vsimp at h
  obtain ⟨w, hw, -⟩ := h
  simp [hw]

/-- The body of a checked task is checked. -/
theorem body_of_validateTask {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) : ∃ at' input, p.validateBody at' task.body = .ok input := by
  unfold Definition.validateTask at h
  vsimp at h
  obtain ⟨-, input, hb, -⟩ := h
  exact ⟨_, input, hb⟩

/-- A checked task of a concurrency with an input has an input transform (§8.1). -/
theorem input_of_validateTask {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) (hc : c.input.isSome = true) : task.input.isSome = true := by
  unfold Definition.validateTask at h
  vsimp at h
  obtain ⟨-, input, -, h⟩ := h
  cases hti : task.input with
  | some _ => rfl
  | none =>
    rw [hti] at h
    cases input with
    | none =>
      vsimp at h
      obtain ⟨h1, -⟩ := h
      cases hci : c.input <;> simp [hci] at hc h1
    | some _ => vsimp at h

/-- Validation checks every task of a concurrency placement. -/
theorem tasks_of_validate (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) {c : Concurrency} (hc : pl.control = .concurrency c) :
    ∀ task ∈ c.tasks, ∃ at_, p.validateTask at_ c task = .ok () :=
  ((((Definition.validate_ok valid).workflows w hw).placements pl hpl).concurrency c hc).2.2.2

/-- A referenced workflow exists in a valid definition. -/
theorem referenced_workflow (valid : p.validate = .ok ()) {wf : String} (h : Referenced p wf) :
    (p.workflow? wf).isSome := by
  rcases h with rfl | ⟨w, hw, pl, hpl, href⟩
  · exact (Definition.validate_ok valid).main
  · rcases hctl : pl.control with body | ⟨judge, arms⟩ | e | e | c <;>
      rw [hctl] at href <;> simp only [Control.workflowRefs, List.not_mem_nil] at href
    · cases body with
      | function f => simp [Body.workflowRef] at href
      | workflow id out =>
        simp only [Body.workflowRef, Option.toList_some, List.mem_singleton] at href
        subst href
        obtain ⟨at_, _, hb⟩ := body_of_call valid hw hpl hctl
        exact workflow_of_validateBody hb
    · obtain ⟨task, htask, href⟩ := List.mem_filterMap.mp href
      obtain ⟨at_, hv⟩ := tasks_of_validate valid hw hpl hctl task htask
      obtain ⟨at', _, hb⟩ := body_of_validateTask hv
      cases hbody : task.body with
      | function f => rw [hbody] at href; simp [Body.workflowRef] at href
      | workflow id out =>
        rw [hbody] at href hb
        simp only [Body.workflowRef, Option.some.injEq] at href
        subst href
        exact workflow_of_validateBody hb

end Suimon.Round3.ProgressInvAux
