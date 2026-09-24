import Suimon.Theorems.Round3.RunConform

/-! Helpers for [22] Round3/CoversOps.lean — task F4: the fields a record takes at its creation.

A call, a run and an execution copy their input, and a call its timeout and policy, from the owner
that creates them, and none of these fields changes later. `Created` states this for every reachable
state, with two facts on tasks: a pending task has no input yet, and a task fails without beginning
only through its declared input transform. The complete run of `covers_invoke` and
`covers_beginTask` needs them to know the records it created, and no Round 2 invariant records these
fields. This file holds the frame argument for steps that create nothing (`Frame`, `Created.of_frame`). -/

namespace Suimon.Round3
namespace CoversOpsAux
open State

variable {p : Definition} {s t u : State}

/-- The fields of a call fixed at its creation. -/
def callFix (c : Call) : String × String × Option String × CallTarget × Option Value × Bool × Timeout × Policy :=
  (c.id, c.owner, c.task, c.target, c.input, c.stream, c.timeout, c.policy)

theorem callFix_eq {c c' : Call} (h : callFix c = callFix c') :
    c.id = c'.id ∧ c.owner = c'.owner ∧ c.task = c'.task ∧ c.target = c'.target ∧ c.input = c'.input ∧
      c.stream = c'.stream ∧ c.timeout = c'.timeout ∧ c.policy = c'.policy := by
  simpa [callFix] using h

/-- A task began, or its declared input transform exists. -/
def Justified (p : Definition) (s : State) (e : Execution) (name : String) : Prop :=
  ¬ NotBegun s e name ∨ ∃ spec tid, s.taskSpec p e name = .ok spec ∧ spec.input = some (.declared tid)

/-- The fields each record takes at its creation from its owner, and two facts on tasks. -/
structure Created (p : Definition) (s : State) : Prop where
  invCall : ∀ c ∈ s.calls, c.task = none → ∀ i ∈ s.invocations, i.id = c.owner →
    c.input = i.input ∧ ∀ w pl, s.workflow? p i.run = some w → w.placement? i.placement = some pl →
      c.timeout = pl.timeout ∧ c.policy = pl.policy
  taskCall : ∀ c ∈ s.calls, ∀ name, c.task = some name → ∀ e ∈ s.executions, e.id = c.owner →
    (∀ tk ∈ e.tasks, tk.name = name → c.input = tk.input) ∧
    ∀ spec, s.taskSpec p e name = .ok spec → c.timeout = spec.timeout ∧ c.policy = spec.policy ∧
      ∃ f decl, spec.body = .function f ∧ p.function? f = some decl ∧ c.target = .function f ∧
        c.stream = (decl.output.kind == .stream)
  invRun : ∀ r ∈ s.runs, r.task = none → ∀ i ∈ s.invocations, r.owner = some i.id → r.input = i.input
  taskRun : ∀ r ∈ s.runs, ∀ name, r.task = some name → ∀ e ∈ s.executions, r.owner = some e.id →
    (∀ tk ∈ e.tasks, tk.name = name → r.input = tk.input) ∧
    ∀ spec, s.taskSpec p e name = .ok spec → ∃ out, spec.body = .workflow r.workflow out
  exec : ∀ e ∈ s.executions, ∀ i ∈ s.invocations, i.id = e.id → e.input = i.input
  names : ∀ e ∈ s.executions, ∀ cc, s.concurrencyOf p e = .ok cc → e.tasks.map (·.name) = cc.tasks.map (·.name)
  pending : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status = .pending → tk.input = none
  failed : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status = .failed → Justified p s e tk.name

/-! ### Lookups that a step keeps -/

/-- Calls and runs are never removed, so a task that has not begun after a step had not begun before. -/
theorem notBegun_back (hk : Delivery.Kept s t) {e e' : Execution} (hid : e'.id = e.id) {name : String}
    (h : NotBegun t e' name) : NotBegun s e name := by
  obtain ⟨hc, hr⟩ := h
  refine ⟨?_, fun r hr₀ hro => ?_⟩
  · rcases hcs : s.call? (Key.task e.id name) with _ | c
    · rfl
    · exfalso
      have h' := hk.grows.call?_isSome (id := Key.task e.id name) (by rw [hcs]; rfl)
      rw [← hid, hc] at h'
      cases h'
  · obtain ⟨r', hr', -, -, -, ho, htk, -⟩ := hk.run r hr₀
    exact hr r' hr' ⟨by rw [ho, hro.1, hid], by rw [htk, hro.2]⟩

theorem Justified.kept (hk : Delivery.Kept s t) (wk : t.WellKeyed) {e e' : Execution} (hid : e'.id = e.id)
    (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) {name : String}
    (h : Justified p s e name) : Justified p t e' name := by
  rcases h with h | ⟨spec, tid, hspec, hin⟩
  · exact Or.inl fun h' => h (notBegun_back hk hid h')
  · exact Or.inr ⟨spec, tid, hk.taskSpec wk hrun hpl hspec, hin⟩

/-- A task with a call began. -/
theorem justified_of_call {e : Execution} {name : String} {c : Call} (hc : c ∈ s.calls)
    (hid : c.id = Key.task e.id name) : Justified p s e name := by
  refine Or.inl fun h => ?_
  exact State.call?_eq_none_iff.mp h.1 (List.mem_map.mpr ⟨c, hc, hid⟩)

/-- A task with a run began. -/
theorem justified_of_run {e : Execution} {name : String} {r : Run} (hr : r ∈ s.runs)
    (ho : r.owner = some e.id) (htk : r.task = some name) : Justified p s e name :=
  Or.inl fun h => h.2 r hr ⟨ho, htk⟩

/-! ### Steps that create nothing -/

/-- How a task may change in a step that creates nothing: its input only when it leaves pending, it
    becomes pending never, and failed only when it began or has a declared input transform. -/
def TaskMove (p : Definition) (t : State) (e : Execution) (tk₀ tk : TaskState) : Prop :=
  tk₀.name = tk.name ∧ (tk₀.input = tk.input ∨ tk₀.status = .pending) ∧
  (tk.status = .pending → tk₀.status = .pending ∧ tk₀.input = tk.input) ∧
  (tk.status = .failed → tk₀.status = .failed ∨ Justified p t e tk.name)

theorem TaskMove.refl {e : Execution} (tk : TaskState) : TaskMove p t e tk tk :=
  ⟨rfl, Or.inl rfl, fun h => ⟨h, rfl⟩, fun h => Or.inl h⟩

/-- Every record after the step is a record from before with the same fixed fields. -/
structure Frame (p : Definition) (s t : State) : Prop where
  kept : Delivery.Kept s t
  calls : ∀ c ∈ t.calls, ∃ c₀ ∈ s.calls, callFix c₀ = callFix c
  invocations : ∀ i ∈ t.invocations, Delivery.InvOld s i
  runs : ∀ r ∈ t.runs, ∃ r₀ ∈ s.runs, r₀.path = r.path ∧ r₀.workflow = r.workflow ∧ r₀.input = r.input ∧
    r₀.owner = r.owner ∧ r₀.task = r.task
  executions : ∀ e ∈ t.executions, ∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.run = e.run ∧
    e₀.placement = e.placement ∧ e₀.input = e.input ∧ e₀.tasks.map (·.name) = e.tasks.map (·.name) ∧
    ∀ tk ∈ e.tasks, ∃ tk₀ ∈ e₀.tasks, TaskMove p t e tk₀ tk

theorem Frame.trans (h₁ : Frame p s u) (h₂ : Frame p u t) (wk : t.WellKeyed) : Frame p s t where
  kept := h₁.kept.trans h₂.kept
  calls c hc := by
    obtain ⟨c₁, hc₁, e₁⟩ := h₂.calls c hc
    obtain ⟨c₀, hc₀, e₀⟩ := h₁.calls c₁ hc₁
    exact ⟨c₀, hc₀, e₀.trans e₁⟩
  invocations i hi := by
    obtain ⟨i₁, hi₁, a1, a2, a3, a4, a5⟩ := h₂.invocations i hi
    obtain ⟨i₀, hi₀, b1, b2, b3, b4, b5⟩ := h₁.invocations i₁ hi₁
    exact ⟨i₀, hi₀, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩
  runs r hr := by
    obtain ⟨r₁, hr₁, a1, a2, a3, a4, a5⟩ := h₂.runs r hr
    obtain ⟨r₀, hr₀, b1, b2, b3, b4, b5⟩ := h₁.runs r₁ hr₁
    exact ⟨r₀, hr₀, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩
  executions e he := by
    obtain ⟨e₁, he₁, a1, a2, a3, a4, a5, a6⟩ := h₂.executions e he
    obtain ⟨e₀, he₀, b1, b2, b3, b4, b5, b6⟩ := h₁.executions e₁ he₁
    refine ⟨e₀, he₀, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, fun tk htk => ?_⟩
    obtain ⟨tk₁, htk₁, m1, m2, m3, m4⟩ := a6 tk htk
    obtain ⟨tk₀, htk₀, n1, n2, n3, n4⟩ := b6 tk₁ htk₁
    refine ⟨tk₀, htk₀, n1.trans m1, ?_, fun hp => ?_, fun hf => ?_⟩
    · rcases m2 with m2 | m2
      · rcases n2 with n2 | n2
        · exact Or.inl (n2.trans m2)
        · exact Or.inr n2
      · exact Or.inr (n3 m2).1
    · obtain ⟨hp₁, hi₁⟩ := m3 hp
      obtain ⟨hp₀, hi₀⟩ := n3 hp₁
      exact ⟨hp₀, hi₀.trans hi₁⟩
    · rcases m4 hf with hf₁ | hj
      · rcases n4 hf₁ with hf₀ | hj
        · exact Or.inl hf₀
        · refine Or.inr ?_
          rw [← m1]
          exact hj.kept h₂.kept wk a1.symm a2.symm a3.symm
      · exact Or.inr hj

/-- Steps that keep every record that `Created` reads. -/
theorem Frame.of_eq (hk : Delivery.Kept s t) (hc : t.calls = s.calls) (hi : t.invocations = s.invocations)
    (hr : t.runs = s.runs) (he : t.executions = s.executions) : Frame p s t where
  kept := hk
  calls c h := ⟨c, hc ▸ h, rfl⟩
  invocations _ h := Delivery.invOld_self (hi ▸ h)
  runs r h := ⟨r, hr ▸ h, rfl, rfl, rfl, rfl, rfl⟩
  executions e h := ⟨e, he ▸ h, rfl, rfl, rfl, rfl, rfl, fun tk htk => ⟨tk, htk, TaskMove.refl tk⟩⟩

/-- Lookups that read only the runs. -/
theorem taskSpec_of_runs (h : t.runs = s.runs) {e : Execution} {name : String} :
    t.taskSpec p e name = s.taskSpec p e name := by
  simp [State.taskSpec, State.concurrencyOf, State.placementOf, State.workflow?, State.run?, h]

theorem Justified.congr {e : Execution} {name : String} (h : Justified p s e name) (hc : t.calls = s.calls)
    (hr : t.runs = s.runs) : Justified p t e name := by
  rcases h with h | ⟨spec, tid, hspec, hin⟩
  · refine Or.inl fun ⟨h1, h2⟩ => h ⟨?_, fun r hr' => h2 r (hr ▸ hr')⟩
    unfold State.call? at h1 ⊢
    rw [← hc]
    exact h1
  · exact Or.inr ⟨spec, tid, by rw [taskSpec_of_runs hr]; exact hspec, hin⟩

/-- A frame to a state with the same records, kept from the start. -/
theorem Frame.congr (F : Frame p s u) (hk : Delivery.Kept s t) (hc : t.calls = u.calls)
    (hi : t.invocations = u.invocations) (hr : t.runs = u.runs) (he : t.executions = u.executions) :
    Frame p s t where
  kept := hk
  calls c h := F.calls c (hc ▸ h)
  invocations i h := F.invocations i (hi ▸ h)
  runs r h := F.runs r (hr ▸ h)
  executions e h := by
    obtain ⟨e₀, he₀, a1, a2, a3, a4, a5, a6⟩ := F.executions e (he ▸ h)
    refine ⟨e₀, he₀, a1, a2, a3, a4, a5, fun tk htk => ?_⟩
    obtain ⟨tk₀, htk₀, m1, m2, m3, m4⟩ := a6 tk htk
    exact ⟨tk₀, htk₀, m1, m2, m3, fun hf => (m4 hf).imp id fun hj => hj.congr hc hr⟩

/-! ### Elementary updates -/

theorem Frame.setCall (wk : s.WellKeyed) {c c' : Call} (hc : c ∈ s.calls) (hfix : callFix c = callFix c')
    (hne : c.status.ended = false) : Frame p s (s.setCall c') := by
  obtain ⟨f1, f2, f3, f4, -, f6, -, -⟩ := callFix_eq hfix
  refine ⟨Delivery.Kept.setCall f1.symm f2.symm f3.symm f4.symm f6.symm hne wk hc, fun x hx => ?_,
    fun i h => Delivery.invOld_self h, fun r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩,
    fun e h => ⟨e, h, rfl, rfl, rfl, rfl, rfl, fun tk htk => ⟨tk, htk, TaskMove.refl tk⟩⟩⟩
  rcases State.mem_setCall_calls hx with rfl | hx
  · exact ⟨c, hc, hfix⟩
  · exact ⟨x, hx, rfl⟩

theorem Frame.setInvocation (wk : s.WellKeyed) {i i' : Invocation} (hi : i ∈ s.invocations) (hid : i'.id = i.id)
    (hrun : i'.run = i.run) (hpl : i'.placement = i.placement) (htr : i'.trigger = i.trigger)
    (hin : i'.input = i.input) : Frame p s (s.setInvocation i') := by
  refine ⟨Delivery.Kept.setInvocation hid hrun hpl htr hin wk hi, fun c h => ⟨c, h, rfl⟩, fun x hx => ?_,
    fun r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩,
    fun e h => ⟨e, h, rfl, rfl, rfl, rfl, rfl, fun tk htk => ⟨tk, htk, TaskMove.refl tk⟩⟩⟩
  rcases State.mem_setInvocation_invocations hx with rfl | hx
  · exact ⟨i, hi, hid.symm, hrun.symm, hpl.symm, htr.symm, hin.symm⟩
  · exact Delivery.invOld_self hx

theorem Frame.setRun (wk : s.WellKeyed) {r : Run} (hr : r ∈ s.runs) (b : Bool) (hb : r.complete = true → b = true) :
    Frame p s (s.setRun { r with complete := b }) := by
  refine ⟨Delivery.Kept.setRun wk hr b hb, fun c h => ⟨c, h, rfl⟩, fun i h => Delivery.invOld_self h,
    fun x hx => ?_, fun e h => ⟨e, h, rfl, rfl, rfl, rfl, rfl, fun tk htk => ⟨tk, htk, TaskMove.refl tk⟩⟩⟩
  rcases State.mem_setRun_runs hx with rfl | hx
  · exact ⟨r, hr, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨x, hx, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.setExecution (wk : s.WellKeyed) {e : Execution} (he : e ∈ s.executions) (b : Bool)
    (hb : e.complete = true → b = true) : Frame p s (s.setExecution { e with complete := b }) := by
  refine ⟨Delivery.Kept.setExecution (e := e) rfl rfl rfl rfl hb wk he, fun c h => ⟨c, h, rfl⟩,
    fun i h => Delivery.invOld_self h, fun r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩, fun x hx => ?_⟩
  rcases State.mem_setExecution_executions hx with rfl | hx
  · exact ⟨e, he, rfl, rfl, rfl, rfl, rfl, fun tk htk => ⟨tk, htk, TaskMove.refl tk⟩⟩
  · exact ⟨x, hx, rfl, rfl, rfl, rfl, rfl, fun tk htk => ⟨tk, htk, TaskMove.refl tk⟩⟩

theorem Frame.setTask (wk : s.WellKeyed) {e : Execution} {ts ts' : TaskState} (he : e ∈ s.executions)
    (hts : ts ∈ e.tasks) (hmove : TaskMove p (s.setTask e ts') (withTask e ts') ts ts') :
    Frame p s (s.setTask e ts') := by
  refine ⟨Delivery.Kept.setTask ts' wk he, fun c h => ⟨c, h, rfl⟩, fun i h => Delivery.invOld_self h,
    fun r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩, fun x hx => ?_⟩
  rcases State.mem_setTask_executions hx with rfl | hx
  · refine ⟨e, he, rfl, rfl, rfl, rfl, (Delivery.Kept.withTask_names e ts').symm, fun tk htk => ?_⟩
    rcases Delivery.mem_withTask htk with rfl | ⟨htk, -⟩
    · exact ⟨ts, hts, hmove⟩
    · exact ⟨tk, htk, TaskMove.refl tk⟩
  · exact ⟨x, hx, rfl, rfl, rfl, rfl, rfl, fun tk htk => ⟨tk, htk, TaskMove.refl tk⟩⟩

theorem callFix_stopCall (c : Call) : callFix (stopCall c) = callFix c := by
  unfold stopCall
  split <;> rfl

theorem Frame.stop : Frame p s s.stop := by
  refine ⟨Delivery.Kept.stop s, fun x hx => ?_, fun i h => Delivery.invOld_self h,
    fun r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩, fun x hx => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := State.mem_stop_calls.mp hx
    exact ⟨c, hc, (callFix_stopCall c).symm⟩
  · obtain ⟨e, he, rfl⟩ := State.mem_stop_executions.mp hx
    refine ⟨e, he, rfl, rfl, rfl, rfl, ?_, fun tk htk => ?_⟩
    · rw [Limit.stopExecution_tasks, List.map_map]
      exact List.map_congr_left fun x _ => by simp
    · rw [Limit.stopExecution_tasks] at htk
      obtain ⟨tk₀, htk₀, rfl⟩ := List.mem_map.mp htk
      refine ⟨tk₀, htk₀, ?_⟩
      by_cases hc : (tk₀.status == .pending || tk₀.status == .ready) = true
      · have e : Limit.stopTask tk₀ = { tk₀ with status := .notStarted } := by simp [Limit.stopTask, hc]
        rw [e]
        refine ⟨rfl, Or.inl rfl, ?_, ?_⟩ <;> intro h <;> cases h
      · have e : Limit.stopTask tk₀ = tk₀ := by simp [Limit.stopTask, hc]
        rw [e]
        exact TaskMove.refl tk₀

/-- The conclusion after a stop ends the tasks that have not ended, keeping their inputs; it fails
    none and makes none pending. -/
theorem Frame.endUnfinished : Frame p s s.endUnfinished := by
  refine ⟨Delivery.Kept.endUnfinished s, fun c h => ⟨c, h, rfl⟩, fun i h => Delivery.invOld_endUnfinished h,
    fun r h => ⟨r, h, rfl, rfl, rfl, rfl, rfl⟩, fun x hx => ?_⟩
  obtain ⟨e, he, rfl⟩ := State.mem_endUnfinished_executions.mp hx
  refine ⟨e, he, rfl, rfl, rfl, rfl, ?_, fun tk htk => ?_⟩
  · rw [endExecution_tasks, List.map_map]
    exact List.map_congr_left fun x _ => by simp
  · rw [endExecution_tasks] at htk
    obtain ⟨tk₀, htk₀, rfl⟩ := List.mem_map.mp htk
    refine ⟨tk₀, htk₀, by simp, Or.inl (by simp), fun h => ?_, fun h => Or.inl ?_⟩
    · have hend := endTask_ended (t := tk₀)
      rw [h] at hend
      cases hend
    · rw [endTask_status] at h
      split at h
      · cases h
      · split at h
        · cases h
        · exact h

theorem Frame.fail (wk : s.WellKeyed) (f : Failure) (policy : Policy) : Frame p s (s.fail f policy) := by
  have h : Frame p s { s with failures := s.failures ++ [f] } :=
    Frame.of_eq (Delivery.Kept.of_eq rfl rfl rfl rfl rfl rfl rfl rfl ⟨[f], rfl⟩) rfl rfl rfl rfl
  cases policy
  · exact h.trans Frame.stop ((wk.fail f .stop))
  · exact h

theorem Frame.accept {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : Frame p s t := by
  obtain ⟨-, -, -, hr, hi, hc, he, -⟩ := accept_frame h
  exact Frame.of_eq (Delivery.accept_kept h) hc hi hr he

/-- Settling the owner of a call: an invocation, or a task that has the call. -/
theorem Frame.settleOwner (wk : s.WellKeyed) {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : s.settleOwner c inv task = .ok t) (hnp : task ≠ .pending)
    (hcall : ∀ name, c.task = some name → task = .failed → ∃ c' ∈ s.calls, c'.id = Key.task c.owner name) :
    Frame p s t := by
  rcases State.settleOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨name, e, ts, htask, he, hts, rfl⟩
  · exact Frame.setInvocation wk (State.invocation?_eq_some hi).1 rfl rfl rfl rfl rfl
  · obtain ⟨hem, hid⟩ := State.execution?_eq_some he
    have hname := Delivery.find?_name_of_task hts
    refine Frame.setTask wk hem (List.mem_of_find?_eq_some hts)
      ⟨rfl, Or.inl rfl, fun hp => absurd hp hnp, fun hf => Or.inr ?_⟩
    obtain ⟨c', hc', hc'id⟩ := hcall name htask hf
    exact justified_of_call (s := s.setTask e _) hc' (by rw [hc'id, withTask_id, hid, hname])

/-- Cancelling the owner of a cancelled call. -/
theorem Frame.cancelOwner (wk : s.WellKeyed) {c : Call} (h : s.cancelOwner c = .ok t) : Frame p s t := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨name, e, ts, -, he, hts, rfl⟩ <;> split
  · exact Frame.setInvocation wk (State.invocation?_eq_some hi).1 rfl rfl rfl rfl rfl
  · exact Frame.of_eq (Delivery.Kept.refl s) rfl rfl rfl rfl
  · refine Frame.setTask wk (State.execution?_eq_some he).1 (List.mem_of_find?_eq_some hts) ?_
    refine ⟨rfl, Or.inl rfl, ?_, ?_⟩ <;> intro h <;> cases h
  · exact Frame.of_eq (Delivery.Kept.refl s) rfl rfl rfl rfl

/-- A call fails: its status changes, its owner fails, and a stop policy stops the workflow. -/
theorem Frame.failCall (wk : s.WellKeyed) (lim : Limit.Inv s) {c : Call} {status : CallStatus} {cause : Cause}
    (hc : c ∈ s.calls) (hne : c.status.ended = false) (h : s.failCall c status cause = .ok t) : Frame p s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  have wk₁ := wk.setCall { c with status }
  have wk₂ := wk₁.settleOwner hso
  have F₁ : Frame p s (s.setCall { c with status }) := Frame.setCall wk hc rfl hne
  have F₂ : Frame p (s.setCall { c with status }) s' := by
    refine Frame.settleOwner wk₁ hso (by simp) fun name htask _ => ⟨{ c with status }, ?_, ?_⟩
    · exact Limit.mem_setCall_self hc rfl
    · exact lim.keys c hc name htask
  exact (F₁.trans F₂ wk₂).trans (Frame.fail wk₂ f c.policy) (wk₂.fail f c.policy)

/-! ### The frame keeps `Created` -/

theorem Created.of_frame (hC : Created p s) (inv : Delivery.Inv p s) (lim : Limit.Inv s) (wk : t.WellKeyed)
    (F : Frame p s t) : Created p t := by
  -- Lookups of stored records read the same after the step.
  have wf : ∀ i₀ ∈ s.invocations, ∀ {w}, t.workflow? p i₀.run = some w → s.workflow? p i₀.run = some w := by
    intro i₀ hi₀ w hw
    obtain ⟨-, w₀, -, -, hw₀, -⟩ := inv.own.invocations i₀ hi₀
    rw [F.kept.workflow? wk hw₀] at hw
    rw [hw₀, hw]
  have conc : ∀ e₀ ∈ s.executions, ∀ {e : Execution}, e.run = e₀.run → e.placement = e₀.placement →
      ∀ {cc}, t.concurrencyOf p e = .ok cc → s.concurrencyOf p e₀ = .ok cc := by
    intro e₀ he₀ e hrun hpl cc h
    obtain ⟨-, -, -, -, -, cc₀, hcc₀⟩ := inv.own.executions e₀ he₀
    rw [F.kept.concurrencyOf wk hrun hpl hcc₀] at h
    cases h
    exact hcc₀
  have spec : ∀ e₀ ∈ s.executions, ∀ {e : Execution}, e.run = e₀.run → e.placement = e₀.placement →
      ∀ {name sp}, t.taskSpec p e name = .ok sp → s.taskSpec p e₀ name = .ok sp := by
    intro e₀ he₀ e hrun hpl name sp h
    obtain ⟨cc, hcc, hf⟩ := State.taskSpec_eq_ok.mp h
    exact State.taskSpec_eq_ok.mpr ⟨cc, conc e₀ he₀ hrun hpl hcc, hf⟩
  -- The task of a call or a run began, so its input did not change.
  have begunInput : ∀ e₀ ∈ s.executions, ∀ tk₀ ∈ e₀.tasks, (∃ c ∈ s.calls, c.task = some tk₀.name ∧ c.owner = e₀.id) ∨
      (∃ r ∈ s.runs, r.task = some tk₀.name ∧ r.owner = some e₀.id) → tk₀.status ≠ .pending := by
    intro e₀ he₀ tk₀ htk₀ h hp
    have hb : ¬ Limit.Begun tk₀.status := fun hb => hb.1 hp
    rcases h with ⟨c, hc, htask, ho⟩ | ⟨r, hr, htask, ho⟩
    · exact lim.no_call he₀ htk₀ hb c hc htask ho
    · exact lim.no_run he₀ htk₀ hb r hr htask ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc htask i hi hid
    obtain ⟨c₀, hc₀, hfix⟩ := F.calls c hc
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := callFix_eq hfix
    obtain ⟨i₀, hi₀, a1, a2, a3, a4, a5⟩ := F.invocations i hi
    obtain ⟨h1, h2⟩ := hC.invCall c₀ hc₀ (f3.trans htask) i₀ hi₀ (a1.trans (hid.trans f2.symm))
    refine ⟨f5.symm.trans (h1.trans a5), fun w pl hw hpl => ?_⟩
    rw [← a2] at hw
    rw [← a3] at hpl
    obtain ⟨h3, h4⟩ := h2 w pl (wf i₀ hi₀ hw) hpl
    exact ⟨f7.symm.trans h3, f8.symm.trans h4⟩
  · intro c hc name htask e he hid
    obtain ⟨c₀, hc₀, hfix⟩ := F.calls c hc
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := callFix_eq hfix
    obtain ⟨e₀, he₀, a1, a2, a3, a4, a5, a6⟩ := F.executions e he
    obtain ⟨h1, h2⟩ := hC.taskCall c₀ hc₀ name (f3.trans htask) e₀ he₀ (a1.trans (hid.trans f2.symm))
    refine ⟨fun tk htk hname => ?_, fun sp hsp => ?_⟩
    · obtain ⟨tk₀, htk₀, m1, m2, -, -⟩ := a6 tk htk
      rcases m2 with m2 | m2
      · rw [f5.symm, h1 tk₀ htk₀ (m1.trans hname), m2]
      · exact absurd m2 (begunInput e₀ he₀ tk₀ htk₀
          (Or.inl ⟨c₀, hc₀, by rw [f3, htask, m1, hname], by rw [f2, ← hid, a1]⟩))
    · obtain ⟨h3, h4, f, decl, h5, h6, h7, h8⟩ := h2 sp (spec e₀ he₀ a2.symm a3.symm hsp)
      exact ⟨f7.symm.trans h3, f8.symm.trans h4, f, decl, h5, h6, f4.symm.trans h7, f6.symm.trans h8⟩
  · intro r hr htask i hi ho
    obtain ⟨r₀, hr₀, b1, b2, b3, b4, b5⟩ := F.runs r hr
    obtain ⟨i₀, hi₀, a1, a2, a3, a4, a5⟩ := F.invocations i hi
    rw [← b3, hC.invRun r₀ hr₀ (b5.trans htask) i₀ hi₀ (by rw [b4, ho, a1]), a5]
  · intro r hr name htask e he ho
    obtain ⟨r₀, hr₀, b1, b2, b3, b4, b5⟩ := F.runs r hr
    obtain ⟨e₀, he₀, a1, a2, a3, a4, a5, a6⟩ := F.executions e he
    obtain ⟨h1, h2⟩ := hC.taskRun r₀ hr₀ name (b5.trans htask) e₀ he₀ (by rw [b4, ho, a1])
    refine ⟨fun tk htk hname => ?_, fun sp hsp => ?_⟩
    · obtain ⟨tk₀, htk₀, m1, m2, -, -⟩ := a6 tk htk
      rcases m2 with m2 | m2
      · rw [← b3, h1 tk₀ htk₀ (m1.trans hname), m2]
      · exact absurd m2 (begunInput e₀ he₀ tk₀ htk₀
          (Or.inr ⟨r₀, hr₀, by rw [b5, htask, m1, hname], by rw [b4, ho, a1]⟩))
    · obtain ⟨out, hout⟩ := h2 sp (spec e₀ he₀ a2.symm a3.symm hsp)
      exact ⟨out, by rw [hout, b2]⟩
  · intro e he i hi hid
    obtain ⟨e₀, he₀, a1, a2, a3, a4, a5, a6⟩ := F.executions e he
    obtain ⟨i₀, hi₀, b1, b2, b3, b4, b5⟩ := F.invocations i hi
    rw [← a4, hC.exec e₀ he₀ i₀ hi₀ (by rw [b1, hid, a1]), b5]
  · intro e he cc hcc
    obtain ⟨e₀, he₀, a1, a2, a3, a4, a5, a6⟩ := F.executions e he
    rw [← a5, hC.names e₀ he₀ cc (conc e₀ he₀ a2.symm a3.symm hcc)]
  · intro e he tk htk hp
    obtain ⟨e₀, he₀, a1, a2, a3, a4, a5, a6⟩ := F.executions e he
    obtain ⟨tk₀, htk₀, m1, -, m3, -⟩ := a6 tk htk
    obtain ⟨hp₀, hin⟩ := m3 hp
    rw [← hin]
    exact hC.pending e₀ he₀ tk₀ htk₀ hp₀
  · intro e he tk htk hf
    obtain ⟨e₀, he₀, a1, a2, a3, a4, a5, a6⟩ := F.executions e he
    obtain ⟨tk₀, htk₀, m1, -, -, m4⟩ := a6 tk htk
    rcases m4 hf with hf₀ | hj
    · rw [← m1]
      exact (hC.failed e₀ he₀ tk₀ htk₀ hf₀).kept F.kept wk a1.symm a2.symm a3.symm
    · exact hj

end CoversOpsAux
end Suimon.Round3
