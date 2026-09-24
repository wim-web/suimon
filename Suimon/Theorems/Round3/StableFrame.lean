import Suimon.Theorems.Round3.Conformance

/-! Helpers for `Round3/Stable.lean` (task E4): which step completes an execution or a run, and the
    task results a step keeps with their values. -/

namespace Suimon.Round3.StableAux
open State

section StableFrame
variable {p : Definition} {s t u : State} {op : Op}

/-! ### Lists -/

theorem nodup_of_map' {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ hne heq => hne (heq ▸ rfl)) h

theorem nodup_filter' {α : Type} (P : α → Bool) {l : List α} (h : l.Nodup) : (l.filter P).Nodup :=
  List.Pairwise.filter P h

theorem nodup_map_on' {α β : Type} {f : α → β} {l : List α} (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (h : l.Nodup) : (l.map f).Nodup :=
  List.pairwise_map.mpr (h.imp_of_mem fun hx hy hne hf => hne (hinj _ hx _ hy hf))

/-- A filter of a list extended at the end keeps its value when every new member passing the filter
    was already there: with no duplicates, the extension adds none. -/
theorem filter_prefix_eq {α : Type} {l₁ l₂ : List α} (hp : l₁ <+: l₂) (hnd : l₂.Nodup) {P : α → Bool}
    (hback : ∀ a ∈ l₂, P a = true → a ∈ l₁) : l₂.filter P = l₁.filter P := by
  obtain ⟨l, rfl⟩ := hp
  rw [List.filter_append]
  suffices h : l.filter P = [] by rw [h, List.append_nil]
  rw [List.filter_eq_nil_iff]
  intro a ha hPa
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd
  exact hdisj a (hback a (List.mem_append_right _ ha) hPa) a ha rfl

/-! ### Complete executions -/

/-- Every complete execution of `t` was complete in `s`, under the same identity. -/
def ExecsFrom (s t : State) : Prop :=
  ∀ e ∈ t.executions, e.complete = true → ∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.complete = true

namespace ExecsFrom

theorem of_eq (h : t.executions = s.executions) : ExecsFrom s t :=
  fun e he hc => ⟨e, h ▸ he, rfl, hc⟩

theorem trans (h₁ : ExecsFrom s t) (h₂ : ExecsFrom t u) : ExecsFrom s u := by
  intro e he hc
  obtain ⟨e₁, he₁, hid₁, hc₁⟩ := h₂ e he hc
  obtain ⟨e₀, he₀, hid₀, hc₀⟩ := h₁ e₁ he₁ hc₁
  exact ⟨e₀, he₀, hid₀.trans hid₁, hc₀⟩

theorem append {l : List Execution} (h : t.executions = s.executions ++ l) (hl : ∀ e ∈ l, e.complete = false) :
    ExecsFrom s t := by
  intro e he hc
  rw [h, List.mem_append] at he
  rcases he with he | he
  · exact ⟨e, he, rfl, hc⟩
  · rw [hl e he] at hc; cases hc

theorem setTask {e₁ : Execution} {ts : TaskState} (he₁ : e₁ ∈ s.executions) : ExecsFrom s (s.setTask e₁ ts) := by
  intro e he hc
  rcases mem_setTask_executions he with rfl | he
  · exact ⟨e₁, he₁, rfl, hc⟩
  · exact ⟨e, he, rfl, hc⟩

theorem stop : ExecsFrom s s.stop := by
  intro e he hc
  obtain ⟨e₀, he₀, rfl⟩ := mem_stop_executions.mp he
  exact ⟨e₀, he₀, rfl, hc⟩

theorem endUnfinished : ExecsFrom s s.endUnfinished := by
  intro e he hc
  obtain ⟨e₀, he₀, rfl⟩ := mem_endUnfinished_executions.mp he
  exact ⟨e₀, he₀, rfl, hc⟩

theorem fail {f : Failure} {policy : Policy} : ExecsFrom s (s.fail f policy) := by
  cases policy
  · rw [fail_stop]; exact (of_eq rfl).trans stop
  · exact of_eq rfl

theorem settleOwner {c : Call} {inv : InvocationStatus} {task : TaskStatus} (h : s.settleOwner c inv task = .ok t) :
    ExecsFrom s t := by
  rcases settleOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨_, e, _, -, he, -, rfl⟩
  · exact of_eq rfl
  · exact setTask (execution?_eq_some he).1

theorem cancelOwner {c : Call} (h : s.cancelOwner c = .ok t) : ExecsFrom s t := by
  rcases cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨_, e, _, -, he, -, rfl⟩ <;> split
  · exact of_eq rfl
  · exact of_eq rfl
  · exact setTask (execution?_eq_some he).1
  · exact of_eq rfl

/-- `settleOwner` on a state with the executions of `s`. -/
theorem settleOwner' {c : Call} {inv : InvocationStatus} {task : TaskStatus} (h : u.settleOwner c inv task = .ok t)
    (hu : u.executions = s.executions) : ExecsFrom s t :=
  (of_eq hu).trans (settleOwner h)

/-- `cancelOwner` on a state with the executions of `s`. -/
theorem cancelOwner' {c : Call} (h : u.cancelOwner c = .ok t) (hu : u.executions = s.executions) : ExecsFrom s t :=
  (of_eq hu).trans (cancelOwner h)

theorem failCall {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    ExecsFrom s t := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  exact (settleOwner' hso rfl).trans fail

end ExecsFrom

/-- Only `closeExecution` completes an execution. -/
theorem step_execsFrom (hs : step p s op = .ok t) : ExecsFrom s t ∨ ∃ eid, op = .closeExecution eid := by
  cases op with
  | closeExecution eid => exact Or.inr ⟨eid, rfl⟩
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact Or.inl (ExecsFrom.of_eq rfl)
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    refine Or.inl ?_
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact ExecsFrom.of_eq rfl
    · exact ExecsFrom.of_eq rfl
    · exact ExecsFrom.of_eq rfl
    · exact ExecsFrom.append rfl (by simp)
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact Or.inl (ExecsFrom.of_eq rfl)
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact Or.inl (ExecsFrom.settleOwner' hso (accept_frame hacc).2.2.2.2.2.2.1)
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact Or.inl (ExecsFrom.of_eq (by simp [(accept_frame hacc).2.2.2.2.2.2.1]))
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact Or.inl (ExecsFrom.of_eq (by simp [(accept_frame hacc).2.2.2.2.2.2.1]))
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact Or.inl (ExecsFrom.settleOwner' hso rfl)
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact Or.inl (ExecsFrom.failCall h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact Or.inl (ExecsFrom.failCall h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact Or.inl (ExecsFrom.failCall h)
    · exact Or.inl (ExecsFrom.cancelOwner' h rfl)
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact Or.inl (ExecsFrom.cancelOwner' h rfl)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact Or.inl (ExecsFrom.of_eq rfl)
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Or.inl ((ExecsFrom.of_eq rfl).trans ExecsFrom.fail)
  | taskInput eid name value =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Or.inl (ExecsFrom.setTask (execution?_eq_some he).1)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact Or.inl ((ExecsFrom.setTask (execution?_eq_some he).1).trans ExecsFrom.fail)
  | beginTask eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;>
      exact Or.inl ((ExecsFrom.setTask (execution?_eq_some he).1).trans (ExecsFrom.of_eq rfl))
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact Or.inl (ExecsFrom.of_eq rfl)
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Or.inl ((ExecsFrom.of_eq rfl).trans ExecsFrom.fail)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact Or.inl (ExecsFrom.of_eq rfl)
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, e, _, -, he, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact Or.inl (ExecsFrom.of_eq rfl)
    · have he' : e ∈ (s.setRun { ‹Run› with complete := true }).executions := (execution?_eq_some he).1
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact Or.inl (((ExecsFrom.of_eq rfl).trans (ExecsFrom.setTask he')).trans (ExecsFrom.of_eq rfl))
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact Or.inl (ExecsFrom.stop.trans (ExecsFrom.of_eq rfl))
    · exact Or.inl (ExecsFrom.of_eq rfl)
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact Or.inl (ExecsFrom.of_eq rfl)
    · exact Or.inl (ExecsFrom.endUnfinished.trans (ExecsFrom.of_eq rfl))

/-- A complete execution after a step was complete before it, or this step closed it. -/
theorem exec_complete_cases (hs : step p s op = .ok t) {e : Execution} (he : e ∈ t.executions)
    (hc : e.complete = true) :
    (∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.complete = true) ∨ op = .closeExecution e.id := by
  rcases step_execsFrom hs with h | ⟨eid, rfl⟩
  · exact Or.inl (h e he hc)
  · obtain ⟨-, -, e₁, _, _, he₁, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    have hte : t.executions = (s.setExecution { e₁ with complete := true }).executions := by
      rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
    rw [hte, setExecution_executions] at he
    rcases Delivery.mem_map_replace' he with rfl | ⟨he, -⟩
    · exact Or.inr (by rw [(execution?_eq_some he₁).2])
    · exact Or.inl ⟨e, he, rfl, hc⟩

/-! ### Complete runs -/

/-- Every complete run of `t` was complete in `s`, under the same path. -/
def RunsFrom (s t : State) : Prop :=
  ∀ r ∈ t.runs, r.complete = true → ∃ r₀ ∈ s.runs, r₀.path = r.path ∧ r₀.complete = true

namespace RunsFrom

theorem of_eq (h : t.runs = s.runs) : RunsFrom s t :=
  fun r hr hc => ⟨r, h ▸ hr, rfl, hc⟩

theorem append {l : List Run} (h : t.runs = s.runs ++ l) (hl : ∀ r ∈ l, r.complete = false) : RunsFrom s t := by
  intro r hr hc
  rw [h, List.mem_append] at hr
  rcases hr with hr | hr
  · exact ⟨r, hr, rfl, hc⟩
  · rw [hl r hr] at hc; cases hc

end RunsFrom

/-- Only `closeRun` and `conclude` complete a run. -/
theorem step_runsFrom (hfresh : s.runs = [] ∨ s.started = true) (hs : step p s op = .ok t) :
    RunsFrom s t ∨ (∃ path, op = .closeRun path) ∨ op = .conclude := by
  cases op with
  | closeRun path => exact Or.inr (Or.inl ⟨path, rfl⟩)
  | conclude => exact Or.inr (Or.inr rfl)
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    have hnil : s.runs = [] := hfresh.resolve_right (by simp [hst])
    exact Or.inl (RunsFrom.append (l := [{ path := [], workflow := p.main, input }]) (by simp [hnil]) (by simp))
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    refine Or.inl ?_
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact RunsFrom.of_eq rfl
    · exact RunsFrom.of_eq rfl
    · exact RunsFrom.append rfl (by simp)
    · exact RunsFrom.of_eq rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact Or.inl (RunsFrom.of_eq rfl)
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact Or.inl (RunsFrom.of_eq (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1]))
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact Or.inl (RunsFrom.of_eq (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1]))
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact Or.inl (RunsFrom.of_eq (by rw [setCall_runs, (accept_frame hacc).2.2.2.1]))
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact Or.inl (RunsFrom.of_eq (by rw [(settleOwner_update hso).runs, setCall_runs]))
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact Or.inl (RunsFrom.of_eq (failCall_runs h))
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact Or.inl (RunsFrom.of_eq (failCall_runs h))
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact Or.inl (RunsFrom.of_eq (failCall_runs h))
    · exact Or.inl (RunsFrom.of_eq (by rw [(cancelOwner_update h).runs, setCall_runs]))
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact Or.inl (RunsFrom.of_eq (by rw [(cancelOwner_update h).runs, setCall_runs]))
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact Or.inl (RunsFrom.of_eq rfl)
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Or.inl (RunsFrom.of_eq (by simp))
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Or.inl (RunsFrom.of_eq rfl)
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact Or.inl (RunsFrom.of_eq (by simp))
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact Or.inl (RunsFrom.of_eq rfl)
    · exact Or.inl (RunsFrom.append rfl (by simp))
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact Or.inl (RunsFrom.of_eq rfl)
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Or.inl (RunsFrom.of_eq (by simp))
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact Or.inl (RunsFrom.of_eq rfl)
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact Or.inl (RunsFrom.of_eq rfl)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact Or.inl (RunsFrom.of_eq rfl)

/-- A complete run after a step was complete before it, or this step closed it (the root run closes
    with `conclude`). -/
theorem run_complete_cases (hfresh : s.runs = [] ∨ s.started = true) (hs : step p s op = .ok t) {r : Run}
    (hr : r ∈ t.runs) (hc : r.complete = true) :
    (∃ r₀ ∈ s.runs, r₀.path = r.path ∧ r₀.complete = true) ∨ op = .closeRun r.path ∨
      (op = .conclude ∧ r.path = []) := by
  rcases step_runsFrom hfresh hs with h | ⟨path, rfl⟩ | rfl
  · exact Or.inl (h r hr hc)
  · obtain ⟨-, -, r₁, _, _, _, _, hr₁, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    have htr : t.runs = (s.setRun { r₁ with complete := true }).runs := by
      rcases hcases with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
        rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    rw [htr, setRun_runs] at hr
    rcases Delivery.mem_map_replace' hr with rfl | ⟨hr, -⟩
    · exact Or.inr (Or.inl (by rw [(run?_eq_some hr₁).2]))
    · exact Or.inl ⟨r, hr, rfl, hc⟩
  · obtain ⟨-, ⟨-, r₁, _, hr₁, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have hr' : r ∈ (s.setRun { r₁ with complete := true }).runs := hr
      rw [setRun_runs] at hr'
      rcases Delivery.mem_map_replace' hr' with rfl | ⟨hr', -⟩
      · exact Or.inr (Or.inr ⟨rfl, (run?_eq_some hr₁).2⟩)
      · exact Or.inl ⟨r, hr', rfl, hc⟩
    · exact Or.inl ⟨r, hr, rfl, hc⟩

/-! ### Task result values -/

/-- Every task result of `s` survives in `t` with its key and value; only its output may change. -/
def ValuesKept (s t : State) : Prop :=
  ∀ tr ∈ s.taskResults, ∃ tr' ∈ t.taskResults, tr'.execution = tr.execution ∧ tr'.task = tr.task ∧
    tr'.index = tr.index ∧ tr'.value = tr.value

namespace ValuesKept

theorem of_eq (h : t.taskResults = s.taskResults) : ValuesKept s t :=
  fun tr htr => ⟨tr, h ▸ htr, rfl, rfl, rfl, rfl⟩

theorem append {l : List TaskResult} (h : t.taskResults = s.taskResults ++ l) : ValuesKept s t :=
  fun tr htr => ⟨tr, h ▸ List.mem_append_left _ htr, rfl, rfl, rfl, rfl⟩

theorem trans (h₁ : ValuesKept s t) (h₂ : ValuesKept t u) : ValuesKept s u := by
  intro tr htr
  obtain ⟨tr₁, htr₁, a1, a2, a3, a4⟩ := h₁ tr htr
  obtain ⟨tr₂, htr₂, b1, b2, b3, b4⟩ := h₂ tr₁ htr₁
  exact ⟨tr₂, htr₂, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

theorem setTaskResult (wk : s.WellKeyed) {r : TaskResult} (hr : r ∈ s.taskResults) (o : TaskOutput) :
    ValuesKept s (s.setTaskResult { r with output := o }) := by
  intro tr htr
  by_cases hk : tr.execution = r.execution ∧ tr.task = r.task ∧ tr.index = r.index
  · -- The replaced record is `r` itself, since keys are unique.
    have hkey : (tr.execution, tr.task, tr.index) = (r.execution, r.task, r.index) := by
      rw [hk.1, hk.2.1, hk.2.2]
    obtain rfl : tr = r := by
      have h1 := find?_eq_some_of_nodup wk.taskResults htr
        (P := fun y => (y.execution, y.task, y.index) == (r.execution, r.task, r.index)) (fun y => by simp [hkey])
      have h2 := find?_eq_some_of_nodup wk.taskResults hr
        (P := fun y => (y.execution, y.task, y.index) == (r.execution, r.task, r.index)) (fun y => by simp)
      exact Option.some.inj (h1.symm.trans h2)
    refine ⟨{ tr with output := o }, ?_, rfl, rfl, rfl, rfl⟩
    rw [setTaskResult_taskResults]
    exact List.mem_map.mpr ⟨tr, htr, by simp⟩
  · refine ⟨tr, ?_, rfl, rfl, rfl, rfl⟩
    rw [setTaskResult_taskResults]
    refine List.mem_map.mpr ⟨tr, htr, ?_⟩
    have : (tr.execution == r.execution && tr.task == r.task && tr.index == r.index) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      by_cases h1 : tr.execution = r.execution
      · by_cases h2 : tr.task = r.task
        · exact Or.inr fun h3 => hk ⟨h1, h2, h3⟩
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl h1)
    simp [this]

theorem accept {c : Call} {index : Nat} {value : Value} {arm : Option String} (h : s.accept c index value arm = .ok t) :
    ValuesKept s t := by
  rcases Delivery.accept_taskResults h with h | ⟨_, -, h⟩
  · exact of_eq h
  · exact append h

end ValuesKept

/-- A step changes a task result only by transforming its output: key and value stay. -/
theorem step_valuesKept (wk : s.WellKeyed) (hs : step p s op = .ok t) : ValuesKept s t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact ValuesKept.of_eq rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      exact ValuesKept.of_eq rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact ValuesKept.of_eq rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact (ValuesKept.accept hacc).trans
      (ValuesKept.of_eq (by rw [(settleOwner_update hso).taskResults, setCall_taskResults]))
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact (ValuesKept.accept hacc).trans (ValuesKept.of_eq rfl)
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (ValuesKept.accept hacc).trans (ValuesKept.of_eq rfl)
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact ValuesKept.of_eq (by rw [(settleOwner_update hso).taskResults, setCall_taskResults])
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact ValuesKept.of_eq (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact ValuesKept.of_eq (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact ValuesKept.of_eq (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
    · exact ValuesKept.of_eq (by rw [(cancelOwner_update h).taskResults, setCall_taskResults])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact ValuesKept.of_eq (by rw [(cancelOwner_update h).taskResults, setCall_taskResults])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact ValuesKept.of_eq rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact ValuesKept.of_eq (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact ValuesKept.of_eq rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact ValuesKept.of_eq (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact ValuesKept.of_eq rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, r, -, -, -, -, hr, -, h⟩ := Step.taskOutput_inv hs
    have k := ValuesKept.setTaskResult wk (List.mem_of_find?_eq_some hr) (.value value)
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact k.trans (ValuesKept.of_eq rfl)
    · exact k
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, hr, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (ValuesKept.setTaskResult wk (List.mem_of_find?_eq_some hr) .failed).trans (ValuesKept.of_eq (by simp))
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact ValuesKept.of_eq rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact ValuesKept.of_eq rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ValuesKept.of_eq rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ValuesKept.append rfl
      all_goals exact ValuesKept.of_eq rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact ValuesKept.of_eq rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact ValuesKept.of_eq rfl

/-! ### Lookups a step keeps -/

/-- The endpoint a run returns depends only on its owner and task. -/
theorem designatedOutput_congr {r r' : Run} (ho : r'.owner = r.owner) (ht : r'.task = r.task) :
    s.designatedOutput p r' = s.designatedOutput p r := by
  unfold State.designatedOutput
  rw [ho, ht]

/-- A step keeps the endpoint a run returns: its owner keeps its run and placement. -/
theorem designatedOutput_kept (K : Delivery.Kept s t) (wk' : t.WellKeyed) {r : Run} {out : String}
    (h : s.designatedOutput p r = .ok out) : t.designatedOutput p r = .ok out := by
  obtain ⟨owner, howner, hcase⟩ := designatedOutput_eq_ok.mp h
  refine designatedOutput_eq_ok.mpr ⟨owner, howner, ?_⟩
  rcases hcase with ⟨htask, i, pl, wf, hi, hpl, hctrl⟩ | ⟨name, e, spec, wf, htask, he, hspec, hbody⟩
  · obtain ⟨him, hiid⟩ := invocation?_eq_some hi
    obtain ⟨i', hi', a1, a2, a3, -, -⟩ := K.invocation i him
    refine Or.inl ⟨htask, i', pl, wf, by rw [← hiid, ← a1]; exact wk'.invocation?_of_mem hi', ?_, hctrl⟩
    obtain ⟨w, hw, hpl'⟩ := placementOf_eq_ok.mp hpl
    exact placementOf_eq_ok.mpr ⟨w, by rw [a2]; exact K.workflow? wk' hw, by rw [a3]; exact hpl'⟩
  · obtain ⟨hem, heid⟩ := execution?_eq_some he
    obtain ⟨e', he', a1, a2, a3, -, -⟩ := K.execution e hem
    exact Or.inr ⟨name, e', spec, wf, htask, by rw [← heid, ← a1]; exact wk'.execution?_of_mem he',
      K.taskSpec wk' a2 a3 hspec, hbody⟩

/-- A run with an owner is a sub-workflow call or a workflow task, so it names an endpoint. -/
theorem designatedOutput_exists (inv : Delivery.Inv p s) {r : Run} (hr : r ∈ s.runs) {o : String}
    (ho : r.owner = some o) : ∃ out, s.designatedOutput p r = .ok out := by
  rcases inv.own.runs r hr with ⟨ho', -, -⟩ | ⟨htask, i, hi, hio, -, w, pl, wf, out, hw, hpl, hctrl⟩ |
      ⟨name, htask, e, he, heo, -, -, spec, wf, out, hspec, hbody⟩
  · rw [ho] at ho'; cases ho'
  · exact ⟨out, designatedOutput_eq_ok.mpr ⟨i.id, hio, Or.inl ⟨htask, i, pl, wf, inv.wk.invocation?_of_mem hi,
      placementOf_eq_ok.mpr ⟨w, hw, hpl⟩, hctrl⟩⟩⟩
  · exact ⟨out, designatedOutput_eq_ok.mpr ⟨e.id, heo, Or.inr ⟨name, e, spec, wf, htask,
      inv.wk.execution?_of_mem he, hspec, hbody⟩⟩⟩

/-- The lookup of an invocation after its status was set. -/
theorem invocation?_setInvocation_of {id : String} {i₁ : Invocation} (hi₁ : s.invocation? id = some i₁)
    (st : InvocationStatus) :
    (s.setInvocation { i₁ with status := st }).invocation? id = some { i₁ with status := st } := by
  have h := (invocation?_eq_some hi₁).2
  rw [invocation?_setInvocation]
  simp [h, hi₁]

/-- The lookup of an execution after one of its tasks was set. -/
theorem execution?_setTask_of {id : String} {e₁ : Execution} (he₁ : s.execution? id = some e₁) (ts : TaskState) :
    (s.setTask e₁ ts).execution? id = some (withTask e₁ ts) := by
  have h := (execution?_eq_some he₁).2
  rw [execution?_setTask]
  simp [h, he₁]

/-- The lookup of a task by name after it was set. -/
theorem find?_withTask {e : Execution} {ts ts' : TaskState} {name : String}
    (hts : e.tasks.find? (·.name == name) = some ts) (hname : ts'.name = ts.name) :
    (withTask e ts').tasks.find? (·.name == name) = some ts' := by
  have hn : ts.name = name := Delivery.find?_name_of_task hts
  rw [withTask_tasks]
  have := find?_map_replace_key (l := e.tasks) (f := fun x : TaskState => x.name) (y := ts') (k := name)
  rw [this]
  simp [hname.trans hn, hts]

/-- Lookups read only the record list they search. -/
theorem invocation?_congr {u v : State} (h : u.invocations = v.invocations) (id : String) :
    u.invocation? id = v.invocation? id := by
  unfold State.invocation?
  rw [h]

theorem execution?_congr {u v : State} (h : u.executions = v.executions) (id : String) :
    u.execution? id = v.execution? id := by
  unfold State.execution?
  rw [h]

/-- A run is determined by its fields. -/
theorem run_ext {r r' : Run} (h1 : r'.path = r.path) (h2 : r'.workflow = r.workflow) (h3 : r'.input = r.input)
    (h4 : r'.owner = r.owner) (h5 : r'.task = r.task) (h6 : r'.complete = r.complete) : r' = r := by
  cases r
  cases r'
  simp_all

end StableFrame

end Suimon.Round3.StableAux
