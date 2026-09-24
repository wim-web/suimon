import Suimon.Theorems.Basic
import Suimon.Theorems.Trace

/-! Each value has at most one payload in a checked record (§12.1). A commit accepts payloads only for
    values its transition introduces, which the state before does not mention, and no step makes a
    reachable state forget a value it mentions (`Reachable.keepsValues`). So a value that has a
    payload is never introduced again, and no later record carries another payload for it
    (`Trace.check_values_nodup`). -/

namespace Suimon

section Lists
variable {α β : Type}

private theorem append_subset_append {a a' b b' : List α} (h₁ : a ⊆ a') (h₂ : b ⊆ b') : a ++ b ⊆ a' ++ b' := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact List.mem_append.2 (Or.inl (h₁ hx))
  · exact List.mem_append.2 (Or.inr (h₂ hx))

private theorem filterMap_subset_filterMap {l l' : List α} {f : α → Option β} (h : ∀ x ∈ l, x ∈ l') :
    l.filterMap f ⊆ l'.filterMap f := by
  intro b hb
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.1 hb
  exact List.mem_filterMap.2 ⟨x, h x hx, hfx⟩

private theorem flatMap_subset_flatMap {l l' : List α} {g : α → List β} (h : ∀ x ∈ l, x ∈ l') :
    l.flatMap g ⊆ l'.flatMap g := by
  intro b hb
  obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.1 hb
  exact List.mem_flatMap.2 ⟨x, h x hx, hbx⟩

private theorem map_subset_map {l l' : List α} {f : α → β} (h : ∀ x ∈ l, x ∈ l') : l.map f ⊆ l'.map f := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  exact List.mem_map_of_mem (h x hx)

private theorem filterMap_congr {l : List α} {f g : α → Option β} (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Replacing the members that `p` selects by `y` keeps every value `f` gives them, if `y` has it. --/
private theorem filterMap_subset_replace {l : List α} {p : α → Bool} {y : α} {f : α → Option β}
    (h : ∀ x ∈ l, p x = true → ∀ b, f x = some b → f y = some b) :
    l.filterMap f ⊆ (l.map fun x => if p x then y else x).filterMap f := by
  intro b hb
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.1 hb
  refine List.mem_filterMap.2 ⟨if p x then y else x, List.mem_map_of_mem hx, ?_⟩
  by_cases hp : p x = true
  · simp only [hp, ↓reduceIte]
    exact h x hx hp b hfx
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    exact hfx

private theorem flatMap_subset_replace {l : List α} {p : α → Bool} {y : α} {g : α → List β}
    (h : ∀ x ∈ l, p x = true → g x ⊆ g y) :
    l.flatMap g ⊆ (l.map fun x => if p x then y else x).flatMap g := by
  intro b hb
  obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.1 hb
  refine List.mem_flatMap.2 ⟨if p x then y else x, List.mem_map_of_mem hx, ?_⟩
  by_cases hp : p x = true
  · simp only [hp, ↓reduceIte]
    exact h x hx hp hbx
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    exact hbx

end Lists

namespace State

/-! ## A step keeps every value -/

/-- Every value that `s` mentions, `t` mentions too. --/
def KeepsValues (s t : State) : Prop := ∀ v ∈ s.values, v ∈ t.values

theorem KeepsValues.refl (s : State) : KeepsValues s s := fun _ h => h

theorem KeepsValues.trans {s t u : State} (h₁ : KeepsValues s t) (h₂ : KeepsValues t u) : KeepsValues s u :=
  fun v hv => h₂ v (h₁ v hv)

/-- The values an execution mentions: its input and the inputs of its tasks. --/
def executionValues (e : Execution) : List Value := e.input.toList ++ e.tasks.filterMap (·.input)

/-- The value a delivery carries. --/
def deliveryValue (d : Delivery) : Option Value :=
  match d.outcome with
  | .value v => some v
  | _ => none

/-- The values a task result mentions: its value and, once transformed, its output. --/
def taskResultValues (r : TaskResult) : List Value := r.value :: r.output.value?.toList

theorem values_eq (s : State) : s.values =
    s.runs.filterMap (·.input) ++ s.invocations.filterMap (·.input) ++ s.calls.filterMap (·.input) ++
      s.executions.flatMap executionValues ++ s.results.map (·.value) ++
      s.deliveries.filterMap deliveryValue ++ s.taskResults.flatMap taskResultValues := rfl

/-- A state keeps the values of another when each kind of record keeps its values. --/
theorem keepsValues_of {s t : State}
    (hr : s.runs.filterMap (·.input) ⊆ t.runs.filterMap (·.input))
    (hi : s.invocations.filterMap (·.input) ⊆ t.invocations.filterMap (·.input))
    (hc : s.calls.filterMap (·.input) ⊆ t.calls.filterMap (·.input))
    (he : s.executions.flatMap executionValues ⊆ t.executions.flatMap executionValues)
    (hres : s.results.map (·.value) ⊆ t.results.map (·.value))
    (hd : s.deliveries.filterMap deliveryValue ⊆ t.deliveries.filterMap deliveryValue)
    (htr : s.taskResults.flatMap taskResultValues ⊆ t.taskResults.flatMap taskResultValues) :
    KeepsValues s t := by
  intro v hv
  rw [values_eq] at hv ⊢
  exact append_subset_append (append_subset_append (append_subset_append (append_subset_append
    (append_subset_append (append_subset_append hr hi) hc) he) hres) hd) htr hv

/-- Adding records keeps every value. --/
theorem keepsValues_of_mem {s t : State} (hr : ∀ x ∈ s.runs, x ∈ t.runs)
    (hi : ∀ x ∈ s.invocations, x ∈ t.invocations) (hc : ∀ x ∈ s.calls, x ∈ t.calls)
    (he : ∀ x ∈ s.executions, x ∈ t.executions) (hres : ∀ x ∈ s.results, x ∈ t.results)
    (hd : ∀ x ∈ s.deliveries, x ∈ t.deliveries) (htr : ∀ x ∈ s.taskResults, x ∈ t.taskResults) :
    KeepsValues s t :=
  keepsValues_of (filterMap_subset_filterMap hr) (filterMap_subset_filterMap hi) (filterMap_subset_filterMap hc)
    (flatMap_subset_flatMap he) (map_subset_map hres) (filterMap_subset_filterMap hd) (flatMap_subset_flatMap htr)

theorem keepsValues_setRun {s : State} {r : Run} (h : ∀ x ∈ s.runs, x.path = r.path → x.input = r.input) :
    KeepsValues s (s.setRun r) :=
  keepsValues_of
    (filterMap_subset_replace fun x hx hp b hb => by
      rw [← h x hx (by simpa using hp)]
      exact hb)
    (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
    (List.Subset.refl _)

theorem keepsValues_setInvocation {s : State} {i : Invocation}
    (h : ∀ x ∈ s.invocations, x.id = i.id → x.input = i.input) : KeepsValues s (s.setInvocation i) :=
  keepsValues_of (List.Subset.refl _)
    (filterMap_subset_replace fun x hx hp b hb => by
      rw [← h x hx (by simpa using hp)]
      exact hb)
    (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)

theorem keepsValues_setCall {s : State} {c : Call} (h : ∀ x ∈ s.calls, x.id = c.id → x.input = c.input) :
    KeepsValues s (s.setCall c) :=
  keepsValues_of (List.Subset.refl _) (List.Subset.refl _)
    (filterMap_subset_replace fun x hx hp b hb => by
      rw [← h x hx (by simpa using hp)]
      exact hb)
    (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)

theorem keepsValues_setExecution {s : State} {e : Execution}
    (h : ∀ x ∈ s.executions, x.id = e.id → executionValues x ⊆ executionValues e) :
    KeepsValues s (s.setExecution e) :=
  keepsValues_of (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
    (flatMap_subset_replace fun x hx hp => h x hx (by simpa using hp))
    (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)

theorem executionValues_withTask {e : Execution} {t : TaskState}
    (h : ∀ y ∈ e.tasks, y.name = t.name → ∀ v, y.input = some v → t.input = some v) :
    executionValues e ⊆ executionValues (withTask e t) :=
  append_subset_append (List.Subset.refl _)
    (filterMap_subset_replace fun y hy hp v hv => h y hy (by simpa using hp) v hv)

theorem keepsValues_setTask {s : State} {e : Execution} {t : TaskState} (wk : s.WellKeyed)
    (he : e ∈ s.executions) (h : ∀ y ∈ e.tasks, y.name = t.name → ∀ v, y.input = some v → t.input = some v) :
    KeepsValues s (s.setTask e t) :=
  keepsValues_setExecution fun x hx hid => by
    obtain rfl := wk.execution_eq_of_id hx he hid
    exact executionValues_withTask h

theorem keepsValues_setTaskResult {s : State} {r : TaskResult}
    (h : ∀ x ∈ s.taskResults, x.execution = r.execution → x.task = r.task → x.index = r.index →
      taskResultValues x ⊆ taskResultValues r) :
    KeepsValues s (s.setTaskResult r) :=
  keepsValues_of (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
    (List.Subset.refl _) (List.Subset.refl _)
    (flatMap_subset_replace fun x hx hp => by
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact h x hx hp.1.1 hp.1.2 hp.2)

theorem stopCall_input {c : Call} : (stopCall c).input = c.input := by
  unfold stopCall; split <;> rfl

theorem executionValues_stopExecution (e : Execution) : executionValues (stopExecution e) = executionValues e := by
  simp only [executionValues, stopExecution, List.filterMap_map]
  congr 1
  apply filterMap_congr
  intro t _
  simp only [Function.comp_apply]
  split <;> rfl

theorem executionValues_endExecution (e : Execution) : executionValues (endExecution e) = executionValues e := by
  simp only [executionValues, endExecution_input, endExecution_tasks, List.filterMap_map]
  congr 1
  apply filterMap_congr
  intro t _
  simp [endTask_input]

theorem keepsValues_stop (s : State) : KeepsValues s s.stop := by
  refine keepsValues_of (List.Subset.refl _) (List.Subset.refl _) ?_ ?_ (List.Subset.refl _)
    (List.Subset.refl _) (List.Subset.refl _)
  · rw [stop_calls, List.filterMap_map]
    intro v hv
    obtain ⟨c, hc, hcv⟩ := List.mem_filterMap.1 hv
    exact List.mem_filterMap.2 ⟨c, hc, by simpa [stopCall_input] using hcv⟩
  · rw [stop_executions, List.flatMap_map]
    intro v hv
    obtain ⟨e, he, hev⟩ := List.mem_flatMap.1 hv
    exact List.mem_flatMap.2 ⟨e, he, by rw [executionValues_stopExecution]; exact hev⟩

theorem keepsValues_endUnfinished (s : State) : KeepsValues s s.endUnfinished := by
  refine keepsValues_of (List.Subset.refl _) ?_ (List.Subset.refl _) ?_ (List.Subset.refl _)
    (List.Subset.refl _) (List.Subset.refl _)
  · rw [endUnfinished_invocations, List.filterMap_map]
    intro v hv
    obtain ⟨i, hi, hiv⟩ := List.mem_filterMap.1 hv
    exact List.mem_filterMap.2 ⟨i, hi, by simpa using hiv⟩
  · rw [endUnfinished_executions, List.flatMap_map]
    intro v hv
    obtain ⟨e, he, hev⟩ := List.mem_flatMap.1 hv
    exact List.mem_flatMap.2 ⟨e, he, by rw [executionValues_endExecution]; exact hev⟩

theorem keepsValues_fail (s : State) (f : Failure) (policy : Policy) : KeepsValues s (s.fail f policy) := by
  cases policy
  · exact (KeepsValues.refl s).trans (keepsValues_stop { s with failures := s.failures ++ [f] })
  · exact KeepsValues.refl s

/-! ### Tasks

Setting the status of a task replaces every task of its execution with that name, and giving it its
input overwrites the input of a pending task. Neither loses a value, since a pending task has no
input yet and tasks of the same name have the same input (`TasksInv`). -/

/-- A pending task of `e` has no input yet, and tasks of `e` with the same name have the same input. --/
def TasksOk (e : Execution) : Prop :=
  (∀ ts ∈ e.tasks, ts.status = .pending → ts.input = none) ∧
    ∀ t₁ ∈ e.tasks, ∀ t₂ ∈ e.tasks, t₁.name = t₂.name → t₁.input = t₂.input

/-- Every execution of `s` satisfies `TasksOk`. --/
def TasksInv (s : State) : Prop := ∀ e ∈ s.executions, TasksOk e

theorem TasksOk.withTask {e : Execution} {t : TaskState} (h : TasksOk e) (ht : t.status = .pending → t.input = none) :
    TasksOk (withTask e t) := by
  constructor
  · intro z hz hpending
    rw [withTask_tasks] at hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    by_cases hn : x.name = t.name
    · simp only [hn, beq_self_eq_true, ↓reduceIte] at hpending ⊢
      exact ht hpending
    · have hn' : (x.name == t.name) = false := by simpa using hn
      simp only [hn', Bool.false_eq_true, ↓reduceIte] at hpending ⊢
      exact h.1 x hx hpending
  · intro z₁ hz₁ z₂ hz₂ hname
    rw [withTask_tasks] at hz₁ hz₂
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.1 hz₁
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.1 hz₂
    by_cases hn₁ : x₁.name = t.name <;> by_cases hn₂ : x₂.name = t.name
    · simp [hn₁, hn₂]
    · have hn₂' : (x₂.name == t.name) = false := by simpa using hn₂
      simp only [hn₁, beq_self_eq_true, ↓reduceIte, hn₂', Bool.false_eq_true] at hname
      exact absurd hname.symm hn₂
    · have hn₁' : (x₁.name == t.name) = false := by simpa using hn₁
      simp only [hn₁', Bool.false_eq_true, ↓reduceIte, hn₂, beq_self_eq_true] at hname
      exact absurd hname hn₁
    · have hn₁' : (x₁.name == t.name) = false := by simpa using hn₁
      have hn₂' : (x₂.name == t.name) = false := by simpa using hn₂
      simp only [hn₁', hn₂', Bool.false_eq_true, ↓reduceIte] at hname ⊢
      exact h.2 x₁ hx₁ x₂ hx₂ hname

theorem TasksOk.stopExecution {e : Execution} (h : TasksOk e) : TasksOk (stopExecution e) := by
  constructor
  · intro z hz hpending
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    split at hpending
    · simp at hpending
    · rename_i hnot
      simp only [hpending, beq_self_eq_true, Bool.true_or, not_true_eq_false] at hnot
  · intro z₁ hz₁ z₂ hz₂ hname
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.1 hz₁
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.1 hz₂
    have hn : ∀ x : TaskState, (if x.status == .pending || x.status == .ready then
        { x with status := .notStarted } else x).name = x.name := fun x => by split <;> rfl
    have hi : ∀ x : TaskState, (if x.status == .pending || x.status == .ready then
        { x with status := .notStarted } else x).input = x.input := fun x => by split <;> rfl
    rw [hn, hn] at hname
    rw [hi, hi]
    exact h.2 x₁ hx₁ x₂ hx₂ hname

theorem TasksOk.endExecution {e : Execution} (h : TasksOk e) : TasksOk (endExecution e) := by
  constructor
  · intro z hz hpending
    rw [endExecution_tasks] at hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    rw [endTask_status] at hpending
    split at hpending
    · cases hpending
    · split at hpending
      · cases hpending
      · rename_i hnot
        exact absurd (Or.inl hpending) hnot
  · intro z₁ hz₁ z₂ hz₂ hname
    rw [endExecution_tasks] at hz₁ hz₂
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.1 hz₁
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.1 hz₂
    simp only [endTask_name] at hname
    simp only [endTask_input]
    exact h.2 x₁ hx₁ x₂ hx₂ hname

namespace TasksInv
variable {s t : State}

theorem empty : TasksInv ({} : State) := fun _ he => by simp at he

theorem of_executions (h : TasksInv s) (he : t.executions = s.executions) : TasksInv t :=
  fun e hmem => h e (he ▸ hmem)

theorem setExecution {e : Execution} (h : TasksInv s) (he : TasksOk e) : TasksInv (s.setExecution e) := by
  intro x hx
  rcases mem_setExecution_executions hx with rfl | hx
  · exact he
  · exact h x hx

theorem setTask {e : Execution} {ts : TaskState} (h : TasksInv s) (he : e ∈ s.executions)
    (hts : ts.status = .pending → ts.input = none) : TasksInv (s.setTask e ts) :=
  h.setExecution ((h e he).withTask hts)

theorem stop (h : TasksInv s) : TasksInv s.stop := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := mem_stop_executions.1 hx
  exact (h e he).stopExecution

theorem endUnfinished (h : TasksInv s) : TasksInv s.endUnfinished := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := mem_endUnfinished_executions.1 hx
  exact (h e he).endExecution

theorem fail (h : TasksInv s) (f : Failure) (policy : Policy) : TasksInv (s.fail f policy) := by
  cases policy
  · exact (h.of_executions (t := { s with failures := s.failures ++ [f] }) rfl).stop
  · exact h.of_executions rfl

theorem accept {c : Call} {index : Nat} {value : Value} {arm : Option String} (h : TasksInv s)
    (ha : s.accept c index value arm = .ok t) : TasksInv t :=
  h.of_executions (accept_frame ha).2.2.2.2.2.2.1

theorem settleOwner {c : Call} {inv : InvocationStatus} {task : TaskStatus} (h : TasksInv s)
    (ht : task ≠ .pending) (ho : s.settleOwner c inv task = .ok t) : TasksInv t := by
  rcases settleOwner_eq_ok.mp ho with ⟨-, i, -, rfl⟩ | ⟨name, e, ts, -, he, -, rfl⟩
  · exact h.of_executions rfl
  · exact h.setTask (execution?_eq_some he).1 fun hp => absurd hp ht

theorem cancelOwner {c : Call} (h : TasksInv s) (ho : s.cancelOwner c = .ok t) : TasksInv t := by
  rcases cancelOwner_eq_ok.mp ho with ⟨-, i, -, rfl⟩ | ⟨name, e, ts, -, he, -, rfl⟩ <;> split
  · exact h.of_executions rfl
  · exact h
  · exact h.setTask (execution?_eq_some he).1 fun hp => by cases hp
  · exact h

theorem failCall {c : Call} {status : CallStatus} {cause : Cause} (h : TasksInv s)
    (hf : s.failCall c status cause = .ok t) : TasksInv t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  exact ((h.of_executions (t := s.setCall { c with status }) rfl).settleOwner (by decide) hso).fail _ _

end TasksInv

/-! ### Updates of one record -/

theorem keepsValues_setCall_of_mem {s : State} {c c' : Call} (wk : s.WellKeyed) (hc : c ∈ s.calls)
    (hid : c'.id = c.id) (hin : c'.input = c.input) : KeepsValues s (s.setCall c') :=
  keepsValues_setCall fun x hx hx' => by
    rw [wk.call_eq_of_id hx hc (hx'.trans hid), hin]

theorem keepsValues_setInvocation_of_mem {s : State} {i i' : Invocation} (wk : s.WellKeyed)
    (hi : i ∈ s.invocations) (hid : i'.id = i.id) (hin : i'.input = i.input) : KeepsValues s (s.setInvocation i') :=
  keepsValues_setInvocation fun x hx hx' => by
    rw [wk.invocation_eq_of_id hx hi (hx'.trans hid), hin]

theorem keepsValues_setRun_of_mem {s : State} {r r' : Run} (wk : s.WellKeyed) (hr : r ∈ s.runs)
    (hpath : r'.path = r.path) (hin : r'.input = r.input) : KeepsValues s (s.setRun r') :=
  keepsValues_setRun fun x hx hx' => by
    rw [wk.run_eq_of_path hx hr (hx'.trans hpath), hin]

/-- Setting the status of a task keeps every value. --/
theorem keepsValues_setTask_of_mem {s : State} {e : Execution} {ts ts' : TaskState} (wk : s.WellKeyed)
    (ti : s.TasksInv) (he : e ∈ s.executions) (hts : ts ∈ e.tasks) (hname : ts'.name = ts.name)
    (hin : ts'.input = ts.input) : KeepsValues s (s.setTask e ts') :=
  keepsValues_setTask wk he fun y hy hyn v hv => by
    rw [hin, ← (ti e he).2 y hy ts hts (hyn.trans hname)]
    exact hv

theorem accept_keepsValues {s t : State} {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : KeepsValues s t := by
  rcases accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
    refine keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;> simp [hx]

theorem settleOwner_keepsValues {s t : State} {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (wk : s.WellKeyed) (ti : s.TasksInv) (h : s.settleOwner c inv task = .ok t) : KeepsValues s t := by
  rcases settleOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨name, e, ts, -, he, hts, rfl⟩
  · exact keepsValues_setInvocation_of_mem wk (invocation?_eq_some hi).1 rfl rfl
  · exact keepsValues_setTask_of_mem wk ti (execution?_eq_some he).1 (find?_key_eq_some hts).1 rfl rfl

theorem cancelOwner_keepsValues {s t : State} {c : Call} (wk : s.WellKeyed) (ti : s.TasksInv)
    (h : s.cancelOwner c = .ok t) : KeepsValues s t := by
  rcases cancelOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨name, e, ts, -, he, hts, rfl⟩ <;> split
  · exact keepsValues_setInvocation_of_mem wk (invocation?_eq_some hi).1 rfl rfl
  · exact KeepsValues.refl s
  · exact keepsValues_setTask_of_mem wk ti (execution?_eq_some he).1 (find?_key_eq_some hts).1 rfl rfl
  · exact KeepsValues.refl s

theorem failCall_keepsValues {s t : State} {c : Call} {status : CallStatus} {cause : Cause}
    (wk : s.WellKeyed) (ti : s.TasksInv) (hc : c ∈ s.calls) (h : s.failCall c status cause = .ok t) :
    KeepsValues s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp h
  exact (keepsValues_setCall_of_mem (c' := { c with status }) wk hc rfl rfl).trans
    ((settleOwner_keepsValues (wk.setCall _) (ti.of_executions rfl) hso).trans (keepsValues_fail _ _ _))

theorem WellKeyed.taskResult_eq {s : State} (wk : s.WellKeyed) {x r : TaskResult} (hx : x ∈ s.taskResults)
    (hr : r ∈ s.taskResults) (hkey : (x.execution, x.task, x.index) = (r.execution, r.task, r.index)) : x = r := by
  have h₁ := find?_eq_some_of_nodup wk.taskResults hx
    (P := fun y => (y.execution, y.task, y.index) == (r.execution, r.task, r.index)) fun y => by simp [hkey]
  have h₂ := find?_eq_some_of_nodup wk.taskResults hr
    (P := fun y => (y.execution, y.task, y.index) == (r.execution, r.task, r.index)) fun y => by simp
  exact Option.some.inj (h₁.symm.trans h₂)

/-- Transforming the output of a pending task result keeps every value. --/
theorem keepsValues_setTaskResult_of_mem {s : State} {r : TaskResult} (wk : s.WellKeyed) (hr : r ∈ s.taskResults)
    (hpending : r.output = .pending) (o : TaskOutput) : KeepsValues s (s.setTaskResult { r with output := o }) :=
  keepsValues_setTaskResult fun x hx h₁ h₂ h₃ => by
    obtain rfl := wk.taskResult_eq hx hr (by simp only at h₁ h₂ h₃; rw [h₁, h₂, h₃])
    simp [taskResultValues, hpending, TaskOutput.value?]

end State

open State in
/-- A step keeps the invariant of the tasks. --/
theorem step_tasksInv {p : Definition} {s t : State} {op : Op} (h : s.TasksInv) (hs : step p s op = .ok t) :
    t.TasksInv := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact h.of_executions rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨c, -, -, rfl⟩
    · exact h.of_executions rfl
    · exact h.of_executions rfl
    · exact h.of_executions rfl
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact h e he
      · rw [List.mem_singleton] at he
        subst he
        constructor
        · intro ts hts _
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 hts
          rfl
        · intro t₁ h₁ t₂ h₂ _
          obtain ⟨x₁, -, rfl⟩ := List.mem_map.1 h₁
          obtain ⟨x₂, -, rfl⟩ := List.mem_map.1 h₂
          rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.of_executions rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have h' : (s'.setCall { c with status := .returned }).TasksInv := (h.accept hacc).of_executions rfl
    exact h'.settleOwner (by decide) hso
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact (h.accept hacc).of_executions rfl
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (h.accept hacc).of_executions rfl
  | ended id =>
    obtain ⟨-, -, c, -, -, -, hso⟩ := Step.ended_inv hs
    have h' : (s.setCall { c with status := .returned }).TasksInv := h.of_executions rfl
    exact h'.settleOwner (by decide) hso
  | failed id =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.failed_inv hs
    exact h.failCall hf
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.timedOut_inv hs
    exact h.failCall hf
  | lost id =>
    obtain ⟨-, -, c, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.failCall hf
    · have h' : (s.setCall { c with status := .cancelled }).TasksInv := h.of_executions rfl
      exact h'.cancelOwner ho
  | terminated id =>
    obtain ⟨-, -, c, -, -, ho⟩ := Step.terminated_inv hs
    have h' : (s.setCall { c with status := .cancelled }).TasksInv := h.of_executions rfl
    exact h'.cancelOwner ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.of_executions rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    let d : Delivery := { run := path, connection := index, source, outcome := .failed }
    have h' : ({ s with deliveries := s.deliveries ++ [d] } : State).TasksInv := h.of_executions rfl
    exact h'.fail _ _
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, _, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.setTask (execution?_eq_some he).1 fun hp => by cases hp
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, _, _, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (h.setTask (execution?_eq_some he).1 fun hp => by cases hp).fail _ _
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    have h' := h.setTask (ts := { ts with status := .active }) (execution?_eq_some he).1 fun hp => by cases hp
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact h'.of_executions rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h.of_executions rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    have h' : (s.setTaskResult { r with output := .failed }).TasksInv := h.of_executions rfl
    exact h'.fail _ _
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h.of_executions rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    have h' := h.setExecution (e := { e with complete := true }) (h e (execution?_eq_some he).1)
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact h'.of_executions rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨-, _, -, hcases⟩ | ⟨_, e, ts, -, he, -, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h.of_executions rfl
    · have h' : (s.setRun { r with complete := true }).TasksInv := h.of_executions rfl
      have he' : e ∈ (s.setRun { r with complete := true }).executions := (execution?_eq_some he).1
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (h'.setTask he' fun hp => by cases hp).of_executions rfl
      · exact h'.setTask he' fun hp => by cases hp
      · exact h'.setTask he' fun hp => by cases hp
      · exact h'.setTask he' fun hp => by cases hp
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.stop.of_executions rfl
    · exact h.of_executions rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact h.of_executions rfl
    · exact h.endUnfinished.of_executions rfl


open State in
/-- A step keeps every value that a state with unique keys and consistent tasks mentions, once the
    workflow started; before the start, a reachable state mentions no value. --/
theorem step_keepsValues {p : Definition} {s t : State} {op : Op} (wk : s.WellKeyed) (ti : s.TasksInv)
    (hst : s.started = true ∨ s.values = []) (hs : step p s op = .ok t) : KeepsValues s t := by
  cases op with
  | start input =>
    obtain ⟨hns, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases hst with h | h
    · simp [h] at hns
    · intro v hv
      rw [h] at hv
      cases hv
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      refine keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;> simp [hx]
  | fetch id =>
    obtain ⟨-, -, c, hc, -, -, rfl⟩ := Step.fetch_inv hs
    exact keepsValues_setCall_of_mem wk (call?_eq_some hc).1 rfl rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have wk' := wk.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact (accept_keepsValues hacc).trans
      ((keepsValues_setCall_of_mem (c' := { c with status := .returned }) wk' hc' rfl rfl).trans
        (settleOwner_keepsValues (wk'.setCall _) ((ti.accept hacc).of_executions rfl) hso))
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', hc, -, -, -, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have wk' := wk.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    have hi' : i ∈ (s'.setCall { c with status := .returned }).invocations := by
      rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]; exact (invocation?_eq_some hi).1
    exact (accept_keepsValues hacc).trans
      ((keepsValues_setCall_of_mem (c' := { c with status := .returned }) wk' hc' rfl rfl).trans
        (keepsValues_setInvocation_of_mem (i' := { i with status := .succeeded, arm := some arm })
          (wk'.setCall _) hi' rfl rfl))
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact (accept_keepsValues hacc).trans
      (keepsValues_setCall_of_mem (c' := { c with status := .running, yields := c.yields + 1 })
        (wk.accept hacc) hc' rfl rfl)
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    exact (keepsValues_setCall_of_mem (c' := { c with status := .returned }) wk (call?_eq_some hc).1 rfl rfl).trans
      (settleOwner_keepsValues (wk.setCall _) (ti.of_executions rfl) hso)
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact failCall_keepsValues wk ti (call?_eq_some hc).1 hf
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    exact failCall_keepsValues wk ti (call?_eq_some hc).1 hf
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact failCall_keepsValues wk ti (call?_eq_some hc).1 hf
    · exact (keepsValues_setCall_of_mem (c' := { c with status := .cancelled }) wk (call?_eq_some hc).1 rfl
        rfl).trans (cancelOwner_keepsValues (wk.setCall _) (ti.of_executions rfl) ho)
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact (keepsValues_setCall_of_mem (c' := { c with status := .cancelled }) wk (call?_eq_some hc).1 rfl
      rfl).trans (cancelOwner_keepsValues (wk.setCall _) (ti.of_executions rfl) ho)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    refine keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;> simp [hx]
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    refine KeepsValues.trans ?_ (keepsValues_fail _ _ _)
    refine keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;> simp [hx]
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, _, he, hts, hpending, -, -, rfl⟩ := Step.taskInput_inv hs
    have he' := (execution?_eq_some he).1
    have hts' := (find?_key_eq_some hts).1
    exact keepsValues_setTask wk he' fun y hy hyn v hv => by
      rw [(ti e he').2 y hy ts hts' hyn, (ti e he').1 ts hts' hpending] at hv
      cases hv
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, _, _, he, hts, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (keepsValues_setTask_of_mem (ts' := { ts with status := .failed }) wk ti (execution?_eq_some he).1
      (find?_key_eq_some hts).1 rfl rfl).trans (keepsValues_fail _ _ _)
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, -, -, hts, -, -, -, hcases⟩ := Step.beginTask_inv hs
    have h₁ := keepsValues_setTask_of_mem (ts' := { ts with status := .active }) wk ti (execution?_eq_some he).1
      (find?_key_eq_some hts).1 rfl rfl
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;>
      refine h₁.trans (keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;> intro x hx <;> simp_all
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, _, _, r, -, -, -, -, hr, hpending, hcases⟩ := Step.taskOutput_inv hs
    have h₁ := keepsValues_setTaskResult_of_mem wk (List.mem_of_find?_eq_some hr) hpending (.value value)
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · refine h₁.trans (keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;> intro x hx <;> simp_all
    · exact h₁
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, hr, hpending, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (keepsValues_setTaskResult_of_mem wk (List.mem_of_find?_eq_some hr) hpending .failed).trans
      (keepsValues_fail _ _ _)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      refine keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;> simp [hx]
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i, he, -, -, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    have h₁ : KeepsValues s (s.setExecution { e with complete := true }) :=
      keepsValues_setExecution fun x hx hid => by
        rw [wk.execution_eq_of_id hx (execution?_eq_some he).1 hid]
        exact List.Subset.refl _
    have wk' := wk.setExecution { e with complete := true }
    have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (invocation?_eq_some hi).1
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h₁.trans (keepsValues_setInvocation_of_mem (i' := { i with status := .skipped }) wk' hi' rfl rfl)
    · refine h₁.trans ((keepsValues_setInvocation_of_mem (i' := { i with status := .succeeded }) wk' hi' rfl
        rfl).trans (keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_)) <;> intro x hx <;> simp_all
    · exact h₁.trans (keepsValues_setInvocation_of_mem (i' := { i with status := .succeeded }) wk' hi' rfl rfl)
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    have h₁ := keepsValues_setRun_of_mem (r' := { r with complete := true }) wk (run?_eq_some hr).1 rfl rfl
    have wk' := wk.setRun { r with complete := true }
    have ti' : (s.setRun { r with complete := true }).TasksInv := ti.of_executions rfl
    rcases hcases with ⟨-, i, hi, hcases⟩ | ⟨_, e, ts, -, he, hts, hcases⟩
    · have hi' : i ∈ (s.setRun { r with complete := true }).invocations := (invocation?_eq_some hi).1
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine h₁.trans ((keepsValues_setInvocation_of_mem (i' := { i with status := .succeeded }) wk' hi' rfl
          rfl).trans (keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_)) <;> intro x hx <;> simp_all
      · exact h₁.trans (keepsValues_setInvocation_of_mem wk' hi' rfl rfl)
      · exact h₁.trans (keepsValues_setInvocation_of_mem wk' hi' rfl rfl)
      · exact h₁.trans (keepsValues_setInvocation_of_mem wk' hi' rfl rfl)
    · have he' : e ∈ (s.setRun { r with complete := true }).executions := (execution?_eq_some he).1
      have hts' := (find?_key_eq_some hts).1
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine h₁.trans ((keepsValues_setTask_of_mem (ts' := { ts with status := .succeeded }) wk' ti' he' hts'
          rfl rfl).trans (keepsValues_of_mem ?_ ?_ ?_ ?_ ?_ ?_ ?_)) <;> intro x hx <;> simp_all
      · exact h₁.trans (keepsValues_setTask_of_mem wk' ti' he' hts' rfl rfl)
      · exact h₁.trans (keepsValues_setTask_of_mem wk' ti' he' hts' rfl rfl)
      · exact h₁.trans (keepsValues_setTask_of_mem wk' ti' he' hts' rfl rfl)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact keepsValues_stop s
    · exact KeepsValues.refl s
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact keepsValues_setRun_of_mem (r' := { r with complete := true }) wk (run?_eq_some hr).1 rfl rfl
    · exact keepsValues_endUnfinished s

/-- In a reachable state, the tasks of each execution satisfy `State.TasksOk`. --/
theorem Reachable.tasksInv {p : Definition} {s : State} (h : Reachable p s) : s.TasksInv := by
  induction h with
  | empty => exact State.TasksInv.empty
  | step op _ hs ih => exact step_tasksInv ih hs

/-- No step makes a reachable state forget a value it mentions. --/
theorem Reachable.keepsValues {p : Definition} {s t : State} {op : Op} (h : Reachable p s)
    (hs : Suimon.step p s op = .ok t) : s.KeepsValues t := by
  refine step_keepsValues h.wellKeyed h.tasksInv ?_ hs
  rcases h.eq_empty_or_started with rfl | hst
  · exact Or.inr rfl
  · exact Or.inl hst


namespace Trace

/-! ## At most one payload per value -/

/-- A transition introduces exactly the values that the state after mentions and the state before
    does not. --/
theorem mem_introduced_iff {before after : State} {v : Value} :
    v ∈ introduced before after ↔ v ∈ after.values ∧ v ∉ before.values := by
  simp [introduced, List.mem_eraseDups]

/-- An op record whose commit checks carries payloads only for values its transition introduces. --/
theorem mem_introduced_of_unexpected {before after : State} {values : List (Value × String)}
    (h : unexpected before after values = []) {v : Value} (hv : v ∈ values.map (·.1)) :
    v ∈ after.values ∧ v ∉ before.values := by
  have := List.filter_eq_nil_iff.1 h v hv
  exact mem_introduced_iff.1 (by simpa using this)

/-- What a replay establishes about payloads: the replayed state is reachable, the committed payloads
    have distinct keys, each a value the state mentions, and so do the payloads of a pending op
    record. --/
structure Replay.Distinct (p : Definition) (r : Replay) : Prop where
  reachable : Reachable p r.state
  nodup : (r.values.map (·.1)).Nodup
  mentioned : ∀ v ∈ r.values.map (·.1), v ∈ r.state.values
  pending : ∀ o values, r.pending = some (o, values) → (values.map (·.1)).Nodup

theorem Replay.distinct_empty (p : Definition) : Replay.Distinct p {} :=
  ⟨.empty, List.nodup_nil, (fun _ h => by simp at h), (fun _ _ h => by simp at h)⟩

theorem replayLine_distinct {c : Codec} (hc : c.DecodesDistinct) {p : Definition} {r r' : Replay}
    {index : Nat} {line : String} (hr : r.Distinct p) (h : replayLine c p r index line = .ok r') :
    r'.Distinct p := by
  simp only [replayLine] at h
  split at h
  · simp at h
  · rename_i record hdecode
    split at h
    · simp at h
    · split at h
      · rename_i seq o values hpending _
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨hr.reachable, hr.nodup, hr.mentioned, fun o' values' hp => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨-, rfl⟩ := hp
        exact hc _ _ hdecode
      · rename_i seq o values hpending _
        cases hstep : step p r.state o with
        | error e => simp [hstep] at h
        | ok next =>
          simp only [hstep] at h
          split at h
          · simp at h
          · rename_i hextra
            split at h
            · simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              have hkeys := hr.pending o values hpending
              have hnew : ∀ v ∈ values.map (·.1), v ∈ next.values ∧ v ∉ r.state.values :=
                fun v hv => mem_introduced_of_unexpected (by simpa using hextra) hv
              refine ⟨hr.reachable.step o hstep, ?_, ?_, fun _ _ hp => by simp at hp⟩
              · rw [List.map_append, List.nodup_append]
                refine ⟨hr.nodup, hkeys, fun a ha b hb hab => ?_⟩
                subst hab
                exact (hnew a hb).2 (hr.mentioned a ha)
              · intro v hv
                rw [List.map_append, List.mem_append] at hv
                rcases hv with hv | hv
                · exact hr.reachable.keepsValues hstep v (hr.mentioned v hv)
                · exact (hnew v hv).1
            · simp at h
      · simp at h
      · simp at h


theorem replayLines_distinct {c : Codec} (hc : c.DecodesDistinct) {p : Definition} :
    ∀ {lines : List (List Char)} {r r' : Replay} {index : Nat}, r.Distinct p →
      replayLines c p r index lines = .ok r' → r'.Distinct p := by
  intro lines
  induction lines with
  | nil =>
    intro r r' index hr h
    simp only [replayLines, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hr
  | cons line rest ih =>
    intro r r' index hr h
    simp only [replayLines] at h
    cases hl : replayLine c p r index (String.ofList line) with
    | error e => simp [hl, bind, Except.bind] at h
    | ok r₁ =>
      simp only [hl, bind, Except.bind] at h
      exact ih (replayLine_distinct hc hr hl) h

/-- Each value has at most one payload among the committed payloads of a checked record (§12.1). The
    payloads of an op record have distinct keys, a commit accepts payloads only for values its
    transition introduces, which the state before does not mention, and a step never makes the state
    forget a value; so a value with a payload is never introduced again. --/
theorem check_values_nodup {c : Codec} (hc : c.DecodesDistinct) {load : Header → Except String Definition}
    {text : String} {checked : Checked} (h : check c load text = .ok checked) :
    (checked.values.map (·.1)).Nodup := by
  rcases check_eq_ok h with ⟨-, -, -, hvalues⟩ | ⟨header, p, lines, r, -, hr, -, -, -, hvalues⟩
  · rw [hvalues]
    exact List.nodup_nil
  · rw [hvalues]
    exact (replayLines_distinct hc (Replay.distinct_empty p) hr).nodup

private theorem eq_of_nodup_map_fst {α β : Type} : ∀ {l : List (α × β)}, (l.map (·.1)).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, x.1 = y.1 → x = y
  | [], _, x, hx, _, _, _ => by cases hx
  | z :: zs, h, x, hx, y, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with hxz | hxs <;> rcases List.mem_cons.1 hy with hyz | hys
    · rw [hxz, hyz]
    · subst hxz
      exact absurd (by rw [hxy]; exact List.mem_map_of_mem hys) h.1
    · subst hyz
      exact absurd (by rw [← hxy]; exact List.mem_map_of_mem hxs) h.1
    · exact eq_of_nodup_map_fst h.2 x hxs y hys hxy

/-- The committed payloads of a checked record never give one value two payloads. --/
theorem check_payload_unique {c : Codec} (hc : c.DecodesDistinct) {load : Header → Except String Definition}
    {text : String} {checked : Checked} (h : check c load text = .ok checked) {v : Value} {a b : String}
    (ha : (v, a) ∈ checked.values) (hb : (v, b) ∈ checked.values) : a = b :=
  (Prod.mk.inj (eq_of_nodup_map_fst (check_values_nodup hc h) _ ha _ hb rfl)).2

/-- In a record that `suimon check` accepts, each value has at most one committed payload. --/
theorem check_values_nodup_wire {load : Header → Except String Definition} {text : String} {checked : Checked}
    (h : check wireCodec load text = .ok checked) : (checked.values.map (·.1)).Nodup :=
  check_values_nodup wireCodec_decodesDistinct h

end Trace

end Suimon
