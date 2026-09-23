import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## [10] Round3/Work.lean — task D1

Formulation of §15.3 for termination. Finitely many elements per generator is the `List` in `Script`.
Every conforming execution is bounded by `workBound`, whatever the scheduler and whether or not the
behavior fits (`bounded`). "Every call and transform eventually answers, cancelled calls terminate"
becomes maximality: an execution that cannot be extended by a conforming operation (`Stuck`) has a
final status, provided the input fits `main` and the behavior answers every call within its contract
(`stuck_terminal`). Fairness is not needed, because executions are finite. -/

section Work
variable {p : Program} {env : Env} {s t : State}

/-- A call's progress: two per element (fetch, then the element), then its status. -/
def callProgress (c : Call) : Nat :=
  2 * c.yields + match c.status with
    | .running => 0 | .fetching => 1 | .cancelling => 2 | .returned | .failed | .lost => 3 | .cancelled => 4

def taskProgress (t : TaskState) : Nat :=
  match t.status with
  | .pending => 0 | .ready => 1 | .active => 2 | _ => 3

def statusProgress : Status → Nat
  | .running => 0 | .stopping => 1 | _ => 2

/-- How far a state has come. Failures are not counted: every step that records one also advances a
    call, a delivery, a task or a task result. -/
def work (s : State) : Nat :=
  (if s.started then 1 else 0) + (if s.cancelled then 1 else 0) + statusProgress s.status +
    s.runs.length + (s.runs.filter (·.complete)).length +
    s.invocations.length + (s.invocations.filter (·.status != .active)).length +
    (s.calls.map fun c => 1 + callProgress c).sum +
    s.executions.length + (s.executions.filter (·.complete)).length +
    (s.executions.map fun e => (e.tasks.map taskProgress).sum).sum +
    s.results.length + s.taskResults.length + (s.taskResults.filter (·.output != .pending)).length +
    s.deliveries.length + s.settled.length

theorem work_empty : work {} = 0 := rfl

/-! ### `work` as a sum of weights, one per record

`work_eq` splits `work` into one weighted sum per record list. A state update then changes one sum,
and replacing a record by one that is not behind it does not lower that sum (`sum_replace_le`). -/

namespace WorkProof

/-- Replacing the members selected by `P` with `y` does not lower a sum when `y` weighs at least as
    much as each of them. -/
theorem sum_replace_le {α : Type} {l : List α} {P : α → Bool} {y : α} {f : α → Nat}
    (h : ∀ x ∈ l, P x = true → f x ≤ f y) :
    (l.map f).sum ≤ ((l.map fun x => if P x then y else x).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.sum_cons]
    by_cases hp : P a = true
    · have := h a List.mem_cons_self hp
      simp only [hp, ite_true]
      omega
    · simp only [hp, Bool.false_eq_true, ite_false]
      omega

/-- The strict version: some replaced member weighs less than `y`. -/
theorem sum_replace_lt {α : Type} {l : List α} {P : α → Bool} {y : α} {f : α → Nat}
    (h : ∀ x ∈ l, P x = true → f x ≤ f y) {x₀ : α} (hx₀ : x₀ ∈ l) (hp₀ : P x₀ = true) (hlt : f x₀ < f y) :
    (l.map f).sum < ((l.map fun x => if P x then y else x).map f).sum := by
  induction l with
  | nil => cases hx₀
  | cons a l ih =>
    have hle := sum_replace_le (l := l) (P := P) (y := y) (f := f) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx₀ with rfl | hx
    · simp only [hp₀, ite_true]
      omega
    · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hx
      by_cases hp : P a = true
      · have := h a List.mem_cons_self hp
        simp only [hp, ite_true]
        omega
      · simp only [hp, Bool.false_eq_true, ite_false]
        omega

/-- A map that lowers no weight does not lower the sum. -/
theorem sum_map_le {α : Type} {l : List α} {g : α → α} {f : α → Nat} (h : ∀ x ∈ l, f x ≤ f (g x)) :
    (l.map f).sum ≤ ((l.map g).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a List.mem_cons_self
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

theorem sum_count {α : Type} (l : List α) (q : α → Bool) :
    (l.map fun x => 1 + if q x then 1 else 0).sum = l.length + (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.filter_cons]
    by_cases hq : q a = true
    · simp only [hq, ite_true, List.length_cons]
      omega
    · simp only [hq, Bool.false_eq_true, ite_false]
      omega

/-! Weights of the records in `work`. -/

def runW (r : Run) : Nat := 1 + if r.complete then 1 else 0
def invW (i : Invocation) : Nat := 1 + if i.status != .active then 1 else 0
def callW (c : Call) : Nat := 1 + callProgress c
def execW (e : Execution) : Nat := 1 + (if e.complete then 1 else 0) + (e.tasks.map taskProgress).sum
def trW (r : TaskResult) : Nat := 1 + if r.output != .pending then 1 else 0
def flagW (s : State) : Nat := s.started.toNat + s.cancelled.toNat + statusProgress s.status

theorem execs_sum (l : List Execution) :
    (l.map execW).sum = l.length + (l.filter (·.complete)).length +
      (l.map fun e => (e.tasks.map taskProgress).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.filter_cons, execW] at ih ⊢
    by_cases hq : a.complete = true
    · simp only [hq, ite_true, List.length_cons]
      omega
    · simp only [hq, Bool.false_eq_true, ite_false]
      omega

theorem work_eq (s : State) : work s = flagW s + (s.runs.map runW).sum + (s.invocations.map invW).sum +
    (s.calls.map callW).sum + (s.executions.map execW).sum + s.results.length +
    (s.taskResults.map trW).sum + s.deliveries.length + s.settled.length := by
  have hr : (s.runs.map runW).sum = s.runs.length + (s.runs.filter (·.complete)).length := sum_count _ _
  have hi : (s.invocations.map invW).sum =
      s.invocations.length + (s.invocations.filter (·.status != .active)).length := sum_count _ _
  have ht : (s.taskResults.map trW).sum =
      s.taskResults.length + (s.taskResults.filter (·.output != .pending)).length := sum_count _ _
  have hb : ∀ b : Bool, (if b then 1 else 0) = b.toNat := fun b => by cases b <;> rfl
  rw [hr, hi, ht, execs_sum]
  unfold work flagW callW
  rw [hb, hb]
  omega

theorem invW_le (i : Invocation) : invW i ≤ 2 := by unfold invW; split <;> omega
theorem runW_le (r : Run) : runW r ≤ 2 := by unfold runW; split <;> omega
theorem trW_le (r : TaskResult) : trW r ≤ 2 := by unfold trW; split <;> omega
theorem taskProgress_le (x : TaskState) : taskProgress x ≤ 3 := by unfold taskProgress; split <;> omega

/-- An ended task has the largest progress. -/
theorem taskProgress_le_ended (x : TaskState) {y : TaskState} (h : y.status.ended = true) :
    taskProgress x ≤ taskProgress y := by
  have : taskProgress y = 3 := by
    unfold taskProgress
    cases hy : y.status <;> simp_all [TaskStatus.ended]
  have := taskProgress_le x
  omega

end WorkProof

open WorkProof

/-- Rewrites both sides of a comparison of `work` into weights, reads the fields a state update keeps
    through it, and splits appended records off their lists. -/
local macro "work_simp" : tactic => `(tactic| (
  rw [work_eq, work_eq]
  simp only [flagW, invW, callW, runW, execW, trW, List.map_append, List.sum_append, List.length_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    Bool.toNat_true, Bool.toNat_false,
    setRun_status, setRun_started, setRun_cancelled, setRun_invocations, setRun_calls, setRun_executions,
    setRun_results, setRun_taskResults, setRun_deliveries, setRun_settled,
    setInvocation_status, setInvocation_started, setInvocation_cancelled, setInvocation_runs,
    setInvocation_calls, setInvocation_executions, setInvocation_results, setInvocation_taskResults,
    setInvocation_deliveries, setInvocation_settled,
    setCall_status, setCall_started, setCall_cancelled, setCall_runs, setCall_invocations,
    setCall_executions, setCall_results, setCall_taskResults, setCall_deliveries, setCall_settled,
    setExecution_status, setExecution_started, setExecution_cancelled, setExecution_runs,
    setExecution_invocations, setExecution_calls, setExecution_results, setExecution_taskResults,
    setExecution_deliveries, setExecution_settled,
    setTask_status, setTask_started, setTask_cancelled, setTask_runs, setTask_invocations, setTask_calls,
    setTask_results, setTask_taskResults, setTask_deliveries, setTask_settled,
    setTaskResult_status, setTaskResult_started, setTaskResult_cancelled, setTaskResult_runs,
    setTaskResult_invocations, setTaskResult_calls, setTaskResult_executions, setTaskResult_results,
    setTaskResult_deliveries, setTaskResult_settled,
    stop_status, stop_started, stop_cancelled, stop_runs, stop_invocations, stop_results, stop_taskResults,
    stop_deliveries, stop_settled]))

namespace WorkProof

/-! ### The state updates of `Step.lean` and `work` -/

section Primitive
variable {s t : State}

/-- With unique call identities, `setCall` replaces the one call with the same identity. -/
theorem work_setCall_le {c c' : Call} (hnd : (s.calls.map (·.id)).Nodup) (hc : c ∈ s.calls)
    (hid : c'.id = c.id) (hle : callProgress c ≤ callProgress c') : work s ≤ work (s.setCall c') := by
  have key : (s.calls.map callW).sum ≤ ((s.setCall c').calls.map callW).sum := by
    rw [setCall_calls]
    apply sum_replace_le
    intro x hx hp
    rw [Limit.eq_of_key hnd hx hc ((beq_iff_eq.mp hp).trans hid)]
    unfold callW
    omega
  work_simp
  omega

theorem work_setCall_lt {c c' : Call} (hnd : (s.calls.map (·.id)).Nodup) (hc : c ∈ s.calls)
    (hid : c'.id = c.id) (hlt : callProgress c < callProgress c') : work s < work (s.setCall c') := by
  have key : (s.calls.map callW).sum < ((s.setCall c').calls.map callW).sum := by
    rw [setCall_calls]
    refine sum_replace_lt ?_ hc (by simp [hid]) (by unfold callW; omega)
    intro x hx hp
    rw [Limit.eq_of_key hnd hx hc ((beq_iff_eq.mp hp).trans hid)]
    unfold callW
    omega
  work_simp
  omega

/-- An invocation that is no longer active has the largest weight. -/
theorem work_setInvocation_le {i' : Invocation} (hst : i'.status ≠ .active) :
    work s ≤ work (s.setInvocation i') := by
  have key : (s.invocations.map invW).sum ≤ ((s.setInvocation i').invocations.map invW).sum := by
    rw [setInvocation_invocations]
    apply sum_replace_le
    intro x _ _
    have h2 : invW i' = 2 := by simp [invW, hst]
    have := invW_le x
    omega
  work_simp
  omega

/-- A complete run has the largest weight. -/
theorem work_setRun_le {r' : Run} (hc : r'.complete = true) : work s ≤ work (s.setRun r') := by
  have key : (s.runs.map runW).sum ≤ ((s.setRun r').runs.map runW).sum := by
    rw [setRun_runs]
    apply sum_replace_le
    intro x _ _
    have h2 : runW r' = 2 := by simp [runW, hc]
    have := runW_le x
    omega
  work_simp
  omega

theorem work_setRun_lt {r r' : Run} (hc : r'.complete = true) (hr : r ∈ s.runs) (hpath : r.path = r'.path)
    (hinc : r.complete = false) : work s < work (s.setRun r') := by
  have h2 : runW r' = 2 := by simp [runW, hc]
  have key : (s.runs.map runW).sum < ((s.setRun r').runs.map runW).sum := by
    rw [setRun_runs]
    refine sum_replace_lt (fun x _ _ => ?_) hr (by simp [hpath]) (by simp [runW, hinc, hc])
    have := runW_le x
    omega
  work_simp
  omega

theorem work_setExecution_lt {e e' : Execution} (hnd : (s.executions.map (·.id)).Nodup)
    (he : e ∈ s.executions) (hid : e'.id = e.id) (hlt : execW e < execW e') :
    work s < work (s.setExecution e') := by
  have key : (s.executions.map execW).sum < ((s.setExecution e').executions.map execW).sum := by
    rw [setExecution_executions]
    refine sum_replace_lt (fun x hx hp => ?_) he (by simp [hid]) hlt
    rw [Limit.eq_of_key hnd hx he ((beq_iff_eq.mp hp).trans hid)]
    omega
  work_simp
  omega

theorem execW_withTask_le {e : Execution} {ts : TaskState}
    (hle : ∀ x ∈ e.tasks, x.name = ts.name → taskProgress x ≤ taskProgress ts) :
    execW e ≤ execW (withTask e ts) := by
  have := sum_replace_le (l := e.tasks) (P := fun x => x.name == ts.name) (y := ts) (f := taskProgress)
    fun x hx hp => hle x hx (beq_iff_eq.mp hp)
  unfold execW
  rw [withTask_complete, withTask_tasks]
  omega

theorem execW_withTask_lt {e : Execution} {ts x : TaskState}
    (hle : ∀ x ∈ e.tasks, x.name = ts.name → taskProgress x ≤ taskProgress ts) (hx : x ∈ e.tasks)
    (hxn : x.name = ts.name) (hlt : taskProgress x < taskProgress ts) :
    execW e < execW (withTask e ts) := by
  have := sum_replace_lt (l := e.tasks) (P := fun x => x.name == ts.name) (y := ts) (f := taskProgress)
    (fun x hx hp => hle x hx (beq_iff_eq.mp hp)) hx (by simp [hxn]) hlt
  unfold execW
  rw [withTask_complete, withTask_tasks]
  omega

/-- `setTask` replaces every task named like `ts` in the one execution with the identity of `e`. -/
theorem work_setTask_le {e : Execution} {ts : TaskState} (hnd : (s.executions.map (·.id)).Nodup)
    (he : e ∈ s.executions) (hle : ∀ x ∈ e.tasks, x.name = ts.name → taskProgress x ≤ taskProgress ts) :
    work s ≤ work (s.setTask e ts) := by
  have key : (s.executions.map execW).sum ≤ ((s.setTask e ts).executions.map execW).sum := by
    rw [setTask_eq, setExecution_executions]
    apply sum_replace_le
    intro x hx hp
    rw [Limit.eq_of_key hnd hx he (beq_iff_eq.mp hp)]
    exact execW_withTask_le hle
  work_simp
  omega

theorem work_setTask_lt {e : Execution} {ts x : TaskState} (hnd : (s.executions.map (·.id)).Nodup)
    (he : e ∈ s.executions) (hle : ∀ x ∈ e.tasks, x.name = ts.name → taskProgress x ≤ taskProgress ts)
    (hx : x ∈ e.tasks) (hxn : x.name = ts.name) (hlt : taskProgress x < taskProgress ts) :
    work s < work (s.setTask e ts) := by
  have key : (s.executions.map execW).sum < ((s.setTask e ts).executions.map execW).sum := by
    rw [setTask_eq, setExecution_executions]
    refine sum_replace_lt (fun y hy hp => ?_) he (by simp) (execW_withTask_lt hle hx hxn hlt)
    rw [Limit.eq_of_key hnd hy he (beq_iff_eq.mp hp)]
    exact execW_withTask_le hle
  work_simp
  omega

theorem work_setTaskResult_lt {r r' : TaskResult} (hr : r ∈ s.taskResults)
    (hkey : r.execution = r'.execution ∧ r.task = r'.task ∧ r.index = r'.index)
    (hpend : r.output = .pending) (hout : r'.output ≠ .pending) : work s < work (s.setTaskResult r') := by
  have h2 : trW r' = 2 := by simp [trW, hout]
  have key : (s.taskResults.map trW).sum < ((s.setTaskResult r').taskResults.map trW).sum := by
    rw [setTaskResult_taskResults]
    refine sum_replace_lt (fun x _ _ => ?_) hr (by simp [hkey]) (by simp [trW, hpend, hout])
    have := trW_le x
    omega
  work_simp
  omega

theorem callProgress_stopCall (c : Call) : callProgress c ≤ callProgress (stopCall c) := by
  rw [stopCall]
  split
  · rename_i h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h <;> simp [callProgress, h]
  · exact Nat.le_refl _

theorem execW_stopExecution (e : Execution) : execW e ≤ execW (stopExecution e) := by
  have := sum_map_le (l := e.tasks) (g := Limit.stopTask) (f := taskProgress) fun x _ => by
    unfold Limit.stopTask
    split
    · exact taskProgress_le_ended x rfl
    · exact Nat.le_refl _
  unfold execW
  rw [stopExecution_complete, Limit.stopExecution_tasks]
  omega

/-- The stop moves calls to `cancelling` and waiting tasks to `notStarted`, never back. -/
theorem work_stop_le (h : s.status = .running ∨ s.status = .stopping) : work s ≤ work s.stop := by
  have hc : (s.calls.map callW).sum ≤ (s.stop.calls.map callW).sum := by
    rw [stop_calls]
    exact sum_map_le fun c _ => by have := callProgress_stopCall c; unfold callW; omega
  have he : (s.executions.map execW).sum ≤ (s.stop.executions.map execW).sum := by
    rw [stop_executions]
    exact sum_map_le fun e _ => execW_stopExecution e
  have hst : statusProgress s.status ≤ statusProgress .stopping := by
    rcases h with h | h <;> simp [h, statusProgress]
  work_simp
  omega

theorem work_stop_lt (h : s.status = .running) : work s < work s.stop := by
  have hc : (s.calls.map callW).sum ≤ (s.stop.calls.map callW).sum := by
    rw [stop_calls]
    exact sum_map_le fun c _ => by have := callProgress_stopCall c; unfold callW; omega
  have he : (s.executions.map execW).sum ≤ (s.stop.executions.map execW).sum := by
    rw [stop_executions]
    exact sum_map_le fun e _ => execW_stopExecution e
  have hst : statusProgress s.status < statusProgress .stopping := by simp [h, statusProgress]
  work_simp
  omega

theorem work_withFailure {f : Failure} : work { s with failures := s.failures ++ [f] } = work s := rfl

theorem work_fail_le {f : Failure} {policy : Policy} (h : s.status = .running ∨ s.status = .stopping) :
    work s ≤ work (s.fail f policy) := by
  cases policy
  · rw [fail_stop, ← work_withFailure (f := f)]
    exact work_stop_le h
  · rw [fail_continue, work_withFailure]
    exact Nat.le_refl _

theorem work_settleOwner_le {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (hnd : (s.executions.map (·.id)).Nodup) (hinv : inv ≠ .active) (htask : task.ended = true)
    (h : s.settleOwner c inv task = .ok t) : work s ≤ work t := by
  rcases settleOwner_eq_ok.mp h with ⟨-, i, -, rfl⟩ | ⟨name, e, ts, -, he, -, rfl⟩
  · exact work_setInvocation_le hinv
  · exact work_setTask_le hnd (execution?_eq_some he).1 fun x _ _ => taskProgress_le_ended x htask

theorem work_cancelOwner_le {c : Call} (hnd : (s.executions.map (·.id)).Nodup)
    (h : s.cancelOwner c = .ok t) : work s ≤ work t := by
  rcases cancelOwner_eq_ok.mp h with ⟨-, i, -, rfl⟩ | ⟨name, e, ts, -, he, -, rfl⟩
  · split
    · exact work_setInvocation_le (by simp)
    · exact Nat.le_refl _
  · split
    · exact work_setTask_le hnd (execution?_eq_some he).1 fun x _ _ => taskProgress_le_ended x rfl
    · exact Nat.le_refl _

/-- Accepting a value appends a result, or a task result that is not transformed yet. -/
theorem work_accept {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : work t = work s + 1 := by
  rcases accept_eq_ok.mp h with ⟨-, i, -, -, rfl⟩ | ⟨name, -, -, rfl⟩
  · work_simp
    omega
  · work_simp
    simp
    omega

theorem work_failCall_lt {c : Call} {status : CallStatus} {cause : Cause}
    (hcn : (s.calls.map (·.id)).Nodup) (hen : (s.executions.map (·.id)).Nodup) (hc : c ∈ s.calls)
    (hlt : callProgress c < callProgress { c with status }) (hst : s.status = .running ∨ s.status = .stopping)
    (h : s.failCall c status cause = .ok t) : work s < work t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp h
  have h1 := work_setCall_lt (c' := { c with status }) hcn hc rfl hlt
  have h2 := work_settleOwner_le (by simpa using hen) (by decide) rfl hso
  have h3 := work_fail_le (s := s') (f := f) (policy := c.policy)
    (by rw [(settleOwner_update hso).status, setCall_status]; exact hst)
  omega

theorem work_withCancelled {u : State} : work { u with cancelled := true } = work u + (!u.cancelled).toNat := by
  work_simp
  cases u.cancelled <;> simp <;> omega

theorem work_withStatus_lt {u : State} {st : Status} (h : statusProgress u.status < statusProgress st) :
    work u < work { u with status := st } := by
  work_simp
  omega

end Primitive

/-! ### Elements stay within the script -/

/-- Every call has yielded at most `Y` of its identity. -/
def YieldsLe (Y : String → Nat) (s : State) : Prop := ∀ c ∈ s.calls, c.yields ≤ Y c.id

namespace YieldsLe
variable {Y : String → Nat} {s t : State}

theorem of_calls (h : YieldsLe Y s) (hc : t.calls = s.calls) : YieldsLe Y t := by
  intro c hc'
  rw [hc] at hc'
  exact h c hc'

theorem setCall (h : YieldsLe Y s) {c' : Call} (hc' : c'.yields ≤ Y c'.id) : YieldsLe Y (s.setCall c') := by
  intro c hc
  rcases mem_setCall_calls hc with rfl | hc
  · exact hc'
  · exact h c hc

theorem stop (h : YieldsLe Y s) : YieldsLe Y s.stop := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := mem_stop_calls.mp hc
  have : (stopCall c').yields = c'.yields := by unfold stopCall; split <;> rfl
  rw [this, stopCall_id]
  exact h c' hc'

theorem fail (h : YieldsLe Y s) {f : Failure} {policy : Policy} : YieldsLe Y (s.fail f policy) := by
  cases policy
  · exact (h.of_calls (t := { s with failures := s.failures ++ [f] }) rfl).stop
  · exact h.of_calls rfl

theorem append (h : YieldsLe Y s) {c : Call} (hc : c.yields ≤ Y c.id) (ht : t.calls = s.calls ++ [c]) :
    YieldsLe Y t := by
  intro x hx
  rw [ht, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h x hx
  · exact hc

theorem failCall (h : YieldsLe Y s) {c : Call} {status : CallStatus} {cause : Cause} (hc : c ∈ s.calls)
    (hf : s.failCall c status cause = .ok t) : YieldsLe Y t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  exact ((h.setCall (c' := { c with status }) (h c hc)).of_calls (settleOwner_update hso).calls).fail

theorem cancelOwner (h : YieldsLe Y s) {c : Call} (hc : c ∈ s.calls)
    (ho : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) : YieldsLe Y t :=
  (h.setCall (c' := { c with status := .cancelled }) (h c hc)).of_calls (cancelOwner_update ho).calls

end YieldsLe

/-- One step keeps every call within `Y`, provided an element is accepted only below `Y`: `yielded`
    is the only step that raises `yields`, and new calls start at 0. -/
theorem step_yieldsLe {Y : String → Nat} {op : Op} (h : YieldsLe Y s) (hs : step p s op = .ok t)
    (hy : ∀ id v c, op = .yielded id v → s.call? id = some c → c.yields < Y id) : YieldsLe Y t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact h.of_calls rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact h.append (Nat.zero_le _) rfl
    · exact h.append (Nat.zero_le _) rfl
    · exact h.of_calls rfl
    · exact h.of_calls rfl
  | fetch id =>
    obtain ⟨-, -, c, hc, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.setCall (c' := { c with status := .fetching }) (h c (call?_eq_some hc).1)
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact ((h.of_calls (accept_frame hacc).2.2.2.2.2.1).setCall (c' := { c with status := .returned })
      (h c (call?_eq_some hc).1)).of_calls (settleOwner_update hso).calls
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact ((h.of_calls (accept_frame hacc).2.2.2.2.2.1).setCall (c' := { c with status := .returned })
      (h c (call?_eq_some hc).1)).of_calls rfl
  | yielded id v =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    refine (h.of_calls (accept_frame hacc).2.2.2.2.2.1).setCall
      (c' := { c with status := .running, yields := c.yields + 1 }) ?_
    show c.yields + 1 ≤ Y c.id
    rw [(call?_eq_some hc).2]
    exact hy id v c rfl hc
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    exact (h.setCall (c' := { c with status := .returned }) (h c (call?_eq_some hc).1)).of_calls
      (settleOwner_update hso).calls
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact h.failCall (call?_eq_some hc).1 hf
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    exact h.failCall (call?_eq_some hc).1 hf
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.failCall (call?_eq_some hc).1 hf
    · exact h.cancelOwner (call?_eq_some hc).1 ho
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact h.cancelOwner (call?_eq_some hc).1 ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.of_calls rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact (h.of_calls (by rfl)).fail
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.of_calls rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (h.of_calls (by rfl)).fail
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact h.append (Nat.zero_le _) rfl
    · exact h.of_calls rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h.of_calls rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (h.of_calls (by rfl)).fail
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h.of_calls rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact h.of_calls rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨-, _, -, hcases⟩ | ⟨_, _, _, -, -, -, hcases⟩ <;>
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h.of_calls rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.stop.of_calls rfl
    · exact h.of_calls rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact h.of_calls rfl

end WorkProof

/-- Every accepted operation that changes a reachable state raises `work`: records are only appended,
    statuses only move forward (`running → fetching → running` adds an element), and the stop moves
    calls to `cancelling` and waiting tasks to `notStarted`. Reachability gives unique keys
    (`WellKeyed`) and equal same-named tasks (Round 2 `Limit.Inv.coherent`), so each `set*` replaces
    records by records that are not behind. Conformance is not needed. -/
theorem step_work_lt (h : Reachable p s) (hs : step p s op = .ok t) (hne : t ≠ s) : work s < work t := by
  have wk := h.wellKeyed
  have coh := (Limit.reachable_inv h).coherent
  cases op with
  | start input =>
    -- Only the empty state is not started.
    obtain ⟨h1, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h.eq_empty_or_started with rfl | h2
    · simp [work, statusProgress]
    · simp [h2] at h1
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      (work_simp; omega)
  | fetch id =>
    obtain ⟨-, -, c, hc, -, hrun, rfl⟩ := Step.fetch_inv hs
    exact work_setCall_lt wk.calls (call?_eq_some hc).1 rfl (by simp [callProgress, hrun])
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, hst, -, hacc, hso⟩ := Step.returned_inv hs
    obtain ⟨-, -, -, -, -, hcalls, hexecs, -⟩ := accept_frame hacc
    have h1 := work_accept hacc
    have h2 := work_setCall_le (c := c) (c' := { c with status := .returned }) (by rw [hcalls]; exact wk.calls)
      (by rw [hcalls]; exact (call?_eq_some hc).1) rfl (by simp [callProgress, hst])
    have h3 := work_settleOwner_le (by simpa [hexecs] using wk.executions) (by decide) rfl hso
    omega
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, hst, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    obtain ⟨-, -, -, -, -, hcalls, -, -⟩ := accept_frame hacc
    have h1 := work_accept hacc
    have h2 := work_setCall_le (c := c) (c' := { c with status := .returned }) (by rw [hcalls]; exact wk.calls)
      (by rw [hcalls]; exact (call?_eq_some hc).1) rfl (by simp [callProgress, hst])
    have h3 := work_setInvocation_le (s := s'.setCall { c with status := .returned })
      (i' := { i with status := .succeeded, arm := some arm }) (by simp)
    omega
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, hst, hacc, rfl⟩ := Step.yielded_inv hs
    obtain ⟨-, -, -, -, -, hcalls, -, -⟩ := accept_frame hacc
    have h1 := work_accept hacc
    have h2 := work_setCall_le (c := c) (c' := { c with status := .running, yields := c.yields + 1 })
      (by rw [hcalls]; exact wk.calls) (by rw [hcalls]; exact (call?_eq_some hc).1) rfl
      (by simp only [callProgress, hst]; omega)
    omega
  | ended id =>
    obtain ⟨-, -, c, hc, -, hst, hso⟩ := Step.ended_inv hs
    have h1 := work_setCall_lt (c' := { c with status := .returned }) wk.calls (call?_eq_some hc).1 rfl
      (by simp [callProgress, hst])
    have h2 := work_settleOwner_le (by simpa using wk.executions) (by decide) rfl hso
    omega
  | failed id =>
    obtain ⟨-, hrun, c, hc, hst, hf⟩ := Step.failed_inv hs
    exact work_failCall_lt wk.calls wk.executions (call?_eq_some hc).1
      (by rcases hst with h | h <;> simp [callProgress, h]) (Or.inl hrun) hf
  | timedOut id element =>
    obtain ⟨-, hrun, c, hc, hst, hf⟩ := Step.timedOut_inv hs
    refine work_failCall_lt wk.calls wk.executions (call?_eq_some hc).1 ?_ (Or.inl hrun) hf
    rcases hst with ⟨-, h, -⟩ | ⟨-, h | h, -⟩ <;> simp [callProgress, h]
  | lost id =>
    obtain ⟨-, hst, c, hc, ⟨hcs, hf⟩ | ⟨hcs, ho⟩⟩ := Step.lost_inv hs
    · exact work_failCall_lt wk.calls wk.executions (call?_eq_some hc).1
        (by rcases hcs with h | h <;> simp [callProgress, h]) hst hf
    · have h1 := work_setCall_lt (c' := { c with status := .cancelled }) wk.calls (call?_eq_some hc).1 rfl
        (by simp [callProgress, hcs])
      have h2 := work_cancelOwner_le (by simpa using wk.executions) ho
      omega
  | terminated id =>
    obtain ⟨-, -, c, hc, hcs, ho⟩ := Step.terminated_inv hs
    have h1 := work_setCall_lt (c' := { c with status := .cancelled }) wk.calls (call?_eq_some hc).1 rfl
      (by simp [callProgress, hcs])
    have h2 := work_cancelOwner_le (by simpa using wk.executions) ho
    omega
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    work_simp
    omega
  | transformFailed path index source =>
    obtain ⟨-, hrun, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Nat.lt_of_lt_of_le (by work_simp; omega) (work_fail_le (Or.inl hrun))
  | taskInput eid name value =>
    -- Same-named tasks are equal, so each task the update replaces was pending.
    obtain ⟨-, -, e, ts, spec, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    have he' := (execution?_eq_some he).1
    have hts' := (find?_key_eq_some hts).1
    refine work_setTask_lt wk.executions he' (fun x hx hxn => ?_) hts' rfl (by simp [taskProgress, hpend])
    rw [coh e he' x hx ts hts' hxn]
    simp [taskProgress, hpend]
  | taskInputFailed eid name =>
    obtain ⟨-, hrun, e, ts, spec, tid, he, hts, hpend, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    have he' := (execution?_eq_some he).1
    have hts' := (find?_key_eq_some hts).1
    have h1 : work s < work (s.setTask e { ts with status := .failed }) :=
      work_setTask_lt wk.executions he' (fun x _ _ => taskProgress_le_ended x rfl) hts' rfl
        (by simp [taskProgress, hpend])
    exact Nat.lt_of_lt_of_le h1 (work_fail_le (s := s.setTask e { ts with status := .failed }) (Or.inl hrun))
  | beginTask eid name =>
    obtain ⟨-, -, e, c, ts, spec, he, -, -, hts, hready, -, -, hcases⟩ := Step.beginTask_inv hs
    have he' := (execution?_eq_some he).1
    have hts' := (find?_key_eq_some hts).1
    have h1 : work s ≤ work (s.setTask e { ts with status := .active }) := by
      refine work_setTask_le wk.executions he' fun x hx hxn => ?_
      rw [coh e he' x hx ts hts' hxn]
      simp [taskProgress, hready]
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;>
      exact Nat.lt_of_le_of_lt h1 (by work_simp; omega)
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, c, spec, r, -, -, -, -, hr, hpend, hcases⟩ := Step.taskOutput_inv hs
    have h1 : work s < work (s.setTaskResult { r with output := .value value }) :=
      work_setTaskResult_lt (r := r) (List.mem_of_find?_eq_some hr) ⟨rfl, rfl, rfl⟩ hpend (by simp)
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact Nat.lt_of_lt_of_le h1 (by work_simp; omega)
    · exact h1
  | taskOutputFailed eid name index =>
    obtain ⟨-, hrun, e, spec, r, -, -, -, hr, hpend, rfl⟩ := Step.taskOutputFailed_inv hs
    have h1 : work s < work (s.setTaskResult { r with output := .failed }) :=
      work_setTaskResult_lt (r := r) (List.mem_of_find?_eq_some hr) ⟨rfl, rfl, rfl⟩ hpend (by simp)
    exact Nat.lt_of_lt_of_le h1 (work_fail_le (s := s.setTaskResult { r with output := .failed }) (Or.inl hrun))
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> (work_simp; omega)
  | closeExecution eid =>
    obtain ⟨-, -, e, c, i, he, hinc, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    have h1 : work s < work (s.setExecution { e with complete := true }) :=
      work_setExecution_lt wk.executions (execution?_eq_some he).1 rfl (by simp [execW, hinc])
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact Nat.lt_of_lt_of_le h1 (work_setInvocation_le (by simp))
    · exact Nat.lt_of_lt_of_le h1 (Nat.le_trans
        (work_setInvocation_le (i' := { i with status := .succeeded }) (by simp)) (by work_simp; omega))
    · exact Nat.lt_of_lt_of_le h1 (work_setInvocation_le (by simp))
  | closeRun path =>
    obtain ⟨-, -, r, w, output, x, owner, hr, hinc, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    have h1 : work s < work (s.setRun { r with complete := true }) :=
      work_setRun_lt rfl (run?_eq_some hr).1 rfl hinc
    rcases hcases with ⟨-, i, -, hcases⟩ | ⟨name, e, ts, -, he, -, hcases⟩
    · rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Nat.lt_of_lt_of_le h1 (Nat.le_trans
          (work_setInvocation_le (i' := { i with status := .succeeded }) (by simp)) (by work_simp; omega))
      all_goals exact Nat.lt_of_lt_of_le h1 (work_setInvocation_le (by simp))
    · have he' := (execution?_eq_some he).1
      have htask : ∀ st : TaskStatus, st.ended = true →
          work (s.setRun { r with complete := true }) ≤
            work ((s.setRun { r with complete := true }).setTask e { ts with status := st }) :=
        fun st hst => work_setTask_le (by simpa using wk.executions) (by simpa using he')
          fun x _ _ => taskProgress_le_ended x hst
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Nat.lt_of_lt_of_le h1 (Nat.le_trans (htask .succeeded rfl) (by work_simp; omega))
      · exact Nat.lt_of_lt_of_le h1 (htask .skipped rfl)
      · exact Nat.lt_of_lt_of_le h1 (htask .failed rfl)
      · exact Nat.lt_of_lt_of_le h1 (htask .upstreamFailed rfl)
  | cancel =>
    obtain ⟨-, ⟨hrun, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · rw [work_withCancelled]
      have := work_stop_lt hrun
      omega
    · -- A repeated cancel while stopping is the one accepted step that changes nothing.
      rw [work_withCancelled]
      cases hc : s.cancelled
      · simp
      · exfalso
        apply hne
        cases s
        simp only at hc
        subst hc
        rfl
  | conclude =>
    obtain ⟨-, ⟨hrun, r, w, -, -, -, rfl⟩ | ⟨hstop, -, rfl⟩⟩ := Step.conclude_inv hs
    · refine Nat.lt_of_le_of_lt (work_setRun_le (r' := { r with complete := true }) rfl)
        (work_withStatus_lt ?_)
      rw [setRun_status, hrun]
      split
      · decide
      · split <;> decide
    · refine work_withStatus_lt ?_
      rw [hstop]
      split <;> decide

theorem Conforming.length_le_work {tr : List Op} (h : Conforming p env tr s) : tr.length ≤ work s := by
  induction h with
  | nil => simp [work_empty]
  | snoc hex _ hs hne ih =>
    have := step_work_lt hex.reachable hs hne
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- A conforming call has yielded no more elements than its script has, in every state of a
    conforming execution, stopped or not: an element conforms only at an index of the script. -/
theorem Conforming.yields_le {tr : List Op} (h : Conforming p env tr s) :
    ∀ c ∈ s.calls, c.yields ≤ (env.behavior.script c.id).yields.length := by
  induction h with
  | nil => intro c hc; cases hc
  | snoc _ hconf hs _ ih =>
    refine step_yieldsLe (Y := fun id => (env.behavior.script id).yields.length) ih hs ?_
    rintro id v c rfl hc
    obtain ⟨c', hc', hget⟩ := hconf
    rw [hc] at hc'
    cases hc'
    exact (List.getElem?_eq_some_iff.mp hget).1

end Work

end Suimon.Round3
