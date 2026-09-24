import Suimon.Theorems.Round3.Ledger

/-! Helpers for [26] Round3/Symmetry.lean — task G1: lookups by unique keys under permutations, the
    ledger of permuted records, how the root run completes, and the records of a complete state. -/

namespace Suimon.Round3
namespace SymmetryAux
open State

/-! ### Lists with unique keys -/

section Lists
variable {α κ : Type}

/-- Unique keys make the list itself duplicate-free. -/
theorem nodup_of_map {l : List α} {f : α → κ} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ hne heq => hne (congrArg f heq)) h

/-- Two members with the same key are equal. -/
theorem eq_of_key {l : List α} {f : α → κ} (h : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hk : f x = f y) : x = y := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd hk.symm (h.1 y hy')
    · exact absurd hk (h.1 x hx')
    · exact ih h.2 hx' hy'

/-- Lists with unique keys that contain each other are permutations of each other. -/
theorem perm_of_mem {l₁ l₂ : List α} {f : α → κ} (nd₁ : (l₁.map f).Nodup) (nd₂ : (l₂.map f).Nodup)
    (h₁ : ∀ x ∈ l₁, x ∈ l₂) (h₂ : ∀ x ∈ l₂, x ∈ l₁) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup (nodup_of_map nd₁) (nodup_of_map nd₂)).mpr fun _ => ⟨h₁ _, h₂ _⟩

/-- Under a permutation with unique keys, a lookup whose predicate selects a single key finds the same
    record. -/
theorem find?_perm {l₁ l₂ : List α} {f : α → κ} {P : α → Bool} (h : l₁.Perm l₂) (nd : (l₁.map f).Nodup)
    (hP : ∀ x y, P x = true → P y = true → f x = f y) : l₁.find? P = l₂.find? P := by
  cases h₁ : l₁.find? P with
  | none =>
    cases h₂ : l₂.find? P with
    | none => rfl
    | some y =>
      rw [List.find?_eq_none] at h₁
      exact absurd (List.find?_some h₂) (h₁ y (h.mem_iff.mpr (List.mem_of_find?_eq_some h₂)))
  | some x =>
    have hx := List.mem_of_find?_eq_some h₁
    cases h₂ : l₂.find? P with
    | none =>
      rw [List.find?_eq_none] at h₂
      exact absurd (List.find?_some h₁) (h₂ x (h.mem_iff.mp hx))
    | some y =>
      have hy := h.mem_iff.mpr (List.mem_of_find?_eq_some h₂)
      exact congrArg some (eq_of_key nd hx hy (hP x y (List.find?_some h₁) (List.find?_some h₂)))

end Lists

/-! ### Lookups in permuted states -/

section Lookups
variable {S T : State}

theorem run?_perm (wk : S.WellKeyed) (h : S.runs.Perm T.runs) (path : Path) : S.run? path = T.run? path :=
  find?_perm h wk.runs fun x y hx hy => by
    simp only [beq_iff_eq] at hx hy
    rw [hx, hy]

theorem workflow?_perm {p : Definition} (wk : S.WellKeyed) (h : S.runs.Perm T.runs) (path : Path) :
    S.workflow? p path = T.workflow? p path := by
  unfold State.workflow?
  rw [run?_perm wk h]

theorem invocation?_perm (wk : S.WellKeyed) (h : S.invocations.Perm T.invocations) (id : String) :
    S.invocation? id = T.invocation? id :=
  find?_perm h wk.invocations fun x y hx hy => by
    simp only [beq_iff_eq] at hx hy
    rw [hx, hy]

theorem call?_perm (wk : S.WellKeyed) (h : S.calls.Perm T.calls) (id : String) : S.call? id = T.call? id :=
  find?_perm h wk.calls fun x y hx hy => by
    simp only [beq_iff_eq] at hx hy
    rw [hx, hy]

theorem execution?_perm (wk : S.WellKeyed) (h : S.executions.Perm T.executions) (id : String) :
    S.execution? id = T.execution? id :=
  find?_perm h wk.executions fun x y hx hy => by
    simp only [beq_iff_eq] at hx hy
    rw [hx, hy]

theorem settled?_perm (wk : S.WellKeyed) (h : S.settled.Perm T.settled) (path : Path) (name : String) :
    S.settled? path name = T.settled? path name :=
  find?_perm h wk.settled fun x y hx hy => by
    simp only [Bool.and_eq_true, beq_iff_eq] at hx hy
    rw [hx.1, hx.2, hy.1, hy.2]

end Lookups

/-! ### The ledger of permuted records

Every part of the ledger reads the records through lookups by unique keys (`invocation?`,
`execution?`, `call?`, `workflow?`) or through `any`, so it is the same function on permuted records. -/

section LedgerPerm
variable {p : Definition} {S T : State}

theorem ownerFailed_perm (wk : S.WellKeyed) (hinv : S.invocations.Perm T.invocations)
    (hexec : S.executions.Perm T.executions) (c : Call) : ownerFailed S c = ownerFailed T c := by
  simp only [ownerFailed, invocation?_perm wk hinv, execution?_perm wk hexec]

theorem callCause_perm (wk : S.WellKeyed) (hinv : S.invocations.Perm T.invocations)
    (hexec : S.executions.Perm T.executions) (c : Call) : callCause S c = callCause T c := by
  simp only [callCause, ownerFailed_perm wk hinv hexec]

theorem callLedger_perm (wk : S.WellKeyed) (hinv : S.invocations.Perm T.invocations)
    (hexec : S.executions.Perm T.executions) (c : Call) : callLedger S c = callLedger T c := by
  simp only [callLedger, callCause_perm wk hinv hexec, invocation?_perm wk hinv, execution?_perm wk hexec]

theorem deliveryLedger_perm (wk : S.WellKeyed) (hruns : S.runs.Perm T.runs) (d : Delivery) :
    deliveryLedger p S d = deliveryLedger p T d := by
  simp only [deliveryLedger, workflow?_perm wk hruns]

theorem taskInputLedger_perm (wk : S.WellKeyed) (hcalls : S.calls.Perm T.calls) (hruns : S.runs.Perm T.runs)
    (e : Execution) (ts : TaskState) : taskInputLedger S e ts = taskInputLedger T e ts := by
  simp only [taskInputLedger, call?_perm wk hcalls, hruns.any_eq]

theorem taskOutputLedger_perm (wk : S.WellKeyed) (hexec : S.executions.Perm T.executions) (r : TaskResult) :
    taskOutputLedger S r = taskOutputLedger T r := by
  simp only [taskOutputLedger, execution?_perm wk hexec]

/-- The ledger of permuted records is a permutation of the ledger. -/
theorem ledger_perm_of (wk : S.WellKeyed) (hcalls : S.calls.Perm T.calls) (hdel : S.deliveries.Perm T.deliveries)
    (hinv : S.invocations.Perm T.invocations) (hexec : S.executions.Perm T.executions)
    (htr : S.taskResults.Perm T.taskResults) (hruns : S.runs.Perm T.runs) :
    (ledger p S).Perm (ledger p T) := by
  have e₁ : callLedger S = callLedger T := funext (callLedger_perm wk hinv hexec)
  have e₂ : deliveryLedger p S = deliveryLedger p T := funext (deliveryLedger_perm wk hruns)
  have e₃ : taskInputLedger S = taskInputLedger T :=
    funext fun e => funext (taskInputLedger_perm wk hcalls hruns e)
  have e₄ : taskOutputLedger S = taskOutputLedger T := funext (taskOutputLedger_perm wk hexec)
  unfold ledger
  rw [e₁, e₂, e₃, e₄]
  exact (((hcalls.filterMap _).append (hdel.filterMap _)).append (hexec.flatMap_right _)).append
    (htr.filterMap _)

end LedgerPerm

/-! ### How the root run completes

Only `conclude` from a running state completes the root run (`closeRun` refuses the root, and `start`
creates it open), and only `cancel` sets the cancel flag, which leaves the workflow stopping for good.
So a complete state was concluded from a running state that was never cancelled, and it takes no
further step. -/

section Root
variable {p : Definition} {s t : State} {op : Op}

/-- The status `conclude` computes from a running state whose root run executes `w` (§11.4, §13.3). -/
def concludedStatus (w : Workflow) (s : State) : Status :=
  if !s.failures.isEmpty then .failed
  else if (w.placements.filter fun pl => w.isEndpoint pl.name).all
      (fun pl => (s.settled? [] pl.name).any (·.outcome == .skipped)) then .skipped
  else .succeeded

theorem concludedStatus_terminal (w : Workflow) (s : State) : (concludedStatus w s).terminal = true := by
  unfold concludedStatus
  split
  · rfl
  · split <;> rfl

/-- What one step does to the root run and to the cancel flag. -/
def RootStep (op : Op) (s t : State) : Prop :=
  (op = .conclude ∧ s.status = .running) ∨
  ((Done t → Done s) ∧ (t.cancelled = true → s.cancelled = true ∨ t.status = .stopping))

theorem RootStep.of_run? (hr : t.run? [] = s.run? []) (hc : t.cancelled = s.cancelled) : RootStep op s t := by
  refine Or.inr ⟨fun hd => ?_, fun h => Or.inl (hc ▸ h)⟩
  unfold Done at hd ⊢
  rwa [hr] at hd

theorem RootStep.of_runs (hr : t.runs = s.runs) (hc : t.cancelled = s.cancelled) : RootStep op s t :=
  RootStep.of_run? (by unfold State.run?; rw [hr]) hc

theorem RootStep.of_append {x : Run} (hx : x.path ≠ []) (hr : t.runs = s.runs ++ [x])
    (hc : t.cancelled = s.cancelled) : RootStep op s t := by
  refine RootStep.of_run? ?_ hc
  unfold State.run?
  rw [hr, List.find?_append]
  have : ([x].find? fun r => r.path == []) = none := by simp [hx]
  rw [this, Option.or_none]

theorem failCall_frame {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    t.runs = s.runs ∧ t.cancelled = s.cancelled := by
  obtain ⟨_, _, -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  have u := State.settleOwner_update hso
  exact ⟨by simp [u.runs], by simp [u.cancelled]⟩

/-- Every step is a `RootStep`: `closeRun` refuses the root, `start` creates it open, and every other step
    keeps the runs or appends a sub-run. -/
theorem step_root (hs : step p s op = .ok t) : RootStep op s t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    refine Or.inr ⟨fun hd => ?_, fun h => Or.inl h⟩
    simp [Done, State.run?] at hd
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact RootStep.of_runs rfl rfl
    · exact RootStep.of_runs rfl rfl
    · exact RootStep.of_append (Key.child_ne_nil _) rfl rfl
    · exact RootStep.of_runs rfl rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact RootStep.of_runs rfl rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have u := settleOwner_update hso
    have a := accept_frame hacc
    exact RootStep.of_runs (by rw [u.runs, setCall_runs, a.2.2.2.1])
      (by rw [u.cancelled, setCall_cancelled, a.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have a := accept_frame hacc
    exact RootStep.of_runs (by rw [setInvocation_runs, setCall_runs, a.2.2.2.1])
      (by rw [setInvocation_cancelled, setCall_cancelled, a.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    have a := accept_frame hacc
    exact RootStep.of_runs (by rw [setCall_runs, a.2.2.2.1]) (by rw [setCall_cancelled, a.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    have u := settleOwner_update hso
    exact RootStep.of_runs (by rw [u.runs, setCall_runs]) (by rw [u.cancelled, setCall_cancelled])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact RootStep.of_runs (failCall_frame h).1 (failCall_frame h).2
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact RootStep.of_runs (failCall_frame h).1 (failCall_frame h).2
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact RootStep.of_runs (failCall_frame h).1 (failCall_frame h).2
    · have u := cancelOwner_update h
      exact RootStep.of_runs (by rw [u.runs, setCall_runs]) (by rw [u.cancelled, setCall_cancelled])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    have u := cancelOwner_update h
    exact RootStep.of_runs (by rw [u.runs, setCall_runs]) (by rw [u.cancelled, setCall_cancelled])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact RootStep.of_runs rfl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact RootStep.of_runs (by simp) (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact RootStep.of_runs rfl rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact RootStep.of_runs (by simp) (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact RootStep.of_runs rfl rfl
    · exact RootStep.of_append (Key.child_ne_nil _) rfl rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact RootStep.of_runs rfl rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact RootStep.of_runs (by simp) (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact RootStep.of_runs rfl rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact RootStep.of_runs rfl rfl
  | closeRun path =>
    -- `closeRun` completes a run with a non-empty path, never the root.
    obtain ⟨-, -, r, _, _, _, _, hr, -, hne, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    have hrp : ({ r with complete := true } : Run).path ≠ [] := by
      show r.path ≠ []
      rw [(run?_eq_some hr).2]
      exact hne
    have key : (s.setRun { r with complete := true }).run? [] = s.run? [] := by
      rw [run?_setRun]
      simp only [hrp, ite_false]
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact RootStep.of_run? ((show _ = _ by unfold State.run?; simp).trans key) (by simp)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨hst, rfl⟩⟩ := Step.cancel_inv hs
    · exact Or.inr ⟨fun hd => hd, fun _ => Or.inr rfl⟩
    · exact Or.inr ⟨fun hd => hd, fun _ => Or.inr hst⟩
  | conclude =>
    obtain ⟨-, ⟨hrun, -⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact Or.inl ⟨rfl, hrun⟩
    · exact RootStep.of_runs rfl rfl

/-- The flags of a reachable state: a cancelled workflow is no longer running, and a complete one was
    concluded from a running state that was never cancelled. -/
def Flags (p : Definition) (s : State) : Prop :=
  (s.cancelled = true → s.status ≠ .running) ∧
  (Done s → ∃ r w, s.run? [] = some r ∧ p.workflow? r.workflow = some w ∧ s.started = true ∧
    s.cancelled = false ∧ s.status = concludedStatus w s)

theorem reachable_flags (h : Reachable p s) : Flags p s := by
  induction h with
  | empty =>
    refine ⟨(by intro h; cases h), fun hd => ?_⟩
    simp [Done, State.run?] at hd
  | @step s t op _ hs ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    rcases step_root hs with ⟨rfl, hrun⟩ | ⟨hdone, hcanc⟩
    · -- The conclusion from a running state, which was not cancelled.
      obtain ⟨hstarted, ⟨-, r, w, hr, hw, -, rfl⟩ | ⟨hstop, -⟩⟩ := Step.conclude_inv hs
      · have hc : s.cancelled = false := by
          cases hc : s.cancelled
          · rfl
          · exact absurd hrun (ih₁ hc)
        refine ⟨fun h => ?_, fun _ => ⟨{ r with complete := true }, w, ?_, hw, hstarted, hc, rfl⟩⟩
        · exact absurd (hc.symm.trans h) (by simp)
        · show (s.setRun { r with complete := true }).run? [] = _
          rw [run?_setRun]
          simp [(run?_eq_some hr).2, hr]
      · rw [hstop] at hrun
        cases hrun
    · refine ⟨fun h => ?_, fun hd => ?_⟩
      · rcases hcanc h with h' | h'
        · exact (step_status hs).1 ((step_source_status hs).resolve_left (ih₁ h'))
        · rw [h']
          simp
      · -- A complete state is final and takes no step.
        obtain ⟨_, w, -, -, -, -, hst⟩ := ih₂ (hdone hd)
        have hterm : s.status.terminal = true := hst ▸ concludedStatus_terminal w s
        rcases step_source_status hs with h' | h' <;> simp [h', Status.terminal] at hterm

/-- A complete state was concluded from a running state that was never cancelled. -/
theorem done_root (h : Reachable p s) (done : Done s) :
    ∃ r w, s.run? [] = some r ∧ p.workflow? r.workflow = some w ∧ s.started = true ∧
      s.cancelled = false ∧ s.status = concludedStatus w s :=
  (reachable_flags h).2 done

end Root

/-! ### The records of a complete state -/

section Records
variable {p : Definition} {s : State}

/-- In a complete state every run and execution completed, every call ended, and no invocation is
    active (Round 2 `Reachable.done_complete`, `Delivery.invocation_ended`). -/
theorem done_records (h : Reachable p s) (done : Done s) :
    (∀ r ∈ s.runs, r.complete = true) ∧ (∀ e ∈ s.executions, e.complete = true) ∧
      (∀ c ∈ s.calls, c.status.ended = true) ∧ (∀ i ∈ s.invocations, i.status ≠ .active) := by
  obtain ⟨hruns, hexecs, hcalls⟩ := Reachable.done_complete h done
  refine ⟨hruns, hexecs, hcalls, fun i hi => ?_⟩
  exact (Delivery.invocationEnded_iff.mp (Delivery.invocation_ended (Delivery.Reachable.inv h) hruns hi)).1

theorem run_ext {r r' : Run} (h₁ : r'.path = r.path) (h₂ : r'.workflow = r.workflow) (h₃ : r'.input = r.input)
    (h₄ : r'.owner = r.owner) (h₅ : r'.task = r.task) (h₆ : r'.complete = r.complete) : r' = r := by
  cases r
  cases r'
  simp only at h₁ h₂ h₃ h₄ h₅ h₆
  subst h₁ h₂ h₃ h₄ h₅ h₆
  rfl

theorem taskResult_ext {r r' : TaskResult} (h₁ : r'.execution = r.execution) (h₂ : r'.task = r.task)
    (h₃ : r'.index = r.index) (h₄ : r'.value = r.value) (h₅ : r'.output = r.output) : r' = r := by
  cases r
  cases r'
  simp only at h₁ h₂ h₃ h₄ h₅
  subst h₁ h₂ h₃ h₄ h₅
  rfl

/-- Task results that correspond both ways, with the same key and value, and identical once transformed,
    are the same records: a pending result cannot correspond to a transformed one, since that one
    corresponds back to itself, and keys are unique. A complete state can keep pending task results (of
    tasks outside the output), so finished records alone would not suffice. -/
theorem taskResult_mem {A B : State} (wk : A.WellKeyed)
    (h₁ : ∀ r ∈ A.taskResults, ∃ r' ∈ B.taskResults, r'.execution = r.execution ∧ r'.task = r.task ∧
      r'.index = r.index ∧ r'.value = r.value ∧ (r.output ≠ .pending → r' = r))
    (h₂ : ∀ r ∈ B.taskResults, ∃ r' ∈ A.taskResults, r'.execution = r.execution ∧ r'.task = r.task ∧
      r'.index = r.index ∧ r'.value = r.value ∧ (r.output ≠ .pending → r' = r))
    {r : TaskResult} (hr : r ∈ A.taskResults) : r ∈ B.taskResults := by
  obtain ⟨r', hr', he, ht, hi, hv, hfin⟩ := h₁ r hr
  by_cases hp : r.output = .pending
  · by_cases hp' : r'.output = .pending
    · rw [← taskResult_ext he ht hi hv (hp'.trans hp.symm)]
      exact hr'
    · obtain ⟨r'', hr'', he', ht', hi', -, hfin'⟩ := h₂ r' hr'
      have h'' : r'' = r' := hfin' hp'
      have hkey : r'' = r := eq_of_key wk.taskResults hr'' hr (by
        show (_, _, _) = (_, _, _)
        rw [he', ht', hi', he, ht, hi])
      exact absurd (by rw [← h'', hkey]; exact hp) hp'
  · rw [← hfin hp]
    exact hr'

end Records

end SymmetryAux
end Suimon.Round3
