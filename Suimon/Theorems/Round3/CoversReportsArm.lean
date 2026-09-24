import Suimon.Theorems.Settle
import Suimon.Theorems.Delivery

namespace Suimon.Round3.CoversReportsAux
open State

/-! ## Helper for [23] Round3/CoversReports.lean — task F5

An invocation carries an arm only once its judge returned, and then it succeeded. A report that fails
the call of a branch leaves the invocation failed without an arm; the covering run must then have no
arm on that invocation either. -/

section Arm
variable {p : Definition}

/-- An invocation with a selected arm succeeded. Only `judged` selects an arm, together with the status
    `succeeded`; every other change of an invocation applies to an active one, which has no arm
    (`Settle.Active.activeArm`). -/
def ArmSucceeded (s : State) : Prop := ∀ i ∈ s.invocations, i.arm ≠ none → i.status = .succeeded

theorem ArmSucceeded.of_eq {s t : State} (h : ArmSucceeded s) (he : t.invocations = s.invocations) :
    ArmSucceeded t :=
  fun i hi => h i (he ▸ hi)

theorem ArmSucceeded.set {s : State} (h : ArmSucceeded s) {i : Invocation}
    (hi : i.arm ≠ none → i.status = .succeeded) : ArmSucceeded (s.setInvocation i) := by
  intro x hx harm
  rcases mem_setInvocation_invocations hx with rfl | hx
  · exact hi harm
  · exact h x hx harm

/-- Settling the owner of a call keeps the invariant if the owner, when it is an invocation, has no arm
    or is set succeeded. -/
theorem ArmSucceeded.settleOwner {s t : State} (h : ArmSucceeded s) {c : Call} {st : InvocationStatus}
    {tst : TaskStatus} (ho : s.settleOwner c st tst = .ok t)
    (hst : c.task = none → ∀ i, s.invocation? c.owner = some i → i.arm = none ∨ st = .succeeded) :
    ArmSucceeded t := by
  rcases settleOwner_eq_ok.mp ho with ⟨htask, i, hi, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · refine h.set fun harm => ?_
    rcases hst htask i hi with ha | hs
    · exact absurd ha harm
    · exact hs
  · exact h.of_eq rfl

/-- `cancelOwner` changes only an active owner, which has no arm. -/
theorem ArmSucceeded.cancelOwner {s t : State} (h : ArmSucceeded s)
    (act : ∀ i ∈ s.invocations, i.status = .active → i.arm = none) {c : Call} (ho : s.cancelOwner c = .ok t) :
    ArmSucceeded t := by
  rcases cancelOwner_eq_ok.mp ho with ⟨-, i, hi, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · split
    · rename_i hact
      exact h.set fun harm => absurd (act i (invocation?_eq_some hi).1 hact) harm
    · exact h
  · split
    · exact h.of_eq rfl
    · exact h

theorem ArmSucceeded.step {s t : State} {op : Op} (h : ArmSucceeded s) (act : Settle.Active p s)
    (wk : s.WellKeyed) (hs : step p s op = .ok t) : ArmSucceeded t := by
  -- The owner of a running or fetching call is active, so it has no arm.
  have running_owner : ∀ {c : Call}, c ∈ s.calls → (c.status = .running ∨ c.status = .fetching) →
      c.task = none → ∀ i, s.invocation? c.owner = some i → i.arm = none := by
    intro c hc hrun htask i hi
    obtain ⟨i', hi', hid', hact⟩ := act.callActive c hc htask hrun
    obtain ⟨him, hiid⟩ := invocation?_eq_some hi
    obtain rfl : i = i' := wk.invocation_eq_of_id him hi' (hiid.trans hid'.symm)
    exact act.activeArm i hi' hact
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact h.of_eq rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    intro i hi harm
    rw [(Delivery.invocable_of_invoke hcases).2, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact h i hi harm
    · exact absurd rfl harm
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.of_eq rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have hinv : s'.invocations = s.invocations := (accept_frame hacc).2.2.2.2.1
    exact (h.of_eq (by simp [hinv])).settleOwner hso fun _ _ _ => Or.inr rfl
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hinv : s'.invocations = s.invocations := (accept_frame hacc).2.2.2.2.1
    exact (h.of_eq (by simp [hinv])).set fun _ => rfl
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact h.of_eq (by simp [(accept_frame hacc).2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, c, -, -, -, hso⟩ := Step.ended_inv hs
    exact (h.of_eq (t := s.setCall _) rfl).settleOwner hso fun _ _ _ => Or.inr rfl
  | failed id =>
    obtain ⟨-, -, c, hc, hrun, hf⟩ := Step.failed_inv hs
    obtain ⟨f, s'', -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact ((h.of_eq (t := s.setCall _) rfl).settleOwner hso fun htask i hi =>
      Or.inl (running_owner (call?_eq_some hc).1 hrun htask i hi)).of_eq fail_invocations
  | timedOut id element =>
    obtain ⟨-, -, c, hc, h3, hf⟩ := Step.timedOut_inv hs
    have hrun : c.status = .running ∨ c.status = .fetching := by
      rcases h3 with ⟨-, h', -⟩ | ⟨-, h', -⟩
      · exact Or.inr h'
      · exact h'
    obtain ⟨f, s'', -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact ((h.of_eq (t := s.setCall _) rfl).settleOwner hso fun htask i hi =>
      Or.inl (running_owner (call?_eq_some hc).1 hrun htask i hi)).of_eq fail_invocations
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨hrun, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · obtain ⟨f, s'', -, hso, rfl⟩ := failCall_eq_ok.mp hf
      exact ((h.of_eq (t := s.setCall _) rfl).settleOwner hso fun htask i hi =>
        Or.inl (running_owner (call?_eq_some hc).1 hrun htask i hi)).of_eq fail_invocations
    · exact (h.of_eq (t := s.setCall _) rfl).cancelOwner act.activeArm ho
  | terminated id =>
    obtain ⟨-, -, c, -, -, ho⟩ := Step.terminated_inv hs
    exact (h.of_eq (t := s.setCall _) rfl).cancelOwner act.activeArm ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.of_eq rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact h.of_eq (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.of_eq rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact h.of_eq (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact h.of_eq rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h.of_eq rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact h.of_eq (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h.of_eq rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i, he, hec, -, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    -- The invocation of an open execution is active, so it has no arm.
    have harm : i.arm = none := by
      obtain ⟨hem, heid⟩ := execution?_eq_some he
      obtain ⟨i', hi', hid', hact⟩ := act.execActive e hem hec
      obtain ⟨him, hiid⟩ := invocation?_eq_some hi
      obtain rfl : i = i' := wk.invocation_eq_of_id him hi' (hiid.trans (heid.symm.trans hid'.symm))
      exact act.activeArm i hi' hact
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact (h.of_eq rfl).set fun ha => absurd harm ha
    · exact ((h.of_eq rfl).set (i := { i with status := .succeeded }) fun _ => rfl).of_eq rfl
    · exact (h.of_eq rfl).set fun _ => rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, hrc, -, -, -, -, -, hown, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨_, _, _, -, -, -, hcases⟩
    · -- The owner of an open sub-workflow run is active, so it has no arm.
      have harm : i.arm = none := by
        obtain ⟨i', hi', hid', hact⟩ := act.runActive r (run?_eq_some hr).1 owner hown htask hrc
        obtain ⟨him, hiid⟩ := invocation?_eq_some hi
        obtain rfl : i = i' := wk.invocation_eq_of_id him hi' (hiid.trans hid'.symm)
        exact act.activeArm i hi' hact
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ((h.of_eq rfl).set (i := { i with status := .succeeded }) fun _ => rfl).of_eq rfl
      all_goals exact (h.of_eq rfl).set fun ha => absurd harm ha
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h.of_eq rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact h.of_eq rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact h.of_eq rfl

/-- Every reachable state satisfies `ArmSucceeded`. -/
theorem Reachable.armSucceeded {s : State} (h : Reachable p s) : ArmSucceeded s := by
  induction h with
  | empty => intro i hi; nomatch hi
  | step op hr hs ih => exact ih.step (Settle.reachable hr).2.1 hr.wellKeyed hs

end Arm

end Suimon.Round3.CoversReportsAux
