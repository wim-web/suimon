import Suimon.Theorems.WorkCandidates

namespace Suimon
open Explore

theorem invariants_withTime (s : State) (now : Nat) : invariants {s with now} = invariants s := rfl

theorem history_withTime (s next : State) (now : Nat) (history : historyOK s next = true)
    (clock : s.now ≤ now) : historyOK s {next with now} = true := by
  simp only [historyOK, Bool.and_eq_true, decide_eq_true_eq] at history ⊢
  exact ⟨⟨clock, history.1.2⟩, history.2⟩

theorem accept_ordinary (s next : State) (op : Op) (started : s.started = true)
    (active : absorbed s op = false) (auth : authorized s op = true) (notIdle : op ≠ .idle)
    (ready : preconditions s op = true) (executed : transition s op = .ok next)
    (safe : Invariants next) (history : historyOK s next = true) : step s op = .ok next := by
  have body : transitionOrIdle s op = .ok next := by cases op <;> first | exact executed | contradiction
  simp [step, guarded, active, auth, prepare, prepareWith, startupAllowed, started, require, ready,
    body, commit, show invariants next = true from safe, history, bind, Except.bind]

theorem hasWork_of_promoteRetry (s next : State) (inst : InstanceId) (now : Nat) (safe : Invariants s)
    (started : s.started = true) (accepted : step s (.promoteRetry inst now) = .ok next) (changed : next ≠ s) :
    s.hasWork = true := by
  obtain ⟨active, terminal⟩ := progress_active accepted changed
  obtain ⟨_, _, _, safeNext, history⟩ := (step_ok_cases s (.promoteRetry inst now) next accepted).resolve_left
    (fun absorbed => changed absorbed.2)
  have executed := transition_of_active accepted active (by simp)
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
  cases found : s.instance? inst with
  | none => simp [found] at executed
  | some i =>
    simp only [found] at executed
    cases guard : require (now ≥ s.now && i.status == .retryWait && i.retryAt.any (· ≤ now)) "RETRY_NOT_DUE" with
    | error reject => simp [guard] at executed
    | ok u =>
      have condition := require_ok _ _ _ u guard
      simp only [Bool.and_eq_true, beq_iff_eq] at condition
      have waiting := condition.1.2
      obtain ⟨due, retryAt, _⟩ := (Option.any_eq_true _ _).mp condition.2
      simp only [guard, bind, Except.bind, Except.ok.injEq] at executed
      let time := max s.now due
      let result : State := {next with now := time}
      have body : transition s (.promoteRetry inst time) = .ok result := by
        dsimp only [result]
        rw [← executed]
        simp [transition, getInstance, found, Option.toExcept, bind, Except.bind, pure, Except.pure, require,
          waiting, retryAt, time, Nat.le_max_left, Nat.le_max_right]
      have invariant : Invariants result := safeNext
      have hist : historyOK s result = true := history_withTime s next time history (Nat.le_max_left _ _)
      have accepted' := accept_ordinary s result (.promoteRetry inst time) started
        (by simp [absorbed, duplicateComplete, terminal]) (by rfl) (by simp) rfl body invariant hist
      have memberI := instance?_mem found
      have different : result ≠ s := by
        intro eq
        let replacement := {i with status := .ready, retryAt := none}
        have memberReplacement : replacement ∈ result.instances := by
          have fields := congrArg State.instances executed.symm
          have instances : result.instances = (setInstance s replacement).instances := by
            simpa only [result, replacement] using fields
          rw [instances]
          simp only [setInstance, List.mem_map]
          exact ⟨i, memberI, by simp [replacement]⟩
        rw [eq] at memberReplacement
        have same := unique_instance safe memberReplacement memberI rfl
        have status := congrArg Instance.status same
        change InstanceStatus.ready = i.status at status
        rw [waiting] at status
        contradiction
      apply hasWork_of_candidate (instance_candidate_mem s started terminal i memberI _ ?_) rfl accepted' different
      simp [instanceCandidates, waiting, retryAt, time, instance?_id found]

end Suimon
