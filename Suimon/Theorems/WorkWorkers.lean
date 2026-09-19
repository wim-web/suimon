import Suimon.Theorems.WorkInvariants
import Suimon.Theorems.Compound

namespace Suimon

/-- Finishing an attempt changes no logical instance identity or channel data. --/
def retireInstance (i : Instance) (retry : Bool) (due : Nat) : Instance :=
  {i with
    status := if retry then .retryWait else .failed
    lease := none
    retryAt := if retry then some due else none}

def retireAttempt (id : AttemptId) (a : Attempt) : Attempt :=
  if a.id == id then {a with status := .abandoned} else a

def retiredState (s : State) (i : Instance) (l : Lease) (time : Nat) (retry : Bool) (delay : Nat) : State :=
  {setInstance (setAttempt s l.attempt .abandoned) (retireInstance i retry (time + delay)) with
    now := time, status := if retry then s.status else .blocked,
    reason := if retry then s.reason else some "LEASE_EXPIRED"}

theorem lease_witness (s : State) (safe : Invariants s) (i : Instance) (member : i ∈ s.instances)
    (running : i.status = .running) (l : Lease) (lease : i.lease = some l) :
    ∃ a ∈ s.attempts, a.id = l.attempt ∧ a.instance = i.id ∧ a.token = l.token ∧ a.status = .running := by
  have h := List.all_eq_true.mp (invariants_parts s |>.mp safe).2.1 i member
  simp only [running, beq_self_eq_true, ↓reduceIte, lease, Option.any_some] at h
  obtain ⟨a, memberA, conditions⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at conditions
  exact ⟨a, memberA, conditions.1.1.1, conditions.1.1.2, conditions.1.2, conditions.2⟩

theorem attempt_ids (s : State) (safe : Invariants s) : (s.attempts.map (·.id)).Nodup := by
  have h := (invariants_parts s |>.mp safe).2.2
  simp only [attemptOK, Bool.and_eq_true] at h
  exact unique_nodup _ h.1.1.1.1

theorem filter_map_length_le {α : Type} (xs : List α) (f : α → α) (p : α → Bool)
    (onlyOld : ∀ x ∈ xs, p (f x) = true → p x = true) :
    ((xs.map f).filter p).length ≤ (xs.filter p).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y member => onlyOld y (by simp [member]))
    rw [List.map_cons]
    by_cases newP : p (f x) = true
    · have oldP := onlyOld x (by simp) newP
      simp only [List.filter_cons, newP, oldP, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ tail
    · have newFalse := Bool.eq_false_iff.mpr newP
      cases oldP : p x <;> simp only [List.filter_cons, newFalse, oldP, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      · exact tail
      · omega

theorem retired_lookup (s : State) (i : Instance) (l : Lease) (time : Nat) (retry : Bool) (delay : Nat) (id : InstanceId) :
    (retiredState s i l time retry delay).instance? id =
      (s.instance? id).map (fun j => if j.id == i.id then retireInstance i retry (time + delay) else j) := by
  have looked := setInstance_lookup (setAttempt s l.attempt .abandoned) i (retireInstance i retry (time + delay)) rfl id
  exact looked

theorem retired_static (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (l : Lease) (time : Nat) (retry : Bool) (delay : Nat) : staticOK (retiredState s i l time retry delay) = staticOK s := by
  apply staticOK_map s (retiredState s i l time retry delay)
    (fun j => if j.id == i.id then retireInstance i retry (time + delay) else j) rfl rfl rfl rfl
  intro j memberJ
  split
  · rename_i sameId
    have same := unique_instance safe memberJ memberI (beq_iff_eq.mp sameId)
    subst j
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem retired_leaseOK (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (running : i.status = .running) (l : Lease) (lease : i.lease = some l)
    (time : Nat) (retry : Bool) (delay : Nat) : leaseOK (retiredState s i l time retry delay) = true := by
  obtain ⟨owned, memberOwned, ownedId, ownedInstance, _, _⟩ := lease_witness s safe i memberI running l lease
  have old := (invariants_parts s |>.mp safe).2.1
  simp only [leaseOK, retiredState, setInstance, setAttempt, List.all_map, List.all_eq_true, Function.comp_def]
  intro j memberJ
  by_cases selected : j.id == i.id
  · cases retry <;> simp [retireInstance, selected]
  · have oldJ := List.all_eq_true.mp old j memberJ
    simp only [retireInstance, selected, Bool.false_eq_true, ↓reduceIte]
    by_cases runningJ : j.status = .running
    · simp only [runningJ, beq_self_eq_true, ↓reduceIte] at oldJ ⊢
      obtain ⟨jl, leaseJ, witness⟩ := (Option.any_eq_true _ _).mp oldJ
      obtain ⟨a, memberA, props⟩ := List.any_eq_true.mp witness
      have ownedByJ : a.instance = j.id := by
        simp only [Bool.and_eq_true, beq_iff_eq] at props
        exact props.1.1.2
      have notTarget : (a.id == l.attempt) = false := by
        apply Bool.eq_false_iff.mpr
        intro sameId
        have same := eq_of_mapped_nodup (·.id) s.attempts (attempt_ids s safe) a owned memberA memberOwned
          ((beq_iff_eq.mp sameId).trans ownedId.symm)
        have ids : j.id = i.id := ownedByJ.symm.trans (congrArg Attempt.instance same |>.trans ownedInstance)
        exact selected (beq_iff_eq.mpr ids)
      rw [leaseJ]
      simp only [Option.any_some, List.any_eq_true, List.mem_map]
      exact ⟨a, ⟨a, memberA, by simp [notTarget]⟩, props⟩
    · simp [runningJ] at oldJ ⊢
      exact oldJ

theorem retired_attemptOK (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (running : i.status = .running) (l : Lease) (lease : i.lease = some l)
    (time : Nat) (retry : Bool) (delay : Nat) : attemptOK (retiredState s i l time retry delay) = true := by
  have old := (invariants_parts s |>.mp safe).2.2
  simp only [attemptOK, Bool.and_eq_true] at old
  have attemptIds : ((s.attempts.map (retireAttempt l.attempt)).map (·.id)) = s.attempts.map (·.id) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a _
    simp [retireAttempt]; split <;> rfl
  have tokens : ((s.attempts.map (retireAttempt l.attempt)).map (·.token)) = s.attempts.map (·.token) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a _
    simp [retireAttempt]; split <;> rfl
  have attempts : (retiredState s i l time retry delay).attempts = s.attempts.map (retireAttempt l.attempt) := rfl
  have instances : (retiredState s i l time retry delay).instances = s.instances.map
      (fun j => if j.id == i.id then retireInstance i retry (time + delay) else j) := rfl
  simp only [attemptOK, Bool.and_eq_true, attempts]
  refine ⟨⟨⟨⟨by rw [attemptIds]; exact old.1.1.1.1, by rw [tokens]; exact old.1.1.1.2⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [List.all_map, List.all_eq_true, Function.comp_def]
    intro a memberA
    have existsOwner := List.all_eq_true.mp old.1.1.2 a memberA
    have sameInstance : (retireAttempt l.attempt a).instance = a.instance := by unfold retireAttempt; split <;> rfl
    simp only [sameInstance, retired_lookup, Option.isSome_map]
    exact existsOwner
  · rw [instances]
    simp only [List.all_map, List.all_eq_true, Function.comp_def]
    intro j memberJ
    have limit := List.all_eq_true.mp old.1.2 j memberJ
    have id : (if j.id == i.id then retireInstance i retry (time + delay) else j).id = j.id := by
      split
      · rename_i selected; exact (beq_iff_eq.mp selected).symm
      · rfl
    rw [id]
    have bound := filter_map_length_le s.attempts (retireAttempt l.attempt)
      (fun a => a.instance == j.id && a.status == .running) (by
        intro a _ accepted
        by_cases selected : a.id == l.attempt
        · simp [retireAttempt, selected] at accepted
        · simpa [retireAttempt, selected] using accepted)
    exact decide_eq_true (Nat.le_trans bound (of_decide_eq_true limit))
  · simp only [List.all_map, List.all_eq_true, Function.comp_def]
    intro a memberA
    by_cases selected : a.id == l.attempt
    · simp [retireAttempt, selected]
    · have oldA := List.all_eq_true.mp old.2 a memberA
      simp only [retireAttempt, selected, ↓reduceIte]
      by_cases runningA : a.status = .running
      · simp only [runningA, beq_self_eq_true, Bool.not_true, Bool.false_or] at oldA ⊢
        obtain ⟨j, foundJ, props⟩ := (Option.any_eq_true _ _).mp oldA
        have notI : (j.id == i.id) = false := by
          apply Bool.eq_false_iff.mpr
          intro sameId
          have same := unique_instance safe (instance?_mem foundJ) memberI (beq_iff_eq.mp sameId)
          subst j
          have leaseMatches := (Bool.and_eq_true_iff.mp props).2
          simp only [lease, Option.any_some, beq_iff_eq] at leaseMatches
          exact selected (beq_iff_eq.mpr leaseMatches.symm)
        have different : j.id ≠ i.id := by simpa using notI
        simpa [retired_lookup, foundJ, different, runningA] using props
      · simp [runningA]

theorem retired_invariants (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (running : i.status = .running) (l : Lease) (lease : i.lease = some l)
    (time : Nat) (retry : Bool) (delay : Nat) : Invariants (retiredState s i l time retry delay) := by
  apply (invariants_parts _).mpr
  exact ⟨by rw [retired_static s safe i memberI l time retry delay]; exact (invariants_parts s |>.mp safe).1,
    retired_leaseOK s safe i memberI running l lease time retry delay,
    retired_attemptOK s safe i memberI running l lease time retry delay⟩


theorem retired_history (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (running : i.status = .running) (l : Lease) (time : Nat) (retry : Bool) (delay : Nat) (clock : s.now ≤ time) :
    historyOK s (retiredState s i l time retry delay) = true := by
  simp only [historyOK, Bool.and_eq_true]
  refine ⟨⟨decide_eq_true clock, ?_⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro j memberJ
    rw [retired_lookup, instance?_of_mem safe j memberJ]
    simp only [Option.map_some, Option.any_some]
    by_cases selected : j.id == i.id
    · have same := unique_instance safe memberJ memberI (beq_iff_eq.mp selected)
      subst j
      cases retry <;> simp [retireInstance, running, allowedStatus, instanceKey]
    · simp [selected, allowedStatus]
  · apply List.all_eq_true.mpr
    intro c memberC
    apply List.any_eq_true.mpr
    exact ⟨c, memberC, by simp⟩

/-- Any running leaf has a finite, accepted maintenance witness, even when its
    lease is already expired or its retry budget has been exhausted. --/
theorem hasWork_of_running (s : State) (safe : Invariants s) (started : s.started = true)
    (terminal : s.status.terminal = false) (i : Instance) (memberI : i ∈ s.instances)
    (running : i.status = .running) (l : Lease) (lease : i.lease = some l)
    (n : Node) (got : getNode s i.path i.node = .ok n) (r : RetryPolicy) (concurrency : Nat)
    (kind : n.kind = .leaf r concurrency) : s.hasWork = true := by
  let time := max (s.now + 1) l.until_
  let retry : Bool := decide (i.attemptCount < r.maxAttempts + i.extraAttempts)
  let result := retiredState s i l time retry r.retrySeconds
  have clock : s.now ≤ time := by
    have bound : s.now + 1 ≤ time := Nat.le_max_left _ _
    exact Nat.le_trans (Nat.le_add_right _ _) bound
  have expired : l.until_ ≤ time := Nat.le_max_right _ _
  have executed : transition s (.expireLease i.id time) = .ok result := by
    simp [transition, getInstance, instance?_of_mem safe i memberI, got, require, clock, running, lease, expired,
      expireOrFail, leafPolicy, kind, Option.toExcept, bind, Except.bind, pure, Except.pure, result, retiredState, retireInstance, retry,
      setInstance, setAttempt]
  have safeResult := retired_invariants s safe i memberI running l lease time retry r.retrySeconds
  have history := retired_history s safe i memberI running l time retry r.retrySeconds clock
  have accepted := accept_ordinary s result (.expireLease i.id time) started
    (by simp [absorbed, duplicateComplete, terminal]) rfl (by simp) rfl executed safeResult history
  have changed : result ≠ s := by
    intro eq
    have found : result.instance? i.id = some (retireInstance i retry (time + r.retrySeconds)) := by
      simp [result, retired_lookup, instance?_of_mem safe i memberI]
    rw [eq, instance?_of_mem safe i memberI] at found
    have status := congrArg Instance.status (Option.some.inj found)
    rw [running] at status
    cases selectedRetry : retry <;> simp [retireInstance, selectedRetry] at status
  apply hasWork_of_candidate (instance_candidate_mem s started terminal i memberI _ ?_) rfl accepted changed
  simp [Explore.instanceCandidates, running, lease, time]

end Suimon
