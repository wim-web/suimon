import Suimon.Theorems.WorkWorkers

namespace Suimon
open Explore

def claimedInstance (i : Instance) (auth : Credentials) (duration : Nat) : Instance :=
  {i with
    status := .running
    attemptCount := i.attemptCount + 1
    lease := some {attempt := auth.attempt, token := auth.token, until_ := auth.now + duration}}

def claimedAttempt (i : Instance) (auth : Credentials) (worker : String) : Attempt := {
  id := auth.attempt
  «instance» := i.id
  no := i.attemptCount + 1
  status := .running
  token := auth.token
  worker := worker}

def claimedState (s : State) (i : Instance) (auth : Credentials) (worker : String) (duration : Nat) : State :=
  {setInstance s (claimedInstance i auth duration) with
    attempts := s.attempts ++ [claimedAttempt i auth worker]
    now := auth.now}

theorem claimed_lookup (s : State) (i : Instance) (auth : Credentials) (worker : String) (duration : Nat) (id : InstanceId) :
    (claimedState s i auth worker duration).instance? id =
      (s.instance? id).map (fun j => if j.id == i.id then claimedInstance i auth duration else j) :=
  setInstance_lookup s i (claimedInstance i auth duration) rfl id

theorem claimed_static (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (auth : Credentials) (worker : String) (duration : Nat) : staticOK (claimedState s i auth worker duration) = staticOK s := by
  apply staticOK_map s (claimedState s i auth worker duration)
    (fun j => if j.id == i.id then claimedInstance i auth duration else j) rfl rfl rfl rfl
  intro j memberJ
  split
  · rename_i selected
    have same := unique_instance safe memberJ memberI (beq_iff_eq.mp selected)
    subst j
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem claimed_leaseOK (s : State) (safe : Invariants s) (i : Instance)
    (auth : Credentials) (worker : String) (duration : Nat) : leaseOK (claimedState s i auth worker duration) = true := by
  have old := (invariants_parts s |>.mp safe).2.1
  simp only [leaseOK, claimedState, setInstance, List.all_map, List.all_eq_true, Function.comp_def]
  intro j memberJ
  by_cases selected : j.id == i.id
  · simp [claimedInstance, claimedAttempt, selected]
  · have oldJ := List.all_eq_true.mp old j memberJ
    simp only [claimedInstance, selected, Bool.false_eq_true, ↓reduceIte]
    by_cases running : j.status = .running
    · simp only [running, beq_self_eq_true, ↓reduceIte] at oldJ ⊢
      obtain ⟨l, lease, witness⟩ := (Option.any_eq_true _ _).mp oldJ
      obtain ⟨a, memberA, props⟩ := List.any_eq_true.mp witness
      rw [lease]
      exact List.any_eq_true.mpr ⟨a, List.mem_append_left _ memberA, props⟩
    · simp [running] at oldJ ⊢
      exact oldJ

theorem unique_of_nodup {xs : List String} (distinct : xs.Nodup) : unique xs = true := by
  simp [unique, eraseDups_of_nodup distinct]

theorem unique_append_fresh (xs : List String) (x : String)
    (uniqueXs : unique xs = true) (fresh : x ∉ xs) : unique (xs ++ [x]) = true := by
  apply unique_of_nodup
  refine List.nodup_append.mpr ⟨unique_nodup xs uniqueXs, by simp, ?_⟩
  intro a memberA b memberB eq
  have bx : b = x := by simpa using memberB
  exact fresh ((eq.trans bx) ▸ memberA)

theorem claimed_attemptOK (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (ready : i.status = .ready) (auth : Credentials) (worker : String) (duration : Nat)
    (freshId : auth.attempt ∉ s.attempts.map (·.id)) (freshToken : auth.token ∉ s.attempts.map (·.token)) :
    attemptOK (claimedState s i auth worker duration) = true := by
  have old := (invariants_parts s |>.mp safe).2.2
  simp only [attemptOK, Bool.and_eq_true] at old
  have noRunning : ∀ a ∈ s.attempts, a.instance = i.id → a.status ≠ .running := by
    intro a memberA owner running
    have oldA := List.all_eq_true.mp old.2 a memberA
    rw [owner, instance?_of_mem safe i memberI] at oldA
    simp [running, ready] at oldA
  have empty : s.attempts.filter (fun a => a.instance == i.id && a.status == .running) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a memberA selected
    obtain ⟨owner, running⟩ := Bool.and_eq_true_iff.mp selected
    exact noRunning a memberA (beq_iff_eq.mp owner) (beq_iff_eq.mp running)
  have attempts : (claimedState s i auth worker duration).attempts = s.attempts ++ [claimedAttempt i auth worker] := rfl
  have instances : (claimedState s i auth worker duration).instances = s.instances.map
      (fun j => if j.id == i.id then claimedInstance i auth duration else j) := rfl
  simp only [attemptOK, Bool.and_eq_true, attempts]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, claimedAttempt]
    exact unique_append_fresh _ _ old.1.1.1.1 freshId
  · simp only [List.map_append, List.map_cons, List.map_nil, claimedAttempt]
    exact unique_append_fresh _ _ old.1.1.1.2 freshToken
  · apply List.all_eq_true.mpr
    intro a memberA
    rw [claimed_lookup, Option.isSome_map]
    rcases List.mem_append.mp memberA with oldA | newA
    · exact List.all_eq_true.mp old.1.1.2 a oldA
    · have same : a = claimedAttempt i auth worker := by simpa using newA
      rw [same]
      simp [claimedAttempt, instance?_of_mem safe i memberI]
  · rw [instances]
    simp only [List.all_map, List.all_eq_true, Function.comp_def]
    intro j memberJ
    have id : (if j.id == i.id then claimedInstance i auth duration else j).id = j.id := by
      split
      · rename_i selected; exact (beq_iff_eq.mp selected).symm
      · rfl
    rw [id]
    by_cases same : j.id = i.id
    · rw [same, List.filter_append, empty]
      simp [claimedAttempt]
    · have limit := List.all_eq_true.mp old.1.2 j memberJ
      simpa [List.filter_append, claimedAttempt, Ne.symm same] using limit
  · apply List.all_eq_true.mpr
    intro a memberA
    rcases List.mem_append.mp memberA with oldA | newA
    · have allowed := List.all_eq_true.mp old.2 a oldA
      by_cases running : a.status = .running
      · simp only [running, bne_self_eq_false, Bool.false_or] at allowed ⊢
        obtain ⟨j, foundJ, props⟩ := (Option.any_eq_true _ _).mp allowed
        have different : j.id ≠ i.id := by
          intro sameId
          have same := unique_instance safe (instance?_mem foundJ) memberI sameId
          subst j
          simp [ready] at props
        simpa [claimed_lookup, foundJ, different] using props
      · simp [running]
    · have same : a = claimedAttempt i auth worker := by simpa using newA
      subst a
      simp [claimedAttempt, claimed_lookup, instance?_of_mem safe i memberI, claimedInstance]

theorem claimed_invariants (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (ready : i.status = .ready) (auth : Credentials) (worker : String) (duration : Nat)
    (freshId : auth.attempt ∉ s.attempts.map (·.id)) (freshToken : auth.token ∉ s.attempts.map (·.token)) :
    Invariants (claimedState s i auth worker duration) := by
  apply (invariants_parts _).mpr
  exact ⟨by rw [claimed_static s safe i memberI]; exact (invariants_parts s |>.mp safe).1,
    claimed_leaseOK s safe i auth worker duration,
    claimed_attemptOK s safe i memberI ready auth worker duration freshId freshToken⟩

theorem claimed_history (s : State) (safe : Invariants s) (i : Instance) (memberI : i ∈ s.instances)
    (ready : i.status = .ready) (auth : Credentials) (worker : String) (duration : Nat) (clock : s.now ≤ auth.now) :
    historyOK s (claimedState s i auth worker duration) = true := by
  simp only [historyOK, Bool.and_eq_true]
  refine ⟨⟨decide_eq_true clock, ?_⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro j memberJ
    rw [claimed_lookup, instance?_of_mem safe j memberJ]
    simp only [Option.map_some, Option.any_some]
    by_cases selected : j.id == i.id
    · have same := unique_instance safe memberJ memberI (beq_iff_eq.mp selected)
      subst j
      simp [claimedInstance, ready, allowedStatus, instanceKey]
    · simp [selected, allowedStatus]
  · apply List.all_eq_true.mpr
    intro c memberC
    exact List.any_eq_true.mpr ⟨c, memberC, by simp⟩


def maintenanceDue (s : State) (time : Nat) : Bool := s.instances.any fun j =>
  (j.status == .running && j.lease.any (·.until_ ≤ time)) ||
  (j.status == .retryWait && j.retryAt.any (· ≤ time))

def concurrencyCount (s : State) (i : Instance) : Nat :=
  (s.instances.filter (fun j => j.node == i.node && (s.frame? j.path).map (·.definition) ==
    (s.frame? i.path).map (·.definition) && j.status == .running)).length

theorem claim_requirements (s next : State) (auth : Credentials) (worker : String)
    (executed : transition s (.claim auth worker) = .ok next) :
    ∃ i n r cap, s.instance? auth.instance = some i ∧ getNode s i.path i.node = .ok n ∧
      leafPolicy n = .ok (r, cap) ∧ s.now ≤ auth.now ∧
      (i.status == .ready && i.lease.isNone && i.retryAt.isNone) = true ∧
      i.attemptCount < r.maxAttempts + i.extraAttempts ∧ maintenanceDue s auth.now = false ∧ concurrencyCount s i < cap := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
  cases found : s.instance? auth.instance with
  | none => simp [found] at executed
  | some i =>
    simp only [found] at executed
    cases got : getNode s i.path i.node with
    | error r => simp [got] at executed
    | ok n =>
      simp only [got] at executed
      cases policy : leafPolicy n with
      | error r => simp [policy] at executed
      | ok policyValue =>
        obtain ⟨r, cap⟩ := policyValue
        simp only [policy] at executed
        repeat (first | split at executed | contradiction)
        refine ⟨i, n, r, cap, rfl, got, policy, ?_, ?_, ?_, ?_, ?_⟩
        · apply of_decide_eq_true
          apply require_ok
          assumption
        · apply require_ok
          assumption
        · apply of_decide_eq_true
          apply require_ok
          assumption
        · have noneDue : Bool.not (maintenanceDue s auth.now) = true := by
            unfold maintenanceDue
            apply require_ok
            assumption
          simpa using noneDue
        · apply of_decide_eq_true
          apply require_ok
          assumption

theorem maintenanceDue_mono (s : State) (a b : Nat) (time : a ≤ b)
    (due : maintenanceDue s a = true) : maintenanceDue s b = true := by
  obtain ⟨i, memberI, cases⟩ := List.any_eq_true.mp due
  apply List.any_eq_true.mpr
  refine ⟨i, memberI, ?_⟩
  rcases Bool.or_eq_true_iff.mp cases with running | retry
  · obtain ⟨status, due⟩ := Bool.and_eq_true_iff.mp running
    obtain ⟨l, lease, expires⟩ := (Option.any_eq_true _ _).mp due
    have expiresB : l.until_ ≤ b := Nat.le_trans (of_decide_eq_true expires) time
    simp [status, lease, expiresB]
  · obtain ⟨status, due⟩ := Bool.and_eq_true_iff.mp retry
    obtain ⟨atTime, retryAt, expires⟩ := (Option.any_eq_true _ _).mp due
    have expiresB : atTime ≤ b := Nat.le_trans (of_decide_eq_true expires) time
    simp [status, retryAt, expiresB]

/-- Fresh representative credentials suffice whenever any claim is accepted.
    Worker identity and a later eligible timestamp cannot enable a missed claim. --/
theorem hasWork_of_claim (s next : State) (auth : Credentials) (worker : String) (safe : Invariants s)
    (started : s.started = true) (accepted : step s (.claim auth worker) = .ok next) (changed : next ≠ s) : s.hasWork = true := by
  obtain ⟨active, terminal⟩ := progress_active accepted changed
  obtain ⟨i, n, r, cap, found, got, policy, clock, readyCondition, budget, maintenance, concurrency⟩ :=
    claim_requirements s next auth worker (transition_of_active accepted active (by simp))
  have memberI := instance?_mem found
  have ready : i.status = .ready := by
    simp only [Bool.and_eq_true, beq_iff_eq] at readyCondition
    exact readyCondition.1.1
  let credentials := claimCredentials s i
  let result := claimedState s i credentials "0" r.leaseSeconds
  have freshAttempt : credentials.attempt ∉ s.attempts.map (·.id) := freshId_not_mem _ _
  have freshToken : credentials.token ∉ s.attempts.map (·.token) := freshId_not_mem _ _
  have fresh : (!credentials.attempt.isEmpty && !credentials.token.isEmpty && !"0".isEmpty &&
      !s.attempts.any (fun a => a.id == credentials.attempt || a.token == credentials.token)) = true := by
    have unused : s.attempts.any (fun a => a.id == credentials.attempt || a.token == credentials.token) = false := by
      apply Bool.eq_false_iff.mpr
      intro exists_
      obtain ⟨a, memberA, conflicts⟩ := List.any_eq_true.mp exists_
      rcases Bool.or_eq_true_iff.mp conflicts with same | same
      · exact freshAttempt (List.mem_map.mpr ⟨a, memberA, beq_iff_eq.mp same⟩)
      · exact freshToken (List.mem_map.mpr ⟨a, memberA, beq_iff_eq.mp same⟩)
    simp [credentials, claimCredentials, freshId_nonempty] at unused ⊢
    exact unused
  have current : maintenanceDue s s.now = false := by
    apply Bool.eq_false_iff.mpr
    intro due
    have later := maintenanceDue_mono s s.now auth.now clock due
    rw [maintenance] at later
    contradiction
  have body : transition s (.claim credentials "0") = .ok result := by
    have authId : credentials.instance = i.id := rfl
    have nowEq : credentials.now = s.now := rfl
    simp only [maintenanceDue] at current
    simp only [concurrencyCount] at concurrency
    simp [transition, getInstance, authId, instance?_of_mem safe i memberI, got, policy, require, nowEq,
      readyCondition, budget, fresh, current, concurrency,
      result, claimedState, claimedInstance, claimedAttempt, setInstance, Option.toExcept, bind, Except.bind, pure, Except.pure]
  have accepted' := accept_ordinary s result (.claim credentials "0") started
    (by simp [absorbed, duplicateComplete, terminal]) rfl (by simp) rfl body
    (claimed_invariants s safe i memberI ready credentials "0" r.leaseSeconds freshAttempt freshToken)
    (claimed_history s safe i memberI ready credentials "0" r.leaseSeconds (Nat.le_refl _))
  have different : result ≠ s := by
    intro eq
    have lookup : result.instance? i.id = some (claimedInstance i credentials r.leaseSeconds) := by
      simp [result, claimed_lookup, instance?_of_mem safe i memberI]
    rw [eq, instance?_of_mem safe i memberI] at lookup
    have status := congrArg Instance.status (Option.some.inj lookup)
    rw [ready] at status
    contradiction
  apply hasWork_of_candidate (instance_candidate_mem s started terminal i memberI _ ?_) rfl accepted' different
  simp [instanceCandidates, ready, credentials]
  rfl

end Suimon
