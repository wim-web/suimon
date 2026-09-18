import Suimon.Axioms
namespace Suimon

/-- Executable and relational transaction semantics coincide. --/
theorem step_iff (s : State) (op : Op) (next : State) :
    step s op = .ok next ↔ Step s op next := by
  constructor
  · intro h
    unfold step at h
    split at h
    · cases h
      exact .absorb ‹_›
    · rename_i active
      have active' : absorbed s op = false := by simpa using active
      split at h
      · contradiction
      · rename_i auth
        have auth' : authorized s op = true := by simpa using auth
        split at h
        · contradiction
        · rename_i result effect
          unfold commit at h
          split at h
          · rename_i safe
            cases h
            have hs := Bool.and_eq_true_iff.mp safe
            exact .execute active' auth' effect hs.1 hs.2
          · contradiction
  · intro h
    cases h with
    | absorb h => simp [step, h]
    | execute active auth effect safe hist =>
      change invariants next = true at safe
      simp [step, active, auth, effect, commit, safe, hist]

/-- I1–I3 (and accounting/loop bounds) hold after every accepted boundary. --/
theorem preserves_invariants (before after : State) (op : Op)
    (initial : Invariants before) (accepted : step before op = .ok after) : Invariants after := by
  cases (step_iff before op after).mp accepted with
  | absorb _ => exact initial
  | execute _ _ _ safe _ => exact safe

/-- I4: retained instances follow the allowed transition table. --/
theorem preserves_history (before after : State) (op : Op)
    (active : absorbed before op = false)
    (accepted : step before op = .ok after) : historyOK before after = true := by
  cases (step_iff before op after).mp accepted with
  | absorb h => simp [active] at h
  | execute _ _ _ _ history => exact history

/-- T13: no accepted operation changes a terminal execution. Rejection also retains the caller's state. --/
theorem terminal_absorbing (s : State) (op : Op) (next : State)
    (terminal : s.status.terminal = true) (accepted : step s op = .ok next) : next = s := by
  cases (step_iff s op next).mp accepted with
  | absorb _ => rfl
  | execute active auth _ _ _ => simp [absorbed, terminal, auth] at active

/-- T8: invalid authority is rejected; exact completion receipts are the documented exception. --/
theorem invalid_lease_rejected (s : State) (op : Op)
    (fresh : duplicateComplete s op = false)
    (bad : authorized s op = false) :
    step s op = .error { code := "INVALID_LEASE", message := "stale, mismatched or expired lease" } := by
  simp [step, absorbed, fresh, bad]

/-- T11: an exact retransmission is an identity transition. --/
theorem complete_idempotent (s : State) (op : Op) (h : duplicateComplete s op = true) :
    step s op = .ok s := by simp [step, absorbed, h]

theorem prepare_preconditions (s : State) (op : Op) (next : State)
    (h : prepare s op = .ok next) : preconditions s op = true := by
  unfold prepare require at h
  split at h
  · split at h
    · assumption
    · simp [bind, Except.bind] at h
  · simp [bind, Except.bind] at h

/-- T1: a newly activated plain consumer has all upstream successes and completed channels. --/
theorem plain_order (s next : State) (path : Path) (node : NodeId)
    (active : s.status.terminal = false) (h : step s (.activate path node) = .ok next) :
    plainReady s path node = true := by
  cases (step_iff s (.activate path node) next).mp h with
  | absorb impossible => simp [absorbed, active, duplicateComplete] at impossible
  | execute _ _ effect _ _ => exact prepare_preconditions _ _ _ effect

/-- T1 for Coalesce concerns the selected input, not the absent arms. --/
theorem coalesce_plain_order (s next : State) (path : Path) (node edge : String) (item : ItemId)
    (active : s.status.terminal = false) (h : step s (.fireCoalesce path node edge item) = .ok next) :
    coalesceReady s path node edge item = true := by
  cases (step_iff s (.fireCoalesce path node edge item) next).mp h with
  | absorb impossible => simp [absorbed, active, duplicateComplete] at impossible
  | execute _ _ effect _ _ => exact prepare_preconditions _ _ _ effect

/-- No status transition can rerun an already succeeded instance. --/
theorem succeeded_status_absorbing (status : InstanceStatus)
    (h : allowedStatus .succeeded status = true) : status = .succeeded := by
  cases status <;> first | rfl | (change false = true at h; contradiction)

/-- T12: idle remains running only when a non-administrative candidate is accepted. --/
theorem idle_explicit (s : State) (h : (idleState s).status = .running) : s.hasWork = true := by
  unfold idleState at h
  split at h
  · assumption
  · dsimp at h
    split at h <;> contradiction

/-- Work probing executes exactly the public rule for every candidate it counts. --/
theorem work_step_eq (s : State) (op : Op) (work : op.countsAsWork = true) :
    step s op = stepNonIdle s op := by
  cases op <;> first | rfl | (change false = true at work; contradiction)

/-- D2: hasWork has a concrete accepted-operation witness from the shared enumeration. --/
theorem hasWork_iff (s : State) : s.hasWork = true ↔
    ∃ op ∈ Explore.candidates {} s, op.countsAsWork = true ∧ ∃ next, step s op = .ok next ∧ (next != s) = true := by
  simp only [State.hasWork, List.any_eq_true, acceptedProgress, Bool.and_eq_true]
  constructor
  · rintro ⟨op, member, work, accepted⟩
    refine ⟨op, member, work, ?_⟩
    cases h : stepNonIdle s op with
    | error e => simp [h] at accepted
    | ok next => exact ⟨next, (work_step_eq s op work).trans h, by simpa [h] using accepted⟩
  · rintro ⟨op, member, work, next, accepted, changed⟩
    refine ⟨op, member, work, ?_⟩
    rw [work_step_eq s op work] at accepted
    rw [accepted]
    exact changed

theorem idle_result_work (s : State) (running : (idleState s).status = .running) :
    (idleState s).hasWork = true := by
  have work := idle_explicit s running
  simp [idleState, work]

/-- The converse for executable hasWork: idle cannot newly block while it is true. --/
theorem idle_enters_blocked_no_work (s : State) (running : s.status = .running)
    (blocked : (idleState s).status = .blocked) : s.hasWork = false := by
  unfold idleState at blocked
  split at blocked
  · simp [running] at blocked
  · simpa using ‹¬s.hasWork = true›

/-- T12 for the public step: a running post-idle state has accepted work. --/
theorem idle_step_work (s next : State) (accepted : step s .idle = .ok next)
    (running : next.status = .running) : next.hasWork = true := by
  cases (step_iff s .idle next).mp accepted with
  | absorb h =>
    have terminal : s.status.terminal = false := by rw [running]; rfl
    simp [absorbed, duplicateComplete, terminal] at h
  | execute _ _ effect _ _ =>
    have result : idleState s = next := by
      unfold prepare require at effect
      split at effect
      · simpa [preconditions, bind, Except.bind, pure, Except.pure] using effect
      · simp [bind, Except.bind] at effect
    rw [← result] at running ⊢
    exact idle_result_work s running

/-- The public idle rule only enters blocked when executable hasWork is false. --/
theorem idle_step_enters_blocked_no_work (s next : State)
    (accepted : step s .idle = .ok next) (running : s.status = .running)
    (blocked : next.status = .blocked) : s.hasWork = false := by
  cases (step_iff s .idle next).mp accepted with
  | absorb _ => simp [running] at blocked
  | execute _ _ effect _ _ =>
    have result : idleState s = next := by
      unfold prepare require at effect
      split at effect
      · simpa [preconditions, bind, Except.bind, pure, Except.pure] using effect
      · simp [bind, Except.bind] at effect
    rw [← result] at blocked
    exact idle_enters_blocked_no_work s running blocked

/-- T3: accounting contains at most one consumer per (channel, token position). --/
theorem consumption_unique (s : State) (h : Invariants s) :
    unique (s.consumed.map fun c => (c.channel, c.index)) = true := by
  simp only [Invariants, invariants, Bool.and_eq_true] at h
  have ha := h.1.2
  simp only [accountingOK, Bool.and_eq_true] at ha
  exact ha.1.1

/-- T7: every stored loop counter remains within its base bound plus manual extensions. --/
theorem loop_bounded (s : State) (h : Invariants s) : loopBoundsOK s = true := by
  exact (Bool.and_eq_true_iff.mp h).2

/-- T2 safety form: a placed prefix is retained at the next transaction boundary. --/
theorem channel_history (s next : State) (op : Op)
    (active : absorbed s op = false)
    (h : step s op = .ok next) :
    s.channels.all (fun c => next.channels.any (fun d => c.id == d.id &&
      c.placed.isPrefixOf d.placed && c.consumed ≤ d.consumed)) = true := by
  exact (Bool.and_eq_true_iff.mp (preserves_history s next op active h)).2
/-- T5: insertion is rejected once an instance key has already been used. --/
theorem once_only (s : State) (i : Instance)
    (existing : s.instances.any (fun j => j.id == i.id || instanceKey j == instanceKey i) = true) :
    freshInstance s i = .error { code := "DUPLICATE_INSTANCE", message := "DUPLICATE_INSTANCE" } := by
  simp [freshInstance, require, existing, bind, Except.bind]

/-- T6: no item is routed to a non-selected branch arm. --/
theorem branch_exclusive (arm port : PortName) (output : Option ItemId) (h : arm ≠ port) :
    routeOutput (some arm) port output = none := by
  simp [routeOutput, h]

/-- T8: every boundary has at most one running attempt for each instance. --/
theorem lease_exclusive (s : State) (h : Invariants s) :
    s.instances.all (fun i => (s.attempts.filter (fun a => a.instance == i.id && a.status == .running)).length ≤ 1) = true := by
  simp only [Invariants, invariants, Bool.and_eq_true] at h
  have ha := h.1.1.2
  simp only [attemptOK, Bool.and_eq_true] at ha
  exact ha.1.2
/-- A succeeded instance is retained as succeeded across every accepted operation. --/
theorem succeeded_retained (s next : State) (op : Op) (id : InstanceId) (i : Instance)
    (found : s.instance? id = some i) (done : i.status = .succeeded)
    (accepted : step s op = .ok next) :
    ∃ j, next.instance? id = some j ∧ j.status = .succeeded := by
  cases (step_iff s op next).mp accepted with
  | absorb _ => exact ⟨i, found, done⟩
  | execute _ _ _ _ hist =>
    have member := List.mem_of_find?_eq_some found
    have sameId : i.id = id := by
      have key := List.find?_some found
      simpa only [beq_iff_eq] using key
    simp only [historyOK, Bool.and_eq_true] at hist
    have retained := List.all_eq_true.mp hist.1.2 i member
    obtain ⟨j, lookup, properties⟩ := (Option.any_eq_true _ _).mp retained
    simp only [Bool.and_eq_true] at properties
    refine ⟨j, ?_, ?_⟩
    · simpa [sameId] using lookup
    · apply succeeded_status_absorbing
      simpa [done] using properties.1.2
end Suimon
