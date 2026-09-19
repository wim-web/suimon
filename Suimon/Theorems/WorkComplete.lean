import Suimon.Theorems.WorkClaim

namespace Suimon

/-- Credentials of an accepted, non-absorbed worker operation resolve to its
    currently running instance and live lease. --/
theorem validLease_running (s : State) (auth : Credentials) (valid : validLease s auth = true) :
    ∃ i l, s.instance? auth.instance = some i ∧ i.status = .running ∧ i.lease = some l := by
  simp only [validLease, Bool.and_eq_true] at valid
  obtain ⟨i, found, properties⟩ := (Option.any_eq_true _ _).mp valid.2
  obtain ⟨running, lease⟩ := Bool.and_eq_true_iff.mp properties
  obtain ⟨l, foundLease, _⟩ := (Option.any_eq_true _ _).mp lease
  exact ⟨i, l, found, beq_iff_eq.mp running, foundLease⟩

def workerCommand : Op → Bool
  | .emit .. | .complete .. | .fail .. | .renew .. => true
  | _ => false

theorem worker_source (s next : State) (op : Op) (worker : workerCommand op = true)
    (valid : authorized s op = true) (executed : transition s op = .ok next) :
    ∃ i l n r cap, i ∈ s.instances ∧ i.status = .running ∧ i.lease = some l ∧
      getNode s i.path i.node = .ok n ∧ n.kind = .leaf r cap := by
  cases op with
  | emit auth port item | complete auth outputs | fail auth code retryable | renew auth =>
    have validAuth : validLease s auth = true := valid
    obtain ⟨i, l, found, running, lease⟩ := validLease_running s auth validAuth
    simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure, found] at executed
    cases got : getNode s i.path i.node with
    | error reject => simp [got] at executed
    | ok n =>
      simp only [got] at executed
      try simp only [expireOrFail] at executed
      cases policy : leafPolicy n with
      | error reject => simp [policy, bind, Except.bind] at executed
      | ok pair =>
        obtain ⟨r, cap, kind⟩ := leafPolicy_kind n pair policy
        exact ⟨i, l, n, r, cap, instance?_mem found, running, lease, got, kind⟩
  | _ => contradiction

theorem expire_source (s next : State) (inst : InstanceId) (now : Nat)
    (executed : transition s (.expireLease inst now) = .ok next) :
    ∃ i l n r cap, i ∈ s.instances ∧ i.status = .running ∧ i.lease = some l ∧
      getNode s i.path i.node = .ok n ∧ n.kind = .leaf r cap := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
  cases found : s.instance? inst with
  | none => simp [found] at executed
  | some i =>
    simp only [found] at executed
    cases got : getNode s i.path i.node with
    | error reject => simp [got] at executed
    | ok n =>
      simp only [got] at executed
      cases allowed : require (now ≥ s.now && i.status == .running && i.lease.any (·.until_ ≤ now)) "LEASE_NOT_EXPIRED" with
      | error reject => simp [allowed] at executed
      | ok u =>
        have checked := require_ok _ _ _ u allowed
        simp only [Bool.and_eq_true, beq_iff_eq] at checked
        obtain ⟨l, lease, _⟩ := (Option.any_eq_true _ _).mp checked.2
        simp only [allowed, bind, Except.bind, expireOrFail] at executed
        cases policy : leafPolicy n with
        | error reject => simp [policy, bind, Except.bind] at executed
        | ok pair =>
          obtain ⟨r, cap, kind⟩ := leafPolicy_kind n pair policy
          exact ⟨i, l, n, r, cap, instance?_mem found, checked.1.2, lease, got, kind⟩

/-- Completeness over all ordinary operations at a started invariant boundary.
    The operation and its arguments are unrestricted; they need not belong to
    the finite candidate list. --/
theorem hasWork_complete (s next : State) (op : Op) (safe : Invariants s) (started : s.started = true)
    (work : op.countsAsWork = true) (accepted : step s op = .ok next) (changed : next ≠ s) : s.hasWork = true := by
  obtain ⟨active, terminal⟩ := progress_active accepted changed
  have notIdle : op ≠ .idle := by intro eq; rw [eq] at work; contradiction
  have executed := transition_of_active accepted active notIdle
  by_cases fixed : fixedArguments op = true
  · exact hasWork_of_fixedArguments s next op safe started fixed accepted changed
  by_cases worker : workerCommand op = true
  · have valid := (step_ok_cases s op next accepted).resolve_left (fun unchanged => changed unchanged.2) |>.2.1
    obtain ⟨i, l, n, r, cap, memberI, running, lease, got, kind⟩ := worker_source s next op worker valid executed
    exact hasWork_of_running s safe started terminal i memberI running l lease n got r cap kind
  cases op with
  | start inputs =>
    have notStarted := (effect_start s next inputs executed).1
    rw [started] at notStarted; contradiction
  | claim auth name => exact hasWork_of_claim s next auth name safe started accepted changed
  | expireLease inst now =>
    obtain ⟨i, l, n, r, cap, memberI, running, lease, got, kind⟩ := expire_source s next inst now executed
    exact hasWork_of_running s safe started terminal i memberI running l lease n got r cap kind
  | promoteRetry inst now => exact hasWork_of_promoteRetry s next inst now safe started accepted changed
  | _ => contradiction

theorem hasWork_iff_all_ops (s : State) (safe : Invariants s) (started : s.started = true) :
    s.hasWork = true ↔ ∃ op next, op.countsAsWork = true ∧ step s op = .ok next ∧ next ≠ s := by
  constructor
  · intro work
    obtain ⟨op, _, counts, next, accepted, changed⟩ := (hasWork_iff s).mp work
    exact ⟨op, next, counts, accepted, by simpa using changed⟩
  · rintro ⟨op, next, counts, accepted, changed⟩
    exact hasWork_complete s next op safe started counts accepted changed

theorem no_work_all_ops (s : State) (safe : Invariants s) (started : s.started = true) (noWork : s.hasWork = false)
    (op : Op) (next : State) (counts : op.countsAsWork = true) (accepted : step s op = .ok next) : next = s := by
  classical
  by_cases unchanged : next = s
  · exact unchanged
  · have work := hasWork_complete s next op safe started counts accepted unchanged
    rw [noWork] at work; contradiction

/-- T12's reverse implication: a newly blocked idle boundary had no ordinary
    state-changing operation, including operations outside the exploration domain. --/
theorem idle_enters_blocked_no_progress (s next : State) (safe : Invariants s) (running : s.status = .running)
    (accepted : step s .idle = .ok next) (blocked : next.status = .blocked) :
    ∀ op result, op.countsAsWork = true → step s op = .ok result → result = s := by
  have noWork := idle_step_enters_blocked_no_work s next accepted running blocked
  have started : s.started = true := by
    rcases step_ok_cases s .idle next accepted with ⟨_, unchanged⟩ | ⟨_, _, prepared, _⟩
    · rw [unchanged, running] at blocked; contradiction
    · cases h : s.started with
      | true => rfl
      | false => simp [prepare, prepareWith, startupAllowed, h, require, bind, Except.bind] at prepared
  exact fun op result counts applied => no_work_all_ops s safe started noWork op result counts applied

end Suimon
