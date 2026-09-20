import Suimon.Scheduler

namespace Suimon.Scheduler

theorem due_earlier (a b : Option Time) (now : Time) :
    due (earlier a b) now = true ↔ due a now = true ∨ due b now = true := by
  cases a <;> cases b <;> simp [earlier, due] <;> (simp only [Time] at *; omega)

theorem due_earliest (ts : List Timer) (now : Time) :
    due (earliest ts) now = true ↔ ∃ t ∈ ts, t.deadline ≤ now := by
  induction ts with
  | nil => simp [earliest, due]
  | cons t ts ih =>
    rw [earliest, due_earlier, ih]
    simp [due]

theorem firstDue_none (ts : List Timer) (now : Time) :
    firstDue now ts = none ↔ ∀ t ∈ ts, now < t.deadline := by
  induction ts with
  | nil => simp [firstDue]
  | cons t ts ih =>
    by_cases h : t.deadline ≤ now
    · simp [firstDue, h]; simp only [Time] at *; omega
    · simp [firstDue, h, ih]; simp only [Time] at *; omega

theorem firstDue_sound (ts : List Timer) (now : Time) (t : Timer)
    (selected : firstDue now ts = some t) : t ∈ ts ∧ t.deadline ≤ now := by
  induction ts with
  | nil => simp [firstDue] at selected
  | cons head ts ih =>
    by_cases h : head.deadline ≤ now
    · simp [firstDue, h] at selected
      subst t
      exact ⟨by simp, h⟩
    · have tail := ih (by simpa [firstDue, h] using selected)
      exact ⟨by simp [tail.1], tail.2⟩

theorem due_selects (ts : List Timer) (now : Time) (pending : ∃ t ∈ ts, t.deadline ≤ now) :
    ∃ t, firstDue now ts = some t := by
  cases selected : firstDue now ts with
  | some t => exact ⟨t, rfl⟩
  | none =>
    obtain ⟨t, member, expired⟩ := pending
    have later := (firstDue_none ts now).mp selected t member
    simp only [Time] at *
    omega

theorem expiry_covered (s : State) (i : Instance) (l : Lease) (member : i ∈ s.instances)
    (running : i.status = .running) (lease : i.lease = some l) :
    {deadline := l.until_, kind := .expireLease, target := i.id : Timer} ∈ mandatoryTimers s := by
  simp only [mandatoryTimers, List.mem_filterMap]
  exact ⟨i, member, by simp [instanceTimer, running, lease]⟩

theorem retry_covered (s : State) (i : Instance) (whenDue : Time) (member : i ∈ s.instances)
    (waiting : i.status = .retryWait) (deadline : i.retryAt = some whenDue) :
    {deadline := whenDue, kind := .promoteRetry, target := i.id : Timer} ∈ mandatoryTimers s := by
  simp only [mandatoryTimers, List.mem_filterMap]
  exact ⟨i, member, by simp [instanceTimer, waiting, deadline]⟩

theorem firstDue_append (ts rest : List Timer) (now : Time) (t : Timer)
    (selected : firstDue now ts = some t) : firstDue now (ts ++ rest) = some t := by
  induction ts with
  | nil => simp [firstDue] at selected
  | cons head ts ih =>
    by_cases h : head.deadline ≤ now
    · simpa [firstDue, h] using selected
    · simpa [firstDue, h] using ih (by simpa [firstDue, h] using selected)

theorem mandatory_before_renewals (s : State) (owned : List AttemptId) (autoRenew : Bool) (now : Time)
    (pending : ∃ t ∈ mandatoryTimers s, t.deadline ≤ now) :
    ∃ t ∈ mandatoryTimers s, maintenance s owned autoRenew now = some (t.operation now) := by
  obtain ⟨t, selected⟩ := due_selects _ _ pending
  have chosen := firstDue_append (mandatoryTimers s) (s.instances.filterMap (renewalTimer s owned autoRenew)) now t selected
  exact ⟨t, (firstDue_sound _ _ _ selected).1, by simp [maintenance, timers, chosen]⟩

theorem renewalAt_valid (until_ duration deadline : Nat) (chosen : renewalAt until_ duration = some deadline) :
    deadline < until_ ∧ until_ < deadline + duration := by
  simp only [renewalAt] at chosen
  split at chosen
  · rename_i before
    have same := Option.some.inj chosen
    subst deadline
    constructor
    · exact before
    · omega
  · contradiction

theorem stall_keeps_deadlines (ts : List Timer) (stale : Option Time) (announced : Bool)
    (now : Time) (pending : ∃ t ∈ ts, t.deadline ≤ now) :
    wake (waitDeadline ts stale announced) now false = true := by
  have ready := (due_earliest ts now).mpr pending
  simp only [wake, Bool.false_or, waitDeadline]
  exact (due_earlier _ _ _).mpr (Or.inl ready)

theorem pending_keeps_poll_enabled (ts : List Timer) (stale : Option Time) (announced : Bool)
    (t : Timer) (member : t ∈ ts) : pollEnabled (waitDeadline ts stale announced) = true := by
  have waking := stall_keeps_deadlines ts stale announced t.deadline ⟨t, member, Nat.le_refl _⟩
  cases deadline : waitDeadline ts stale announced <;> simp [pollEnabled, deadline, wake, due] at *

theorem no_stall_with_due_work (ts : List Timer) (stale : Option Time) (announced : Bool)
    (now : Time) (pending : ∃ t ∈ ts, t.deadline ≤ now) :
    announceStall ts stale announced now = false := by
  simp [announceStall, (due_earliest ts now).mpr pending]

theorem notified_stall_deadline (ts : List Timer) (stale : Option Time) :
    waitDeadline ts stale true = earliest ts := by simp [waitDeadline, earlier]; cases earliest ts <;> rfl

theorem message_wakes (deadline : Option Time) (now : Time) : wake deadline now true = true := by
  simp [wake]

theorem service_not_silent (s : State) (owned : List AttemptId) (autoRenew : Bool) (now : Time)
    (pending : ∃ t ∈ timers s owned autoRenew, t.deadline ≤ now) :
    (∃ next, service s owned autoRenew now = .ok (some next)) ∨
      (∃ error, service s owned autoRenew now = .error error) := by
  obtain ⟨t, selected⟩ := due_selects _ _ pending
  simp only [service, maintenance, selected, Option.map_some]
  cases step s (t.operation now) with
  | ok next => exact Or.inl ⟨next, rfl⟩
  | error error => exact Or.inr ⟨error, rfl⟩

theorem progress_poll (clock : Nat → Time) (poll : Nat → Bool) (progress : PollProgress clock poll)
    (whenDue : Time) : ∃ n, poll n = true ∧ whenDue ≤ clock n := by
  obtain ⟨start, elapsed⟩ := progress.unbounded whenDue
  obtain ⟨n, after, scheduled⟩ := progress.fair start
  exact ⟨n, scheduled, Nat.le_trans elapsed (progress.monotone start n after)⟩

theorem eventually_wakes (ts : List Timer) (stale : Option Time) (announced : Bool)
    (t : Timer) (member : t ∈ ts) (clock : Nat → Time) (poll : Nat → Bool)
    (progress : PollProgress clock poll) :
    ∃ n, waitPrefix (waitDeadline ts stale announced) clock poll n = true := by
  obtain ⟨n, scheduled, elapsed⟩ := progress_poll clock poll progress t.deadline
  refine ⟨n + 1, ?_⟩
  simp [waitPrefix, scheduled, stall_keeps_deadlines ts stale announced (clock n) ⟨t, member, elapsed⟩]

/-- For a cached state awaiting a message or timer, fair polls of a progressing
    clock eventually wake and attempt actual `step` maintenance. Stalled may
    change at every opportunity; it cannot mask a state deadline. --/
theorem eventually_services (s : State) (owned : List AttemptId) (autoRenew : Bool)
    (t : Timer) (member : t ∈ mandatoryTimers s) (stale : Option Time)
    (announced : Nat → Bool) (clock : Nat → Time) (poll : Nat → Bool)
    (progress : PollProgress clock poll) :
    ∃ n, poll n = true ∧ wake (waitDeadline (timers s owned autoRenew) stale (announced n)) (clock n) false = true ∧
      ((∃ next, service s owned autoRenew (clock n) = .ok (some next)) ∨
       (∃ error, service s owned autoRenew (clock n) = .error error)) := by
  obtain ⟨n, scheduled, elapsed⟩ := progress_poll clock poll progress t.deadline
  have included : t ∈ timers s owned autoRenew := by simp [timers, member]
  have pending : ∃ t ∈ timers s owned autoRenew, t.deadline ≤ clock n := ⟨t, included, elapsed⟩
  exact ⟨n, scheduled, stall_keeps_deadlines _ _ _ _ pending, service_not_silent _ _ _ _ pending⟩

theorem pending_expiry_eventually_wakes_service (s : State) (i : Instance) (l : Lease)
    (member : i ∈ s.instances) (running : i.status = .running) (lease : i.lease = some l)
    (owned : List AttemptId) (autoRenew : Bool) (stale : Option Time) (announced : Nat → Bool)
    (clock : Nat → Time) (poll : Nat → Bool) (progress : PollProgress clock poll) :
    ∃ n, poll n = true ∧ wake (waitDeadline (timers s owned autoRenew) stale (announced n)) (clock n) false = true ∧
      ((∃ next, service s owned autoRenew (clock n) = .ok (some next)) ∨
       (∃ error, service s owned autoRenew (clock n) = .error error)) :=
  eventually_services s owned autoRenew _ (expiry_covered s i l member running lease) stale announced clock poll progress

theorem pending_retry_eventually_wakes_service (s : State) (i : Instance) (whenDue : Time)
    (member : i ∈ s.instances) (waiting : i.status = .retryWait) (deadline : i.retryAt = some whenDue)
    (owned : List AttemptId) (autoRenew : Bool) (stale : Option Time) (announced : Nat → Bool)
    (clock : Nat → Time) (poll : Nat → Bool) (progress : PollProgress clock poll) :
    ∃ n, poll n = true ∧ wake (waitDeadline (timers s owned autoRenew) stale (announced n)) (clock n) false = true ∧
      ((∃ next, service s owned autoRenew (clock n) = .ok (some next)) ∨
       (∃ error, service s owned autoRenew (clock n) = .error error)) :=
  eventually_services s owned autoRenew _ (retry_covered s i whenDue member waiting deadline) stale announced clock poll progress

end Suimon.Scheduler
