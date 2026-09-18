import Suimon.Theorems.Safety
namespace Suimon.Trace

/-- T11: replaying a durable first and then a second equals uninterrupted replay. --/
theorem replay_append (s : State) (first second : List Op) :
    replayOps s (first ++ second) = (replayOps s first >>= fun next => replayOps next second) := by
  induction first generalizing s with
  | nil => rfl
  | cons op rest ih =>
    simp only [replayOps, List.cons_append, List.foldlM_cons]
    cases h : step s op with
    | error e => rfl
    | ok next => exact ih next

/-- Recovery from the same committed log is independent of the crashed worker. --/
theorem replay_durable (s : State) (logged recovered : List Op) (durable : recovered = logged) :
    replayOps s recovered = replayOps s logged := by rw [durable]

/-- Safety is preserved for arbitrarily long accepted logs, not just explored firstes. --/
theorem replay_invariants (s next : State) (ops : List Op)
    (initial : Invariants s) (h : replayOps s ops = .ok next) : Invariants next := by
  induction ops generalizing s with
  | nil => cases h; exact initial
  | cons op rest ih =>
    simp only [replayOps, List.foldlM_cons] at h
    cases hs : step s op with
    | error e => simp [hs, bind, Except.bind] at h
    | ok mid =>
      apply ih mid (preserves_invariants s mid op initial hs)
      simpa [hs, bind, Except.bind, replayOps] using h
/-- T11: no successful instance can be re-executed in any accepted continuation after replay. --/
theorem replay_retains_success (s next : State) (ops : List Op) (id : InstanceId) (i : Instance)
    (found : s.instance? id = some i) (done : i.status = .succeeded)
    (accepted : replayOps s ops = .ok next) :
    ∃ j, next.instance? id = some j ∧ j.status = .succeeded := by
  induction ops generalizing s i with
  | nil => cases accepted; exact ⟨i, found, done⟩
  | cons op rest ih =>
    simp only [replayOps, List.foldlM_cons] at accepted
    cases hs : step s op with
    | error e => simp [hs, bind, Except.bind] at accepted
    | ok mid =>
      obtain ⟨j, lookup, success⟩ := succeeded_retained s mid op id i found done hs
      apply ih mid j lookup success
      simpa [hs, bind, Except.bind, replayOps] using accepted
end Suimon.Trace
