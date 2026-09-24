import Suimon.Theorems.Basic
import Suimon.Theorems.Static
import Suimon.Theorems.LimitCount

/-! The concurrency limit (§8.2) and the separation of executions (§8.4). The invariants and the
    counting of slot holders live in `Suimon.Limit` (`LimitInv.lean`, `LimitCount.lean`). -/

namespace Suimon

/-- Every task call belongs to a task of an existing execution, and that task has left pending/ready. --/
def State.TaskCallsOwned (s : State) : Prop :=
  ∀ c ∈ s.calls, ∀ name, c.task = some name →
    ∃ e ∈ s.executions, e.id = c.owner ∧ ∃ t ∈ e.tasks, t.name = name ∧ t.status ≠ .pending ∧ t.status ≠ .ready

theorem Reachable.taskCallsOwned {p : Definition} {s : State} (h : Reachable p s) : s.TaskCallsOwned :=
  (Limit.reachable_inv h).calls

/-- Task names are distinct within each execution (from a valid definition, §8.1). --/
theorem Reachable.taskNames {p : Definition} {s : State} (valid : p.validate = .ok ()) (h : Reachable p s) :
    ∀ e ∈ s.executions, (e.tasks.map (·.name)).Nodup :=
  (Limit.reachable_limit valid h).1

/-- A concurrency execution never runs more tasks than its limit, counting a cancelled call until it
    terminates (§8.2). --/
theorem Reachable.withinLimit {p : Definition} {s : State} (valid : p.validate = .ok ()) (h : Reachable p s) :
    ∀ e ∈ s.executions, ∀ c, s.concurrencyOf p e = .ok c → (e.tasks.filter (s.holdsSlot e)).length ≤ c.limit :=
  (Limit.reachable_limit valid h).2

/-- An ended task holds no slot, so its slot is free for another task (§8.2). --/
theorem State.holdsSlot_of_taskEnded {s : State} {e : Execution} {t : TaskState} (h : s.taskEnded e t = true) :
    s.holdsSlot e t = false := by
  simp only [State.taskEnded, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

/-- Task results and task calls stay inside their own execution (§8.4). --/
theorem Reachable.taskResultsOwned {p : Definition} {s : State} (h : Reachable p s) :
    ∀ r ∈ s.taskResults, ∃ e ∈ s.executions, e.id = r.execution ∧ ∃ t ∈ e.tasks, t.name = r.task := by
  intro r hr
  obtain ⟨e, he, hid, x, hx, hn, -⟩ := (Limit.reachable_inv h).results r hr
  exact ⟨e, he, hid, x, hx, hn⟩

end Suimon
