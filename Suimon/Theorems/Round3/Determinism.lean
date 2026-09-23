import Suimon.Theorems.Round3.Symmetry
import Suimon.Theorems.Round3.NoStop
import Suimon.Theorems.Round3.Termination

namespace Suimon.Round3
open State

/-! ## [28] Round3/Determinism.lean — proven assembly -/

section Determinism
variable {p : Program} {env : Env}

/-- **Determinism of results.** Two conforming executions of a valid program in the same environment
    (input, behavior of calls and transforms) that complete (the root run completed, so neither stopped
    nor was cancelled) end in states equal up to the order of every record list, whatever the schedule,
    including the order in which tasks got concurrency slots. -/
theorem determinism (valid : p.validate = .ok ()) {tr₁ tr₂ : List Op} {s₁ s₂ : State}
    (h₁ : Conforming p env tr₁ s₁) (h₂ : Conforming p env tr₂ s₂) (d₁ : Done s₁) (d₂ : Done s₂) : Same s₁ s₂ := by
  have c₁ : Covers p s₂ s₁ := covers_of_execution valid h₂ d₂ h₁ (Or.inr d₁)
  have c₂ : Covers p s₁ s₂ := covers_of_execution valid h₁ d₁ h₂ (Or.inr d₂)
  have hrec := covers_symm_records h₁.reachable h₂.reachable d₁ d₂ c₁ c₂
  obtain ⟨hres, hdel, hset, hinv, hcalls, hexec, htr, hruns⟩ := hrec
  have hf : s₁.failures.Perm s₂.failures :=
    ((Reachable.failures_ledger valid h₁.reachable).trans
      (ledger_perm h₁.reachable h₂.reachable ⟨hres, hdel, hset, hinv, hcalls, hexec, htr, hruns⟩)).trans
      (Reachable.failures_ledger valid h₂.reachable).symm
  obtain ⟨st₁, ca₁⟩ := done_flags h₁.reachable d₁
  obtain ⟨st₂, ca₂⟩ := done_flags h₂.reachable d₂
  refine ⟨?_, st₁.trans st₂.symm, ca₁.trans ca₂.symm, hruns, hinv, hcalls, hexec, hres, htr, hdel, hset, hf⟩
  rw [complete_status h₁.reachable d₁, complete_status h₂.reachable d₂]
  exact conclusionStatus_congr h₁.reachable h₂.reachable hf hset hruns

/-- **T9 (§15.4).** The results (list values are multisets through `listValue`), the values on every
    connection, the endpoint results, the settlements, the failures (as a multiset) and the final status
    agree. -/
theorem T9 (valid : p.validate = .ok ()) {tr₁ tr₂ : List Op} {s₁ s₂ : State}
    (h₁ : Conforming p env tr₁ s₁) (h₂ : Conforming p env tr₂ s₂) (d₁ : Done s₁) (d₂ : Done s₂) :
    s₁.status = s₂.status ∧ s₁.results.Perm s₂.results ∧ s₁.deliveries.Perm s₂.deliveries ∧
      s₁.settled.Perm s₂.settled ∧ s₁.failures.Perm s₂.failures ∧
      (∀ path j, (s₁.deliveriesOn path j).Perm (s₂.deliveriesOn path j)) ∧
      (∀ name, (s₁.resultsOf [] name).Perm (s₂.resultsOf [] name)) := by
  have e := determinism valid h₁ h₂ d₁ d₂
  exact ⟨e.status, e.results, e.deliveries, e.settled, e.failures,
    fun _ _ => e.deliveries.filter _, fun _ => e.results.filter _⟩

/-- Completion does not depend on the schedule: if one conforming execution completes, every conforming
    execution that cannot be extended, in which the caller does not cancel, completes too, in the same
    state up to list order. -/
theorem completion_schedule_independent (valid : p.validate = .ok ()) (hin : env.InputFits p) (fits : env.Fits p)
    (nocancel : env.cancels = false) {tr₁ tr₂ : List Op} {s₁ s₂ : State}
    (h₁ : Conforming p env tr₁ s₁) (d₁ : Done s₁) (h₂ : Conforming p env tr₂ s₂) (stuck : Stuck p env s₂) :
    Done s₂ ∧ Same s₂ s₁ := by
  have hterm := stuck_terminal valid hin fits h₂ stuck
  have d₂ : Done s₂ := by
    rcases no_stop valid nocancel h₁ d₁ h₂ with hrun | hd
    · simp [hrun, Status.terminal] at hterm
    · exact hd
  exact ⟨d₂, determinism valid h₂ h₁ d₂ d₁⟩

end Determinism

end Suimon.Round3
