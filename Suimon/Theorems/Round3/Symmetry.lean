import Suimon.Theorems.Round3.CoversStep
import Suimon.Theorems.Round3.Ledger
import Suimon.Theorems.Round3.SymmetryBase

namespace Suimon.Round3
open State

/-! ## [26] Round3/Symmetry.lean — task G1 -/

section Symmetry
variable {p : Program}

/-- The status `conclude` gives from a running state (§11.4, §13.3), read off the records. -/
def conclusionStatus (p : Program) (s : State) : Status :=
  match (s.run? []).bind fun r => p.workflow? r.workflow with
  | none => .running
  | some w =>
    if !s.failures.isEmpty then .failed
    else if (w.placements.filter fun pl => w.isEndpoint pl.name).all
        (fun pl => (s.settled? [] pl.name).any (·.outcome == .skipped)) then .skipped
    else .succeeded

/-- A complete state carries the status its conclusion computed; nothing changes after it. -/
theorem complete_status {s : State} (h : Reachable p s) (done : Done s) : s.status = conclusionStatus p s := by
  -- The conclusion completed the root run and computed the status from records it did not change.
  obtain ⟨r, w, hr, hw, -, -, hst⟩ := SymmetryAux.done_root h done
  rw [hst]
  simp only [conclusionStatus, hr, Option.bind_some, hw]
  rfl

/-- A complete state was started and never cancelled (a cancel stops, and a stopped workflow never
    completes its root run). -/
theorem done_flags {s : State} (h : Reachable p s) (done : Done s) : s.started = true ∧ s.cancelled = false := by
  obtain ⟨-, -, -, -, hs, hc, -⟩ := SymmetryAux.done_root h done
  exact ⟨hs, hc⟩

/-- Two complete states covering each other agree record by record: mutual membership and unique keys
    give permutations, and in complete states every record is finished. -/
theorem covers_symm_records {S T : State} (hS : Reachable p S) (hT : Reachable p T) (dS : Done S) (dT : Done T)
    (c₁ : Covers p T S) (c₂ : Covers p S T) :
    S.results.Perm T.results ∧ S.deliveries.Perm T.deliveries ∧ S.settled.Perm T.settled ∧
    S.invocations.Perm T.invocations ∧ S.calls.Perm T.calls ∧ S.executions.Perm T.executions ∧
    S.taskResults.Perm T.taskResults ∧ S.runs.Perm T.runs := by
  have wkS := hS.wellKeyed
  have wkT := hT.wellKeyed
  obtain ⟨rS, eS, cS, iS⟩ := SymmetryAux.done_records hS dS
  obtain ⟨rT, eT, cT, iT⟩ := SymmetryAux.done_records hT dT
  refine ⟨SymmetryAux.perm_of_mem wkS.results wkT.results c₁.results c₂.results,
    SymmetryAux.perm_of_mem wkS.deliveries wkT.deliveries c₁.deliveries c₂.deliveries,
    SymmetryAux.perm_of_mem wkS.settled wkT.settled c₁.settled c₂.settled,
    SymmetryAux.perm_of_mem wkS.invocations wkT.invocations (fun i hi => ?_) (fun i hi => ?_),
    SymmetryAux.perm_of_mem wkS.calls wkT.calls (fun c hc => ?_) (fun c hc => ?_),
    SymmetryAux.perm_of_mem wkS.executions wkT.executions (fun e he => ?_) (fun e he => ?_),
    SymmetryAux.perm_of_mem wkS.taskResults wkT.taskResults
      (fun _ hr => SymmetryAux.taskResult_mem wkS c₁.taskResults c₂.taskResults hr)
      (fun _ hr => SymmetryAux.taskResult_mem wkT c₂.taskResults c₁.taskResults hr),
    SymmetryAux.perm_of_mem wkS.runs wkT.runs (fun r hr => ?_) (fun r hr => ?_)⟩
  -- Ended invocations and calls, completed executions and completed runs are identical in both states.
  · obtain ⟨i', hi', -, -, -, -, -, heq⟩ := c₁.invocations i hi
    rw [← heq (iS i hi)]
    exact hi'
  · obtain ⟨i', hi', -, -, -, -, -, heq⟩ := c₂.invocations i hi
    rw [← heq (iT i hi)]
    exact hi'
  · obtain ⟨c', hc', -, -, -, -, -, -, -, -, heq⟩ := c₁.calls c hc
    rw [← heq (cS c hc)]
    exact hc'
  · obtain ⟨c', hc', -, -, -, -, -, -, -, -, heq⟩ := c₂.calls c hc
    rw [← heq (cT c hc)]
    exact hc'
  · obtain ⟨e', he', -, -, -, -, -, -, heq⟩ := c₁.executions e he
    rw [← heq (eS e he)]
    exact he'
  · obtain ⟨e', he', -, -, -, -, -, -, heq⟩ := c₂.executions e he
    rw [← heq (eT e he)]
    exact he'
  · obtain ⟨r', hr', h₁, h₂, h₃, h₄, h₅⟩ := c₁.runs r hr
    rw [← SymmetryAux.run_ext h₁ h₂ h₃ h₄ h₅ ((rT r' hr').trans (rS r hr).symm)]
    exact hr'
  · obtain ⟨r', hr', h₁, h₂, h₃, h₄, h₅⟩ := c₂.runs r hr
    rw [← SymmetryAux.run_ext h₁ h₂ h₃ h₄ h₅ ((rS r' hr').trans (rT r hr).symm)]
    exact hr'

/-- The ledger reads records only through lookups by unique keys. -/
theorem ledger_perm {S T : State} (hS : Reachable p S) (hT : Reachable p T)
    (h : S.results.Perm T.results ∧ S.deliveries.Perm T.deliveries ∧ S.settled.Perm T.settled ∧
      S.invocations.Perm T.invocations ∧ S.calls.Perm T.calls ∧ S.executions.Perm T.executions ∧
      S.taskResults.Perm T.taskResults ∧ S.runs.Perm T.runs) :
    (ledger p S).Perm (ledger p T) := by
  -- Unique keys in `S` suffice; `T` inherits them through the permutations.
  have _ := hT
  obtain ⟨-, hdel, -, hinv, hcalls, hexec, htr, hruns⟩ := h
  exact SymmetryAux.ledger_perm_of hS.wellKeyed hcalls hdel hinv hexec htr hruns

theorem conclusionStatus_congr {S T : State} (hS : Reachable p S) (hT : Reachable p T)
    (hf : S.failures.Perm T.failures) (hset : S.settled.Perm T.settled) (hruns : S.runs.Perm T.runs) :
    conclusionStatus p S = conclusionStatus p T := by
  -- As in `ledger_perm`, unique keys in `S` suffice for the lookups.
  have _ := hT
  have wk := hS.wellKeyed
  simp only [conclusionStatus, SymmetryAux.run?_perm wk hruns, hf.isEmpty_eq, SymmetryAux.settled?_perm wk hset]

end Symmetry

end Suimon.Round3
