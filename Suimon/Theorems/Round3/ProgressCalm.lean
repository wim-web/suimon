import Suimon.Theorems.Round3.ProgressEasy
import Suimon.Theorems.Round3.SettledValue
import Suimon.Theorems.Round3.ShapeFits
import Suimon.Theorems.Round3.ProgressCalmSteps

namespace Suimon.Round3
open State

/-! ## [8] Round3/ProgressCalm.lean — task C2 -/

section ProgressCalm
variable {p : Definition} {s : State}

/-- In a calm state the deepest open run moves: a ready task of one of its executions begins (no slot
    is held there: every call ended and every run below is complete), an execution closes, the first
    unsettled placement in rank order is invoked or settles, or the run closes (the root concludes).
    None of these operations has external data. -/
theorem calm_progress (valid : p.validate = .ok ()) (h : Reachable p s) (running : s.status = .running)
    (calm : Calm p s) {r : Run} (hr : DeepestOpen s r) :
    ∃ op t, engine op = true ∧
      (op = .conclude ∨ op = .closeRun r.path ∨ (∃ n, op = .settle r.path n) ∨ (∃ n tr, op = .invoke r.path n tr) ∨
        (∃ e, op = .closeExecution e) ∨ (∃ e n, op = .beginTask e n)) ∧
      step p s op = .ok t ∧ t ≠ s := by
  have hrm := hr.1
  have hopen := hr.2.1
  have started : s.started = true := by
    rcases h.eq_empty_or_started with rfl | hs
    · cases hrm
    · exact hs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (run_workflow valid h r hrm)
  by_cases hall : ∀ pl ∈ w.placements, (s.settled? r.path pl.name).isSome
  · -- Every placement settled: the run closes, or the root concludes.
    obtain ⟨op, t, hop, hs, hne⟩ := CalmAux.close_step valid h started running hrm hopen hw hall
    rcases hop with rfl | rfl
    · exact ⟨_, t, rfl, Or.inl rfl, hs, hne⟩
    · exact ⟨_, t, rfl, Or.inr (Or.inl rfl), hs, hne⟩
  by_cases hex : ∃ e ∈ s.executions, e.run = r.path ∧ e.complete = false
  · -- An open execution of the run begins a task or closes.
    obtain ⟨e, he, herun, heopen⟩ := hex
    obtain ⟨op, t, hop, hs, hne⟩ := CalmAux.exec_step valid h started running calm hr he herun heopen
    rcases hop with ⟨e', rfl⟩ | ⟨e', n, rfl⟩
    · exact ⟨_, t, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e', rfl⟩)))), hs, hne⟩
    · exact ⟨_, t, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e', n, rfl⟩)))), hs, hne⟩
  -- Every execution of the run completed, so every invocation of the run ended; the first unsettled
  -- placement in rank order is invoked or settles.
  have hexec : ∀ e ∈ s.executions, e.run = r.path → e.complete = true := by
    intro e he herun
    cases hc : e.complete with
    | true => rfl
    | false => exact absurd ⟨e, he, herun, hc⟩ hex
  obtain ⟨pl, hpl, hunset, hsrc⟩ := CalmAux.min_unsettled valid (Definition.workflow?_eq_some hw).1 hall
  have hended : ∀ i ∈ s.invocationsOf r.path pl.name, s.invocationEnded i = true := fun i hi =>
    CalmAux.inv_ended h calm hr hexec (Delivery.mem_invocationsOf.mp hi).1 (Delivery.mem_invocationsOf.mp hi).2.1
  obtain ⟨op, t, hop, hs, hne⟩ :=
    CalmAux.placement_step valid h started running calm hrm hopen hw hpl hunset hsrc hended
  rcases hop with ⟨n, rfl⟩ | ⟨n, tr, rfl⟩
  · exact ⟨_, t, rfl, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)), hs, hne⟩
  · exact ⟨_, t, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨n, tr, rfl⟩))), hs, hne⟩

end ProgressCalm

end Suimon.Round3
