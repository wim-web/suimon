import Suimon.Theorems.FrameTree

namespace Suimon
open Semantics Effects

theorem step_frameOwners {s next : State} {op : Op} (safe : Invariants s)
    (distinct : (next.frames.map Frame.path).Nodup) (accepted : step s op = .ok next)
    (owners : FrameOwners s) : FrameOwners next := by
  have one : ConformingSteps (fun _ _ => True) s [op] next := .cons trivial accepted (.nil next)
  intro f memberF id ownerF
  rcases step_frames_origin s next op safe accepted f memberF with ⟨old, memberOld, pathOld⟩ | opened
  · have definitions := one.frame_definition old memberOld distinct f memberF pathOld.symm
    obtain ⟨i, memberI, idI, segment, pathI⟩ := owners old memberOld id (definitions.2.1.symm.trans ownerF)
    obtain ⟨j, memberJ, bindingJ⟩ := one.retains_binding safe i memberI
    exact ⟨j, memberJ, (congrArg Prod.fst bindingJ).trans idI, segment,
      by rw [Instance.binding_path bindingJ, ← pathOld, pathI]⟩
  · rcases opened with
      ⟨P, N, n, inputs, body, iteration, _, _, _, _, shape, _, _, instances⟩ |
      ⟨P, N, item, n, body, c, _, _, _, _, _, shape, _, _, instances, _⟩ |
      ⟨inst, i, n, body, limit, old, items, item, _, found, _, _, _, _, _, _, _, shape, _, _, instances⟩ |
      ⟨inst, i, n, body, limit, old, items, _, found, _, _, _, _, _, _, shape, _, _, instances⟩
    · let initial := { makeInstance P n .waitingInputs inputs with iteration }
      exact ⟨initial, by rw [instances]; simp [initial], Option.some.inj (shape.2.2.1.symm.trans ownerF), _, shape.1⟩
    · let initial := makeInstance P n .waitingInputs [("item", item)] (some item)
      exact ⟨initial, by rw [instances]; simp [initial], Option.some.inj (shape.2.2.1.symm.trans ownerF), _, shape.1⟩
    · let updated := {i with iteration := i.iteration + 1}
      exact ⟨updated, by rw [instances]; exact setInstance_self_mem s i updated (instance?_mem found) rfl,
        Option.some.inj (shape.2.2.1.symm.trans ownerF), _, shape.1⟩
    · let updated := {i with status := .waitingInputs, extraIterations := i.extraIterations + 1, iteration := i.iteration + 1}
      exact ⟨updated, by rw [instances]; exact setInstance_self_mem s i updated (instance?_mem found) rfl,
        Option.some.inj (shape.2.2.1.symm.trans ownerF), _, shape.1⟩

theorem ConformingSteps.frameOwners {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (distinct : (s.frames.map Frame.path).Nodup)
    (owners : FrameOwners s) : FrameOwners last := by
  induction run with
  | nil => exact owners
  | cons allowed accepted tail ih =>
    have one : ConformingSteps (fun _ _ => True) _ [_] _ := .cons trivial accepted (.nil _)
    have distinctNext := one.unique_frames distinct
    exact ih (preserves_invariants _ _ _ safe accepted) distinctNext (step_frameOwners safe distinctNext accepted owners)

end Suimon
