import Suimon.Trace.AtomGrammar

namespace Suimon.Trace
open Lean

private theorem jsonAtoms_array_of_value (j : Json) (stack : List JsonContext)
    (value : ∀ tail, (jsonAtoms j).foldlM advanceJson (.value :: tail) = some tail) :
    (jsonAtoms j).foldlM advanceJson (.array :: stack) = some (.array :: stack) := by
  have h := value (.array :: stack)
  cases j <;> simpa only [jsonAtoms, List.cons_append, List.foldlM_cons, advanceJson, beginValue] using h

mutual
  theorem jsonAtoms_value (j : Json) (stack : List JsonContext) :
      (jsonAtoms j).foldlM advanceJson (.value :: stack) = some stack := by
    cases j with
    | null => simp [jsonAtoms, List.foldlM_cons, advanceJson, beginValue, pure]
    | bool b => simp [jsonAtoms, List.foldlM_cons, advanceJson, beginValue, pure]
    | num n => simp [jsonAtoms, List.foldlM_cons, advanceJson, beginValue, pure]
    | str s => simp [jsonAtoms, List.foldlM_cons, advanceJson, beginValue, pure]
    | arr items =>
      simp only [jsonAtoms, List.cons_append, List.foldlM_cons, advanceJson, beginValue, bind, Option.bind, List.foldlM_append]
      rw [jsonArrayAtoms_values items.toList stack]
      rfl
    | obj fields =>
      simp only [jsonAtoms, List.cons_append, List.foldlM_cons, advanceJson, beginValue, bind, Option.bind, List.foldlM_append]
      rw [jsonObjectAtoms_fields fields.inner.inner stack]
      rfl
  termination_by sizeOf j
  decreasing_by
    · cases items; simp; omega
    · cases fields with | mk inner => cases inner; simp; omega

  theorem jsonArrayAtoms_values (items : List Json) (stack : List JsonContext) :
      (jsonArrayAtoms items).foldlM advanceJson (.array :: stack) = some (.array :: stack) := by
    cases items with
    | nil => simp [jsonArrayAtoms, pure]
    | cons item rest =>
      rw [jsonArrayAtoms, List.foldlM_append,
        jsonAtoms_array_of_value item stack (jsonAtoms_value item)]
      exact jsonArrayAtoms_values rest stack
  termination_by sizeOf items
  decreasing_by all_goals simp_all <;> omega

  theorem jsonObjectAtoms_fields (fields : Std.DTreeMap.Internal.Impl String (fun _ => Json)) (stack : List JsonContext) :
      (jsonObjectAtoms fields).foldlM advanceJson (.object :: stack) = some (.object :: stack) := by
    cases fields with
    | leaf => simp [jsonObjectAtoms, pure]
    | inner size key value left right =>
      simp only [jsonObjectAtoms, List.foldlM_append]
      rw [jsonObjectAtoms_fields left stack]
      simp only [bind, Option.bind, List.foldlM_cons, advanceJson]
      rw [jsonAtoms_value value (.object :: stack)]
      exact jsonObjectAtoms_fields right stack
  termination_by sizeOf fields
  decreasing_by all_goals simp_all <;> omega
end

theorem validJsonAtoms_json (j : Json) : validJsonAtoms (jsonAtoms j) = true := by
  simp [validJsonAtoms, jsonAtoms_value]

end Suimon.Trace
