import Suimon.Json
import Suimon.Theorems.WireText

namespace Suimon.Codec

/-! ## The canonical form of a definition repeats no key

The header of an execution record holds `definitionWire`, and a line may not repeat a key
(`Wire.parse`). Each object of the canonical form has fixed, distinct keys, so the header of every
record a recorder writes reads back (`Trace.check_torn`). -/

/-- The keys of the fields that are present are among the keys of all fields, in order. --/
theorem obj_keys_sublist (fields : List (String × Option Wire)) :
    ((fields.filterMap fun (key, value) => value.map (key, ·)).map (·.1)).Sublist (fields.map (·.1)) := by
  induction fields with
  | nil => simp
  | cons f fs ih =>
    obtain ⟨key, value⟩ := f
    cases value with
    | none => simpa using ih.cons key
    | some w => simpa using ih.cons_cons key

theorem obj_distinctKeys {fields : List (String × Option Wire)} (hkeys : (fields.map (·.1)).Nodup)
    (hvalues : ∀ f ∈ fields, ∀ w ∈ f.2, w.DistinctKeys) : (obj fields).DistinctKeys :=
  .obj ((obj_keys_sublist fields).nodup hkeys) fun f hf => by
    obtain ⟨⟨key, value⟩, hmem, hf⟩ := List.mem_filterMap.1 hf
    cases value with
    | none => simp at hf
    | some w =>
      obtain rfl : (key, w) = f := by simpa using hf
      exact hvalues _ hmem w rfl

theorem arr_map_distinctKeys {α : Type} {f : α → Wire} (h : ∀ a, (f a).DistinctKeys) (xs : List α) :
    (Wire.arr (xs.map f)).DistinctKeys :=
  .arr fun w hw => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
    exact h a

theorem valueTypeWire_distinctKeys : ∀ t, (valueTypeWire t).DistinctKeys
  | .named name => .str name
  | .list element => .obj (by simp) (by simp [valueTypeWire_distinctKeys element])

theorem contractWire_distinctKeys (c : Contract) : (contractWire c).DistinctKeys := by
  cases c <;> simp [contractWire, Wire.distinctKeys_obj_iff, valueTypeWire_distinctKeys]

theorem policyWire_distinctKeys (p : Policy) : (policyWire p).DistinctKeys := by
  cases p <;> exact .str _

theorem transformRefWire_distinctKeys (t : TransformRef) : (transformRefWire t).DistinctKeys := by
  cases t <;> exact .str _

theorem collectWire_distinctKeys (c : Collect) : (collectWire c).DistinctKeys := by
  cases c <;> exact .str _

theorem timeoutWire_distinctKeys (t : Timeout) : ∀ w, timeoutWire t = some w → w.DistinctKeys := by
  intro w hw
  simp only [timeoutWire] at hw
  split at hw
  · simp at hw
  · obtain rfl : _ = w := Option.some.inj hw
    exact obj_distinctKeys (by simp) (by simp [Wire.DistinctKeys.nat])

theorem bodyWire_distinctKeys (b : Body) : (bodyWire b).DistinctKeys := by
  cases b <;> simp [bodyWire, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.str]

theorem taskWire_distinctKeys (t : TaskSpec) : (taskWire t).DistinctKeys :=
  obj_distinctKeys (by simp) (by
    simpa [Wire.DistinctKeys.str, bodyWire_distinctKeys, transformRefWire_distinctKeys, policyWire_distinctKeys]
      using timeoutWire_distinctKeys t.timeout)

theorem controlWire_distinctKeys (c : Control) : (controlWire c).DistinctKeys := by
  cases c with
  | call b => exact bodyWire_distinctKeys b
  | branch judge arms =>
    simp [controlWire, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.str, arr_map_distinctKeys]
  | waitStream element =>
    simp [controlWire, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.str, valueTypeWire_distinctKeys]
  | merge element => simp [controlWire, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.str, valueTypeWire_distinctKeys]
  | concurrency c =>
    exact obj_distinctKeys (by simp) (by
      simp [Wire.DistinctKeys.str, Wire.DistinctKeys.nat, valueTypeWire_distinctKeys, collectWire_distinctKeys,
        arr_map_distinctKeys taskWire_distinctKeys])

theorem placementWire_distinctKeys (p : Placement) : (placementWire p).DistinctKeys :=
  obj_distinctKeys (by simp) (by
    simpa [Wire.DistinctKeys.str, controlWire_distinctKeys, policyWire_distinctKeys]
      using timeoutWire_distinctKeys p.timeout)

theorem connectionWire_distinctKeys (c : Connection) : (connectionWire c).DistinctKeys :=
  obj_distinctKeys (by simp) (by simp [Wire.DistinctKeys.str, transformRefWire_distinctKeys])

theorem workflowWire_distinctKeys (w : Workflow) : (workflowWire w).DistinctKeys :=
  obj_distinctKeys (by simp) (by
    simp [Wire.DistinctKeys.str, Wire.distinctKeys_obj_iff, valueTypeWire_distinctKeys,
      arr_map_distinctKeys placementWire_distinctKeys, arr_map_distinctKeys connectionWire_distinctKeys])

/-- The canonical form of every definition repeats no key, so a recorder's header reads back. --/
theorem definitionWire_distinctKeys (p : Definition) : (definitionWire p).DistinctKeys := by
  simp only [definitionWire, Wire.distinctKeys_obj_iff]
  refine ⟨by simp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨.str _, ?_, ?_, ?_, arr_map_distinctKeys workflowWire_distinctKeys _⟩
  · exact arr_map_distinctKeys (fun f => obj_distinctKeys (by simp) (by
      simp [Wire.DistinctKeys.str, valueTypeWire_distinctKeys, contractWire_distinctKeys])) _
  · exact arr_map_distinctKeys (fun j => .obj (by simp) (by
      simp [Wire.DistinctKeys.str, valueTypeWire_distinctKeys])) _
  · exact arr_map_distinctKeys (fun t => .obj (by simp) (by
      simp [Wire.DistinctKeys.str, valueTypeWire_distinctKeys])) _

end Suimon.Codec
