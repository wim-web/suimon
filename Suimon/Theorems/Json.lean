import Suimon.Json
import Suimon.Normal
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

theorem entryWire_distinctKeys (e : Entry) : (entryWire e).DistinctKeys :=
  .obj (by simp) (by simp [Wire.DistinctKeys.str, valueTypeWire_distinctKeys])

theorem workflowWire_distinctKeys (w : Workflow) : (workflowWire w).DistinctKeys :=
  obj_distinctKeys (by simp) (by
    simp [Wire.DistinctKeys.str, entryWire_distinctKeys, arr_map_distinctKeys placementWire_distinctKeys,
      arr_map_distinctKeys connectionWire_distinctKeys])

theorem functionWire_distinctKeys (f : FunctionDecl) : (functionWire f).DistinctKeys :=
  obj_distinctKeys (by simp) (by simp [Wire.DistinctKeys.str, valueTypeWire_distinctKeys, contractWire_distinctKeys])

theorem judgeWire_distinctKeys (j : JudgeDecl) : (judgeWire j).DistinctKeys :=
  .obj (by simp) (by simp [Wire.DistinctKeys.str, valueTypeWire_distinctKeys])

theorem transformWire_distinctKeys (t : TransformDecl) : (transformWire t).DistinctKeys :=
  .obj (by simp) (by simp [Wire.DistinctKeys.str, valueTypeWire_distinctKeys])

/-- The canonical form of every definition repeats no key, so a recorder's header reads back. --/
theorem definitionWire_distinctKeys (p : Definition) : (definitionWire p).DistinctKeys := by
  simp only [definitionWire, Wire.distinctKeys_obj_iff]
  refine ⟨by simp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨.str _, arr_map_distinctKeys functionWire_distinctKeys _, arr_map_distinctKeys judgeWire_distinctKeys _,
    arr_map_distinctKeys transformWire_distinctKeys _, arr_map_distinctKeys workflowWire_distinctKeys _⟩

end Suimon.Codec

/-! ## The canonical form of a normal definition decodes back to it

The header of a record holds `definitionWire p`, and a loader decodes its `Json` with `Codec.definition`
(and then validates it). The decoder reads fields by key and rejects what the definition file cannot
express: an empty string or type name, a number above `maxNat`. `Definition.Expressible` states what it
can express; every normal definition is expressible (`Definition.Normal.expressible`), and the canonical
form of an expressible definition decodes back to it (`Codec.definition_definitionWire_of_expressible`). -/

namespace Suimon

/-- A body whose names are not empty. --/
def Body.Expressible : Body → Prop
  | .function id => id ≠ ""
  | .workflow id output => id ≠ "" ∧ output ≠ ""

/-- `discard`, or the non-empty name of another transform: the decoder reads the name `discard` as the
    library's transform. --/
def TransformRef.Expressible : TransformRef → Prop
  | .discard => True
  | .declared id => id ≠ "" ∧ id ≠ TransformRef.discardName

/-- Durations that implementations hold in 64 bits. --/
def Timeout.Expressible (t : Timeout) : Prop :=
  ∀ ms ∈ t.callMs.toList ++ t.elementMs.toList, ms ≤ maxNat

structure TaskSpec.Expressible (t : TaskSpec) : Prop where
  name : t.name ≠ ""
  body : t.body.Expressible
  input : ∀ r ∈ t.input, r.Expressible
  output : ∀ id ∈ t.output, id ≠ ""
  timeout : t.timeout.Expressible

def Control.Expressible : Control → Prop
  | .call body => body.Expressible
  | .branch judge arms => judge ≠ "" ∧ ∀ arm ∈ arms, arm ≠ ""
  | .waitStream e | .merge e => e.name ≠ ""
  | .concurrency c => (∀ t ∈ c.input, t.name ≠ "") ∧ c.limit ≤ maxNat ∧ (∀ t ∈ c.tasks, t.Expressible) ∧
      c.element.name ≠ ""

structure Placement.Expressible (pl : Placement) : Prop where
  name : pl.name ≠ ""
  control : pl.control.Expressible
  timeout : pl.timeout.Expressible

structure Connection.Expressible (c : Connection) : Prop where
  source : c.source ≠ ""
  arm : ∀ a ∈ c.arm, a ≠ ""
  target : c.target ≠ ""
  transform : c.transform.Expressible

structure Workflow.Expressible (w : Workflow) : Prop where
  id : w.id ≠ ""
  input : ∀ e ∈ w.input, e.valueType.name ≠ "" ∧ e.placement ≠ ""
  placements : ∀ pl ∈ w.placements, pl.Expressible
  connections : ∀ c ∈ w.connections, c.Expressible

/-- What the definition file can express: names, identifiers and type names that are not empty,
    numbers at most `maxNat`, and the name of a declared transform other than `discard` wherever one
    is named. --/
structure Definition.Expressible (p : Definition) : Prop where
  main : p.main ≠ ""
  functions : ∀ f ∈ p.functions, f.id ≠ "" ∧ (∀ t ∈ f.input, t.name ≠ "") ∧ f.output.element.name ≠ ""
  judges : ∀ j ∈ p.judges, j.id ≠ "" ∧ j.input.name ≠ ""
  transforms : ∀ t ∈ p.transforms, t.id ≠ "" ∧ t.input.name ≠ "" ∧ t.output.name ≠ ""
  workflows : ∀ w ∈ p.workflows, w.Expressible

private theorem find?_key {α κ : Type} [BEq κ] [LawfulBEq κ] {l : List α} {f : α → κ} {k : κ} {x : α}
    (h : l.find? (fun x => f x == k) = some x) : x ∈ l ∧ f x = k :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

private theorem isSome_find?_key {α κ : Type} [BEq κ] [LawfulBEq κ] {l : List α} {f : α → κ} {k : κ}
    (h : (l.find? (fun x => f x == k)).isSome) : ∃ x ∈ l, f x = k := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  exact ⟨x, find?_key hx⟩

private theorem mem_input {t : ValueType} {input : Option ValueType} {last : ValueType} (ht : t ∈ input) :
    t ∈ input.toList ++ [last] := by
  cases input with
  | none => cases ht
  | some u => cases ht; simp

theorem Timeout.Legal.expressible {t : Timeout} {function : Option Contract} {judge : Bool}
    (ht : t.Legal function judge) : t.Expressible :=
  fun ms hms => (ht.positive ms hms).2

namespace Definition.Normal
variable {p : Definition} (h : p.Normal)
include h

theorem workflow_id {id : String} {w : Workflow} (hw : p.workflow? id = some w) : id ≠ "" := by
  obtain ⟨hm, rfl⟩ := find?_key hw
  exact (h.workflows w hm).id

theorem function_id {id : String} (hf : (p.function? id).isSome) : id ≠ "" := by
  obtain ⟨f, hm, rfl⟩ := isSome_find?_key hf
  exact (h.functions f hm).1

theorem judge_id {id : String} (hj : (p.judge? id).isSome) : id ≠ "" := by
  obtain ⟨j, hm, rfl⟩ := isSome_find?_key hj
  exact (h.judges j hm).1

theorem transform_id {id : String} {t : TransformDecl} (ht : p.transform? id = some t) :
    id ≠ "" ∧ id ≠ TransformRef.discardName := by
  obtain ⟨hm, rfl⟩ := find?_key ht
  exact ⟨(h.transforms t hm).1, h.discard t hm⟩

theorem body {b : Body} (hb : b.Normal p) : b.Expressible := by
  cases b with
  | function id => exact h.function_id hb
  | workflow id output =>
    obtain ⟨w, hw, hpl, -⟩ := hb
    obtain ⟨pl, hm, rfl⟩ := isSome_find?_key hpl
    exact ⟨h.workflow_id hw, (h.workflows w (find?_key hw).1).names pl hm⟩

theorem transformRef {source : ValueType} {r : TransformRef} {input : Option ValueType}
    (hr : p.TransformFits source r input) : r.Expressible := by
  cases r with
  | discard => trivial
  | declared id =>
    cases input with
    | none => cases hr
    | some _ =>
      obtain ⟨t, ht, -⟩ := hr
      exact h.transform_id ht

theorem task {c : Concurrency} {task : TaskSpec} (ht : task.Normal p c) : task.Expressible := by
  refine ⟨ht.name, h.body ht.body, fun r hr => ?_, fun id hid => ?_, ht.timeout.expressible⟩
  · obtain ⟨input, -, hin⟩ := ht.input
    cases hc : c.input with
    | none => rw [hc] at hin; rw [hin.2] at hr; cases hr
    | some source =>
      rw [hc] at hin
      obtain ⟨r', hr', hfits⟩ := hin
      rw [hr'] at hr
      cases hr
      exact h.transformRef hfits
  · obtain ⟨t, htr, -⟩ := ht.output id hid
    exact (h.transform_id htr).1

theorem placement {w : Workflow} (hw : w ∈ p.workflows) {pl : Placement} (hpl : pl ∈ w.placements) :
    pl.Expressible := by
  have hn := (h.workflows w hw).placements pl hpl
  refine ⟨(h.workflows w hw).names pl hpl, ?_, hn.timeout.expressible⟩
  rcases hc : pl.control with body | ⟨judge, arms⟩ | e | e | c
  · exact h.body (hn.call body hc)
  · obtain ⟨hj, -, -, harms, -⟩ := hn.branch judge arms hc
    exact ⟨h.judge_id hj, harms⟩
  · exact (hn.waitStream e hc).1
  · exact (hn.merge e hc).1
  · obtain ⟨htypes, -, hlimit, -, -, -, htasks⟩ := hn.concurrency c hc
    exact ⟨fun t ht => htypes t (mem_input ht), hlimit, fun t ht => h.task (htasks t ht),
      htypes c.element (by simp)⟩

theorem connection {w : Workflow} (hw : w ∈ p.workflows) {c : Connection} (hc : c ∈ w.connections) :
    c.Expressible := by
  have hwn := h.workflows w hw
  obtain ⟨src, dst, hsrc, hdst, hbranch, hnot, produced, input, -, -, hfits⟩ := (hwn.connections c hc).ends
  obtain ⟨hsm, hsn⟩ := find?_key hsrc
  obtain ⟨hdm, hdn⟩ := find?_key hdst
  refine ⟨hsn ▸ hwn.names src hsm, fun a ha => ?_, hdn ▸ hwn.names dst hdm, h.transformRef hfits⟩
  by_cases hb : ∃ judge arms, src.control = .branch judge arms
  · obtain ⟨judge, arms, hctl⟩ := hb
    obtain ⟨arm, harm, hca⟩ := hbranch judge arms hctl
    obtain rfl : a = arm := by rw [hca] at ha; exact (Option.some.inj ha).symm
    exact ((hwn.placements src hsm).branch judge arms hctl).2.2.2.1 a harm
  · rw [hnot fun j as hj => hb ⟨j, as, hj⟩] at ha
    cases ha

theorem workflow {w : Workflow} (hw : w ∈ p.workflows) : w.Expressible := by
  have hwn := h.workflows w hw
  refine ⟨hwn.id, fun e he => ?_, fun pl hpl => h.placement hw hpl, fun c hc => h.connection hw hc⟩
  obtain ⟨pl, hpl, -, -⟩ := (hwn.entry e he).placement
  obtain ⟨hm, hn⟩ := find?_key hpl
  exact ⟨(hwn.entry e he).type, hn ▸ hwn.names pl hm⟩

/-- The definition file can express a normal definition. --/
theorem expressible : p.Expressible := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h.main
  exact ⟨h.workflow_id hw, fun f hf => ⟨(h.functions f hf).1, fun t ht => (h.functions f hf).2 t (mem_input ht),
    (h.functions f hf).2 _ (by simp)⟩, h.judges, h.transforms, fun w hw => h.workflow hw⟩

end Definition.Normal

end Suimon

namespace Suimon.Codec
open Lean

/-! ### Objects of `Json` -/

theorem fieldsToJson_eq : ∀ fields : List (String × Wire),
    Wire.fieldsToJson fields = fields.map fun f => (f.1, f.2.toJson)
  | [] => rfl
  | (_, _) :: fs => by simp [Wire.fieldsToJson, fieldsToJson_eq fs]

theorem itemsToJson_eq : ∀ items : List Wire, Wire.itemsToJson items = items.map Wire.toJson
  | [] => rfl
  | _ :: ws => by simp [Wire.itemsToJson, itemsToJson_eq ws]

theorem toJson_str (s : String) : (Wire.str s).toJson = .str s := rfl

theorem toJson_arr (items : List Wire) : (Wire.arr items).toJson = .arr (items.map Wire.toJson).toArray := by
  simp [Wire.toJson, itemsToJson_eq]

/-- A key of an object with distinct keys finds its value. --/
theorem getElem?_ofList_of_mem {l : List (String × Json)} (hl : (l.map (·.1)).Nodup) {k : String} {v : Json}
    (h : (k, v) ∈ l) : (Std.TreeMap.Raw.ofList l compare)[k]? = some v := by
  refine Std.TreeMap.Raw.getElem?_ofList_of_mem (k := k) (by simp) ?_ h
  exact (List.pairwise_map.1 hl).imp fun hne heq => hne (Std.LawfulEqOrd.compare_eq_iff_eq.1 heq)

/-- A key missing from an object finds nothing. --/
theorem getElem?_ofList_of_not_mem {l : List (String × Json)} {k : String} (h : k ∉ l.map (·.1)) :
    (Std.TreeMap.Raw.ofList l compare)[k]? = none :=
  Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simpa using h)

/-- Every key of an object is a key of the list it is made of. --/
theorem mem_keys_of_mem_toList {l : List (String × Json)} {k : String} {v : Json}
    (h : (k, v) ∈ (Std.TreeMap.Raw.ofList l compare).toList) : k ∈ l.map (·.1) := by
  rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some Std.TreeMap.Raw.WF.ofList] at h
  refine Classical.byContradiction fun hk => ?_
  rw [getElem?_ofList_of_not_mem hk] at h
  cases h

theorem field?_json_obj (fields : Std.TreeMap.Raw String Json) (k : String) :
    field? (Json.obj fields) k = fields.get? k := by
  simp only [field?, Json.getObjVal?]
  cases fields.get? k <;> rfl

/-- A loop whose every iteration continues succeeds. --/
theorem forIn_ok_of_yield {α ε : Type} {xs : List α} {f : α → PUnit → Except ε (ForInStep PUnit)}
    (h : ∀ x ∈ xs, f x PUnit.unit = .ok (.yield PUnit.unit)) : forIn xs PUnit.unit f = .ok PUnit.unit := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, h x List.mem_cons_self]
    exact ih fun y hy => h y (List.mem_cons_of_mem x hy)

theorem strict_mkObj {l : List (String × Json)} {allowed : List String} (at_ : String)
    (h : ∀ k ∈ l.map (·.1), k ∈ allowed) : strict (Json.mkObj l) allowed at_ = .ok () := by
  simp only [strict, Json.mkObj]
  rw [forIn_ok_of_yield]
  · rfl
  · rintro ⟨k, v⟩ hkv
    simp [h k (mem_keys_of_mem_toList hkv), pure, Except.pure]

/-! ### Objects of the canonical form -/

theorem toJson_obj (fields : List (String × Wire)) :
    (Wire.obj fields).toJson = Json.mkObj (fields.map fun f => (f.1, f.2.toJson)) := by
  simp [Wire.toJson, fieldsToJson_eq]

theorem keys_toJson (fields : List (String × Wire)) :
    (fields.map fun f => (f.1, f.2.toJson)).map (·.1) = fields.map (·.1) := by
  simp [Function.comp_def]

theorem field?_wire_of_mem {fields : List (String × Wire)} (hkeys : (fields.map (·.1)).Nodup) {k : String}
    {w : Wire} (h : (k, w) ∈ fields) : field? (Wire.obj fields).toJson k = some w.toJson := by
  rw [toJson_obj]
  simp only [field?, Json.mkObj, Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?,
    getElem?_ofList_of_mem (by rw [keys_toJson]; exact hkeys) (List.mem_map.2 ⟨(k, w), h, rfl⟩)]
  rfl

theorem field?_wire_of_not_mem {fields : List (String × Wire)} {k : String} (h : k ∉ fields.map (·.1)) :
    field? (Wire.obj fields).toJson k = none := by
  rw [toJson_obj]
  simp only [field?, Json.mkObj, Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?,
    getElem?_ofList_of_not_mem (by rw [keys_toJson]; exact h)]
  rfl

theorem strict_wire {fields : List (String × Wire)} {allowed : List String} (at_ : String)
    (h : ∀ k ∈ fields.map (·.1), k ∈ allowed) : strict (Wire.obj fields).toJson allowed at_ = .ok () := by
  rw [toJson_obj]
  exact strict_mkObj at_ (by rw [keys_toJson]; exact h)

theorem strict_obj {fields : List (String × Option Wire)} {allowed : List String} (at_ : String)
    (h : ∀ k ∈ fields.map (·.1), k ∈ allowed) : strict (obj fields).toJson allowed at_ = .ok () :=
  strict_wire at_ fun k hk => h k ((obj_keys_sublist fields).subset hk)

theorem lookup_of_mem {α : Type} {fields : List (String × α)} (hkeys : (fields.map (·.1)).Nodup) {k : String}
    {v : α} (h : (k, v) ∈ fields) : fields.lookup k = some v := by
  induction fields with
  | nil => cases h
  | cons f fs ih =>
    obtain ⟨k', v'⟩ := f
    rw [List.map_cons, List.nodup_cons] at hkeys
    rcases List.mem_cons.1 h with h | h
    · cases h; simp [List.lookup]
    · have hne : (k == k') = false :=
        beq_eq_false_iff_ne.2 fun he => hkeys.1 (he ▸ List.mem_map.2 ⟨(k, v), h, rfl⟩)
      simp [List.lookup, hne, ih hkeys.2 h]

theorem lookup_of_not_mem {α : Type} {fields : List (String × α)} {k : String} (h : k ∉ fields.map (·.1)) :
    fields.lookup k = none := by
  induction fields with
  | nil => rfl
  | cons f fs ih =>
    obtain ⟨k', v'⟩ := f
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (k == k') = false := beq_eq_false_iff_ne.2 h.1
    simp [List.lookup, hne, ih h.2]

/-- A field of an object of the canonical form, by its key. --/
theorem field?_wire {fields : List (String × Wire)} (hkeys : (fields.map (·.1)).Nodup) (k : String) :
    field? (Wire.obj fields).toJson k = (fields.lookup k).map Wire.toJson := by
  by_cases hk : k ∈ fields.map (·.1)
  · obtain ⟨⟨k', w⟩, hmem, rfl⟩ := List.mem_map.1 hk
    rw [field?_wire_of_mem hkeys hmem, lookup_of_mem hkeys hmem]
    rfl
  · rw [field?_wire_of_not_mem hk, lookup_of_not_mem hk]
    rfl

/-- With distinct keys, members with the same key are the same. --/
theorem eq_of_key {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.2 ⟨y, hy', he.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨x, hx', he⟩) h.1
    · exact eq_of_key h.2 hx' hy' he

/-- A field of `obj` is its value, and an absent optional field is missing. --/
theorem field?_obj_of_mem {fields : List (String × Option Wire)} (hkeys : (fields.map (·.1)).Nodup) {k : String}
    {v : Option Wire} (h : (k, v) ∈ fields) : field? (obj fields).toJson k = v.map Wire.toJson := by
  have hsub := obj_keys_sublist fields
  cases v with
  | some w => exact field?_wire_of_mem (hsub.nodup hkeys) (List.mem_filterMap.2 ⟨(k, some w), h, rfl⟩)
  | none =>
    refine field?_wire_of_not_mem fun hk => ?_
    obtain ⟨⟨k', w'⟩, hmem, rfl⟩ := List.mem_map.1 hk
    obtain ⟨⟨k'', v''⟩, hmem'', hkv⟩ := List.mem_filterMap.1 hmem
    cases v'' with
    | none => cases hkv
    | some w'' =>
      obtain ⟨rfl, rfl⟩ : k'' = k' ∧ w'' = w' := by simpa using hkv
      cases eq_of_key hkeys hmem'' h rfl

/-- A field of `obj`, by its key: an absent optional field is missing. --/
theorem field?_obj {fields : List (String × Option Wire)} (hkeys : (fields.map (·.1)).Nodup) (k : String) :
    field? (obj fields).toJson k = ((fields.lookup k).bind id).map Wire.toJson := by
  by_cases hk : k ∈ fields.map (·.1)
  · obtain ⟨⟨k', v⟩, hmem, rfl⟩ := List.mem_map.1 hk
    rw [field?_obj_of_mem hkeys hmem, lookup_of_mem hkeys hmem]
    rfl
  · rw [lookup_of_not_mem hk]
    exact field?_wire_of_not_mem fun hk' => hk ((obj_keys_sublist fields).subset hk')

/-! ### Decoding inverts encoding -/

theorem text_str {s : String} (h : s ≠ "") (at_ : String) : text (.str s) at_ = .ok s := by
  simp [text, h, pure, Except.pure]

theorem textField?_of {json : Json} {key : String} {s : Option String}
    (h : field? json key = s.map fun s => (Wire.str s).toJson) (hs : ∀ x ∈ s, x ≠ "") (at_ : String) :
    textField? json key at_ = .ok s := by
  cases s with
  | none => simp [textField?, h, pure, Except.pure]
  | some s => simp [textField?, h, toJson_str, text_str (hs s rfl), Option.mapM, Functor.map, Except.map]

theorem nat?_nat (n : Nat) : nat? (Wire.nat n).toJson = some n := by
  cases n with
  | zero => rfl
  | succ n =>
    show (if n + 1 = 0 then some 0 else nat?.strip (n + 1) 0) = some (n + 1)
    simp [nat?.strip]

theorem natField?_of {json : Json} {key : String} {n : Option Nat}
    (h : field? json key = n.map fun n => (Wire.nat n).toJson) (hn : ∀ x ∈ n, x ≤ maxNat) (at_ : String) :
    natField? json key at_ = .ok n := by
  cases n with
  | none => simp [natField?, h, pure, Except.pure]
  | some n => simp [natField?, h, nat?_nat, hn n rfl, Option.mapM, pure, Except.pure, Functor.map, Except.map]

/-- Decoding each item of a list gives the list back if it gives each item back. --/
theorem mapM_ok {α : Type} {g : α → Except String α} :
    ∀ {xs : List α}, (∀ x ∈ xs, g x = .ok x) → xs.mapM g = .ok xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x List.mem_cons_self, mapM_ok fun y hy => h y (List.mem_cons_of_mem x hy)]
    rfl

theorem valueType_valueTypeWire (at_ : String) :
    ∀ t : ValueType, t.name ≠ "" → valueType (valueTypeWire t).toJson at_ = .ok t
  | .named name, h => by
    simp only [ValueType.name] at h
    simp only [valueTypeWire, Wire.toJson]
    rw [valueType.eq_1]
    simp [h, pure, Except.pure]
  | .list e, h => by
    have ih := valueType_valueTypeWire at_ e h
    have hstrict := strict_wire at_ (fields := [("list", valueTypeWire e)]) (allowed := ["list"]) (by simp)
    have hget := field?_wire_of_mem (fields := [("list", valueTypeWire e)]) (by simp) (List.mem_singleton_self _)
    rw [valueTypeWire, toJson_obj, Json.mkObj] at *
    rw [field?_json_obj] at hget
    rw [valueType.eq_2, hstrict]
    simp only [bind, Except.bind]
    split
    · rename_i element heq
      rw [hget] at heq
      cases heq
      rw [ih]
      rfl
    · rename_i heq
      rw [hget] at heq
      cases heq

theorem policy_policyWire (p : Policy) (at_ : String) : policy (policyWire p).toJson at_ = .ok p := by
  cases p <;> rfl

theorem collect_collectWire (c : Collect) (at_ : String) : collect (collectWire c).toJson at_ = .ok c := by
  cases c <;> rfl

theorem contract_contractWire {c : Contract} (h : c.element.name ≠ "") (at_ : String) :
    contract (contractWire c).toJson at_ = .ok c := by
  cases c with
  | single t =>
    simp only [Contract.element] at h
    simp [contract, contractWire, strict_wire, field?_wire, List.lookup, valueType_valueTypeWire _ t h, bind,
      Except.bind, pure, Except.pure]
  | stream t =>
    simp only [Contract.element] at h
    simp [contract, contractWire, strict_wire, field?_wire, List.lookup, valueType_valueTypeWire _ t h, bind,
      Except.bind, pure, Except.pure]

/-- The timeout of the object `json`, whose field `timeout` is the canonical form of `t`. --/
theorem timeout_of {json : Json} {t : Timeout} (h : field? json "timeout" = (timeoutWire t).map Wire.toJson)
    (ht : t.Expressible) (at_ : String) : timeout json at_ = .ok t := by
  unfold timeoutWire at h
  split at h
  · rename_i he
    obtain rfl : t = {} := by
      rcases t with ⟨_ | _, _ | _⟩ <;> simp_all [Timeout.isEmpty]
    simp [timeout, h, pure, Except.pure]
  · simp only [Timeout.Expressible, List.mem_append, Option.mem_toList] at ht
    have hcall := natField?_of (json := (obj [("callMs", t.callMs.map .nat), ("elementMs", t.elementMs.map .nat)]).toJson)
      (key := "callMs") (n := t.callMs) (by simp [field?_obj, List.lookup, Option.map_map, Function.comp_def])
      (fun x hx => ht x (.inl hx)) s!"{at_}.timeout"
    have helement := natField?_of (json := (obj [("callMs", t.callMs.map .nat), ("elementMs", t.elementMs.map .nat)]).toJson)
      (key := "elementMs") (n := t.elementMs) (by simp [field?_obj, List.lookup, Option.map_map, Function.comp_def])
      (fun x hx => ht x (.inr hx)) s!"{at_}.timeout"
    simp [timeout, h, strict_obj, hcall, helement, bind, Except.bind, pure, Except.pure]

theorem body_bodyWire {b : Body} (h : b.Expressible) (at_ : String) : body (bodyWire b).toJson at_ = .ok b := by
  cases b with
  | function id =>
    simp only [Body.Expressible] at h
    simp [body, bodyWire, textField, field, field?_wire, List.lookup, toJson_str, strict_wire, text_str, h,
      bind, Except.bind, pure, Except.pure]
  | workflow id output =>
    simp only [Body.Expressible] at h
    simp [body, bodyWire, textField, field, field?_wire, List.lookup, toJson_str, strict_wire, text_str, h,
      bind, Except.bind, pure, Except.pure]

/-- The name that `transformRefWire` writes. --/
def refName : TransformRef → String
  | .declared id => id
  | .discard => TransformRef.discardName

theorem transformRefWire_eq (r : TransformRef) : transformRefWire r = .str (refName r) := by
  cases r <;> rfl

theorem refName_ne {r : TransformRef} (h : r.Expressible) : refName r ≠ "" := by
  cases r with
  | discard => simp [refName, TransformRef.discardName]
  | declared id => exact h.1

theorem transformRef_refName {r : TransformRef} (h : r.Expressible) : transformRef (refName r) = r := by
  cases r with
  | discard => rfl
  | declared id => simp [transformRef, refName, h.2]

theorem task_taskWire {t : TaskSpec} (h : t.Expressible) (at_ : String) : task (taskWire t).toJson at_ = .ok t := by
  have hjson : (taskWire t).toJson = (obj [("name", some (.str t.name)), ("body", some (bodyWire t.body)),
      ("inputTransform", t.input.map transformRefWire), ("outputTransform", t.output.map .str),
      ("policy", some (policyWire t.policy)), ("timeout", timeoutWire t.timeout)]).toJson := rfl
  have hin : ∀ at_, textField? (taskWire t).toJson "inputTransform" at_ = .ok (t.input.map refName) :=
    textField?_of (by simp [hjson, field?_obj, List.lookup, Option.map_map, Function.comp_def, transformRefWire_eq])
      (by simpa using fun r hr => refName_ne (h.input r hr))
  have hout : ∀ at_, textField? (taskWire t).toJson "outputTransform" at_ = .ok t.output :=
    textField?_of (by simp [hjson, field?_obj, List.lookup, Option.map_map, Function.comp_def]) h.output
  have htimeout : ∀ at_, timeout (taskWire t).toJson at_ = .ok t.timeout :=
    timeout_of (by simp [hjson, field?_obj, List.lookup]) h.timeout
  have hinput : (t.input.map refName).map transformRef = t.input := by
    cases hti : t.input with
    | none => rfl
    | some r => simp [transformRef_refName (h.input r (by simp [hti]))]
  rw [hjson] at hin hout htimeout
  simp [task, hjson, strict_obj, textField, field, field?_obj, List.lookup, toJson_str, text_str, h.name,
    body_bodyWire h.body, policy_policyWire, hin, hout, htimeout, hinput, bind, Except.bind, pure, Except.pure]

theorem control_controlWire {c : Control} (h : c.Expressible) (at_ : String) :
    control (controlWire c).toJson at_ = .ok c := by
  cases c with
  | call b =>
    have hb := body_bodyWire (b := b) h
    simp only [Control.Expressible] at h
    cases b with
    | function id =>
      simp only [Body.Expressible] at h
      simp only [bodyWire] at hb
      simp [control, controlWire, bodyWire, textField, field, field?_wire, List.lookup, toJson_str, text_str,
        hb, bind, Except.bind, pure, Except.pure]
    | workflow id output =>
      simp only [Body.Expressible] at h
      simp only [bodyWire] at hb
      simp [control, controlWire, bodyWire, textField, field, field?_wire, List.lookup, toJson_str, text_str,
        hb, bind, Except.bind, pure, Except.pure]
  | branch judge arms =>
    simp only [Control.Expressible] at h
    have harms : ∀ at_, arms.mapM ((text · at_) ∘ Wire.toJson ∘ Wire.str) = .ok arms :=
      fun at_ => mapM_ok fun a ha => text_str (h.2 a ha) at_
    simp [control, controlWire, textField, field, field?_wire, List.lookup, toJson_str, toJson_arr, text_str, h.1,
      list, harms, strict_wire, bind, Except.bind, pure, Except.pure]
  | waitStream e =>
    simp only [Control.Expressible] at h
    simp [control, controlWire, textField, field, field?_wire, List.lookup, toJson_str, text_str,
      valueType_valueTypeWire _ e h, strict_wire, bind, Except.bind, pure, Except.pure]
  | merge e =>
    simp only [Control.Expressible] at h
    simp [control, controlWire, textField, field, field?_wire, List.lookup, toJson_str, text_str,
      valueType_valueTypeWire _ e h, strict_wire, bind, Except.bind, pure, Except.pure]
  | concurrency c =>
    simp only [Control.Expressible] at h
    obtain ⟨hinput, hlimit, htasks, helement⟩ := h
    have hjson : (controlWire (.concurrency c)).toJson = (obj [("type", some (.str "concurrency")),
        ("input", c.input.map valueTypeWire), ("limit", some (.nat c.limit)),
        ("tasks", some (.arr (c.tasks.map taskWire))), ("output", some (collectWire c.output)),
        ("element", some (valueTypeWire c.element))]).toJson := rfl
    have hlim : ∀ at_, natField? (controlWire (.concurrency c)).toJson "limit" at_ = .ok (some c.limit) :=
      natField?_of (by simp [hjson, field?_obj, List.lookup]) (by simpa using hlimit)
    have hin : ∀ at_, (c.input.map (Wire.toJson ∘ valueTypeWire)).mapM (valueType · at_) = .ok c.input := by
      intro at_
      cases hci : c.input with
      | none => rfl
      | some t => simp [Option.mapM, valueType_valueTypeWire _ t (hinput t hci), Functor.map, Except.map]
    have htasks' : ∀ at_, c.tasks.mapM ((task · at_) ∘ Wire.toJson ∘ taskWire) = .ok c.tasks :=
      fun at_ => mapM_ok fun t ht => task_taskWire (htasks t ht) at_
    rw [hjson] at hlim
    simp [control, hjson, textField, field, field?_obj, List.lookup, toJson_str, toJson_arr, text_str, list,
      strict_obj, hlim, hin, htasks', collect_collectWire, valueType_valueTypeWire _ _ helement, bind,
      Except.bind, pure, Except.pure]

theorem placement_placementWire {pl : Placement} (h : pl.Expressible) (at_ : String) :
    placement (placementWire pl).toJson at_ = .ok pl := by
  have hjson : (placementWire pl).toJson = (obj [("name", some (.str pl.name)),
      ("node", some (controlWire pl.control)), ("policy", some (policyWire pl.policy)),
      ("timeout", timeoutWire pl.timeout)]).toJson := rfl
  have htimeout : ∀ at_, timeout (placementWire pl).toJson at_ = .ok pl.timeout :=
    timeout_of (by simp [hjson, field?_obj, List.lookup]) h.timeout
  rw [hjson] at htimeout
  simp [placement, hjson, strict_obj, textField, field, field?_obj, List.lookup, toJson_str, text_str, h.name,
    control_controlWire h.control, policy_policyWire, htimeout, bind, Except.bind, pure, Except.pure]

theorem connection_connectionWire {c : Connection} (h : c.Expressible) (at_ : String) :
    connection (connectionWire c).toJson at_ = .ok c := by
  have hjson : (connectionWire c).toJson = (obj [("source", some (.str c.source)), ("arm", c.arm.map .str),
      ("target", some (.str c.target)), ("transform", some (transformRefWire c.transform))]).toJson := rfl
  have harm : ∀ at_, textField? (connectionWire c).toJson "arm" at_ = .ok c.arm :=
    textField?_of (by simp [hjson, field?_obj, List.lookup, Option.map_map, Function.comp_def]) h.arm
  rw [hjson] at harm
  simp only [transformRefWire_eq] at harm
  simp [connection, hjson, strict_obj, textField, field, field?_obj, List.lookup, toJson_str, text_str, h.source,
    h.target, harm, transformRefWire_eq, refName_ne h.transform, transformRef_refName h.transform, bind, Except.bind,
    pure, Except.pure]

theorem workflow_workflowWire {w : Workflow} (h : w.Expressible) (at_ : String) :
    workflow (workflowWire w).toJson at_ = .ok w := by
  have hjson : (workflowWire w).toJson = (obj [("id", some (.str w.id)), ("input", w.input.map entryWire),
      ("placements", some (.arr (w.placements.map placementWire))),
      ("connections", some (.arr (w.connections.map connectionWire)))]).toJson := rfl
  have hpl : ∀ at_, w.placements.mapM ((placement · at_) ∘ Wire.toJson ∘ placementWire) = .ok w.placements :=
    fun at_ => mapM_ok fun pl hpl => placement_placementWire (h.placements pl hpl) at_
  have hc : ∀ at_, w.connections.mapM ((connection · at_) ∘ Wire.toJson ∘ connectionWire) = .ok w.connections :=
    fun at_ => mapM_ok fun c hc => connection_connectionWire (h.connections c hc) at_
  rcases w with ⟨id, _ | e, placements, connections⟩
  · simp [workflow, hjson, strict_obj, textField, field, field?_obj, List.lookup, toJson_str, toJson_arr, text_str,
      h.id, list, hpl, hc, bind, Except.bind, pure, Except.pure]
  · obtain ⟨htype, hplace⟩ := h.input e rfl
    simp [workflow, hjson, entryWire, strict_obj, strict_wire, textField, field, field?_obj, field?_wire,
      List.lookup, toJson_str, toJson_arr, text_str, h.id, hplace, list, hpl, hc, valueType_valueTypeWire _ _ htype,
      Option.mapM, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem functionDecl_functionWire {f : FunctionDecl}
    (h : f.id ≠ "" ∧ (∀ t ∈ f.input, t.name ≠ "") ∧ f.output.element.name ≠ "") (at_ : String) :
    functionDecl (functionWire f).toJson at_ = .ok f := by
  have hjson : (functionWire f).toJson = (obj [("id", some (.str f.id)), ("input", f.input.map valueTypeWire),
      ("output", some (contractWire f.output))]).toJson := rfl
  have hinput : ∀ at_, (f.input.map (Wire.toJson ∘ valueTypeWire)).mapM (valueType · at_) = .ok f.input := by
    intro at_
    cases hfi : f.input with
    | none => rfl
    | some t => simp [Option.mapM, valueType_valueTypeWire _ t (h.2.1 t hfi), Functor.map, Except.map]
  simp [functionDecl, hjson, strict_obj, textField, field, field?_obj, List.lookup, toJson_str, text_str, h.1,
    hinput, contract_contractWire h.2.2, bind, Except.bind, pure, Except.pure]

theorem judgeDecl_judgeWire {j : JudgeDecl} (h : j.id ≠ "" ∧ j.input.name ≠ "") (at_ : String) :
    judgeDecl (judgeWire j).toJson at_ = .ok j := by
  simp [judgeDecl, judgeWire, strict_wire, textField, field, field?_wire, List.lookup, toJson_str, text_str, h.1,
    valueType_valueTypeWire _ _ h.2, bind, Except.bind, pure, Except.pure]

theorem transformDecl_transformWire {t : TransformDecl} (h : t.id ≠ "" ∧ t.input.name ≠ "" ∧ t.output.name ≠ "")
    (at_ : String) : transformDecl (transformWire t).toJson at_ = .ok t := by
  simp [transformDecl, transformWire, strict_wire, textField, field, field?_wire, List.lookup, toJson_str, text_str,
    h.1, valueType_valueTypeWire _ _ h.2.1, valueType_valueTypeWire _ _ h.2.2, bind, Except.bind, pure, Except.pure]

/-- The canonical form of a definition the definition file can express decodes back to it. --/
theorem definition_definitionWire_of_expressible {p : Definition} (h : p.Expressible) :
    definition (definitionWire p).toJson = .ok p := by
  have hf : ∀ at_, p.functions.mapM ((functionDecl · at_) ∘ Wire.toJson ∘ functionWire) = .ok p.functions :=
    fun at_ => mapM_ok fun f hf => functionDecl_functionWire (h.functions f hf) at_
  have hj : ∀ at_, p.judges.mapM ((judgeDecl · at_) ∘ Wire.toJson ∘ judgeWire) = .ok p.judges :=
    fun at_ => mapM_ok fun j hj => judgeDecl_judgeWire (h.judges j hj) at_
  have ht : ∀ at_, p.transforms.mapM ((transformDecl · at_) ∘ Wire.toJson ∘ transformWire) = .ok p.transforms :=
    fun at_ => mapM_ok fun t ht => transformDecl_transformWire (h.transforms t ht) at_
  have hw : ∀ at_, p.workflows.mapM ((workflow · at_) ∘ Wire.toJson ∘ workflowWire) = .ok p.workflows :=
    fun at_ => mapM_ok fun w hw => workflow_workflowWire (h.workflows w hw) at_
  simp [definition, definitionWire, strict_wire, textField, field, field?_wire, List.lookup, toJson_str, toJson_arr,
    text_str, h.main, list, hf, hj, ht, hw, bind, Except.bind, pure, Except.pure]

/-- The canonical form of a normal definition decodes back to it. --/
theorem definition_definitionWire {p : Definition} (h : p.Normal) : definition (definitionWire p).toJson = .ok p :=
  definition_definitionWire_of_expressible h.expressible

/-- The canonical form determines a definition the definition file can express, since both
    definitions decode from it. --/
theorem definitionWire_inj_of_expressible {p q : Definition} (hp : p.Expressible) (hq : q.Expressible) :
    definitionWire p = definitionWire q ↔ p = q := by
  refine ⟨fun h => ?_, congrArg _⟩
  have hdecode := definition_definitionWire_of_expressible hp
  rw [h, definition_definitionWire_of_expressible hq] at hdecode
  exact (Except.ok.inj hdecode).symm

end Suimon.Codec
