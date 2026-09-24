namespace Suimon

/-- The JSON values an execution record is made of. Fields keep their order, so a record has
    exactly one rendering; payloads are strings the runtime serialized. --/
inductive Wire where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | arr (items : List Wire)
  | obj (fields : List (String × Wire))
  deriving Repr, Inhabited

/-- No object in the value repeats a key, at any depth. The text form rejects a repeated key; a
    value without one reads back from its rendering (`Wire.parse_render`). --/
inductive Wire.DistinctKeys : Wire → Prop where
  | null : Wire.DistinctKeys .null
  | bool (b : Bool) : Wire.DistinctKeys (.bool b)
  | nat (n : Nat) : Wire.DistinctKeys (.nat n)
  | str (s : String) : Wire.DistinctKeys (.str s)
  | arr {items : List Wire} (items_distinct : ∀ w ∈ items, Wire.DistinctKeys w) :
      Wire.DistinctKeys (.arr items)
  | obj {fields : List (String × Wire)} (keys_nodup : (fields.map (·.1)).Nodup)
      (fields_distinct : ∀ f ∈ fields, Wire.DistinctKeys f.2) : Wire.DistinctKeys (.obj fields)

end Suimon
