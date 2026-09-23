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

end Suimon
