import Lean

namespace Suimon.Trace
open Lean

/-- A lossless structural view of JSON. Object fields follow the map's key
    order; numeric mantissa/exponent are preserved rather than rounded. --/
inductive JsonAtom where
  | null
  | boolean (value : Bool)
  | number (mantissa : Int) (exponent : Nat)
  | string (value : String)
  | arrayStart | arrayEnd | objectStart | objectEnd
  | field (name : String)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

mutual
  /-- Total structural traversal of JSON, including arrays and object maps. --/
  def jsonAtoms (j : Json) : List JsonAtom :=
    match j with
    | .null => [.null]
    | .bool b => [.boolean b]
    | .num n => [.number n.mantissa n.exponent]
    | .str s => [.string s]
    | .arr items => .arrayStart :: jsonArrayAtoms items.toList ++ [.arrayEnd]
    | .obj fields => .objectStart :: jsonObjectAtoms fields.inner.inner ++ [.objectEnd]
  termination_by sizeOf j
  decreasing_by
    · cases items; simp; omega
    · cases fields with | mk inner => cases inner; simp; omega

  def jsonArrayAtoms (items : List Json) : List JsonAtom :=
    match items with
    | [] => []
    | item :: rest => jsonAtoms item ++ jsonArrayAtoms rest
  termination_by sizeOf items
  decreasing_by all_goals simp_all <;> omega

  def jsonObjectAtoms (fields : Std.DTreeMap.Internal.Impl String (fun _ => Json)) : List JsonAtom :=
    match fields with
    | .leaf => []
    | .inner _ key value left right => jsonObjectAtoms left ++ (.field key :: jsonAtoms value) ++ jsonObjectAtoms right
  termination_by sizeOf fields
  decreasing_by all_goals simp_all <;> omega
end

def sameJson (a b : Json) : Bool := jsonAtoms a == jsonAtoms b

@[simp] theorem sameJson_self (j : Json) : sameJson j j = true := by simp [sameJson]

theorem sameJson_iff (a b : Json) : sameJson a b = true ↔ jsonAtoms a = jsonAtoms b := by simp [sameJson]

end Suimon.Trace
