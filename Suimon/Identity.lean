import Suimon.WireText

namespace Suimon

/-- One part: its length in code points, `:`, then its characters. --/
def encodePart (part : String) : List Char :=
  WireText.natDigits part.length [] ++ ':' :: part.toList

/-- A structured identity. Each part carries its length, so nesting an identity adds a constant per
    level instead of escaping it again, and other languages reproduce it easily; `decodeIdentity`
    inverts it. --/
def identity (parts : List String) : String :=
  String.ofList (parts.flatMap encodePart)

/-- The fuel bounds the parts by the remaining characters, since each part uses at least one. --/
def decodeParts : Nat → List Char → Option (List String)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, c :: cs =>
    match WireText.spanDigits (c :: cs) 0 with
    | (n, ':' :: body) =>
      if n ≤ body.length then (decodeParts fuel (body.drop n)).map (String.ofList (body.take n) :: ·)
      else none
    | _ => none

def decodeIdentity (id : String) : Option (List String) := decodeParts id.toList.length id.toList

end Suimon
