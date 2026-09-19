import Suimon.Trace.JsonEquality

namespace Suimon.Trace
open Lean

/-- The lexical layer recognizes punctuation; this stack checks that it forms
    exactly one JSON value, including object field/value alternation. --/
inductive JsonContext where
  | value | array | object
  deriving BEq, DecidableEq

def beginValue (stack : List JsonContext) : JsonAtom → Option (List JsonContext)
  | .null | .boolean _ | .number .. | .string _ => some stack
  | .arrayStart => some (.array :: stack)
  | .objectStart => some (.object :: stack)
  | _ => none

def advanceJson : List JsonContext → JsonAtom → Option (List JsonContext)
  | .value :: stack, atom => beginValue stack atom
  | .array :: stack, .arrayEnd => some stack
  | .array :: stack, atom => beginValue (.array :: stack) atom
  | .object :: stack, .objectEnd => some stack
  | .object :: stack, .field _ => some (.value :: .object :: stack)
  | _, _ => none

def validJsonAtoms (atoms : List JsonAtom) : Bool :=
  atoms.foldlM advanceJson [.value] == some []

end Suimon.Trace
