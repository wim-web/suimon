import Suimon.Trace.Event

namespace Suimon.Trace
open Lean

abbrev AtomReader (α : Type) := List JsonAtom → Option (α × List JsonAtom)

structure AtomCodec (α : Type) where
  encode : α → List JsonAtom
  decode : AtomReader α

/-- Prefix round-trip is compositional. Value codecs never start with the
    array terminator and always consume at least one atom. --/
structure LawfulAtomCodec {α : Type} (codec : AtomCodec α) : Prop where
  nonempty : ∀ a, codec.encode a ≠ []
  notEnd : ∀ a, (codec.encode a).head? ≠ some .arrayEnd
  roundtrip : ∀ a tail, codec.decode (codec.encode a ++ tail) = some (a, tail)

def stringCodec : AtomCodec String where
  encode value := [.string value]
  decode
    | .string value :: rest => some (value, rest)
    | _ => none

def natCodec : AtomCodec Nat where
  encode value := [.number (Int.ofNat value) 0]
  decode
    | .number (Int.ofNat value) 0 :: rest => some (value, rest)
    | _ => none

def boolCodec : AtomCodec Bool where
  encode value := [.boolean value]
  decode
    | .boolean value :: rest => some (value, rest)
    | _ => none

def expectAtom (atom : JsonAtom) : List JsonAtom → Option (List JsonAtom)
  | current :: rest => if current == atom then some rest else none
  | [] => none

def readMany (reader : AtomReader α) : Nat → AtomReader (List α)
  | 0, _ => none
  | fuel + 1, atoms =>
    if atoms.head? == some .arrayEnd then some ([], atoms.tail) else do
      let (value, rest) ← reader atoms
      let (values, tail) ← readMany reader fuel rest
      return (value :: values, tail)

def arrayCodec (codec : AtomCodec α) : AtomCodec (List α) where
  encode values := .arrayStart :: values.flatMap codec.encode ++ [.arrayEnd]
  decode atoms := do
    let rest ← expectAtom .arrayStart atoms
    readMany codec.decode rest.length rest

def refCodec : AtomCodec PortRef where
  encode ref := [.objectStart, .field "node"] ++ stringCodec.encode ref.node ++
    [.field "port"] ++ stringCodec.encode ref.port ++ [.objectEnd]
  decode atoms := do
    let atoms ← expectAtom .objectStart atoms
    let atoms ← expectAtom (.field "node") atoms
    let (node, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "port") atoms
    let (port, atoms) ← stringCodec.decode atoms
    let rest ← expectAtom .objectEnd atoms
    return (⟨node, port⟩, rest)

def inputCodec : AtomCodec Input where
  encode input := [.objectStart, .field "entry"] ++ refCodec.encode input.entry ++
    [.field "items"] ++ (arrayCodec stringCodec).encode input.items ++ [.objectEnd]
  decode atoms := do
    let atoms ← expectAtom .objectStart atoms
    let atoms ← expectAtom (.field "entry") atoms
    let (entry, atoms) ← refCodec.decode atoms
    let atoms ← expectAtom (.field "items") atoms
    let (items, atoms) ← (arrayCodec stringCodec).decode atoms
    let rest ← expectAtom .objectEnd atoms
    return (⟨entry, items⟩, rest)

def outputCodec : AtomCodec Output where
  encode output := [.objectStart, .field "port"] ++ stringCodec.encode output.port ++
    [.field "items"] ++ (arrayCodec stringCodec).encode output.items ++ [.objectEnd]
  decode atoms := do
    let atoms ← expectAtom .objectStart atoms
    let atoms ← expectAtom (.field "port") atoms
    let (port, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "items") atoms
    let (items, atoms) ← (arrayCodec stringCodec).decode atoms
    let rest ← expectAtom .objectEnd atoms
    return (⟨port, items⟩, rest)

def credentialsCodec : AtomCodec Credentials where
  encode auth := [.objectStart, .field "instance"] ++ stringCodec.encode auth.instance ++
    [.field "attempt"] ++ stringCodec.encode auth.attempt ++ [.field "token"] ++ stringCodec.encode auth.token ++
    [.field "now"] ++ natCodec.encode auth.now ++ [.objectEnd]
  decode atoms := do
    let atoms ← expectAtom .objectStart atoms
    let atoms ← expectAtom (.field "instance") atoms
    let (instanceId, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "attempt") atoms
    let (attempt, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "token") atoms
    let (token, atoms) ← stringCodec.decode atoms
    let atoms ← expectAtom (.field "now") atoms
    let (now, atoms) ← natCodec.decode atoms
    let rest ← expectAtom .objectEnd atoms
    return (⟨instanceId, attempt, token, now⟩, rest)

end Suimon.Trace
