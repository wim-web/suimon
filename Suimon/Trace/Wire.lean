import Suimon.Trace.Check
import Suimon.Trace.OpAtoms
import Suimon.Trace.Text
import Suimon.Trace.AtomGrammar

namespace Suimon.Trace
open Lean

/-- A decoded line retains the lossless structural view of its data. No JSON
    map is rebuilt merely to compare it to the model's public projection. --/
structure WireEvent where
  schema_version : Nat
  sequence : Nat
  txn : String
  recorded_at : Nat
  type : String
  op : Option Op
  data : List JsonAtom

def Event.toWire (e : Event) : WireEvent :=
  ⟨e.schema_version, e.sequence, e.txn, e.recorded_at, e.type, e.op, jsonAtoms e.data⟩

def WireEvent.metadata (e : WireEvent) : Event :=
  {schema_version := e.schema_version, sequence := e.sequence, txn := e.txn,
    recorded_at := e.recorded_at, type := e.type, op := e.op}

/-- Object key order is a lexical choice, not part of schema v2. Data is last
    so its validated token sequence can be retained without rebuilding a map. --/
def encodeWireAtoms (e : WireEvent) : List JsonAtom :=
  [.objectStart, .field "schema_version"] ++ natCodec.encode e.schema_version ++
  [.field "sequence"] ++ natCodec.encode e.sequence ++
  [.field "txn"] ++ stringCodec.encode e.txn ++
  [.field "recorded_at"] ++ natCodec.encode e.recorded_at ++
  [.field "type"] ++ stringCodec.encode e.type ++
  [.field "op"] ++ optionalOpCodec.encode e.op ++
  [.field "data"] ++ e.data ++ [.objectEnd]

def decodeWireAtoms (atoms : List JsonAtom) : Option WireEvent := do
  let atoms ← expectAtom .objectStart atoms
  let atoms ← expectAtom (.field "schema_version") atoms
  let (schema_version, atoms) ← natCodec.decode atoms
  let atoms ← expectAtom (.field "sequence") atoms
  let (sequence, atoms) ← natCodec.decode atoms
  let atoms ← expectAtom (.field "txn") atoms
  let (txn, atoms) ← stringCodec.decode atoms
  let atoms ← expectAtom (.field "recorded_at") atoms
  let (recorded_at, atoms) ← natCodec.decode atoms
  let atoms ← expectAtom (.field "type") atoms
  let (type, atoms) ← stringCodec.decode atoms
  let atoms ← expectAtom (.field "op") atoms
  let (op, atoms) ← optionalOpCodec.decode atoms
  let atoms ← expectAtom (.field "data") atoms
  match atoms.reverse with
  | .objectEnd :: back =>
    let data := back.reverse
    if validJsonAtoms data then some ⟨schema_version, sequence, txn, recorded_at, type, op, data⟩ else none
  | _ => none

def encodeEvent (e : Event) : String := Text.encode (encodeWireAtoms e.toWire)

/-- The fast, proved path recognizes exactly the canonical spelling, optionally
    with a line terminator. Re-encoding enforces commas/whitespace, which the
    lexical scanner alone does not validate. Other JSON spellings use parseEvent. --/
def decodeWire (text : String) : Option WireEvent := do
  let atoms ← Text.decode text
  let event ← decodeWireAtoms atoms
  let canonical := Text.encode (encodeWireAtoms event)
  if event.schema_version == 2 &&
      (text == canonical || text == canonical ++ "\n" || text == canonical ++ "\r\n") then
    some event
  else none

def parseWireEvent (text : String) : Except String WireEvent :=
  match decodeWire text with
  | some e => .ok e
  | none => (parseEvent text).map Event.toWire

def checkWireEvent (c : Cursor) (e : WireEvent) : Except Diagnostic Cursor := do
  checkPayloadWith (← checkMetadata c e.metadata) e.metadata (fun expected => e.data == jsonAtoms expected)

/-- This is the pure one-line core used by the CLI. --/
def checkLine (c : Cursor) (text : String) : Except String (Except Diagnostic Cursor) :=
  (parseWireEvent text).map (checkWireEvent c)

/-- Parse and check one physical, complete line. This function is shared by
    the CLI and the pure log APIs, including their malformed-input diagnostics. --/
def checkTextLine (c : Cursor) (text : String) : Except Diagnostic Cursor :=
  match parseWireEvent text with
  | .error reason => .error {
      sequence := c.sequence, txn := c.txn.getD "", op := c.currentOp,
      reason := {code := "INVALID_JSON", message := s!"line {c.sequence}: {reason}"},
      boundary := summary c.boundary }
  | .ok event => checkWireEvent c event

def checkText (g : Graph) (lines : List String) : Except Diagnostic State := do
  let initial := State.initial g
  let c ← lines.foldlM checkTextLine {state := initial, boundary := initial}
  finish c

/-- The storage layer supplies complete lines. An incomplete final physical
    line is not a record; malformed complete lines are rejected. --/
def recoverText (g : Graph) (lines : List String) : Except Diagnostic State := do
  let initial := State.initial g
  let c ← lines.foldlM checkTextLine {state := initial, boundary := initial}
  return c.boundary

end Suimon.Trace
