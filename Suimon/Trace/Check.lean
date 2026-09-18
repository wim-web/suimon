import Suimon.Trace.Event
namespace Suimon.Trace
open Lean

structure Diagnostic where
  sequence : Nat
  txn : String
  op : Option Op
  reason : Reject
  boundary : Json
  deriving ToJson

def summary (s : State) : Json := Json.mkObj [
  ("status", toJson s.status), ("now", toJson s.now), ("instances", toJson s.instances), ("attempts", toJson s.attempts), ("channels", toJson s.channels), ("reason", toJson s.reason)]

def diagnose (e : Event) (op : Option Op) (boundary : State) (code message : String) : Diagnostic :=
  { sequence := e.sequence, txn := e.txn, op, reason := { code, message }, boundary := summary boundary }

def replayOps (s : State) (ops : List Op) : Result State := ops.foldlM step s

/-- Rejecting any operation returns no intermediate state. --/
def transaction (s : State) (ops : List Op) : Result State := replayOps s ops

structure Cursor where
  state : State
  boundary : State
  sequence : Nat := 1
  time : Nat := 0
  txn : Option String := none
  completed : List String := []
  expected : List Fact := []
  currentOp : Option Op := none
  commands : Nat := 0

/-- Reads one event at a time, retaining model state and committed transaction IDs. --/
def checkEvent (c : Cursor) (e : Event) : Except Diagnostic Cursor := do
  let err := fun code msg => diagnose e (e.op.or c.currentOp) c.boundary code msg
  unless e.sequence == c.sequence do throw (err "SEQUENCE" "sequence must be contiguous and start at 1")
  unless !e.txn.isEmpty && e.recorded_at ≥ c.time do throw (err "METADATA" "empty transaction or non-monotone clock")
  let c ← match c.txn with
    | none => do
      unless !c.completed.contains e.txn do throw (err "TXN_REUSE" "transaction id was already committed")
      pure { c with txn := some e.txn }
    | some t => do
      unless t == e.txn do throw (err "UNCOMMITTED_TXN" "previous transaction has no commit marker")
      pure c
  let c := { c with sequence := c.sequence + 1, time := e.recorded_at }
  match c.expected with
  | f :: rest =>
    unless e.op.isNone && e.type == f.type && e.data == f.data do
      throw (err "EFFECT_MISMATCH" s!"expected {f.type}: {f.data.compress}")
    return { c with expected := rest }
  | [] =>
    if e.type == "transaction.committed" then
      unless e.op.isNone && e.data == Json.mkObj [] && c.commands > 0 do
        throw (err "INVALID_COMMIT" "commit must follow at least one complete operation")
      unless invariants c.state do throw (err "INVARIANT" "invalid transaction boundary")
      return { c with boundary := c.state, txn := none, completed := c.completed ++ [e.txn], currentOp := none, commands := 0 }
    let op ← e.op.toExcept (err "MISSING_OPERATION" "expected a command with op")
    unless e.type == commandType op && e.data == Json.mkObj [] do
      throw (err "COMMAND_MISMATCH" "event type does not match operation")
    unless (opTime op).all (· == e.recorded_at) do throw (err "CLOCK_MISMATCH" "operation time differs from recorded_at")
    match step c.state op with
    | .error r => throw { (err r.code r.message) with reason := r }
    | .ok next =>
      return { c with state := next, expected := effects c.state next op, currentOp := some op, commands := c.commands + 1 }

def finish (c : Cursor) : Except Diagnostic State :=
  match c.txn with
  | none => .ok c.boundary
  | some txn => .error {
      sequence := c.sequence
      txn
      op := c.currentOp
      reason := { code := "TRUNCATED_TRANSACTION", message := "missing effects or commit marker" }
      boundary := summary c.boundary }

def check (g : Graph) (events : List Event) : Except Diagnostic State := do
  let initial := State.initial g
  let c ← events.foldlM checkEvent { state := initial, boundary := initial }
  finish c

/-- Recovery deliberately retains only the last committed boundary of a torn suffix. --/
def recover (g : Graph) (events : List Event) : Except Diagnostic State := do
  let initial := State.initial g
  let c ← events.foldlM checkEvent { state := initial, boundary := initial }
  return c.boundary
end Suimon.Trace
