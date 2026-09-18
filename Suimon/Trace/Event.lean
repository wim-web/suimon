import Suimon.Step
namespace Suimon.Trace
open Lean

/-- A transaction contains command records, their exact effect records, then a commit marker. --/
structure Event where
  sequence : Nat
  txn : String
  recorded_at : Time
  type : String
  op : Option Op := none
  data : Json := Json.mkObj []
  deriving BEq, ToJson, FromJson

/-- Reject missing/extra keys instead of silently normalizing an external event. --/
def parseEvent (line : String) : Except String Event := do
  let json ← Json.parse line
  let event : Event ← fromJson? json
  unless toJson event == json do throw "event fields do not match the canonical schema"
  return event

structure Fact where
  type : String
  data : Json
  deriving BEq, ToJson, FromJson

def commandType : Op → String
  | .start _ => "execution.started"
  | .activate .. | .spawn .. => "instance.created"
  | .claim .. => "attempt.started"
  | .renew .. => "lease.renewed"
  | .complete .. | .fail .. | .expireLease .. => "attempt.finished"
  | .fireBranch .. => "branch.taken"
  | .loopIterate .. => "loop.iterated"
  | .fireFilter .. => "filter.judged"
  | .fireWaitAll .. | .fireCoalesce .. | .fireCollect .. | .fireMerge .. | .propagateEos .. | .emit .. => "token.placed"
  | .finishSubworkflow .. => "instance.completed"
  | .skip .. => "instance.skipped"
  | .promoteRetry .. => "retry.promoted"
  | .manualRetry .. => "retry.requested"
  | .idle | .cancel => "execution.state_changed"

def opTime : Op → Option Time
  | .claim c .. | .renew c | .emit c .. | .complete c .. | .fail c .. => some c.now
  | .expireLease _ t | .promoteRetry _ t => some t
  | _ => none

def opActor : Op → String
  | .activate p n | .fireWaitAll p n | .fireBranch p n _ | .fireCollect p n
  | .fireFilter p n .. | .fireCoalesce p n .. | .fireMerge p n .. | .propagateEos p n | .skip p n => instanceId p n
  | .spawn p n i => instanceId p n (some i)
  | .claim c .. | .renew c | .emit c .. | .complete c .. | .fail c .. => c.instance
  | .expireLease i _ | .promoteRetry i _ | .finishSubworkflow i | .loopIterate i _ | .manualRetry i => i
  | _ => "$execution"

/-- Every externally observable mutation must be present, in this canonical order. --/
def effects (before after : State) (op : Op) : List Fact := Id.run do
  let mut facts := []
  for i in after.instances do
    if !(before.instance? i.id).isSome then
      facts := facts ++ [{ type := "instance.created", data := toJson i }]
  for a in after.attempts do
    match before.attempts.find? (·.id == a.id) with
    | none =>
      let lease := (after.instance? a.instance).bind (·.lease)
      facts := facts ++ [{ type := "attempt.started", data := Json.mkObj [
        ("attempt", toJson a), ("lease_until", toJson (lease.map (·.until_)))] }]
    | some b =>
      if a.status != b.status then
        facts := facts ++ [{ type := "attempt.finished", data := toJson a }]
  for i in after.instances do
    if let some b := before.instance? i.id then
      if i.lease != b.lease && i.lease.isSome && b.lease.isSome then
        facts := facts ++ [{ type := "lease.renewed", data := Json.mkObj [
          ("instance", toJson i.id), ("lease", toJson i.lease)] }]
  for c in after.channels do
    let oldLength := ((before.channels.find? (·.id == c.id)).map (·.placed.length)).getD 0
    for t in c.placed.drop oldLength do
      facts := facts ++ [{ type := "token.placed", data := Json.mkObj [
        ("edge", toJson c.id), ("token", toJson t), ("by_instance", toJson (opActor op))] }]
  for c in after.consumed.drop before.consumed.length do
    facts := facts ++ [{ type := "token.consumed", data := toJson c }]
  if before.status != after.status then
    facts := facts ++ [{ type := "execution.state_changed", data := Json.mkObj [
      ("status", toJson after.status), ("reason", toJson after.reason)] }]
  return facts

def recordOp (before after : State) (op : Op) (sequence : Nat) (txn : String) (time : Nat) : List Event :=
  let command : Event := { sequence, txn, recorded_at := time, type := commandType op, op := some op }
  command :: ((effects before after op).zipIdx.map fun (f, idx) => {
    sequence := sequence + idx + 1, txn, recorded_at := time, type := f.type, data := f.data })

def commitEvent (sequence : Nat) (txn : String) (time : Nat) : Event :=
  { sequence, txn, recorded_at := time, type := "transaction.committed" }

def recordTransaction (s : State) (ops : List Op) (sequence : Nat) (txn : String)
    (time : Nat) : Result (State × List Event) := do
  let mut state := s
  let mut events := []
  let mut clock := time
  for op in ops do
    clock := max clock ((opTime op).getD clock)
    let next ← step state op
    events := events ++ recordOp state next op (sequence + events.length) txn clock
    state := next
  return (state, events ++ [commitEvent (sequence + events.length) txn clock])
end Suimon.Trace
