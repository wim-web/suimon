import Suimon.Step
import Suimon.Trace.Projection
import Suimon.Trace.JsonEquality
namespace Suimon.Trace
open Lean

/-- A transaction contains commands, exact public projections, then a commit marker. --/
structure Event where
  schema_version : Nat := 2
  sequence : Nat
  txn : String
  recorded_at : Time
  type : String
  op : Option Op := none
  data : Json := Json.mkObj []
  deriving BEq, ToJson, FromJson

/-- Reject missing/extra keys instead of silently normalizing an external event. --/
def parseEventJson (json : Json) : Except String Event := do
  let event : Event ← fromJson? json
  unless event.schema_version == 2 do throw "unsupported event schema_version (expected 2)"
  unless sameJson (toJson event) json do throw "event fields do not match the canonical schema"
  return event

def parseEvent (line : String) : Except String Event := do
  parseEventJson (← Json.parse line)

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

/-- All public facts are mandatory; internal fields are reconstructed by replay.
    Within each category, sort by logical ID rather than State storage order. --/
def effects (before after : State) (op : Op) : List Fact := Id.run do
  let mut facts := []
  for i in after.instances.mergeSort (fun a b => a.id ≤ b.id) do
    if !(before.instance? i.id).isSome then
      facts := facts ++ [{ type := "instance.created", data := Projection.instanceCreated i }]
  for a in after.attempts.mergeSort (fun a b => a.id ≤ b.id) do
    match before.attempts.find? (·.id == a.id) with
    | none =>
      let lease := (after.instance? a.instance).bind (·.lease)
      facts := facts ++ [{ type := "attempt.started", data := Json.mkObj [
        ("attempt", Projection.attempt a), ("lease_until", toJson (lease.map (·.until_)))] }]
    | some b =>
      if a.status != b.status then
        facts := facts ++ [{ type := "attempt.finished", data := Projection.attempt a }]
  for i in after.instances.mergeSort (fun a b => a.id ≤ b.id) do
    if let some b := before.instance? i.id then
      if i.lease.map Projection.lease != b.lease.map Projection.lease && i.lease.isSome && b.lease.isSome then
        facts := facts ++ [{ type := "lease.renewed", data := Json.mkObj [
          ("instance", toJson i.id), ("lease", (i.lease.map Projection.lease).getD .null)] }]
  for c in after.channels.mergeSort (fun a b => a.id ≤ b.id) do
    let oldLength := ((before.channels.find? (·.id == c.id)).map (·.placed.length)).getD 0
    for t in c.placed.drop oldLength do
      facts := facts ++ [{ type := "token.placed", data := Json.mkObj [
        ("edge", toJson c.id), ("token", Projection.token t), ("by_instance", toJson (opActor op))] }]
  for c in (after.consumed.drop before.consumed.length).mergeSort
      (fun a b => a.channel < b.channel || (a.channel == b.channel && a.index ≤ b.index)) do
    facts := facts ++ [{ type := "token.consumed", data := Projection.consumption c }]
  if before.status != after.status then
    facts := facts ++ [{ type := "execution.state_changed", data := Json.mkObj [
      ("status", toJson (Projection.execStatus after.status)), ("reason", toJson after.reason)] }]
  return facts

def recordFacts : List Fact → Nat → String → Nat → List Event
  | [], _, _, _ => []
  | f :: rest, sequence, txn, time =>
    { sequence, txn, recorded_at := time, type := f.type, data := f.data } ::
      recordFacts rest (sequence + 1) txn time

def recordOp (before after : State) (op : Op) (sequence : Nat) (txn : String) (time : Nat) : List Event :=
  { sequence, txn, recorded_at := time, type := commandType op, op := some op } ::
    recordFacts (effects before after op) (sequence + 1) txn time

def commitEvent (sequence : Nat) (txn : String) (time : Nat) : Event :=
  { sequence, txn, recorded_at := time, type := "transaction.committed" }

/-- A timed command must keep its own timestamp; increasing recorded_at alone
    would produce a command which the checker rejects. --/
def recordTime (time : Nat) (op : Op) : Result Nat := do
  let next := (opTime op).getD time
  require (time ≤ next) "CLOCK_REGRESSION"
  return next

def recordCommands (s : State) (ops : List Op) (sequence : Nat) (txn : String)
    (time : Nat) : Result (State × List Event × Nat) := do
  match ops with
  | [] => return (s, [], time)
  | op :: rest =>
    let clock ← recordTime time op
    let next ← step s op
    let events := recordOp s next op sequence txn clock
    let (last, tail, lastTime) ← recordCommands next rest (sequence + events.length) txn clock
    return (last, events ++ tail, lastTime)

def recordTransaction (s : State) (ops : List Op) (sequence : Nat) (txn : String)
    (time : Nat) : Result (State × List Event) := do
  require (!ops.isEmpty) "EMPTY_TRANSACTION"
  require (!txn.isEmpty) "EMPTY_TRANSACTION_ID"
  let (state, events, clock) ← recordCommands s ops sequence txn time
  return (state, events ++ [commitEvent (sequence + events.length) txn clock])
end Suimon.Trace
