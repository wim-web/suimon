import Suimon
import Test.Examples
import Test.Schema

namespace Suimon.Test.TraceProjection
open Lean

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def runOps (graph : Graph) (ops : List Op) : IO (State × List Trace.Event) :=
  match Trace.recordTransaction (.initial graph) ops 1 "projection" 0 with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"projection setup: {error.code}")

private def fieldNames : IO Unit := do
  let auth : Credentials := {
    «instance» := instanceId [] "work", attempt := "attempt", token := "lease", now := 0 }
  let renewed := { auth with now := 1 }
  let (_, events) ← runOps minimal [.start (Explore.inputValues minimal), .activate [] "work",
    .claim auth "worker", .renew renewed, .complete renewed [{ port := "out", items := ["result"] }], .idle]
  let schema ← match Json.parse (← IO.FS.readFile "schema/events.schema.json") >>= Schema.compile with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  for event in events do
    ensure ((schema.validate (toJson event)) matches .ok _) "renamed fact violates schema"
  let some consumed := events.find? (fun e => e.type == "token.consumed" && e.op.isNone)
    | throw (IO.userError "missing consumption fact")
  ensure (consumed.data.getObjValD "by_instance" == toJson auth.instance)
    "consumption did not use by_instance"
  let oldConsumption := Json.mkObj (
    (["channel", "index", "item"].map fun key => (key, consumed.data.getObjValD key)) ++
    [("byInstance", consumed.data.getObjValD "by_instance")])
  let some renewal := events.find? (fun e => e.type == "lease.renewed" && e.op.isNone)
    | throw (IO.userError "missing lease renewal fact")
  let lease := renewal.data.getObjValD "lease"
  ensure (lease == Json.mkObj [("attempt", toJson "attempt"), ("token", toJson "lease"),
    ("lease_until", toJson (4 : Nat))]) "renewal did not use lease_until"
  let oldLease := Json.mkObj [("instance", toJson auth.instance), ("lease", Json.mkObj [
    ("attempt", toJson "attempt"), ("token", toJson "lease"), ("until_", toJson (4 : Nat))])]
  for (event, oldData) in [(consumed, oldConsumption), (renewal, oldLease)] do
    let oldEvent := { event with data := oldData }
    ensure ((schema.validate (toJson oldEvent)) matches .error _) "schema accepted legacy fact field"
    ensure ((Trace.check minimal (events.map fun e => if e == event then oldEvent else e)) matches .error _)
      "checker accepted legacy fact field"
  ensure ((Trace.check minimal events) matches .ok _) "canonical field names rejected"

def run : IO Unit := do
  fieldNames
  let ops := [.start (Explore.inputValues minimal), .activate [] "work"]
  let (state, events) ← runOps minimal ops
  let some created := events.find? (fun e => e.type == "instance.created" && e.op.isNone)
    | throw (IO.userError "missing instance projection")
  let expected := Json.mkObj [("id", toJson (instanceId [] "work")),
    ("node", toJson "work"), ("path", toJson ([] : Path)), ("trigger", .null)]
  ensure (created.data == expected) "instance.created public contract changed"
  let (before, _) ← runOps minimal (ops.take 1)
  -- Deliberately vary excluded representation fields: this is a projection test,
  -- not a claim that these synthetic states are reachable by step.
  let changedInstances := state.instances.map fun i => {
    i with
    status := .failed
    attemptCount := 17
    retryAt := some 20
    iteration := 3
    extraAttempts := 4
    extraIterations := 5
    inputs := [] }
  let changed := { state with instances := changedInstances }
  ensure (Trace.effects before state (.activate [] "work") ==
    Trace.effects before changed (.activate [] "work")) "internal Instance fields leaked into facts"
  let (placed, _) ← runOps merging [.start (Explore.inputValues merging)]
  ensure (Trace.effects (.initial merging) placed (.start (Explore.inputValues merging)) ==
    Trace.effects (.initial merging) { placed with channels := placed.channels.reverse }
      (.start (Explore.inputValues merging))) "fact order depends on channel storage order"
  for bad in [created.data.setObjVal! "extraIterations" (toJson (0 : Nat)),
      created.data.setObjVal! "node" (toJson "forged")] do
    let forged := events.map fun e => if e == created then { e with data := bad } else e
    ensure ((Trace.check minimal forged) matches .error _) "invalid public projection accepted"
  let missing := (events.filter (· != created)).zipIdx.map fun (e, idx) => { e with sequence := idx + 1 }
  ensure ((Trace.check minimal missing) matches .error _) "public facts became optional"
  let old := events.map fun e => { e with schema_version := 1 }
  ensure ((Trace.check minimal old) matches .error _) "v1 event accepted as v2"
  for e in old do
    ensure ((Trace.parseEvent (toJson e).compress) matches .error _) "v1 wire event accepted"
  match Trace.check minimal events with
  | .ok replayed => ensure (replayed == state) "projected facts lost internal replay state"
  | .error error => throw (IO.userError (toJson error).compress)
  IO.println "ok: v2 public fact projection, strict checking, internal-field independence"

end Suimon.Test.TraceProjection
