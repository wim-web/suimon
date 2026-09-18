import Suimon
import Test.Examples

namespace Suimon.Test.Work
open Lean

-- Adding an Op requires consciously updating this independent generator as well.
run_meta do
  let some (.inductInfo info) := (← getEnv).find? ``Op | throwError "Op declaration not found"
  let covered := [``Op.start, ``Op.activate, ``Op.spawn, ``Op.claim, ``Op.renew,
    ``Op.expireLease, ``Op.promoteRetry, ``Op.emit, ``Op.complete, ``Op.fail,
    ``Op.fireWaitAll, ``Op.fireBranch, ``Op.fireCoalesce, ``Op.fireCollect,
    ``Op.fireFilter, ``Op.fireMerge, ``Op.propagateEos, ``Op.finishSubworkflow,
    ``Op.loopIterate, ``Op.skip, ``Op.idle, ``Op.cancel, ``Op.manualRetry]
  unless info.ctors == covered do throwError "Update Test.Work.probes for the changed Op constructors"

/-- Independent of Explore.candidates: try operations by their arguments, not by
    the scheduler's node/status dispatch. Most malformed combinations reject. --/
def probes (s : State) (seed : Nat) : List Op := Id.run do
  let mut result := [.idle, .cancel]
  if let some root := s.frame? [] then
    let inputs := root.graph.entries.map fun entry =>
      let count := if (root.graph.input? entry).any (·.kind == .stream) then seed % 3 else 1
      { entry, items := (List.range count).map (fun idx => identity ["input", toString seed, entry.node, entry.port, toString idx]) : Input }
    result := result ++ [.start inputs]
  for frame in s.frames do
    for node in frame.graph.nodes do
      let path := frame.path
      let name := node.id
      result := result ++ [.activate path name, .fireWaitAll path name, .fireCollect path name,
        .propagateEos path name, .skip path name]
      for port in node.outputs do result := result ++ [.fireBranch path name port.name]
      for channel in s.incoming path name do
        if let some (.item item) := channel.pending.head? then
          result := result ++ [.spawn path name item, .fireCoalesce path name channel.id item,
            .fireMerge path name channel.id item, .fireFilter path name item true, .fireFilter path name item false]
  for inst in s.instances do
    let unique := identity ["independent", toString seed, toString s.attempts.length, inst.id]
    let fresh : Credentials := { «instance» := inst.id, attempt := unique, token := unique ++ "-token", now := s.now + seed % 5 }
    result := result ++ [.claim fresh "independent-worker", .manualRetry inst.id,
      .finishSubworkflow inst.id, .loopIterate inst.id true, .loopIterate inst.id false,
      .promoteRetry inst.id (max s.now (inst.retryAt.getD s.now) + seed % 5),
      .expireLease inst.id (max s.now ((inst.lease.map (·.until_)).getD s.now))]
    let credentials := match inst.lease with
      | some lease => { fresh with attempt := lease.attempt, token := lease.token, now := s.now }
      | none => fresh
    for now in [s.now, s.now + seed % 7] do
      let credentials := { credentials with now }
      result := result ++ [.renew credentials, .fail credentials "FUZZ" true, .fail credentials "FUZZ" false]
      if let some node := s.node? inst.path inst.node then
        let outputs := (node.outputs.filter (·.kind == .plain)).map fun port =>
          { port := port.name, items := [identity ["output", toString seed, port.name]] : Output }
        result := result ++ [.complete credentials outputs]
        for port in node.outputs do
          result := result ++ [.emit credentials port.name (identity ["yield", toString seed, port.name])]
  for receipt in s.receipts do
    result := result ++ [.complete {
      «instance» := receipt.instance
      attempt := receipt.attempt
      token := receipt.token
      now := s.now } receipt.outputs]
  return result

private def checkOperations (s : State) (ops : List Op) (hasWork : Bool) : Except String (List (Op × State)) := do
  let mut progressing := []
  for op in ops do
    match step s op with
    | .error e => if e.code == "INVARIANT" then throw s!"INVARIANT: {(toJson op).compress}"
    | .ok next =>
      if next != s then
        if op.countsAsWork && !hasWork then throw s!"hasWork missed {(toJson op).compress}"
        progressing := (op, next) :: progressing
  return progressing.reverse

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def sensitivity : IO Unit := do
  let startOp := Op.start [{ entry := ref "work" "in", items := ["input"] }]
  let .ok ready := Trace.replayOps (.initial minimal) [startOp, .activate [] "work"]
    | throw (IO.userError "failed to construct reachable ready state")
  let withoutClaim := (Explore.candidates {} ready).filter fun op =>
    match op with | .claim .. => false | _ => true
  let missed := withoutClaim.any (acceptedProgress ready)
  ensure (!missed) "claim omission fixture still has other work"
  ensure ((checkOperations ready (probes ready 7) missed).toOption.isNone)
    "independent probes failed to detect an omitted claim family"
  let path := ([] : Path)
  let startOp := Op.start [{ entry := ref "choose" "in", items := ["input"] }]
  let simple : Graph := {
    nodes := [{ id := "choose", kind := .branch ["left", "right"], inputs := [plain "in"], outputs := [plain "left", plain "right"] },
      { id := "join", kind := .coalesce, inputs := [plain "left", plain "right"], outputs := [plain "out"] }]
    edges := [edge "choose" "left" "join" "left", edge "choose" "right" "join" "right"]
    entries := [ref "choose" "in"]
    exits := [ref "join" "out"] }
  let .ok ready := Trace.replayOps (.initial simple) [startOp, .fireBranch path "choose" "left"]
    | throw (IO.userError "failed to construct reachable Coalesce state")
  let withoutCoalesce := (Explore.candidates {} ready).filter fun op =>
    match op with | .fireCoalesce .. => false | _ => true
  let missed := withoutCoalesce.any (acceptedProgress ready)
  ensure (!missed) "Coalesce omission fixture still has other work"
  ensure ((checkOperations ready (probes ready 11) missed).toOption.isNone)
    "independent probes failed to detect an omitted Coalesce family"

def run : IO Unit := do
  sensitivity
  let mut states := 0
  let mut tried := 0
  let mut accepted := 0
  for (name, graph) in examples ++ [("shared", sharedCoalesce), ("nested-joins", nestedCoalesce)] do
    ensure (graph.validate matches .ok _) s!"invalid graph in independent work test: {name}"
    for initialSeed in List.range 16 do
      let mut seed := initialSeed + 1
      let mut state := State.initial graph
      let mut trace := []
      for _ in List.range 48 do
        if state.status.terminal then break
        let operations := probes state seed
        states := states + 1
        tried := tried + operations.length
        let valid ← match checkOperations state operations state.hasWork with
          | .ok choices => pure choices
          | .error reason => throw (IO.userError (Json.mkObj [
              ("graph", toJson name), ("seed", toJson initialSeed), ("reason", toJson reason),
              ("trace", toJson trace), ("state", toJson state)]).compress)
        accepted := accepted + valid.length
        let ordinary := valid.filter (·.1.countsAsWork)
        let choices := if ordinary.isEmpty then valid.filter (fun pair => match pair.1 with | .cancel => false | _ => true) else ordinary
        if choices.isEmpty then break
        seed := Explore.nextSeed seed
        if let some (op, next) := choices[seed % choices.length]? then
          trace := trace ++ [op]
          state := next
  IO.println s!"ok: independent work coverage ({states} reachable states, {tried} probes, {accepted} progressing acceptances)"
end Suimon.Test.Work
