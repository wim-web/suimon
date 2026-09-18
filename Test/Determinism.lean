import Suimon
import Test.Examples

namespace Suimon.Test.Determinism
open Lean

private def channelSequences (s : State) : List (String × List ItemId) :=
  (s.channels.map fun c => (c.id, c.items)).mergeSort (fun a b => a.1 ≤ b.1)

private def choice (oracleSeed : Nat) (key : String) : Nat :=
  key.toList.foldl (fun value char => (33 * value + char.toNat) % 4294967296) oracleSeed

/-- One fixed finite oracle per comparison group. No scheduler seed enters here.
    Candidate leaf outputs and occurrence IDs are the same on every attempt. --/
private def oracleAllows (oracleSeed : Nat) (s : State) : Op → Bool
  | .fireBranch path node arm => Id.run do
    let some n := s.node? path node | return false
    let .branch arms := n.kind | return false
    let item := (((s.incoming path node).head?).bind (·.pendingItems.head?)).getD ""
    return arms[choice oracleSeed (identity [node, item]) % arms.length]? == some arm
  | .fireFilter _ node item keep => keep == (choice oracleSeed (identity [node, item]) % 2 == 0)
  | .loopIterate inst done => Id.run do
    let some i := s.instance? inst | return false
    let some n := s.node? i.path i.node | return false
    let .loop _ limit := n.kind | return false
    return done == (i.iteration ≥ 1 + choice oracleSeed n.id % limit)
  | _ => true

inductive FaultMode | none | lease | failure
  deriving BEq, Repr, ToJson

structure Emission where
  «instance» : InstanceId
  attempt : AttemptId
  port : PortName
  item : ItemId
  deriving BEq

structure Schedule where
  mode : FaultMode
  target : Option InstanceId := none
  faulted : Bool := false
  sent : List Emission := []

private def sentOnAttempt (plan : Schedule) (auth : Credentials) (port : PortName) (item : ItemId) : Bool :=
  plan.sent.contains { «instance» := auth.instance, attempt := auth.attempt, port, item }

private def expired (s : State) : Bool :=
  s.instances.any (fun i => i.status == .running && i.lease.any (·.until_ ≤ s.now))

private def faultPending (plan : Schedule) (id : InstanceId) : Bool :=
  plan.mode != .none && !plan.faulted && plan.target == some id

/-- Fault after zero emits for plain leaves, or after a partial/full stream prefix.
    Only the schedule seed chooses the fault point, never the oracle output set. --/
private def faultReady (cfg : Explore.Config) (scheduleSeed : Nat) (plan : Schedule)
    (s : State) (id : InstanceId) : Bool := Id.run do
  unless faultPending plan id do return false
  let some i := s.instance? id | return false
  let some n := s.node? i.path i.node | return false
  let total := (n.outputs.filter (·.kind == .stream)).length * cfg.maxItems
  let quota := if total == 0 then 0 else 1 + scheduleSeed % total
  return i.attemptCount == 1 &&
    (plan.sent.filter (fun e => e.instance == id)).length ≥ quota

private def scheduleAllows (cfg : Explore.Config) (scheduleSeed : Nat) (plan : Schedule)
    (s : State) : Op → Bool
  | .claim .. => !expired s && !s.instances.any (·.status == .retryWait)
  | .emit auth port item => !sentOnAttempt plan auth port item &&
      !faultReady cfg scheduleSeed plan s auth.instance
  | .complete auth _ => Id.run do
    if faultPending plan auth.instance then return false
    let some i := s.instance? auth.instance | return false
    let some n := s.node? i.path i.node | return false
    return (n.outputs.filter (·.kind == .stream)).all fun port =>
      (List.range cfg.maxItems).all fun index =>
        let item := derivedItem "emit" i.path i.node [port.name, toString index]
        sentOnAttempt plan auth port.name item
  | .expireLease id _ => plan.mode != .none &&
      ((s.instance? id).any (fun i => i.lease.any (·.until_ ≤ s.now)) ||
        (plan.mode == .lease && faultReady cfg scheduleSeed plan s id))
  | .fail auth _ retryable => plan.mode == .failure && retryable &&
      faultReady cfg scheduleSeed plan s auth.instance
  -- Reap all expired attempts before moving to retry times. Finish maintenance
  -- before fresh claims so a single fault wave cannot exhaust a new attempt.
  | .promoteRetry .. => plan.mode != .none && !expired s
  | .renew .. | .cancel | .manualRetry .. => false
  | _ => true

structure Run where
  state : State
  trace : List Op
  reemits : Nat := 0
  consumedReemits : Nat := 0

private def runSchedule (graph : Graph) (oracleSeed scheduleSeed : Nat)
    (mode : FaultMode) : Except String Run := do
  let cfg : Explore.Config := { workers := 2, maxItems := oracleSeed % 3 }
  let mut state := State.initial graph
  let mut trace := []
  let mut seed := scheduleSeed
  let mut plan : Schedule := { mode }
  let mut reemits := 0
  let mut consumedReemits := 0
  for _ in List.range 256 do
    if state.status.terminal then break
    let mut choices := []
    for op in (Explore.candidates cfg state).filter (fun op =>
        oracleAllows oracleSeed state op && scheduleAllows cfg scheduleSeed plan state op) do
      match step state op with
      | .error error =>
        if error.code == "INVARIANT" then
          throw s!"invariant rejection: {(toJson (trace ++ [op])).compress}: {error.message}"
      | .ok next =>
        -- A deduplicated emit is a real send on this attempt even if State is
        -- unchanged. The per-attempt sent set prevents an endless retry loop.
        let emission := match op with | .emit .. => true | _ => false
        if next != state || emission then choices := choices ++ [(op, next)]
    if choices.isEmpty then
      throw s!"no progressing candidate: {(toJson trace).compress}"
    seed := Explore.nextSeed seed
    let some (op, next) := choices[(seed / 65536) % choices.length]?
      | throw "random choice out of bounds"
    match op with
    | .claim auth _ =>
      if plan.target.isNone && mode != .none then plan := { plan with target := some auth.instance }
    | .expireLease id _ =>
      if plan.target == some id then plan := { plan with faulted := true }
    | .fail auth .. =>
      if plan.target == some auth.instance then plan := { plan with faulted := true }
    | .emit auth port item =>
      if plan.sent.any (fun e => e.instance == auth.instance && e.attempt != auth.attempt &&
          e.port == port && e.item == item) then
        reemits := reemits + 1
        unless next.channels == state.channels do
          throw s!"retry emit changed channel history: {(toJson (trace ++ [op])).compress}"
        if let some i := state.instance? auth.instance then
          if (state.outgoing i.path i.node port).any
              (fun c => (c.placed.take c.consumed).contains (.item item)) then
            consumedReemits := consumedReemits + 1
      plan := { plan with sent := plan.sent ++ [{ «instance» := auth.instance, attempt := auth.attempt, port, item }] }
    | _ => pure ()
    trace := trace ++ [op]
    state := next
  unless succeededDrained state do
    throw s!"did not succeed and drain within 256 steps: {(toJson trace).compress}"
  if plan.target.isSome && !plan.faulted then throw "scheduled fault was not exercised"
  return { state, trace, reemits, consumedReemits }

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def execute (name : String) (graph : Graph) (oracleSeed scheduleSeed : Nat)
    (mode : FaultMode := .none) : IO Run :=
  match runSchedule graph oracleSeed scheduleSeed mode with
  | .ok result => pure result
  | .error reason => throw (IO.userError s!"T9 {name}, oracle={oracleSeed}, schedule={scheduleSeed}, mode={repr mode}: {reason}")

private def sensitivity : IO Unit := do
  let one ← execute "streaming" streaming 1 1
  let two ← execute "streaming" streaming 2 1
  ensure (channelBags one.state != channelBags two.state) "comparison missed different oracle outputs"
  let some channel := two.state.channels.find? (fun c => c.kind == .stream && !c.items.isEmpty)
    | throw (IO.userError "missing stream for multiplicity check")
  let item := channel.items.head!
  let duplicate := { two.state with channels := two.state.channels.map fun c =>
    if c.id == channel.id then { c with placed := .item item :: c.placed } else c }
  ensure (channelBags duplicate != channelBags two.state) "comparison erased item multiplicity"
  ensure (channelBags { two.state with channels := two.state.channels.reverse } == channelBags two.state)
    "comparison depends on State channel order"

def run : IO Unit := do
  sensitivity
  let mut executions := 0
  let mut comparisons := 0
  let mut differentSchedules := 0
  let mut differentArrivalOrders := 0
  let mut expirations := 0
  let mut failures := 0
  let mut promotions := 0
  let mut reclaims := 0
  let mut reemits := 0
  let mut consumedReemits := 0
  for (name, graph) in examples ++ [("shared", sharedCoalesce), ("nested-joins", nestedCoalesce)] do
    ensure (graph.validate matches .ok _) s!"T9 invalid example: {name}"
    for oracleSeed in List.range 6 do
      let baseline ← execute name graph oracleSeed 1
      executions := executions + 1
      for mode in [FaultMode.none, .lease, .failure] do
        for scheduleSeed in (List.range 16).map (· + 1) do
          if mode == .none && scheduleSeed == 1 then continue
          let current ← execute name graph oracleSeed scheduleSeed mode
          executions := executions + 1
          comparisons := comparisons + 1
          expirations := expirations + (current.state.attempts.filter (·.status == .abandoned)).length
          failures := failures + (current.state.attempts.filter (·.status == .failed)).length
          promotions := promotions + (current.trace.filter fun op => match op with | .promoteRetry .. => true | _ => false).length
          reclaims := reclaims + (current.state.attempts.filter (·.no > 1)).length
          reemits := reemits + current.reemits
          consumedReemits := consumedReemits + current.consumedReemits
          unless channelBags baseline.state == channelBags current.state do
            throw (IO.userError (Json.mkObj [
              ("property", toJson "T9 channel multisets"), ("graph", toJson name),
              ("oracle_seed", toJson oracleSeed), ("schedule_seeds", toJson [1, scheduleSeed]),
              ("fault_mode", toJson mode),
              ("left_trace", toJson baseline.trace), ("right_trace", toJson current.trace),
              ("left_channels", toJson (channelBags baseline.state)),
              ("right_channels", toJson (channelBags current.state))]).compress)
          if baseline.trace != current.trace then differentSchedules := differentSchedules + 1
          if channelSequences baseline.state != channelSequences current.state then
            differentArrivalOrders := differentArrivalOrders + 1
  ensure (differentSchedules > 0 && differentArrivalOrders > 0) "T9 schedules did not vary actual arrival order"
  ensure (expirations > 0 && failures > 0 && promotions == expirations + failures && reclaims == promotions)
    "T9 did not exercise complete fault/promotion/reclaim chains"
  ensure (reemits > 0 && consumedReemits > 0) "T9 did not exercise retry emits after downstream consumption"
  IO.println s!"ok: T9 finite-oracle schedules ({executions} succeeded/drained runs, {comparisons} multiset comparisons, {differentSchedules} different schedules, {differentArrivalOrders} different arrival orders)"
  IO.println s!"ok: T9 retries ({expirations} expirations, {failures} retryable failures, {promotions} promotions, {reclaims} reclaims, {reemits} re-emits, {consumedReemits} after consumption)"

end Suimon.Test.Determinism
