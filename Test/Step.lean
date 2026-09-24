import Suimon.Explore
import Test.Validate

namespace Suimon.Test.Step
open Lean Suimon Suimon.Test.Validate

def engineOp : Op → Bool
  | .start _ | .invoke .. | .fetch _ | .deliver .. | .taskInput .. | .beginTask .. | .taskOutput ..
  | .settle .. | .closeExecution _ | .closeRun _ | .conclude => true
  | _ => false

/-- Engine operations run first; then each running call reports what `decide` says. --/
def drive (p : Definition) (decide : State → Call → Option Op) (limit : Nat := 10000) : State := Id.run do
  let mut s : State := {}
  for _ in List.range limit do
    let engine := (Explore.candidates p { failures := false } s).filter engineOp
    match engine.findSome? fun op => (step p s op).toOption.filter (· != s) with
    | some next => s := next
    | none =>
      match s.calls.findSome? fun c => (decide s c).bind fun op => (step p s op).toOption.filter (· != s) with
      | some next => s := next
      | none => break
  return s

def functionOf (c : Call) : String :=
  match c.target with
  | .function f | .judge f => f

/-- Reports that let every call succeed; a Stream function yields `count` elements. --/
def succeed (count : Nat) (arm : State → Call → String) (s : State) (c : Call) : Option Op :=
  match c.status, c.target with
  | .running, .judge _ => some (.judged c.id (arm s c))
  | .running, .function _ => if c.stream then none else some (.returned c.id (Explore.value ["return", c.id]))
  | .fetching, _ => some (if c.yields < count then .yielded c.id (Explore.value ["yield", c.id, toString c.yields]) else .ended c.id)
  | .cancelling, _ => some (.terminated c.id)
  | _, _ => none

def outcome (s : State) (path : Path) (name : String) : Option Outcome := (s.settled? path name).map (·.outcome)

def expectStatus (label : String) (s : State) (status : Status) : IO Unit :=
  ensure (s.status == status) s!"{label}: expected {repr status}, got {repr s.status} with {s.failures.length} failures"

/-- Invariants checked at every accepted transition of a random walk. --/
def checkTransition (p : Definition) (label : String) (before after : State) (op : Op) : IO Unit := do
  ensure (unique (after.results.map (·.id))) s!"{label}: duplicate result after {repr op}"
  ensure (unique (after.invocations.map (·.id))) s!"{label}: duplicate invocation after {repr op}"
  ensure (unique (after.deliveries.map fun d => (d.run, d.connection, d.source))) s!"{label}: duplicate delivery"
  for e in after.executions do
    if let .ok c := after.concurrencyOf p e then
      ensure ((e.tasks.filter (after.holdsSlot e)).length ≤ c.limit) s!"{label}: limit exceeded after {repr op}"
  if before.status == .stopping then
    ensure (after.results == before.results && after.deliveries == before.deliveries &&
      after.invocations.length == before.invocations.length) s!"{label}: work accepted after the stop: {repr op}"
  ensure (after.failures.take before.failures.length == before.failures) s!"{label}: failure record removed"
  ensure (before.results.all after.results.contains) s!"{label}: accepted result withdrawn by {repr op}"
  -- A new result names its producer: the reporting call, the closed execution, the sub-workflow
  -- invocation, or the aggregating placement.
  let producer : Option String := match op with
    | .returned id _ | .judged id _ | .yielded id _ => some id
    | .taskOutput eid .. | .closeExecution eid => some eid
    | .closeRun path => (before.run? path).bind (·.owner)
    | .settle path name => some (Key.aggregate path name)
    | _ => none
  for r in after.results do
    unless before.results.contains r do
      ensure (producer == some r.producer) s!"{label}: result {r.id} with producer {r.producer} after {repr op}"

def randomWalks (label : String) (p : Definition) (cfg : Explore.Config) (seeds : Nat) : IO Unit := do
  for seed in List.range seeds do
    let mut s : State := {}
    let mut rng := seed + 1
    let mut steps := 0
    while steps < 5000 do
      let choices := Explore.accepted p cfg s
      if choices.isEmpty then break
      rng := Explore.nextSeed rng
      let some (op, next) := Explore.pick cfg s rng choices | break
      checkTransition p s!"{label} seed {seed}" s next op
      s := next
      steps := steps + 1
    ensure s.status.terminal s!"{label} seed {seed}: stuck in {repr s.status} after {steps} steps"
    if !s.failures.isEmpty then
      ensure (s.status == .failed) s!"{label} seed {seed}: a recorded failure must fail the workflow"
    else if s.cancelled then
      ensure (s.status == .cancelled) s!"{label} seed {seed}: cancelled without failures must be cancelled"

def run : IO Unit := do
  let users ← load "users"
  let branch ← load "branch"
  let merge ← load "merge"

  -- Every interleaving reaches a final state, with or without failures.
  for (label, p) in [("users", users), ("branch", branch), ("merge", merge)] do
    randomWalks label p {} 200
    randomWalks s!"{label} without failures" p { failures := false, cancel := false } 50

  -- §8.5: each user gets one list from the profile sub-workflow and the orders call.
  let s := drive users (succeed 2 fun _ _ => "")
  expectStatus "users" s .succeeded
  ensure ((s.resultsOf [] "perUser").length == 2) "users: one list per user"
  ensure ((s.resultsOf [] "all").length == 1) "users: one list of all users"
  let s := drive users fun s c => if functionOf c == "fetchAllUsers" then some (.failed c.id) else succeed 2 (fun _ _ => "") s c
  expectStatus "users: stop" s .failed
  ensure s.results.isEmpty "users: nothing is accepted after the stop"

  -- §7.3: every order goes to the other arm, so the arm and its waitStream are skipped.
  let s := drive branch (succeed 2 fun _ _ => "unpaid")
  expectStatus "branch: unpaid" s .skipped
  ensure (outcome s [] "ship" == some .skipped && outcome s [] "receipts" == some .skipped) "branch: skipped arm"
  let s := drive branch (succeed 2 fun s _ => if (s.resultsOf [] "paid").isEmpty then "paid" else "unpaid")
  expectStatus "branch: one paid" s .succeeded
  ensure ((s.resultsOf [] "receipts").map (·.value) ==
    [listValue ((s.deliveriesOn [] 2).filterMap fun d => match d.outcome with | .value v => some v | _ => none)])
    "branch: the receipts of the selected orders"
  let s := drive branch (succeed 0 fun _ _ => "unpaid")
  expectStatus "branch: no orders" s .succeeded
  ensure ((s.resultsOf [] "receipts").map (·.value) == [listValue []]) "branch: an empty stream is not skipped"
  let s := drive branch fun s c =>
    if functionOf c == "isPaid" && (s.failures.isEmpty) then some (.failed c.id) else succeed 2 (fun _ _ => "unpaid") s c
  expectStatus "branch: failed judge" s .failed
  ensure (outcome s [] "receipts" == some .normal) "branch: a failed judge is not a non-selection"

  -- §9.2: Merge keeps the successful inputs; the failed input's other targets are not run.
  let s := drive merge fun s c => if functionOf c == "fetchSales" then some (.failed c.id) else succeed 0 (fun _ _ => "") s c
  expectStatus "merge: failed input" s .failed
  ensure ((s.resultsOf [] "widgets").length == 1 && outcome s [] "page" == some .normal) "merge: list of the rest"
  ensure (outcome s [] "archive" == some .upstreamFailed && outcome s [] "notify" == some .upstreamFailed)
    "merge: targets of a failed call are not run"
  let s := drive merge (succeed 0 fun _ _ => "")
  expectStatus "merge" s .succeeded
  ensure ((s.invocationsOf [] "notify").length == 1) "merge: discard runs its target once"

  -- The JSON of a task result tells a pending output from a failed one.
  let pending : TaskResult := { execution := "e", task := "t", index := 0, value := "v" }
  let outputs := [pending, { pending with output := .failed }, { pending with output := .value "w" }]
  ensure (unique (outputs.map fun r => (toJson r).compress)) "task outputs: ambiguous JSON"
  ensure (outputs.all fun r => (fromJson? (toJson r)).toOption == some r) "task outputs: JSON round trip"
  IO.println "step: ok"

end Suimon.Test.Step
