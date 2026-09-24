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
  -- A value stays mentioned once it is, so a value a transition introduces is new (§12.1).
  ensure (before.values.all after.values.contains) s!"{label}: a value withdrawn by {repr op}"
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

/-- In a final state reached through a stop, nothing is running: no invocation is active, every task
    ended and none holds a slot (§8.2, §11.3). --/
def nothingRunning (s : State) : Bool :=
  s.invocations.all (·.status != .active) &&
    s.executions.all fun e => e.tasks.all fun ts => ts.status.ended && !s.holdsSlot e ts

def randomWalks (label : String) (p : Definition) (cfg : Explore.Config) (seeds : Nat) : IO Unit := do
  for seed in List.range seeds do
    let mut s : State := {}
    let mut rng : UInt64 := .ofNat (seed + 1)
    let mut steps := 0
    while steps < 5000 do
      let choices := Explore.accepted p cfg s
      if choices.isEmpty then break
      rng := Explore.nextSeed rng
      let some (op, next) := Explore.pick cfg s rng choices | break
      checkTransition p s!"{label} seed {seed}" s next op
      unless cfg.cancel do
        ensure (!(op matches .cancel)) s!"{label} seed {seed}: cancelled by a walk without cancellation"
      s := next
      steps := steps + 1
    ensure s.status.terminal s!"{label} seed {seed}: stuck in {repr s.status} after {steps} steps"
    unless (s.run? []).any (·.complete) do
      ensure (nothingRunning s) s!"{label} seed {seed}: something runs after the conclusion of a stop"
    if !s.failures.isEmpty then
      ensure (s.status == .failed) s!"{label} seed {seed}: a recorded failure must fail the workflow"
    else if s.cancelled then
      ensure (s.status == .cancelled) s!"{label} seed {seed}: cancelled without failures must be cancelled"

/-- How the random walks of the default exploration mix disruptive operations with the others. --/
structure Mixing where
  walks : Nat := 0
  /-- Walks that pick two disruptive operations at most 4 steps apart. --/
  near : Nat := 0
  /-- Walks that cancel after a stop. --/
  cancelAfterStop : Nat := 0
  /-- Choices between disruptive operations and others, and those that took a disruptive one. --/
  choices : Nat := 0
  disrupted : Nat := 0

/-- Adds the walks of the first `seeds` seeds of `p` to `m`. --/
def mixing (p : Definition) (seeds : Nat) (m : Mixing) : Mixing := Id.run do
  let cfg : Explore.Config := {}
  let mut m := m
  for seed in List.range seeds do
    let mut s : State := {}
    let mut rng : UInt64 := .ofNat (seed + 1)
    let mut last : Option Nat := none
    let mut near := false
    let mut cancelAfterStop := false
    for i in List.range 5000 do
      let choices := Explore.accepted p cfg s
      if choices.isEmpty then break
      rng := Explore.nextSeed rng
      let some (op, next) := Explore.pick cfg s rng choices | break
      let disruptive := Explore.disruptive cfg s op
      if choices.any (Explore.disruptive cfg s ·.1) && choices.any (!Explore.disruptive cfg s ·.1) then
        m := { m with choices := m.choices + 1, disrupted := m.disrupted + if disruptive then 1 else 0 }
      if disruptive then
        near := near || last.any (i ≤ · + 4)
        last := some i
      cancelAfterStop := cancelAfterStop || (op == .cancel && s.status == .stopping)
      s := next
    m := { m with
      walks := m.walks + 1
      near := m.near + (if near then 1 else 0)
      cancelAfterStop := m.cancelAfterStop + (if cancelAfterStop then 1 else 0) }
  return m

/-- One function, whose failure stops the workflow. --/
def singleStopText : String :=
  "{\"main\": \"w\", \"functions\": [{\"id\": \"f\", \"output\": {\"single\": \"T\"}}], \"workflows\": [" ++
  "{\"id\": \"w\", \"placements\": [{\"name\": \"only\", \"node\": {\"type\": \"function\", " ++
  "\"function\": \"f\"}, \"policy\": \"stop\"}]}]}"

/-- An exploration without cancellation does not cancel after a stop either, though the caller may. --/
def walkWithoutCancel : IO Unit := do
  let p ← decoded "single stop" singleStopText
  accepted "single stop" p
  let call := Key.invocation [] "only" none
  let (final, ops) := Explore.walk p { cancel := false, disruption := 1 } 1 20
  ensure (ops == [.start none, .invoke [] "only" none, .failed call, .conclude] && final.status == .failed &&
    !final.cancelled) s!"single stop without cancellation: {repr ops}"
  let stopped ← [Op.start none, .invoke [] "only" none, .failed call].foldlM (init := {}) fun s op =>
    IO.ofExcept (step p s op)
  ensure (stopped.status == .stopping && (Explore.candidates p {} stopped).contains .cancel &&
    !(Explore.candidates p { cancel := false } stopped).contains .cancel) "single stop: cancellation after the stop"

/-- A concurrency task and a placement whose bodies are sub-workflows, each running one call. --/
def stoppedText : String :=
  "{\"main\": \"outer\", \"functions\": [{\"id\": \"child\", \"output\": {\"single\": \"T\"}}], " ++
  "\"transforms\": [{\"id\": \"pass\", \"input\": \"T\", \"output\": \"T\"}], \"workflows\": [" ++
  "{\"id\": \"outer\", \"placements\": [" ++
  "{\"name\": \"fan\", \"node\": {\"type\": \"concurrency\", \"limit\": 1, \"output\": \"list\", " ++
  "\"element\": \"T\", \"tasks\": [{\"name\": \"sub\", \"body\": {\"type\": \"subworkflow\", " ++
  "\"workflow\": \"inner\", \"output\": \"leaf\"}, \"outputTransform\": \"pass\", \"policy\": \"continue\"}]}, " ++
  "\"policy\": \"stop\"}, " ++
  "{\"name\": \"call\", \"node\": {\"type\": \"subworkflow\", \"workflow\": \"inner\", \"output\": \"leaf\"}, " ++
  "\"policy\": \"stop\"}]}, " ++
  "{\"id\": \"inner\", \"placements\": [{\"name\": \"leaf\", \"node\": {\"type\": \"function\", " ++
  "\"function\": \"child\"}, \"policy\": \"stop\"}]}]}"

/-- §8.2, §11.3: the conclusion after a stop ends the task and the invocation whose sub-workflows were
    still open, without a result, and leaves their runs as they are. --/
def stoppedSubworkflows : IO Unit := do
  let p ← decoded "stopped sub-workflows" stoppedText
  accepted "stopped sub-workflows" p
  let exec := Key.invocation [] "fan" none
  let taskRun := Key.child (Key.task exec "sub")
  let call := Key.invocation [] "call" none
  let callRun := Key.child call
  let ops : List Op := [.start none, .invoke [] "fan" none, .beginTask exec "sub", .invoke taskRun "leaf" none,
    .invoke [] "call" none, .invoke callRun "leaf" none, .cancel, .terminated (Key.invocation taskRun "leaf" none),
    .terminated (Key.invocation callRun "leaf" none)]
  let s ← ops.foldlM (init := {}) fun s op => match step p s op with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"stopped sub-workflows: {repr op} rejected: {e}")
  let task (s : State) : Option TaskState := (s.execution? exec).bind (·.tasks.head?)
  let holds (s : State) : Bool := match s.execution? exec, task s with
    | some e, some ts => s.holdsSlot e ts
    | _, _ => false
  ensure (s.status == .stopping && s.calls.all (·.status.ended)) "stopped sub-workflows: every call ended"
  ensure ((task s).map (·.status) == some .active && holds s) "stopped sub-workflows: the task holds its slot"
  ensure ((s.invocation? call).map (·.status) == some .active) "stopped sub-workflows: the call is active"
  let t ← match step p s .conclude with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"stopped sub-workflows: conclude rejected: {e}")
  ensure (t.status == .cancelled) "stopped sub-workflows: cancelled"
  ensure ((task t).map (·.status) == some .cancelled && !holds t) "stopped sub-workflows: the task ended"
  ensure ((t.invocation? exec).map (·.status) == some .cancelled &&
    (t.invocation? call).map (·.status) == some .cancelled) "stopped sub-workflows: the invocations ended"
  ensure (nothingRunning t) "stopped sub-workflows: something still runs"
  ensure (t.results == s.results && t.deliveries == s.deliveries && t.settled == s.settled &&
    t.taskResults == s.taskResults && t.failures == s.failures) "stopped sub-workflows: something was published"
  ensure (t.runs == s.runs && t.runs.all (!·.complete) && t.executions.all (!·.complete))
    "stopped sub-workflows: runs and executions are left as they are"
  ensure ((step p t .conclude).toOption.isNone) "stopped sub-workflows: final"

def run : IO Unit := do
  let users ← load "users"
  let branch ← load "branch"
  let merge ← load "merge"

  -- Every interleaving reaches a final state, with or without failures.
  for (label, p) in [("users", users), ("branch", branch), ("merge", merge)] do
    randomWalks label p {} 200
    randomWalks s!"{label} without failures" p { failures := false, cancel := false } 50
    randomWalks s!"{label} without cancellation" p { cancel := false } 50
  -- Random walks pick two disruptive operations close together, and cancel after a stop, though
  -- they pick about one disruptive operation in 40 choices between both kinds. The remainders of a
  -- linear congruential generator, whose low bits cycle, kept disruptive operations 8 steps apart:
  -- none of these walks did either.
  let m := [users, branch, merge].foldl (fun m p => mixing p 300 m) {}
  ensure (100 * m.near ≥ m.walks && 500 * m.cancelAfterStop ≥ m.walks && 32 * m.disrupted ≤ m.choices &&
      m.choices ≤ 50 * m.disrupted)
    (s!"mixing: of {m.walks} walks, {m.near} pick two disruptive operations at most 4 steps apart and " ++
      s!"{m.cancelAfterStop} cancel after a stop; {m.disrupted} of {m.choices} choices take a disruptive operation")

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

  stoppedSubworkflows
  walkWithoutCancel

  -- An identity is the run path followed by the record's label; the run a record owns is at the
  -- record's identity read as a path. The Go port pins the same values (identity_test.go).
  let p1 := Key.invocation [] "p" none
  let p2 := Key.invocation (Key.child p1) "p" none
  ensure (p1 == "16:10:invocation1:p" && Key.child p1 == ["10:invocation1:p"]) "keys: root"
  ensure (p2 == "16:10:invocation1:p16:10:invocation1:p" && Key.child p2 == ["10:invocation1:p", "10:invocation1:p"])
    "keys: one level down"
  let r := Key.callResult (Key.invocation [] "a" none) 0
  let q := Key.invocation [] "q" (some r)
  ensure (r == "30:6:result16:10:invocation1:a1:0" && q == "49:10:invocation1:q30:6:result16:10:invocation1:a1:0")
    "keys: a trigger by its label"
  ensure (Key.child (Key.task q "t") == ["4:task49:10:invocation1:q30:6:result16:10:invocation1:a1:01:t"])
    "keys: the run of a task"
  ensure (Key.invocation ["x"] "b" (some r) == "1:x54:10:invocation1:b33:30:6:result16:10:invocation1:a1:00:")
    "keys: a result of another run"
  -- The first draws of SplitMix64 from seed 0, as its reference implementation gives them. A walk
  -- uses every bit of the seed, modulo 2^64. The Go port pins the same values (identity_test.go).
  let draws := ((List.range 3).foldl (init := ((0 : UInt64), ([] : List UInt64))) fun (seed, draws) _ =>
    (Explore.nextSeed seed, draws ++ [Explore.mix (Explore.nextSeed seed)])).2
  ensure (draws == [0xe220a8397b1dcdaf, 0x6e789e6aa1b965f4, 0x06c45d188009454f] &&
    Explore.mix (Explore.nextSeed (.ofNat (2 ^ 40))) != Explore.mix (Explore.nextSeed 0)) s!"SplitMix64: {draws}"
  ensure ((Explore.walk merge {} (2 ^ 64 + 3) 10000).2 == (Explore.walk merge {} 3 10000).2 &&
    (Explore.walk merge {} (2 ^ 32 + 3) 10000).2 != (Explore.walk merge {} 3 10000).2) "the seed of a walk"
  -- The JSON of a task result tells a pending output from a failed one.
  let pending : TaskResult := { execution := "e", task := "t", index := 0, value := "v" }
  let outputs := [pending, { pending with output := .failed }, { pending with output := .value "w" }]
  ensure (unique (outputs.map fun r => (toJson r).compress)) "task outputs: ambiguous JSON"
  ensure (outputs.all fun r => (fromJson? (toJson r)).toOption == some r) "task outputs: JSON round trip"
  IO.println "step: ok"

end Suimon.Test.Step
