import Suimon.Step

namespace Suimon.Explore
open Lean

structure Config where
  /-- A Stream function yields at most this many elements. --/
  maxYields : Nat := 2
  /-- Include failures, timeouts and lost calls among the reports of user processes. --/
  failures : Bool := true
  /-- Include cancellation by the caller. --/
  cancel : Bool := true
  /-- A random walk picks a disruptive operation once in this many choices, when one is accepted. --/
  disruption : Nat := 40
  deriving Repr, ToJson, FromJson

/-- Values in exploration are derived from where they come from, so a run is reproducible. --/
def value (parts : List String) : Value := identity ("value" :: parts)

def armsOf (p : Program) (s : State) (c : Call) : List String :=
  match (s.invocation? c.owner).bind fun i => (s.workflow? p i.run).bind (·.placement? i.placement) with
  | some { control := .branch _ arms, .. } => arms
  | _ => []

def callCandidates (p : Program) (cfg : Config) (s : State) (c : Call) : List Op :=
  let failures (fetching : Bool) : List Op :=
    if cfg.failures then
      [.failed c.id, .timedOut c.id false, .lost c.id] ++ (if fetching then [.timedOut c.id true] else [])
    else []
  match c.status with
  | .running => match c.target with
    | .judge _ => (armsOf p s c).map (.judged c.id ·) ++ failures false
    | .function _ =>
      (if c.stream then [.fetch c.id] else [.returned c.id (value ["return", c.id])]) ++ failures false
  | .fetching =>
    (if c.yields < cfg.maxYields then [.yielded c.id (value ["yield", c.id, toString c.yields])] else []) ++
      [.ended c.id] ++ failures true
  | .cancelling => [.terminated c.id, .lost c.id]
  | _ => []

def invokeCandidates (p : Program) (s : State) (path : Path) (w : Workflow) (name : String) : List Op :=
  match w.shape? p name with
  | some .none | some .entry => [.invoke path name none]
  | some (.single i c) => match s.resolveSingle path i c with
    | .value source _ => [.invoke path name (some source)]
    | _ => []
  | some (.stream i _) => (s.deliveriesOn path i).filterMap fun d =>
    if d.outcome == .failed then none else some (.invoke path name (some d.source))
  | _ => []

def deliveryCandidates (p : Program) (cfg : Config) (s : State) (r : Result) : List Op :=
  match s.workflow? p r.run with
  | none => []
  | some w => w.connections.zipIdx.flatMap fun (c, i) =>
    if c.source != r.placement || (c.arm.isSome && c.arm != r.arm) || (s.delivery? r.run i r.id).isSome then []
    else match c.transform with
      | .declared _ => [.deliver r.run i r.id (some (value ["transform", toString i, r.id]))] ++
          (if cfg.failures then [.transformFailed r.run i r.id] else [])
      | .discard => [.deliver r.run i r.id none]

def taskCandidates (p : Program) (cfg : Config) (s : State) (e : Execution) : List Op :=
  let tasks := e.tasks.flatMap fun t =>
    match (s.taskSpec p e t.name).toOption, t.status with
    | some spec, .pending => match spec.input with
      | some (.declared _) => [.taskInput e.id t.name (some (value ["input", e.id, t.name]))] ++
          (if cfg.failures then [.taskInputFailed e.id t.name] else [])
      | some .discard => [.taskInput e.id t.name none]
      | none => []
    | some _, .ready => [.beginTask e.id t.name]
    | _, _ => []
  let outputs := (s.taskResults.filter fun r => r.execution == e.id && r.output == .pending).flatMap fun r =>
    [.taskOutput e.id r.task r.index (value ["output", e.id, r.task, toString r.index])] ++
      (if cfg.failures then [.taskOutputFailed e.id r.task r.index] else [])
  .closeExecution e.id :: tasks ++ outputs

/-- Every operation that might be accepted; the step decides which ones are. --/
def candidates (p : Program) (cfg : Config) (s : State) : List Op :=
  if !s.started then
    [.start (if ((p.workflow? p.main).bind (·.input)).isSome then some (value ["input"]) else none)]
  else match s.status with
  | .running =>
    let runs := (s.runs.filter (!·.complete)).flatMap fun r =>
      match p.workflow? r.workflow with
      | none => []
      | some w => (if r.path.isEmpty then [] else [.closeRun r.path]) ++
          w.placements.flatMap fun pl => .settle r.path pl.name :: invokeCandidates p s r.path w pl.name
    .conclude :: (if cfg.cancel then [.cancel] else []) ++ runs ++ s.results.flatMap (deliveryCandidates p cfg s) ++
      s.calls.flatMap (callCandidates p cfg s) ++
      (s.executions.filter (!·.complete)).flatMap (taskCandidates p cfg s)
  | .stopping =>
    .conclude :: (if s.cancelled then [] else [.cancel]) ++
      (s.calls.filter (·.status == .cancelling)).flatMap fun c => [.terminated c.id, .lost c.id]
  | _ => []

def accepted (p : Program) (cfg : Config) (s : State) : List (Op × State) :=
  (candidates p cfg s).filterMap fun op => match step p s op with
    | .ok next => if next == s then none else some (op, next)
    | .error _ => none

/-- A portable generator, so that a failing seed reproduces anywhere. --/
def nextSeed (seed : Nat) : Nat := (1664525 * seed + 1013904223) % 4294967296

/-- Failures, cancellation and short streams end work early, so a walk picks them rarely. --/
def disruptive (cfg : Config) (s : State) : Op → Bool
  | .failed _ | .timedOut .. | .lost _ | .transformFailed .. | .taskInputFailed .. | .taskOutputFailed ..
  | .cancel => true
  | .ended id => (s.call? id).any (·.yields < cfg.maxYields)
  | _ => false

def pick (cfg : Config) (s : State) (seed : Nat) (choices : List (Op × State)) : Option (Op × State) :=
  let (bad, good) := choices.partition (disruptive cfg s ·.1)
  let pool := if good.isEmpty || (!bad.isEmpty && seed % cfg.disruption == 0) then bad else good
  pool[(seed / cfg.disruption) % pool.length]?

/-- A random walk until no operation is accepted, or the limit is reached. --/
def walk (p : Program) (cfg : Config) (seed limit : Nat) : State × List Op := Id.run do
  let mut state : State := {}
  let mut trace : Array Op := #[]
  let mut seed := seed
  for _ in List.range limit do
    let choices := accepted p cfg state
    if choices.isEmpty then break
    seed := nextSeed seed
    let some (op, next) := pick cfg state seed choices | break
    trace := trace.push op
    state := next
  return (state, trace.toList)

end Suimon.Explore
