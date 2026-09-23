import Suimon.Validate
import Suimon.Identity

namespace Suimon
open Lean

/-- Values stay opaque; the model only moves their identities. --/
abbrev Value := String
/-- A run is a workflow executed as the root or as one sub-workflow call; `[]` is the root. --/
abbrev Path := List String
/-- A result is identified by where it came from, never by its value (§5.4). --/
abbrev ResultId := String

deriving instance ToJson, FromJson for Policy, Timeout

/-- A list value is identified by the multiset of its elements (§15.4). --/
def listValue (values : List Value) : Value := identity ("list" :: values.mergeSort (· ≤ ·))

/-! Identities of the records the engine creates. Each kind starts with its own tag, so identities
    of different kinds never coincide (by `identity_injective`), and each is a function of where the
    record comes from, never of the schedule. -/
namespace Key
def invocation (path : Path) (placement : String) (trigger : Option ResultId) : String :=
  identity (["invocation", identity path, placement] ++ trigger.toList)
def task (execution task : String) : String := identity ["task", execution, task]
def callResult (call : String) (index : Nat) : ResultId := identity ["result", call, toString index]
def aggregate (path : Path) (placement : String) : ResultId := identity ["aggregate", identity path, placement]
def taskOutput (execution task : String) (index : Nat) : ResultId :=
  identity ["output", execution, task, toString index]
def list (execution : String) : ResultId := identity ["list", execution]
def returned (invocation : String) : ResultId := identity ["return", invocation]
end Key

inductive Cause where
  | error | timeout | lost | transform
  deriving DecidableEq, Repr, ToJson, FromJson

/-- How a placement ended in one run. A Single output has a value (`normal`) or the reason it has
    none; a Stream output ends `normal` or `skipped`, and failures stay in the failure records. --/
inductive Outcome where
  | normal | skipped | failed | upstreamFailed
  deriving DecidableEq, Repr, ToJson, FromJson

inductive Status where
  | running | stopping | succeeded | failed | cancelled | skipped
  deriving DecidableEq, Repr, ToJson, FromJson

def Status.terminal : Status → Bool
  | .running | .stopping => false
  | _ => true

inductive CallStatus where
  | running | fetching | cancelling | returned | failed | lost | cancelled
  deriving DecidableEq, Repr, ToJson, FromJson

/-- A cancelled call keeps running until it terminates (§8.2, §11.5). --/
def CallStatus.ended : CallStatus → Bool
  | .running | .fetching | .cancelling => false
  | _ => true

inductive InvocationStatus where
  | active | succeeded | skipped | failed | upstreamFailed | cancelled
  deriving DecidableEq, Repr, ToJson, FromJson

inductive TaskStatus where
  | pending | ready | active | succeeded | skipped | failed | upstreamFailed | notStarted | cancelled
  deriving DecidableEq, Repr, ToJson, FromJson

def TaskStatus.ended : TaskStatus → Bool
  | .pending | .ready | .active => false
  | _ => true

structure Run where
  path : Path
  workflow : String
  input : Option Value := none
  /-- The invocation, or the execution of the task, that called this workflow; `none` for the root. --/
  owner : Option String := none
  task : Option String := none
  complete : Bool := false
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One application of a placement: once for a Single input, once per element of a Stream. --/
structure Invocation where
  id : String
  run : Path
  placement : String
  trigger : Option ResultId := none
  input : Option Value := none
  status : InvocationStatus := .active
  /-- The arm a branch judge selected. --/
  arm : Option String := none
  deriving DecidableEq, Repr, ToJson, FromJson

inductive CallTarget where
  | function (id : String)
  | judge (id : String)
  deriving DecidableEq, Repr, ToJson, FromJson

/-- A call of a user process. Its owner is an invocation, or the execution of a task. --/
structure Call where
  id : String
  owner : String
  task : Option String := none
  target : CallTarget
  input : Option Value := none
  stream : Bool := false
  status : CallStatus := .running
  yields : Nat := 0
  timeout : Timeout := {}
  policy : Policy
  deriving DecidableEq, Repr, ToJson, FromJson

structure TaskState where
  name : String
  input : Option Value := none
  status : TaskStatus
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One execution of a concurrency placement for one input. --/
structure Execution where
  id : String
  run : Path
  placement : String
  input : Option Value := none
  tasks : List TaskState
  complete : Bool := false
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The output transform of a task applied to one of its results: not yet, the transformed value,
    or a failure. --/
inductive TaskOutput where
  | pending
  | value (v : Value)
  | failed
  deriving DecidableEq, Repr, ToJson, FromJson

def TaskOutput.value? : TaskOutput → Option Value
  | .value v => some v
  | _ => none

/-- A result of a task body, before the task's output transform. --/
structure TaskResult where
  execution : String
  task : String
  index : Nat
  value : Value
  output : TaskOutput := .pending
  deriving DecidableEq, Repr, ToJson, FromJson

/-- An accepted result of a placement in a run. A branch result carries its selected arm. --/
structure Result where
  id : ResultId
  run : Path
  placement : String
  /-- What produced the result: the call for a call result, the execution for a concurrency result,
      the invocation for a sub-workflow call result, and `Key.aggregate run placement` for the list
      of a waitStream or Merge. --/
  producer : String
  arm : Option String := none
  value : Value
  deriving DecidableEq, Repr, ToJson, FromJson

inductive Delivered where
  | value (v : Value)
  | trigger
  | failed
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The transform of one connection applied to one result. --/
structure Delivery where
  run : Path
  connection : Nat
  source : ResultId
  outcome : Delivered
  deriving DecidableEq, Repr, ToJson, FromJson

structure Settled where
  run : Path
  placement : String
  outcome : Outcome
  /-- A branch settles each arm separately. --/
  arms : List (String × Outcome) := []
  deriving DecidableEq, Repr, ToJson, FromJson

structure Failure where
  run : Path
  placement : String
  task : Option String := none
  cause : Cause
  deriving DecidableEq, Repr, ToJson, FromJson

structure State where
  status : Status := .running
  started : Bool := false
  /-- The caller cancelled the workflow. --/
  cancelled : Bool := false
  runs : List Run := []
  invocations : List Invocation := []
  calls : List Call := []
  executions : List Execution := []
  results : List Result := []
  taskResults : List TaskResult := []
  deliveries : List Delivery := []
  settled : List Settled := []
  failures : List Failure := []
  deriving DecidableEq, Repr, ToJson, FromJson

instance : Inhabited State := ⟨{}⟩

namespace Workflow

/-- Input connections with their indices, which identify connections in a run. --/
def inputs (w : Workflow) (name : String) : List (Nat × Connection) :=
  w.connections.zipIdx.filterMap fun (c, i) => if c.target == name then some (i, c) else none

/-- Where one placement gets its input from. --/
inductive Shape where
  | none
  | entry
  | single (index : Nat) (connection : Connection)
  | stream (index : Nat) (connection : Connection)
  | merge (connections : List (Nat × Connection))

def shape? (p : Program) (w : Workflow) (name : String) : Option Shape := do
  let placement ← w.placement? name
  if placement.control matches .merge _ then return .merge (w.inputs name)
  if w.isEntry name then return .entry
  match w.inputs name with
  | [] => return .none
  | [(i, c)] => match w.outputKind? p c.source with
    | some .single => return .single i c
    | some .stream => return .stream i c
    | none => none
  | _ => none

end Workflow

namespace State

def run? (s : State) (path : Path) : Option Run := s.runs.find? (·.path == path)
def workflow? (p : Program) (s : State) (path : Path) : Option Workflow := do p.workflow? (← s.run? path).workflow
def invocation? (s : State) (id : String) : Option Invocation := s.invocations.find? (·.id == id)
def call? (s : State) (id : String) : Option Call := s.calls.find? (·.id == id)
def execution? (s : State) (id : String) : Option Execution := s.executions.find? (·.id == id)
def result? (s : State) (id : ResultId) : Option Result := s.results.find? (·.id == id)
def settled? (s : State) (path : Path) (name : String) : Option Settled :=
  s.settled.find? fun x => x.run == path && x.placement == name
def delivery? (s : State) (path : Path) (index : Nat) (source : ResultId) : Option Delivery :=
  s.deliveries.find? fun d => d.run == path && d.connection == index && d.source == source

def invocationsOf (s : State) (path : Path) (name : String) : List Invocation :=
  s.invocations.filter fun i => i.run == path && i.placement == name

def resultsOf (s : State) (path : Path) (name : String) : List Result :=
  s.results.filter fun r => r.run == path && r.placement == name

def deliveriesOn (s : State) (path : Path) (index : Nat) : List Delivery :=
  s.deliveries.filter fun d => d.run == path && d.connection == index

/-- Calls, child runs and executions record their owner, so ending checks follow ownership. --/
def invocationEnded (s : State) (i : Invocation) : Bool :=
  i.status != .active &&
  (s.calls.filter fun c => c.owner == i.id && c.task.isNone).all (·.status.ended) &&
  (s.runs.filter fun r => r.owner == some i.id && r.task.isNone).all (·.complete) &&
  (s.executions.filter (·.id == i.id)).all (·.complete)

def armOutcome (x : Settled) : Option String → Outcome
  | none => x.outcome
  | some arm => ((x.arms.find? (·.1 == arm)).map (·.2)).getD x.outcome

/-- The results a connection carries: those of its source, on its arm for a branch. --/
def eligible (s : State) (path : Path) (c : Connection) : List Result :=
  (s.resultsOf path c.source).filter fun r => c.arm.isNone || r.arm == c.arm

inductive Resolution where
  | pending
  | value (source : ResultId) (input : Option Value)
  | transformFailed
  | skipped
  | failure
  deriving DecidableEq, Repr

/-- A Single connection resolves to its delivered value, or to why no value will come. --/
def resolveSingle (s : State) (path : Path) (index : Nat) (c : Connection) : Resolution :=
  match s.deliveriesOn path index with
  | d :: _ => match d.outcome with
    | .value v => .value d.source (some v)
    | .trigger => .value d.source none
    | .failed => .transformFailed
  | [] => match s.settled? path c.source with
    | none => .pending
    | some x => match armOutcome x c.arm with
      | .normal => .pending
      | .skipped => .skipped
      | .failed | .upstreamFailed => .failure

/-- A Stream connection ends once its source settled and each of its results was delivered. --/
def streamEnd? (s : State) (path : Path) (index : Nat) (c : Connection) : Option Outcome := do
  let x ← s.settled? path c.source
  guard ((s.eligible path c).all fun r => (s.delivery? path index r.id).isSome)
  pure (armOutcome x c.arm)

def taskId (execution task : String) : String := Key.task execution task

/-- A task holds a slot while its body runs, including a cancelled call that has not terminated. --/
def holdsSlot (s : State) (e : Execution) (t : TaskState) : Bool :=
  t.status == .active ||
    s.calls.any fun c => c.owner == e.id && c.task == some t.name && c.status == .cancelling

def taskEnded (s : State) (e : Execution) (t : TaskState) : Bool :=
  t.status.ended && !s.holdsSlot e t &&
  (s.runs.filter fun r => r.owner == some e.id && r.task == some t.name).all (·.complete)

/-- Every value the state mentions, with repeats. A recovered state needs the payload of each (§12.1). --/
def values (s : State) : List Value :=
  s.runs.filterMap (·.input) ++ s.invocations.filterMap (·.input) ++ s.calls.filterMap (·.input) ++
    s.executions.flatMap (fun e => e.input.toList ++ e.tasks.filterMap (·.input)) ++
    s.results.map (·.value) ++
    s.deliveries.filterMap (fun d => match d.outcome with
      | .value v => some v
      | _ => none) ++
    s.taskResults.flatMap fun r => r.value :: r.output.value?.toList

end State

end Suimon
