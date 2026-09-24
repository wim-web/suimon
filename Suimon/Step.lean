import Suimon.State

namespace Suimon
open Lean

/-- Engine decisions and reports from user processes. Each accepted operation is one state
    transition; the order of operations is left to the scheduler. --/
inductive Op where
  | start (input : Option Value)
  | invoke (run : Path) (placement : String) (trigger : Option ResultId)
  | fetch (call : String)
  | returned (call : String) (value : Value)
  | judged (call : String) (arm : String)
  | yielded (call : String) (value : Value)
  | ended (call : String)
  | failed (call : String)
  | timedOut (call : String) (element : Bool)
  | lost (call : String)
  | terminated (call : String)
  | deliver (run : Path) (connection : Nat) (source : ResultId) (value : Option Value)
  | transformFailed (run : Path) (connection : Nat) (source : ResultId)
  | taskInput (execution : String) (task : String) (value : Option Value)
  | taskInputFailed (execution : String) (task : String)
  | beginTask (execution : String) (task : String)
  | taskOutput (execution : String) (task : String) (index : Nat) (value : Value)
  | taskOutputFailed (execution : String) (task : String) (index : Nat)
  | settle (run : Path) (placement : String)
  | closeExecution (execution : String)
  | closeRun (run : Path)
  | cancel
  | conclude
  deriving DecidableEq, Repr, ToJson, FromJson

abbrev Result' := Except String

def require (ok : Bool) (code : String) : Result' Unit :=
  if ok then pure () else throw code

def need (value : Option α) (code : String) : Result' α :=
  match value with
  | some v => pure v
  | none => throw code

namespace State

def setRun (s : State) (r : Run) : State :=
  { s with runs := s.runs.map fun x => if x.path == r.path then r else x }
def setInvocation (s : State) (i : Invocation) : State :=
  { s with invocations := s.invocations.map fun x => if x.id == i.id then i else x }
def setCall (s : State) (c : Call) : State :=
  { s with calls := s.calls.map fun x => if x.id == c.id then c else x }
def setExecution (s : State) (e : Execution) : State :=
  { s with executions := s.executions.map fun x => if x.id == e.id then e else x }
def setTask (s : State) (e : Execution) (t : TaskState) : State :=
  s.setExecution { e with tasks := e.tasks.map fun x => if x.name == t.name then t else x }
def setTaskResult (s : State) (r : TaskResult) : State :=
  { s with taskResults := s.taskResults.map fun x =>
      if x.execution == r.execution && x.task == r.task && x.index == r.index then r else x }

/-- Stopping cancels running calls and leaves waiting tasks unstarted, in one transition (§11.3). --/
def stop (s : State) : State :=
  { s with
    status := .stopping
    calls := s.calls.map fun c =>
      if c.status == .running || c.status == .fetching then { c with status := .cancelling } else c
    executions := s.executions.map fun e => { e with tasks := e.tasks.map fun t =>
      if t.status == .pending || t.status == .ready then { t with status := .notStarted } else t } }

/-- The policy is chosen where the failure happened, never again by an enclosing placement (§11.2). --/
def fail (s : State) (f : Failure) (policy : Policy) : State :=
  let s := { s with failures := s.failures ++ [f] }
  match policy with
  | .stop => s.stop
  | .«continue» => s

def placementOf (p : Definition) (s : State) (path : Path) (name : String) : Result' Placement := do
  let w ← need (s.workflow? p path) "UNKNOWN_RUN"
  need (w.placement? name) "UNKNOWN_PLACEMENT"

def concurrencyOf (p : Definition) (s : State) (e : Execution) : Result' Concurrency := do
  let .concurrency c := (← s.placementOf p e.run e.placement).control | throw "NOT_CONCURRENCY"
  pure c

def taskSpec (p : Definition) (s : State) (e : Execution) (name : String) : Result' TaskSpec := do
  need ((← s.concurrencyOf p e).tasks.find? (·.name == name)) "UNKNOWN_TASK"

def task (e : Execution) (name : String) : Result' TaskState :=
  need (e.tasks.find? (·.name == name)) "UNKNOWN_TASK"

def callFailure (s : State) (c : Call) (cause : Cause) : Result' Failure := do
  match c.task with
  | none =>
    let i ← need (s.invocation? c.owner) "UNKNOWN_INVOCATION"
    pure { run := i.run, placement := i.placement, cause }
  | some name =>
    let e ← need (s.execution? c.owner) "UNKNOWN_EXECUTION"
    pure { run := e.run, placement := e.placement, task := some name, cause }

/-- Accept one value of a call as a result of its owner at this transition (§10.2). --/
def accept (s : State) (c : Call) (index : Nat) (value : Value) (arm : Option String := none) : Result' State := do
  match c.task with
  | none =>
    let i ← need (s.invocation? c.owner) "UNKNOWN_INVOCATION"
    let r : Result := {
      id := Key.callResult c.id index, run := i.run, placement := i.placement, producer := c.id, arm, value }
    require (s.result? r.id).isNone "DUPLICATE_RESULT"
    pure { s with results := s.results ++ [r] }
  | some name =>
    require (!s.taskResults.any fun x => x.execution == c.owner && x.task == name && x.index == index)
      "DUPLICATE_RESULT"
    pure { s with taskResults := s.taskResults ++ [{ execution := c.owner, task := name, index, value : TaskResult }] }

def settleOwner (s : State) (c : Call) (invocation : InvocationStatus) (task : TaskStatus) : Result' State := do
  match c.task with
  | none =>
    let i ← need (s.invocation? c.owner) "UNKNOWN_INVOCATION"
    pure (s.setInvocation { i with status := invocation })
  | some name =>
    let e ← need (s.execution? c.owner) "UNKNOWN_EXECUTION"
    let t ← State.task e name
    pure (s.setTask e { t with status := task })

/-- A terminated call ends its owner as cancelled, unless the owner already failed. --/
def cancelOwner (s : State) (c : Call) : Result' State := do
  match c.task with
  | none =>
    let i ← need (s.invocation? c.owner) "UNKNOWN_INVOCATION"
    pure (if i.status == .active then s.setInvocation { i with status := .cancelled } else s)
  | some name =>
    let e ← need (s.execution? c.owner) "UNKNOWN_EXECUTION"
    let t ← State.task e name
    pure (if t.status == .active then s.setTask e { t with status := .cancelled } else s)

def failCall (s : State) (c : Call) (status : CallStatus) (cause : Cause) : Result' State := do
  let f ← s.callFailure c cause
  let s ← (s.setCall { c with status }).settleOwner c .failed .failed
  pure (s.fail f c.policy)

def invocationOutcome (kind : Kind) : InvocationStatus → Outcome
  | .succeeded => .normal
  | .skipped => .skipped
  | .upstreamFailed => if kind == .stream then .normal else .upstreamFailed
  | _ => if kind == .stream then .normal else .failed

/-- A Stream output that got no value ends normally unless it was not selected (§7.3). --/
def missingOutcome (kind : Kind) (reason : Outcome) : Outcome :=
  if kind == .stream && reason != .skipped then .normal else reason

/-- When a placement has taken all its input and its invocations ended, how it settles (§7.3, §9, §10.3). --/
def settleOutcome (s : State) (path : Path) (pl : Placement) (shape : Workflow.Shape)
    (kind : Kind) : Option (Settled × Option Result) := do
  let invs := s.invocationsOf path pl.name
  guard (invs.all s.invocationEnded)
  let done := fun (outcome : Outcome) => some ({ run := path, placement := pl.name, outcome : Settled }, none)
  let key := Key.aggregate path pl.name
  let aggregate := fun (values : List Value) =>
    some ({ run := path, placement := pl.name, outcome := .normal : Settled },
      some { id := key, run := path, placement := pl.name, producer := key, value := listValue values })
  let triggered := fun (index : Nat) =>
    (s.deliveriesOn path index).all fun d => d.outcome == .failed || invs.any (·.trigger == some d.source)
  let ownFailures := fun (index : Nat) =>
    ((s.deliveriesOn path index).filter (·.outcome == .failed)).length +
      (invs.filter fun i => i.status == .failed || i.status == .cancelled).length
  match pl.control, shape with
  | .waitStream _, .stream i c =>
    if (← s.streamEnd? path i c) == .skipped then done .skipped
    else aggregate ((s.deliveriesOn path i).filterMap fun d => match d.outcome with
      | .value v => some v
      | _ => none)
  | .merge _, .merge cs =>
    let resolutions := cs.map fun (i, c) => s.resolveSingle path i c
    guard (resolutions.all (· != .pending))
    if resolutions.all (· == .skipped) then done .skipped
    else aggregate (resolutions.filterMap fun r => match r with
      | .value _ (some v) => some v
      | _ => none)
  | .branch _ arms, _ =>
    let settleArms := fun (outcome : Outcome) (arm : String → Outcome) =>
      some ({ run := path, placement := pl.name, outcome, arms := arms.map fun a => (a, arm a) : Settled }, none)
    let byInvocation := fun (inv : Invocation) =>
      match inv.status with
      | .succeeded =>
        settleArms .normal fun a => if inv.arm == some a then .normal else .skipped
      | .skipped => settleArms .skipped fun _ => .skipped
      | .upstreamFailed => settleArms .upstreamFailed fun _ => .upstreamFailed
      | _ => settleArms .failed fun _ => .failed
    match shape with
    | .entry => byInvocation (← invs.find? (·.trigger.isNone))
    | .single i c => match s.resolveSingle path i c with
      | .pending => none
      | .value source _ => byInvocation (← invs.find? (·.trigger == some source))
      | .transformFailed => settleArms .failed fun _ => .failed
      | .skipped => settleArms .skipped fun _ => .skipped
      | .failure => settleArms .upstreamFailed fun _ => .upstreamFailed
    | .stream i c =>
      let ended ← s.streamEnd? path i c
      guard (triggered i)
      if ended == .skipped then settleArms .skipped fun _ => .skipped
      else
        let chosen := (s.resultsOf path pl.name).filterMap (·.arm)
        let own := ownFailures i
        settleArms .normal fun a => if !chosen.isEmpty && !chosen.contains a && own == 0 then .skipped else .normal
    | _ => none
  | .call _, _ | .concurrency _, _ =>
    match shape with
    | .none | .entry => done (invocationOutcome kind (← invs.find? (·.trigger.isNone)).status)
    | .single i c => match s.resolveSingle path i c with
      | .pending => none
      | .value source _ => done (invocationOutcome kind (← invs.find? (·.trigger == some source)).status)
      | .transformFailed => done (missingOutcome kind .failed)
      | .skipped => done .skipped
      | .failure => done (missingOutcome kind .upstreamFailed)
    | .stream i c =>
      let ended ← s.streamEnd? path i c
      guard (triggered i)
      if ended == .skipped then done .skipped
      else done (if !invs.isEmpty && invs.all (·.status == .skipped) && ownFailures i == 0 then .skipped else .normal)
    | .merge _ => none
  | _, _ => none

/-- The endpoint whose result a sub-workflow call returns. --/
def designatedOutput (p : Definition) (s : State) (r : Run) : Result' String := do
  let owner ← need r.owner "ROOT_RUN"
  let body ← match r.task with
    | none =>
      let i ← need (s.invocation? owner) "UNKNOWN_INVOCATION"
      let .call body := (← s.placementOf p i.run i.placement).control | throw "NOT_A_CALL"
      pure body
    | some name =>
      let e ← need (s.execution? owner) "UNKNOWN_EXECUTION"
      pure (← s.taskSpec p e name).body
  let .workflow _ output := body | throw "NOT_A_WORKFLOW_CALL"
  pure output

end State

namespace Step
open State

def running (s : State) : Result' Unit := require (s.started && s.status == .running) "NOT_RUNNING"

def getCall (s : State) (id : String) : Result' Call := need (s.call? id) "UNKNOWN_CALL"

def getExecution (s : State) (id : String) : Result' Execution := need (s.execution? id) "UNKNOWN_EXECUTION"

def start (p : Definition) (s : State) (input : Option Value) : Result' State := do
  require (!s.started && s.status == .running) "ALREADY_STARTED"
  let w ← need (p.workflow? p.main) "UNKNOWN_MAIN"
  require (w.input.isSome == input.isSome) "INPUT_MISMATCH"
  pure { s with started := true, runs := [{ path := [], workflow := p.main, input }] }

/-- The input one invocation takes, if its trigger is available (§3.1, §5.3). --/
def invocationInput (p : Definition) (s : State) (r : Run) (w : Workflow) (name : String)
    (trigger : Option ResultId) : Result' (Option Value) := do
  match (← need (w.shape? p name) "INVALID_SHAPE"), trigger with
  | .none, none => pure none
  | .entry, none => pure r.input
  | .single i c, some source => match s.resolveSingle r.path i c with
    | .value delivered input => do require (delivered == source) "WRONG_TRIGGER"; pure input
    | _ => throw "INPUT_NOT_READY"
  | .stream i _, some source => match ((s.delivery? r.path i source).map (·.outcome) : Option Delivered) with
    | some (.value v) => pure (some v)
    | some .trigger => pure none
    | _ => throw "INPUT_NOT_READY"
  | _, _ => throw "INVALID_TRIGGER"

def invoke (p : Definition) (s : State) (path : Path) (name : String) (trigger : Option ResultId) : Result' State := do
  running s
  let r ← need (s.run? path) "UNKNOWN_RUN"
  require (!r.complete) "RUN_COMPLETE"
  let w ← need (p.workflow? r.workflow) "UNKNOWN_WORKFLOW"
  let pl ← need (w.placement? name) "UNKNOWN_PLACEMENT"
  let input ← invocationInput p s r w name trigger
  let id := Key.invocation path name trigger
  require (!(s.invocationsOf path name).any (·.trigger == trigger) && (s.invocation? id).isNone)
    "DUPLICATE_INVOCATION"
  let s := { s with invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input : Invocation }] }
  match pl.control with
  | .call (.function f) =>
    let decl ← need (p.function? f) "UNKNOWN_FUNCTION"
    require (s.call? id).isNone "DUPLICATE_CALL"
    let call : Call := {
      id, owner := id, target := .function f, input
      stream := decl.output.kind == .stream, timeout := pl.timeout, policy := pl.policy }
    pure { s with calls := s.calls ++ [call] }
  | .branch judge _ =>
    require (s.call? id).isNone "DUPLICATE_CALL"
    let call : Call := { id, owner := id, target := .judge judge, input, timeout := pl.timeout, policy := pl.policy }
    pure { s with calls := s.calls ++ [call] }
  | .call (.workflow workflow _) =>
    require (s.run? (path ++ [id])).isNone "DUPLICATE_RUN"
    pure { s with runs := s.runs ++ [{ path := path ++ [id], workflow, input, owner := some id : Run }] }
  | .concurrency c =>
    require (s.execution? id).isNone "DUPLICATE_EXECUTION"
    let tasks := c.tasks.map fun t => { name := t.name, status := if c.input.isSome then .pending else .ready : TaskState }
    pure { s with executions := s.executions ++ [{ id, run := path, placement := name, input, tasks : Execution }] }
  | _ => throw "NOT_INVOCABLE"

def fetch (s : State) (id : String) : Result' State := do
  running s
  let c ← getCall s id
  require (c.stream && c.status == .running) "NOT_FETCHABLE"
  pure (s.setCall { c with status := .fetching })

def returned (s : State) (id : String) (value : Value) : Result' State := do
  running s
  let c ← getCall s id
  require (!c.stream && c.status == .running && c.target matches .function _) "NOT_RETURNABLE"
  let s ← s.accept c 0 value
  (s.setCall { c with status := .returned }).settleOwner c .succeeded .succeeded

def judged (p : Definition) (s : State) (id : String) (arm : String) : Result' State := do
  running s
  let c ← getCall s id
  require (c.status == .running && c.target matches .judge _ && c.task.isNone) "NOT_JUDGING"
  let i ← need (s.invocation? c.owner) "UNKNOWN_INVOCATION"
  let .branch _ arms := (← s.placementOf p i.run i.placement).control | throw "NOT_BRANCH"
  require (arms.contains arm) "UNKNOWN_ARM"
  let s ← s.accept c 0 (i.input.getD "") (some arm)
  pure ((s.setCall { c with status := .returned }).setInvocation { i with status := .succeeded, arm := some arm })

def yielded (s : State) (id : String) (value : Value) : Result' State := do
  running s
  let c ← getCall s id
  require (c.stream && c.status == .fetching) "NOT_FETCHING"
  let s ← s.accept c c.yields value
  pure (s.setCall { c with status := .running, yields := c.yields + 1 })

def ended (s : State) (id : String) : Result' State := do
  running s
  let c ← getCall s id
  require (c.stream && c.status == .fetching) "NOT_FETCHING"
  (s.setCall { c with status := .returned }).settleOwner c .succeeded .succeeded

def failed (s : State) (id : String) : Result' State := do
  running s
  let c ← getCall s id
  require (c.status == .running || c.status == .fetching) "NOT_RUNNING"
  s.failCall c .failed .error

def timedOut (s : State) (id : String) (element : Bool) : Result' State := do
  running s
  let c ← getCall s id
  require (if element then c.status == .fetching && c.timeout.elementMs.isSome
    else (c.status == .running || c.status == .fetching) && c.timeout.callMs.isSome) "NO_TIMEOUT"
  s.failCall c .cancelling .timeout

def lost (s : State) (id : String) : Result' State := do
  require (s.started && (s.status == .running || s.status == .stopping)) "TERMINAL"
  let c ← getCall s id
  match c.status with
  | .running | .fetching => s.failCall c .lost .lost
  | .cancelling => (s.setCall { c with status := .cancelled }).cancelOwner c
  | _ => throw "NOT_RUNNING"

def terminated (s : State) (id : String) : Result' State := do
  require (s.started && (s.status == .running || s.status == .stopping)) "TERMINAL"
  let c ← getCall s id
  require (c.status == .cancelling) "NOT_CANCELLING"
  (s.setCall { c with status := .cancelled }).cancelOwner c

/-- The connection and result of one delivery, checked for eligibility. --/
def deliveryTarget (p : Definition) (s : State) (path : Path) (index : Nat) (source : ResultId) :
    Result' (Workflow × Connection) := do
  let w ← need (s.workflow? p path) "UNKNOWN_RUN"
  let c ← need w.connections[index]? "UNKNOWN_CONNECTION"
  let r ← need (s.result? source) "UNKNOWN_RESULT"
  require (r.run == path && r.placement == c.source && (c.arm.isNone || r.arm == c.arm)) "NOT_ELIGIBLE"
  require (s.delivery? path index source).isNone "DUPLICATE_DELIVERY"
  pure (w, c)

def deliver (p : Definition) (s : State) (path : Path) (index : Nat) (source : ResultId) (value : Option Value) :
    Result' State := do
  running s
  let (_, c) ← deliveryTarget p s path index source
  let outcome ← match c.transform, value with
    | .declared _, some v => pure (Delivered.value v)
    | .discard, none => pure .trigger
    | _, _ => throw "TRANSFORM_MISMATCH"
  pure { s with deliveries := s.deliveries ++ [{ run := path, connection := index, source, outcome : Delivery }] }

def transformFailed (p : Definition) (s : State) (path : Path) (index : Nat) (source : ResultId) : Result' State := do
  running s
  let (w, c) ← deliveryTarget p s path index source
  require (c.transform matches .declared _) "DISCARD_CANNOT_FAIL"
  let target ← need (w.placement? c.target) "UNKNOWN_PLACEMENT"
  let s := { s with deliveries := s.deliveries ++ [{ run := path, connection := index, source, outcome := .failed : Delivery }] }
  pure (s.fail { run := path, placement := c.target, cause := .transform } target.policy)

def taskInput (p : Definition) (s : State) (eid name : String) (value : Option Value) : Result' State := do
  running s
  let e ← getExecution s eid
  let t ← State.task e name
  require (t.status == .pending) "NOT_PENDING"
  match (← s.taskSpec p e name).input, value with
  | some (.declared _), some _ | some .discard, none => pure (s.setTask e { t with status := .ready, input := value })
  | _, _ => throw "TRANSFORM_MISMATCH"

def taskInputFailed (p : Definition) (s : State) (eid name : String) : Result' State := do
  running s
  let e ← getExecution s eid
  let t ← State.task e name
  require (t.status == .pending) "NOT_PENDING"
  let spec ← s.taskSpec p e name
  require (spec.input matches some (.declared _)) "DISCARD_CANNOT_FAIL"
  let s := s.setTask e { t with status := .failed }
  pure (s.fail { run := e.run, placement := e.placement, task := some name, cause := .transform } spec.policy)

def beginTask (p : Definition) (s : State) (eid name : String) : Result' State := do
  running s
  let e ← getExecution s eid
  require (!e.complete) "EXECUTION_COMPLETE"
  let c ← s.concurrencyOf p e
  let t ← State.task e name
  require (t.status == .ready) "NOT_READY"
  require ((e.tasks.filter (s.holdsSlot e)).length < c.limit) "NO_SLOT"
  let spec ← s.taskSpec p e name
  let s := s.setTask e { t with status := .active }
  let id := taskId e.id name
  match spec.body with
  | .function f =>
    let decl ← need (p.function? f) "UNKNOWN_FUNCTION"
    require (s.call? id).isNone "DUPLICATE_CALL"
    let call : Call := {
      id, owner := e.id, task := some name, target := .function f, input := t.input
      stream := decl.output.kind == .stream, timeout := spec.timeout, policy := spec.policy }
    pure { s with calls := s.calls ++ [call] }
  | .workflow workflow _ =>
    require (s.run? (e.run ++ [id])).isNone "DUPLICATE_RUN"
    let child : Run := { path := e.run ++ [id], workflow, input := t.input, owner := some e.id, task := some name }
    pure { s with runs := s.runs ++ [child] }

def taskResult (s : State) (eid name : String) (index : Nat) : Result' TaskResult :=
  need (s.taskResults.find? fun x => x.execution == eid && x.task == name && x.index == index) "UNKNOWN_RESULT"

def taskOutput (p : Definition) (s : State) (eid name : String) (index : Nat) (value : Value) : Result' State := do
  running s
  let e ← getExecution s eid
  let c ← s.concurrencyOf p e
  require (← s.taskSpec p e name).output.isSome "NOT_IN_OUTPUT"
  let r ← taskResult s eid name index
  require (r.output == .pending) "ALREADY_TRANSFORMED"
  let s := s.setTaskResult { r with output := .value value }
  match c.output with
  | .stream =>
    let result : Result := {
      id := Key.taskOutput eid name index, run := e.run, placement := e.placement, producer := eid, value }
    require (s.result? result.id).isNone "DUPLICATE_RESULT"
    pure { s with results := s.results ++ [result] }
  | .list => pure s

def taskOutputFailed (p : Definition) (s : State) (eid name : String) (index : Nat) : Result' State := do
  running s
  let e ← getExecution s eid
  let spec ← s.taskSpec p e name
  require spec.output.isSome "NOT_IN_OUTPUT"
  let r ← taskResult s eid name index
  require (r.output == .pending) "ALREADY_TRANSFORMED"
  let s := s.setTaskResult { r with output := .failed }
  pure (s.fail { run := e.run, placement := e.placement, task := some name, cause := .transform } spec.policy)

def settle (p : Definition) (s : State) (path : Path) (name : String) : Result' State := do
  running s
  let r ← need (s.run? path) "UNKNOWN_RUN"
  require (!r.complete) "RUN_COMPLETE"
  let w ← need (p.workflow? r.workflow) "UNKNOWN_WORKFLOW"
  let pl ← need (w.placement? name) "UNKNOWN_PLACEMENT"
  require (s.settled? path name).isNone "ALREADY_SETTLED"
  let shape ← need (w.shape? p name) "INVALID_SHAPE"
  let kind ← need (w.outputKind? p name) "INVALID_KIND"
  let (settled, result) ← need (s.settleOutcome path pl shape kind) "NOT_READY"
  let s := { s with settled := s.settled ++ [settled] }
  match result with
  | some r =>
    require (s.result? r.id).isNone "DUPLICATE_RESULT"
    pure { s with results := s.results ++ [r] }
  | none => pure s

def closeExecution (p : Definition) (s : State) (eid : String) : Result' State := do
  running s
  let e ← getExecution s eid
  require (!e.complete) "EXECUTION_COMPLETE"
  let c ← s.concurrencyOf p e
  require (e.tasks.all (s.taskEnded e)) "TASKS_RUNNING"
  let included := (c.tasks.filter (·.output.isSome)).map (·.name)
  let outputs := s.taskResults.filter fun x => x.execution == eid && included.contains x.task
  require (outputs.all (·.output != .pending)) "OUTPUT_PENDING"
  let s := s.setExecution { e with complete := true }
  let i ← need (s.invocation? eid) "UNKNOWN_INVOCATION"
  if (e.tasks.filter fun t => included.contains t.name).all (·.status == .skipped) then
    pure (s.setInvocation { i with status := .skipped })
  else match c.output with
    | .list =>
      let value := listValue (outputs.filterMap (·.output.value?))
      let result : Result := {
        id := Key.list eid, run := e.run, placement := e.placement, producer := eid, value }
      require (s.result? result.id).isNone "DUPLICATE_RESULT"
      pure { s.setInvocation { i with status := .succeeded } with results := s.results ++ [result] }
    | .stream => pure (s.setInvocation { i with status := .succeeded })

def closeRun (p : Definition) (s : State) (path : Path) : Result' State := do
  running s
  let r ← need (s.run? path) "UNKNOWN_RUN"
  require (!r.complete && !path.isEmpty) "NOT_CLOSABLE"
  let w ← need (p.workflow? r.workflow) "UNKNOWN_WORKFLOW"
  require (w.placements.all fun pl => (s.settled? path pl.name).isSome) "NOT_SETTLED"
  let output ← s.designatedOutput p r
  let x ← need (s.settled? path output) "NOT_SETTLED"
  let value := ((s.resultsOf path output).head?).map (·.value)
  let s := s.setRun { r with complete := true }
  let owner ← need r.owner "ROOT_RUN"
  match r.task with
  | none =>
    let i ← need (s.invocation? owner) "UNKNOWN_INVOCATION"
    match x.outcome, value with
    | .normal, some v =>
      let result : Result := {
        id := Key.returned i.id, run := i.run, placement := i.placement, producer := i.id, value := v }
      require (s.result? result.id).isNone "DUPLICATE_RESULT"
      pure { s.setInvocation { i with status := .succeeded } with results := s.results ++ [result] }
    | .normal, none => throw "MISSING_RESULT"
    | .skipped, _ => pure (s.setInvocation { i with status := .skipped })
    | .failed, _ => pure (s.setInvocation { i with status := .failed })
    | .upstreamFailed, _ => pure (s.setInvocation { i with status := .upstreamFailed })
  | some name =>
    let e ← getExecution s owner
    let t ← State.task e name
    match x.outcome, value with
    | .normal, some v =>
      require (!s.taskResults.any fun x => x.execution == e.id && x.task == name && x.index == 0) "DUPLICATE_RESULT"
      let s := s.setTask e { t with status := .succeeded }
      pure { s with taskResults := s.taskResults ++ [{ execution := e.id, task := name, index := 0, value := v : TaskResult }] }
    | .normal, none => throw "MISSING_RESULT"
    | .skipped, _ => pure (s.setTask e { t with status := .skipped })
    | .failed, _ => pure (s.setTask e { t with status := .failed })
    | .upstreamFailed, _ => pure (s.setTask e { t with status := .upstreamFailed })

def cancel (s : State) : Result' State := do
  require s.started "NOT_STARTED"
  match s.status with
  | .running => pure { s.stop with cancelled := true }
  | .stopping => pure { s with cancelled := true }
  | _ => throw "TERMINAL"

/-- The final status (§11.3, §13.3). --/
def conclude (p : Definition) (s : State) : Result' State := do
  require s.started "NOT_STARTED"
  match s.status with
  | .running =>
    let r ← need (s.run? []) "NO_ROOT"
    let w ← need (p.workflow? r.workflow) "UNKNOWN_WORKFLOW"
    require (w.placements.all fun pl => (s.settled? [] pl.name).isSome) "NOT_SETTLED"
    let endpoints := w.placements.filter fun pl => w.isEndpoint pl.name
    let status : Status :=
      if !s.failures.isEmpty then .failed
      else if endpoints.all fun pl => (s.settled? [] pl.name).any (·.outcome == .skipped) then .skipped
      else .succeeded
    pure { s.setRun { r with complete := true } with status }
  | .stopping =>
    require (s.calls.all (·.status.ended)) "CALLS_RUNNING"
    pure { s with status := if s.failures.isEmpty then .cancelled else .failed }
  | _ => throw "TERMINAL"

end Step

/-- Operational rules. Each rule checks its own preconditions; a rejected operation changes nothing. --/
def step (p : Definition) (s : State) : Op → Result' State
  | .start input => Step.start p s input
  | .invoke path name trigger => Step.invoke p s path name trigger
  | .fetch id => Step.fetch s id
  | .returned id value => Step.returned s id value
  | .judged id arm => Step.judged p s id arm
  | .yielded id value => Step.yielded s id value
  | .ended id => Step.ended s id
  | .failed id => Step.failed s id
  | .timedOut id element => Step.timedOut s id element
  | .lost id => Step.lost s id
  | .terminated id => Step.terminated s id
  | .deliver path index source value => Step.deliver p s path index source value
  | .transformFailed path index source => Step.transformFailed p s path index source
  | .taskInput eid name value => Step.taskInput p s eid name value
  | .taskInputFailed eid name => Step.taskInputFailed p s eid name
  | .beginTask eid name => Step.beginTask p s eid name
  | .taskOutput eid name index value => Step.taskOutput p s eid name index value
  | .taskOutputFailed eid name index => Step.taskOutputFailed p s eid name index
  | .settle path name => Step.settle p s path name
  | .closeExecution eid => Step.closeExecution p s eid
  | .closeRun path => Step.closeRun p s path
  | .cancel => Step.cancel s
  | .conclude => Step.conclude p s

end Suimon
