import Suimon.Derive

namespace Suimon

def unique [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

/-- Kahn elimination, bounded by the number of vertices. --/
def acyclic (edges : List (String × String)) : Nat → List String → Bool
  | 0, vertices => vertices.isEmpty
  | fuel + 1, vertices =>
    if vertices.isEmpty then true else
    let roots := vertices.filter fun v => !edges.any fun (src, dst) => dst == v && vertices.contains src
    !roots.isEmpty && acyclic edges fuel (vertices.filter (!roots.contains ·))

namespace Validate

def check (ok : Bool) (message : String) : Except String Unit :=
  if ok then pure () else throw message

def need (value : Option α) (message : String) : Except String α :=
  match value with
  | some v => pure v
  | none => throw message

end Validate
open Validate

def Body.workflowRef : Body → Option String
  | .workflow id _ => some id
  | .function _ => none

def Control.workflowRefs : Control → List String
  | .call body => body.workflowRef.toList
  | .concurrency c => c.tasks.filterMap (·.body.workflowRef)
  | _ => []

/-- A workflow may not call itself, directly or through other workflows (§13.1). --/
def Definition.callsAcyclic (p : Definition) : Bool :=
  let edges := p.workflows.flatMap fun w =>
    w.placements.flatMap fun pl => pl.control.workflowRefs.map (w.id, ·)
  acyclic edges p.workflows.length (p.workflows.map (·.id))

def Workflow.acyclic (w : Workflow) : Bool :=
  Suimon.acyclic (w.connections.map fun c => (c.source, c.target)) w.placements.length
    (w.placements.map (·.name))

namespace Definition

/-- Checks a call body and returns its input. --/
def validateBody (p : Definition) (at_ : String) : Body → Except String (Option ValueType)
  | .function id => return (← need (p.function? id) s!"{at_}: unknown function {id}").input
  | .workflow id output => do
    let w ← need (p.workflow? id) s!"{at_}: unknown workflow {id}"
    check (w.placement? output).isSome s!"{at_}: workflow {id} has no placement {output}"
    check (w.isEndpoint output) s!"{at_}: {output} is not an endpoint of workflow {id}"
    return w.input.map (·.valueType)

/-- Timeouts are for function calls and branch judges; element timeouts only for Stream functions. --/
def validateTimeout (at_ : String) (timeout : Timeout) (function : Option Contract) (judge : Bool) :
    Except String Unit := do
  if timeout.isEmpty then return
  check (function.isSome || judge) s!"{at_}: a timeout is only for a function call or a branch judge"
  check (timeout.callMs.all (· > 0) && timeout.elementMs.all (· > 0)) s!"{at_}: a timeout must be positive"
  if timeout.elementMs.isSome then
    check (function.any (·.kind == .stream)) s!"{at_}: an element timeout is only for a Stream function"

def validateTask (p : Definition) (at_ : String) (c : Concurrency) (task : TaskSpec) : Except String Unit := do
  let at_ := s!"{at_} task {task.name}"
  check (!task.name.isEmpty) s!"{at_}: empty task name"
  let input ← p.validateBody at_ task.body
  match input, task.input with
  | none, none => check c.input.isNone s!"{at_}: the body takes no input, so the input transform must be discard"
  | none, some .discard => check c.input.isSome s!"{at_}: the concurrency has no input to discard"
  | none, some (.declared _) => throw s!"{at_}: the body takes no input, so the input transform must be discard"
  | some _, none => throw s!"{at_}: an input transform is required"
  | some expected, some .discard => throw s!"{at_}: discard passes no value, but the body takes {expected}"
  | some expected, some (.declared id) =>
    let t ← need (p.transform? id) s!"{at_}: unknown transform {id}"
    let source ← need c.input s!"{at_}: the concurrency has no input for the task"
    check (t.input == source) s!"{at_}: transform {id} takes {t.input}, but the concurrency input is {source}"
    check (t.output == expected) s!"{at_}: transform {id} returns {t.output}, but the body takes {expected}"
  if let some id := task.output then
    let t ← need (p.transform? id) s!"{at_}: unknown transform {id}"
    let element ← need (p.bodyElement p.depth task.body) s!"{at_}: the result type cannot be derived"
    check (t.input == element) s!"{at_}: transform {id} takes {t.input}, but the body produces {element}"
    check (t.output == c.element)
      s!"{at_}: transform {id} returns {t.output}, but the output element is {c.element}"
  let function := match task.body with
    | .function id => (p.function? id).map (·.output)
    | .workflow .. => none
  validateTimeout at_ task.timeout function false

def validateConnection (p : Definition) (w : Workflow) (c : Connection) : Except String Unit := do
  let at_ := s!"{w.id}: connection {c.source} -> {c.target}"
  let source ← need (w.placement? c.source) s!"{at_}: unknown source"
  let target ← need (w.placement? c.target) s!"{at_}: unknown target"
  match source.control, c.arm with
  | .branch _ arms, some arm => check (arms.contains arm) s!"{at_}: unknown arm {arm}"
  | .branch .., none => throw s!"{at_}: a connection from a branch needs an arm"
  | _, some _ => throw s!"{at_}: only a connection from a branch has an arm"
  | _, none => pure ()
  let produced ← need (p.resultType source.control) s!"{at_}: the result type of {c.source} cannot be derived"
  let expected ← need (p.inputType target.control) s!"{at_}: {c.target} has an unknown reference"
  match c.transform, expected with
  | .discard, none => pure ()
  | .discard, some expected => throw s!"{at_}: discard passes no value, but {c.target} takes {expected}"
  | .declared _, none => throw s!"{at_}: {c.target} takes no input, so the transform must be discard"
  | .declared id, some expected =>
    let t ← need (p.transform? id) s!"{at_}: unknown transform {id}"
    check (t.input == produced) s!"{at_}: transform {id} takes {t.input}, but {c.source} produces {produced}"
    check (t.output == expected) s!"{at_}: transform {id} returns {t.output}, but {c.target} takes {expected}"

def validateEntry (p : Definition) (w : Workflow) (e : Entry) : Except String Unit := do
  let at_ := s!"{w.id}: entry {e.placement}"
  let placement ← need (w.placement? e.placement) s!"{at_}: unknown placement"
  check (!(placement.control matches .merge _)) s!"{at_}: Merge cannot be the entry"
  let expected ← need (p.inputType placement.control) s!"{at_}: unknown reference"
  check (expected == some e.valueType) s!"{at_}: the input type {e.valueType} does not match the placement"
  check (w.incoming e.placement).isEmpty s!"{at_}: the entry cannot have an input connection"

def validatePlacement (p : Definition) (w : Workflow) (pl : Placement) : Except String Unit := do
  let at_ := s!"{w.id}.{pl.name}"
  let incoming := w.incoming pl.name
  let expected ← match pl.control with
    | .call body => p.validateBody at_ body
    | .branch judge arms => do
      let j ← need (p.judge? judge) s!"{at_}: unknown judge {judge}"
      check (!arms.isEmpty && unique arms && arms.all (!·.isEmpty)) s!"{at_}: arms must be distinct non-empty names"
      check (arms.any fun arm => (w.outgoing pl.name).any (·.arm == some arm))
        s!"{at_}: at least one arm needs a connection"
      pure (some j.input)
    | .waitStream element => pure (some element)
    | .merge element => do
      check (!incoming.isEmpty) s!"{at_}: Merge needs input connections"
      pure (some element)
    | .concurrency c => do
      check (c.limit > 0) s!"{at_}: limit must be positive"
      check (!c.tasks.isEmpty) s!"{at_}: concurrency needs tasks"
      check (unique (c.tasks.map (·.name))) s!"{at_}: duplicate task name"
      check (c.tasks.any (·.output.isSome)) s!"{at_}: at least one task must be in the output"
      for task in c.tasks do p.validateTask at_ c task
      pure c.input
  unless pl.control matches .merge _ do
    let count := incoming.length + (if w.isEntry pl.name then 1 else 0)
    if expected.isSome then check (count == 1) s!"{at_}: needs exactly one input"
    else check (count ≤ 1) s!"{at_}: accepts at most one connection"
  match pl.control with
  | .waitStream _ =>
    check (w.inputKind? p pl.name == some (some .stream)) s!"{at_}: waitStream needs a Stream input"
  | .merge _ =>
    for c in incoming do
      check (w.outputKind? p c.source == some .single) s!"{at_}: Merge accepts only Single inputs ({c.source})"
  | _ => pure ()
  check (w.outputKind? p pl.name).isSome s!"{at_}: Single/Stream cannot be derived"
  let function := match pl.control with
    | .call (.function id) => (p.function? id).map (·.output)
    | _ => none
  validateTimeout at_ pl.timeout function (pl.control matches .branch ..)

def validateWorkflow (p : Definition) (w : Workflow) : Except String Unit := do
  let at_ := s!"workflow {w.id}"
  check (!w.id.isEmpty) "empty workflow id"
  check (!w.placements.isEmpty) s!"{at_}: no placements"
  check (w.placements.all (!·.name.isEmpty)) s!"{at_}: empty placement name"
  check (unique (w.placements.map (·.name))) s!"{at_}: duplicate placement name"
  for c in w.connections do p.validateConnection w c
  check w.acyclic s!"{at_}: connections contain a cycle"
  if let some e := w.input then p.validateEntry w e
  for pl in w.placements do p.validatePlacement w pl
  for pl in w.placements do
    if w.isEndpoint pl.name then
      check (w.outputKind? p pl.name == some .single) s!"{at_}: endpoint {pl.name} must be Single"

/-- Structural checks of §14. `run` executes only definitions accepted here. --/
def validate (p : Definition) : Except String Unit := do
  check (unique (p.functions.map (·.id))) "duplicate function id"
  check (unique (p.judges.map (·.id))) "duplicate judge id"
  check (unique (p.transforms.map (·.id))) "duplicate transform id"
  check (!p.transforms.any (·.id == TransformRef.discardName))
    s!"{TransformRef.discardName} is provided by the library and cannot be declared"
  check (unique (p.workflows.map (·.id))) "duplicate workflow id"
  check (p.workflow? p.main).isSome s!"unknown main workflow {p.main}"
  check p.callsAcyclic "workflows call each other in a cycle"
  for w in p.workflows do p.validateWorkflow w

end Definition

def Definition.WellFormed (p : Definition) : Prop := p.validate = .ok ()

end Suimon
