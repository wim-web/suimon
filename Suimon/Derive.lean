import Suimon.Workflow

namespace Suimon

/-- The input of one call: `some none` for a body without input, `none` for an unknown body. --/
def Definition.bodyInput (p : Definition) : Body → Option (Option ValueType)
  | .function id => (p.function? id).map (·.input)
  | .workflow id _ => (p.workflow? id).map (·.input.map (·.valueType))

def Definition.bodyKind (p : Definition) : Body → Option Kind
  | .function id => (p.function? id).map (·.output.kind)
  | .workflow id _ => (p.workflow? id).map fun _ => .single

/-- Result element types of the controls other than calls. --/
def Definition.localResult (p : Definition) : Control → Option ValueType
  | .call _ => none
  | .branch judge _ => (p.judge? judge).map (·.input)
  | .waitStream element | .merge element => some (.list element)
  | .concurrency c => some (match c.output with
      | .list => .list c.element
      | .stream => c.element)

/-- Element type of a body's results. The fuel bounds nested workflow references. --/
def Definition.bodyElement (p : Definition) : Nat → Body → Option ValueType
  | 0, _ => none
  | _ + 1, .function id => (p.function? id).map (·.output.element)
  | fuel + 1, .workflow id output => do
    let placement ← (← p.workflow? id).placement? output
    match placement.control with
    | .call body => p.bodyElement fuel body
    | control => p.localResult control

/-- Enough fuel for an acyclic call graph, where each nested reference names another workflow. --/
def Definition.depth (p : Definition) : Nat := p.workflows.length + 1

/-- Element type of the results of one placement. --/
def Definition.resultType (p : Definition) : Control → Option ValueType
  | .call body => p.bodyElement p.depth body
  | control => p.localResult control

/-- What an input connection's transform returns: `some none` when the control takes no input. --/
def Definition.inputType (p : Definition) : Control → Option (Option ValueType)
  | .call body => p.bodyInput body
  | .branch judge _ => (p.judge? judge).map (some ·.input)
  | .waitStream element | .merge element => some (some element)
  | .concurrency c => some c.input

/-- Output kind of one placement from its input kind (§5.2, §8.4). --/
def Definition.outputKind (p : Definition) (control : Control) (input : Option Kind) : Option Kind :=
  match control, input with
  | .call body, none | .call body, some .single => p.bodyKind body
  | .call _, some .stream => some .stream
  | .branch .., some kind => some kind
  | .waitStream _, some .stream => some .single
  | .merge _, some .single => some .single
  | .concurrency c, none | .concurrency c, some .single =>
    some (match c.output with | .list => .single | .stream => .stream)
  | .concurrency _, some .stream => some .stream
  | _, _ => none

/-- An entry supplies one Single input; otherwise every source must agree. --/
def Workflow.combineInput (w : Workflow) (name : String) (sources : List Kind) : Option (Option Kind) :=
  if w.isEntry name then
    if sources.isEmpty then some (some .single) else none
  else match sources with
    | [] => some none
    | kind :: rest => if rest.all (· == kind) then some (some kind) else none

/-- Output kind of a placement; the fuel bounds the length of connection paths. --/
def Workflow.kind? (p : Definition) (w : Workflow) : Nat → String → Option Kind
  | 0, _ => none
  | fuel + 1, name => do
    let placement ← w.placement? name
    let sources ← (w.incoming name).mapM fun c => w.kind? p fuel c.source
    p.outputKind placement.control (← w.combineInput name sources)

def Workflow.depth (w : Workflow) : Nat := w.placements.length + 1

def Workflow.inputKind? (p : Definition) (w : Workflow) (name : String) : Option (Option Kind) := do
  let sources ← (w.incoming name).mapM fun c => w.kind? p w.depth c.source
  w.combineInput name sources

def Workflow.outputKind? (p : Definition) (w : Workflow) (name : String) : Option Kind :=
  w.kind? p w.depth name

end Suimon
