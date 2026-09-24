import Suimon.Derive

/-! The normality conditions of a definition (§14), stated without the validator: the validator accepts
    only normal definitions (`Definition.normal_of_validate`). They use the derivations of
    `Suimon/Derive.lean` for the types of results and inputs and for the Single/Stream kinds. -/

namespace Suimon

/-- A call names a declared function, or a declared workflow and one of its endpoints (§4.5). --/
def Body.Normal (p : Definition) : Body → Prop
  | .function id => (p.function? id).isSome
  | .workflow id output => ∃ w, p.workflow? id = some w ∧ (w.placement? output).isSome ∧ w.isEndpoint output

/-- The body a placement calls, if it is a call. --/
def Control.body? : Control → Option Body
  | .call body => some body
  | _ => none

/-- The contract of the function a body calls, which decides the timeouts of the call (§11.5). --/
def Definition.calledContract (p : Definition) : Body → Option Contract
  | .function id => (p.function? id).map (·.output)
  | .workflow .. => none

/-- `transform` takes a value of type `source` to a target that takes `input`: `discard` exactly when
    the target takes no input (`none`), otherwise a declared transform from `source` to that input
    (§4.2). --/
def Definition.TransformFits (p : Definition) (source : ValueType) : TransformRef → Option ValueType → Prop
  | .discard, none => True
  | .declared id, some input => ∃ t, p.transform? id = some t ∧ t.input = source ∧ t.output = input
  | _, _ => False

/-- The connections into a placement, with the entry counted as one. --/
def Workflow.inputCount (w : Workflow) (name : String) : Nat :=
  (w.incoming name).length + (if w.isEntry name then 1 else 0)

/-- A timeout is set only on a function call or a branch judge, with durations that are positive and
    at most `maxNat`, and an element timeout only on a call of a Stream function (§11.5). `function`
    is the contract of the function called, if any; `judge` whether the timeout is on a branch. --/
structure Timeout.Legal (t : Timeout) (function : Option Contract) (judge : Bool) : Prop where
  target : t ≠ {} → function.isSome ∨ judge = true
  positive : ∀ ms ∈ t.callMs.toList ++ t.elementMs.toList, 0 < ms ∧ ms ≤ maxNat
  element : t.elementMs.isSome → ∃ c, function = some c ∧ c.kind = .stream

/-- One task of the concurrency `c` (§8.1). --/
structure TaskSpec.Normal (p : Definition) (c : Concurrency) (task : TaskSpec) : Prop where
  name : task.name ≠ ""
  body : task.body.Normal p
  /-- Without a concurrency input, the body takes none and there is no input transform; with one, the
      input transform takes it to the input of the body. --/
  input : ∃ input, p.bodyInput task.body = some input ∧
    match c.input with
    | none => input = none ∧ task.input = none
    | some source => ∃ transform, task.input = some transform ∧ p.TransformFits source transform input
  /-- A task in the output maps the results of its body to the output element (§8.3). --/
  output : ∀ id ∈ task.output, ∃ t, p.transform? id = some t ∧
    p.bodyElement p.depth task.body = some t.input ∧ t.output = c.element
  timeout : task.timeout.Legal (p.calledContract task.body) false

/-- One placement of the workflow `w`. --/
structure Placement.Normal (p : Definition) (w : Workflow) (pl : Placement) : Prop where
  call : ∀ body, pl.control = .call body → body.Normal p
  /-- A branch names a declared judge and distinct non-empty arms, and one arm has a connection (§7.1). --/
  branch : ∀ judge arms, pl.control = .branch judge arms →
    (p.judge? judge).isSome ∧ arms ≠ [] ∧ arms.Nodup ∧ (∀ arm ∈ arms, arm ≠ "") ∧
      ∃ arm ∈ arms, ∃ c ∈ w.outgoing pl.name, c.arm = some arm
  /-- A waitStream takes a Stream (§9.1). --/
  waitStream : ∀ e, pl.control = .waitStream e → e.name ≠ "" ∧ w.inputKind? p pl.name = some (some .stream)
  /-- A Merge takes one or more Single inputs (§9.2). --/
  merge : ∀ e, pl.control = .merge e → e.name ≠ "" ∧ w.incoming pl.name ≠ [] ∧
    ∀ c ∈ w.incoming pl.name, w.outputKind? p c.source = some .single
  /-- A concurrency has a positive limit that fits in 64 bits, and tasks with distinct names, at least
      one of them in the output (§8.1, §8.2). --/
  concurrency : ∀ c, pl.control = .concurrency c →
    (∀ t ∈ c.input.toList ++ [c.element], t.name ≠ "") ∧ 0 < c.limit ∧ c.limit ≤ maxNat ∧ c.tasks ≠ [] ∧
      (c.tasks.map (·.name)).Nodup ∧ (∃ task ∈ c.tasks, task.output.isSome) ∧ ∀ task ∈ c.tasks, task.Normal p c
  /-- A placement that takes an input has exactly one, from a connection or the entry, and one without
      input at most one connection; a Merge has any number (§3.2). --/
  inputs : ∃ input, p.inputType pl.control = some input ∧
    ((∀ e, pl.control ≠ .merge e) → w.inputCount pl.name ≤ 1 ∧ (input.isSome → w.inputCount pl.name = 1))
  /-- Single/Stream can be derived (§5.2). --/
  kind : (w.outputKind? p pl.name).isSome
  timeout : pl.timeout.Legal (pl.control.body?.bind p.calledContract) (pl.control matches .branch ..)

/-- A connection of the workflow `w` joins two of its placements, names an arm exactly when it leaves a
    branch, and then one of the branch's arms, and its transform takes the result of the source to the
    input of the target (§3.3, §4.2, §7.1). --/
structure Connection.Normal (p : Definition) (w : Workflow) (c : Connection) : Prop where
  ends : ∃ src dst, w.placement? c.source = some src ∧ w.placement? c.target = some dst ∧
    (∀ judge arms, src.control = .branch judge arms → ∃ arm ∈ arms, c.arm = some arm) ∧
    ((∀ judge arms, src.control ≠ .branch judge arms) → c.arm = none) ∧
    ∃ produced input, p.resultType src.control = some produced ∧ p.inputType dst.control = some input ∧
      p.TransformFits produced c.transform input

/-- The entry of the workflow `w` is a placement other than a Merge, without input connections, that
    takes the input type (§3.1). --/
structure Entry.Normal (p : Definition) (w : Workflow) (e : Entry) : Prop where
  type : e.valueType.name ≠ ""
  placement : ∃ pl, w.placement? e.placement = some pl ∧ (∀ el, pl.control ≠ .merge el) ∧
    p.inputType pl.control = some (some e.valueType)
  alone : w.incoming e.placement = []

structure Workflow.Normal (p : Definition) (w : Workflow) : Prop where
  id : w.id ≠ ""
  nonempty : w.placements ≠ []
  names : ∀ pl ∈ w.placements, pl.name ≠ ""
  distinct : (w.placements.map (·.name)).Nodup
  connections : ∀ c ∈ w.connections, c.Normal p w
  /-- The connections form a DAG (§13.1). --/
  acyclic : ∃ rank : String → Nat, ∀ c ∈ w.connections, rank c.source < rank c.target
  entry : ∀ e, w.input = some e → e.Normal p w
  placements : ∀ pl ∈ w.placements, pl.Normal p w
  /-- An endpoint is Single (§13.2). --/
  endpoints : ∀ pl ∈ w.placements, w.isEndpoint pl.name → w.outputKind? p pl.name = some .single

/-- A normal definition (§14, §15.2): declarations with distinct identifiers that the definition file
    can write, a main workflow, calls between workflows without a cycle, and normal workflows. --/
structure Definition.Normal (p : Definition) : Prop where
  functions : ∀ f ∈ p.functions, f.id ≠ "" ∧ ∀ t ∈ f.input.toList ++ [f.output.element], t.name ≠ ""
  judges : ∀ j ∈ p.judges, j.id ≠ "" ∧ j.input.name ≠ ""
  transforms : ∀ t ∈ p.transforms, t.id ≠ "" ∧ t.input.name ≠ "" ∧ t.output.name ≠ ""
  functionIds : (p.functions.map (·.id)).Nodup
  judgeIds : (p.judges.map (·.id)).Nodup
  transformIds : (p.transforms.map (·.id)).Nodup
  /-- `discard` is the library's (§4.2). --/
  discard : ∀ t ∈ p.transforms, t.id ≠ TransformRef.discardName
  workflowIds : (p.workflows.map (·.id)).Nodup
  main : (p.workflow? p.main).isSome
  /-- A workflow calls only workflows of higher rank, so none calls itself (§13.1). --/
  calls : ∃ rank : String → Nat, ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ id ∈ pl.control.workflowRefs,
    rank w.id < rank id
  workflows : ∀ w ∈ p.workflows, w.Normal p

end Suimon
