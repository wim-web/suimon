import Suimon.Types

namespace Suimon

structure FunctionDecl where
  id : String
  input : Option ValueType := none
  output : Contract
  deriving DecidableEq, Repr

/-- A branch judge receives the branch input and names one arm. --/
structure JudgeDecl where
  id : String
  input : ValueType
  deriving DecidableEq, Repr

structure TransformDecl where
  id : String
  input : ValueType
  output : ValueType
  deriving DecidableEq, Repr

/-- A call body: a function, or a workflow whose designated endpoint is the call output. --/
inductive Body where
  | function (id : String)
  | workflow (id : String) (output : String)
  deriving DecidableEq, Repr

inductive Collect where
  | list
  | stream
  deriving DecidableEq, Repr

/-- A declared transform, or `discard`, which the library provides for a target without input:
    it accepts any value, never fails, and passes nothing. --/
inductive TransformRef where
  | declared (id : String)
  | discard
  deriving DecidableEq, Repr

def TransformRef.discardName : String := "discard"

structure TaskSpec where
  name : String
  body : Body
  input : Option TransformRef := none
  /-- `none` leaves the task's results out of the concurrency output. --/
  output : Option String := none
  policy : Policy
  timeout : Timeout := {}
  deriving DecidableEq, Repr

structure Concurrency where
  input : Option ValueType := none
  limit : Nat
  tasks : List TaskSpec
  output : Collect
  element : ValueType
  deriving DecidableEq, Repr

inductive Control where
  | call (body : Body)
  | branch (judge : String) (arms : List String)
  | waitStream (element : ValueType)
  | merge (element : ValueType)
  | concurrency (spec : Concurrency)
  deriving DecidableEq, Repr

structure Placement where
  name : String
  control : Control
  policy : Policy
  timeout : Timeout := {}
  deriving DecidableEq, Repr

structure Connection where
  source : String
  arm : Option String := none
  target : String
  transform : TransformRef
  deriving DecidableEq, Repr

structure Entry where
  valueType : ValueType
  placement : String
  deriving DecidableEq, Repr

structure Workflow where
  id : String
  input : Option Entry := none
  placements : List Placement
  connections : List Connection := []
  deriving DecidableEq, Repr

structure Definition where
  functions : List FunctionDecl := []
  judges : List JudgeDecl := []
  transforms : List TransformDecl := []
  workflows : List Workflow
  main : String
  deriving DecidableEq, Repr

namespace Definition
def function? (p : Definition) (id : String) : Option FunctionDecl := p.functions.find? (·.id == id)
def judge? (p : Definition) (id : String) : Option JudgeDecl := p.judges.find? (·.id == id)
def transform? (p : Definition) (id : String) : Option TransformDecl := p.transforms.find? (·.id == id)
def workflow? (p : Definition) (id : String) : Option Workflow := p.workflows.find? (·.id == id)
end Definition

namespace Workflow
def placement? (w : Workflow) (name : String) : Option Placement := w.placements.find? (·.name == name)
def incoming (w : Workflow) (name : String) : List Connection := w.connections.filter (·.target == name)
def outgoing (w : Workflow) (name : String) : List Connection := w.connections.filter (·.source == name)
def isEntry (w : Workflow) (name : String) : Bool := w.input.any (·.placement == name)
/-- A placement without outgoing connections is an endpoint. --/
def isEndpoint (w : Workflow) (name : String) : Bool := (w.outgoing name).isEmpty
end Workflow

end Suimon
