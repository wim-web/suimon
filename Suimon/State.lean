import Suimon.Graph
namespace Suimon
open Lean
abbrev ItemId := String
abbrev InstanceId := String
abbrev AttemptId := String
abbrev LeaseToken := String
abbrev Time := Nat
abbrev Path := List InstanceId

inductive Token | item (id : ItemId) | eos
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, ToJson, FromJson
structure Channel where
  id : String
  edge : Edge
  path : Path
  kind : PortKind
  entry : Bool := false
  exit : Bool := false
  placed : List Token := []
  consumed : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, Repr, ToJson, FromJson
inductive InstanceStatus
  | waitingInputs | ready | running | retryWait | succeeded | failed | cancelled
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, ToJson, FromJson
structure Lease where
  attempt : AttemptId
  token : LeaseToken
  until_ : Time
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
structure Instance where
  id : InstanceId
  node : NodeId
  path : Path
  trigger : Option ItemId := none
  status : InstanceStatus
  attemptCount : Nat := 0
  lease : Option Lease := none
  retryAt : Option Time := none
  iteration : Nat := 0
  extraAttempts : Nat := 0
  extraIterations : Nat := 0
  inputs : List (PortName × ItemId) := []
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
inductive AttemptStatus | running | succeeded | failed | abandoned | cancelled
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
structure Attempt where
  id : AttemptId
  «instance» : InstanceId
  no : Nat
  status : AttemptStatus
  token : LeaseToken
  worker : String
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
inductive ExecStatus | running | blocked | succeeded | failed | cancelled
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr, ToJson, FromJson
structure Frame where
  path : Path
  graph : Graph
  definition : List NodeId := []
  owner : Option InstanceId := none
  closed : Bool := false
  deriving BEq, Repr, ToJson, FromJson
structure Consumption where
  channel : String
  index : Nat
  item : ItemId
  byInstance : InstanceId
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
structure Output where
  port : PortName
  items : List ItemId
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
structure Receipt where
  «instance» : InstanceId
  attempt : AttemptId
  token : LeaseToken
  outputs : List Output
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
structure Decision where
  key : String
  value : String
  deriving DecidableEq, BEq, Repr, ToJson, FromJson
structure State where
  status : ExecStatus := .running
  channels : List Channel := []
  instances : List Instance := []
  attempts : List Attempt := []
  frames : List Frame := []
  consumed : List Consumption := []
  receipts : List Receipt := []
  decisions : List Decision := []
  now : Time := 0
  started : Bool := false
  reason : Option String := none
  deriving BEq, Repr, ToJson, FromJson

def identity (parts : List String) : String := (toJson parts).compress

def instanceId (path : Path) (node : NodeId) (trigger : Option ItemId := none) : InstanceId :=
  (toJson (path, node, trigger)).compress

def Frame.edgeChannels (f : Frame) : List Channel :=
  f.graph.edges.zipIdx.map fun (e, i) => {
      id := identity (f.path ++ ["edge", toString i])
      edge := e
      path := f.path
      kind := ((f.graph.output? e.src).map (·.kind)).getD .plain }

def Frame.entryChannels (f : Frame) : List Channel :=
  f.graph.entries.zipIdx.map fun (p, i) => {
      id := identity (f.path ++ ["entry", toString i])
      edge := { src := { node := "$input", port := toString i }, dst := p }
      path := f.path
      kind := ((f.graph.input? p).map (·.kind)).getD .plain
      entry := true }

def Frame.exitChannels (f : Frame) : List Channel :=
  f.graph.exits.zipIdx.map fun (p, i) => {
      id := identity (f.path ++ ["exit", toString i])
      edge := { src := p, dst := { node := "$output", port := toString i } }
      path := f.path
      kind := ((f.graph.output? p).map (·.kind)).getD .plain
      exit := true }

def Frame.channels (f : Frame) : List Channel :=
  f.edgeChannels ++ f.entryChannels ++ f.exitChannels

def State.initial (g : Graph) : State :=
  let f : Frame := { path := [], graph := g }
  { frames := [f], channels := f.channels }

def ExecStatus.terminal : ExecStatus → Bool
  | .succeeded | .failed | .cancelled => true
  | _ => false

def InstanceStatus.finished : InstanceStatus → Bool
  | .succeeded | .failed | .cancelled => true
  | _ => false

def Channel.items (c : Channel) : List ItemId := c.placed.filterMap fun t =>
  match t with | .item id => some id | .eos => none

def Channel.closed (c : Channel) : Bool := c.placed.contains .eos

def Channel.pending (c : Channel) : List Token := c.placed.drop c.consumed

def Channel.pendingItems (c : Channel) : List ItemId := c.pending.filterMap fun t =>
  match t with | .item id => some id | .eos => none

def State.instance? (s : State) (id : InstanceId) : Option Instance := s.instances.find? (·.id == id)
/-- Internal scheduling addresses a logical node, independently of its wire ID. --/
def State.nodeInstance? (s : State) (path : Path) (node : NodeId) : Option Instance :=
  s.instances.find? (fun i => i.path == path && i.node == node && i.trigger.isNone)
def State.frame? (s : State) (path : Path) : Option Frame := s.frames.find? (·.path == path)
def State.node? (s : State) (path : Path) (node : NodeId) : Option Node := do
  let f ← s.frame? path
  f.graph.node? node

def State.incoming (s : State) (path : Path) (node : NodeId) : List Channel :=
  s.channels.filter fun c => c.path == path && !c.exit && c.edge.dst.node == node

def State.outgoing (s : State) (path : Path) (node : NodeId) (port : PortName) : List Channel :=
  s.channels.filter fun c => c.path == path && !c.entry && c.edge.src == { node, port }

structure Credentials where
  «instance» : InstanceId
  attempt : AttemptId
  token : LeaseToken
  now : Time
  deriving DecidableEq, BEq, Repr, ToJson, FromJson

/-- A stale worker cannot regain authority by merely naming the current instance. --/
def validLease (s : State) (c : Credentials) : Bool :=
  !s.status.terminal && c.now ≥ s.now && (s.instance? c.instance).any fun i =>
    i.status == .running && i.lease.any (fun l =>
      l.attempt == c.attempt && l.token == c.token && c.now < l.until_)

def ValidLease (s : State) (c : Credentials) : Prop := validLease s c = true
end Suimon
