import Lean

namespace Suimon
open Lean

abbrev NodeId := String
abbrev PortName := String

inductive PortKind | plain | stream
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq, ToJson, FromJson
structure Port where
  name : PortName
  kind : PortKind
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq, ToJson, FromJson
structure PortRef where
  node : NodeId
  port : PortName
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq, ToJson, FromJson
structure RetryPolicy where
  maxAttempts : Nat := 1
  leaseSeconds : Nat := 30
  retrySeconds : Nat := 0
  deriving DecidableEq, Repr, BEq, ToJson, FromJson

structure Edge where
  src : PortRef
  dst : PortRef
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq, ToJson, FromJson

mutual
inductive NodeKind where
  | leaf (retry : RetryPolicy) (concurrency : Nat)
  | waitAll
  | branch (arms : List PortName)
  | coalesce
  | loop (body : Graph) (maxIterations : Nat)
  | subworkflow (body : Graph)
  | forEach (body : Graph)
  | collect
  | filter
  | merge
  deriving Repr, BEq
structure Node where
  id : NodeId
  kind : NodeKind
  inputs : List Port
  outputs : List Port
  deriving Repr, BEq
structure Graph where
  nodes : List Node
  edges : List Edge
  entries : List PortRef
  exits : List PortRef
  deriving Repr, BEq
end

def Graph.node? (g : Graph) (id : NodeId) : Option Node :=
  g.nodes.find? (·.id == id)
def Graph.input? (g : Graph) (r : PortRef) : Option Port := do
  let n ← g.node? r.node
  n.inputs.find? (·.name == r.port)
def Graph.output? (g : Graph) (r : PortRef) : Option Port := do
  let n ← g.node? r.node
  n.outputs.find? (·.name == r.port)

def unique [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

def allKind (ps : List Port) (k : PortKind) : Bool := ps.all (·.kind == k)

def Node.shapeOK (n : Node) : Bool :=
  let plainIn := allKind n.inputs .plain
  let plainOut := allKind n.outputs .plain
  let streamIn := allKind n.inputs .stream
  let streamOut := allKind n.outputs .stream
  match n.kind with
  | .leaf r c => plainIn && r.maxAttempts > 0 && r.leaseSeconds > 0 && c > 0
  | .waitAll => plainIn && plainOut && n.outputs.length == 1
  | .coalesce => plainIn && plainOut && !n.inputs.isEmpty && n.outputs.length == 1
  | .branch arms => plainIn && plainOut && n.inputs.length == 1 &&
      !arms.isEmpty && unique arms && arms == n.outputs.map (·.name)
  | .loop b m => plainIn && plainOut && n.inputs.length == 1 &&
      n.outputs.length == 1 && m > 0 && b.entries.length == 1 && b.exits.length == 1 &&
      b.entries.all (fun p => (b.input? p).any (·.kind == .plain)) &&
      b.exits.all (fun p => (b.output? p).any (·.kind == .plain))
  | .subworkflow b => plainIn && plainOut && n.inputs.length == b.entries.length &&
      n.outputs.length == b.exits.length &&
      b.entries.all (fun p => (b.input? p).any (·.kind == .plain)) &&
      b.exits.all (fun p => (b.output? p).any (·.kind == .plain))
  | .forEach b => streamIn && streamOut && n.inputs.length == 1 &&
      n.outputs.length == 1 && b.entries.length == 1 && b.exits.length == 1 &&
      b.entries.all (fun p => (b.input? p).any (·.kind == .plain)) &&
      b.exits.all (fun p => (b.output? p).any (·.kind == .plain))
  | .collect => streamIn && plainOut && n.inputs.length == 1 && n.outputs.length == 1
  | .filter => streamIn && streamOut && n.inputs.length == 1 && n.outputs.length == 1
  | .merge => streamIn && streamOut && !n.inputs.isEmpty && n.outputs.length == 1

/-- Kahn elimination, bounded by the number of vertices. --/
def acyclicAux (edges : List Edge) : Nat → List NodeId → Bool
  | 0, ns => ns.isEmpty
  | fuel + 1, ns =>
    if ns.isEmpty then true else
    let roots := ns.filter fun n => !edges.any (fun e => e.dst.node == n && ns.contains e.src.node)
    !roots.isEmpty && acyclicAux edges fuel (ns.filter (!roots.contains ·))

/-- Every path from an arm must reach the same Coalesce before leaving a body. --/
def Graph.rejoinsAt (g : Graph) (target : NodeId) : Nat → PortRef → Bool
  | 0, _ => false
  | fuel + 1, src =>
    let edges := g.edges.filter (·.src == src)
    !g.exits.contains src && !edges.isEmpty && edges.all (fun e =>
      e.dst.node == target || (g.node? e.dst.node).any (fun n =>
        !n.outputs.isEmpty && n.outputs.all (fun p => g.rejoinsAt target fuel ⟨n.id, p.name⟩)))

def Graph.branchesCoalesced (g : Graph) : Bool := g.nodes.all fun n =>
  match n.kind with
  | .branch _ => g.nodes.any fun join =>
    (match join.kind with | .coalesce => true | _ => false) &&
    n.outputs.all (fun p => g.rejoinsAt join.id g.nodes.length ⟨n.id, p.name⟩)
  | _ => true

abbrev BranchConditions := List (NodeId × PortName)

private def combineConditions (a b : BranchConditions) : Option BranchConditions :=
  let combined := (a ++ b).eraseDups
  if combined.all (fun x => combined.all (fun y => x.1 != y.1 || x.2 == y.2)) then some combined else none

/-- Exact branch-selection conditions for a plain value, apart from runtime failure.
    A validated inner Coalesce removes its own arm condition. Collect produces a
    value even for an empty stream, so it does not inherit an upstream arm. --/
def Graph.outputConditions (g : Graph) : Nat → PortRef → Option BranchConditions
  | 0, _ => none
  | fuel + 1, src => do
    let port ← g.output? src
    if port.kind != .plain then none else do
      let n ← g.node? src.node
      let input := fun (node : Node) (p : Port) =>
        if g.entries.contains ⟨node.id, p.name⟩ then some [] else do
          let edge ← g.edges.find? (fun e => e.dst == ⟨node.id, p.name⟩)
          g.outputConditions fuel edge.src
      let allInputs := fun (node : Node) => node.inputs.foldlM (fun required p => do
        combineConditions required (← input node p)) []
      match n.kind with
      | .leaf .. | .waitAll | .loop .. | .subworkflow _ => allInputs n
      | .branch arms =>
        if !arms.contains src.port then none else do
          combineConditions (← allInputs n) [(n.id, src.port)]
      | .collect => some []
      | .coalesce => do
        if n.inputs.isEmpty then none else do
          let actual ← n.inputs.mapM (input n)
          g.nodes.findSome? fun source => do
            let .branch arms := source.kind | none
            if !actual.all (fun condition => condition.any (·.1 == source.id)) then none else do
              let base ← allInputs source
              let origins := actual.map fun condition => arms.filter fun arm =>
                let expected := (base ++ [(source.id, arm)]).eraseDups
                condition.length == expected.length && condition.all expected.contains
              if origins.all (·.length == 1) && unique origins && origins.length == arms.length then some base else none
      | _ => none

/-- Independent inputs, repeated arms, and additional incompatible branch gates are invalid. --/
def Graph.exclusiveCoalesce (g : Graph) (join : Node) : Bool :=
  join.outputs.head?.any (fun p => (g.outputConditions (g.nodes.length + 1) ⟨join.id, p.name⟩).isSome)

def Graph.validateEdge (g : Graph) (e : Edge) : Except String Unit := do
  match g.output? e.src, g.input? e.dst with
  | some a, some b => unless a.kind == b.kind do throw "edge port kinds differ"
  | _, _ => throw "edge references an unknown port"

def Graph.validateEntry (g : Graph) (p : PortRef) : Except String Unit := do
  unless (g.input? p).isSome do throw "unknown entry port"

def Graph.validateExit (g : Graph) (p : PortRef) : Except String Unit := do
  unless (g.output? p).isSome do throw "unknown exit port"

def Graph.validateInput (g : Graph) (n : Node) (p : Port) : Except String Unit := do
  let ref := { node := n.id, port := p.name : PortRef }
  let count := (g.edges.filter (·.dst == ref)).length + (if g.entries.contains ref then 1 else 0)
  unless count == 1 do throw s!"input must have exactly one source: {n.id}.{p.name}"

def Graph.validateShape (g : Graph) (n : Node) : Except String Unit := do
  unless !n.id.isEmpty && unique (n.inputs.map (·.name)) && unique (n.outputs.map (·.name)) &&
    (n.inputs ++ n.outputs).all (fun p => !p.name.isEmpty) do throw "invalid port or node name"
  unless n.shapeOK do throw s!"invalid port shape: {n.id}"
  if n.kind matches .coalesce then
    unless g.exclusiveCoalesce n do throw s!"Coalesce inputs must correspond to distinct arms of one Branch: {n.id}"
  let _ ← n.inputs.mapM (g.validateInput n)
  pure ()

mutual
def Graph.validate (g : Graph) (isBody : Bool := false) : Except String Unit := do
  unless unique (g.nodes.map (·.id)) do throw "duplicate node id"
  unless unique g.entries && unique g.exits do throw "duplicate graph boundary"
  unless acyclicAux g.edges g.nodes.length (g.nodes.map (·.id)) do throw "graph contains a cycle"
  unless !isBody || g.branchesCoalesced do throw "body Branch must rejoin through Coalesce"
  let _ ← g.nodes.attach.mapM fun n => g.validateNode n.val
  let _ ← g.edges.mapM g.validateEdge
  let _ ← g.entries.mapM g.validateEntry
  let _ ← g.exits.mapM g.validateExit
  pure ()
termination_by 2 * sizeOf g
decreasing_by
  have smaller := List.sizeOf_lt_of_mem n.property
  cases g
  simp_all
  omega

def Graph.validateNode (g : Graph) (n : Node) : Except String Unit := do
  g.validateShape n
  match _kind : n.kind with
  | .loop body _ | .subworkflow body | .forEach body => body.validate true
  | _ => pure ()
termination_by 2 * sizeOf n + 1
decreasing_by
  all_goals
    cases n
    simp_all
    omega
end

/-- The same check is used at every external graph boundary. --/
def Graph.WellFormed (g : Graph) : Prop := g.validate = .ok ()

partial def graphToJson (g : Graph) : Json :=
  let nodeJson (n : Node) :=
    let (tag, fields) : String × List (String × Json) := match n.kind with
      | .leaf r c => ("leaf", [("retry", toJson r), ("concurrency", toJson c)])
      | .waitAll => ("waitAll", [])
      | .branch a => ("branch", [("arms", toJson a)])
      | .coalesce => ("coalesce", [])
      | .loop b m => ("loop", [("body", graphToJson b), ("maxIterations", toJson m)])
      | .subworkflow b => ("subworkflow", [("body", graphToJson b)])
      | .forEach b => ("forEach", [("body", graphToJson b)])
      | .collect => ("collect", [])
      | .filter => ("filter", [])
      | .merge => ("merge", [])
    Json.mkObj [("id", toJson n.id), ("kind", Json.mkObj (("type", toJson tag) :: fields)), ("inputs", toJson n.inputs), ("outputs", toJson n.outputs)]
  Json.mkObj [("nodes", toJson (g.nodes.map nodeJson)), ("edges", toJson g.edges), ("entries", toJson g.entries), ("exits", toJson g.exits)]

partial def graphFromJson (j : Json) : Except String Graph := do
  let ns : List Json ← j.getObjValAs? _ "nodes"
  let nodes : List Node ← ns.mapM fun n => do
    let k ← n.getObjVal? "kind"
    let tag : String ← k.getObjValAs? _ "type"
    let kind ← (match tag with
      | "leaf" => do return NodeKind.leaf (← k.getObjValAs? _ "retry") (← k.getObjValAs? _ "concurrency")
      | "waitAll" => pure .waitAll
      | "branch" => do return .branch (← k.getObjValAs? _ "arms")
      | "coalesce" => pure .coalesce
      | "loop" => do return .loop (← graphFromJson (← k.getObjVal? "body")) (← k.getObjValAs? _ "maxIterations")
      | "subworkflow" => do return .subworkflow (← graphFromJson (← k.getObjVal? "body"))
      | "forEach" => do return .forEach (← graphFromJson (← k.getObjVal? "body"))
      | "collect" => pure .collect
      | "filter" => pure .filter
      | "merge" => pure .merge
      | _ => throw s!"unknown node kind: {tag}" : Except String NodeKind)
    let id ← n.getObjValAs? _ "id"
    let inputs ← n.getObjValAs? _ "inputs"
    let outputs ← n.getObjValAs? _ "outputs"
    return { id, kind, inputs, outputs : Node }
  let edges ← j.getObjValAs? _ "edges"
  let entries ← j.getObjValAs? _ "entries"
  let exits ← j.getObjValAs? _ "exits"
  return { nodes, edges, entries, exits }
instance : ToJson Graph := ⟨graphToJson⟩
instance : FromJson Graph := ⟨graphFromJson⟩
end Suimon
