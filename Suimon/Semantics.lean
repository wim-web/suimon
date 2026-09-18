import Suimon.Execution

namespace Suimon.Semantics

abbrev PortData := List (PortName × List ItemId)
abbrev ChannelData := List (String × List ItemId)

structure Result where
  outputs : List (List ItemId)
  channels : ChannelData

structure NodeResult where
  outputs : List Output
  children : ChannelData := []

abbrev Values := NodeId → NodeResult

def canonical (items : List ItemId) : List ItemId := sortedItems items.eraseDups

def inputData (g : Graph) (inputs : List Input) (values : Values) (n : Node) : PortData :=
  n.inputs.map fun p =>
    let ref : PortRef := ⟨n.id, p.name⟩
    let items := if g.entries.contains ref then
        ((inputs.find? (·.entry == ref)).map (·.items)).getD []
      else match g.edges.find? (·.dst == ref) with
        | none => []
        | some e => outputItems (values e.src.node).outputs e.src.port
    (p.name, canonical items)

def plainValues (inputs : PortData) : List (PortName × ItemId) :=
  inputs.map fun (port, items) => (port, items.headD "")

def suppressed (n : Node) (inputs : PortData) : Bool :=
  allKind n.inputs .plain && match n.kind with
    | .coalesce => !inputs.isEmpty && inputs.all (·.2.isEmpty)
    | _ => inputs.any (·.2.isEmpty)

def ports (n : Node) (items : PortName → List ItemId) : List Output :=
  n.outputs.map fun p => { port := p.name, items := canonical (items p.name) }

def bodyInputs (g : Graph) (items : List ItemId) : List Input :=
  (g.entries.zip items).map fun (entry, item) => { entry, items := [item] }

def childPath (path : Path) (node : NodeId) (trigger : Option ItemId) (iteration : Nat) : Path :=
  path ++ [identity [instanceId path node trigger, toString iteration]]

def inputChannel (g : Graph) (path : Path) (node port : String) : String :=
  (((({ path, graph := g : Frame }).channels).find? (fun c => !c.exit && c.edge.dst == ⟨node, port⟩)).map (·.id)).getD ""

/-- Pure local equations for nodes without child executions. --/
def primitive (oracle : ScopedOracle) (g : Graph) (path : Path) (n : Node) (inputs : PortData) : Option NodeResult :=
  if suppressed n inputs then some { outputs := ports n (fun _ => []) } else
  let values := plainValues inputs
  let first := (values.head?.map (·.2)).getD ""
  match n.kind with
  | .leaf .. => some { outputs := ports n (outputItems ((oracle path).leaf n.id values)) }
  | .waitAll => some { outputs := ports n (fun _ =>
      [derivedItem "record" path n.id (values.map fun (p, i) => identity [p, i])]) }
  | .branch _ => some { outputs := ports n (fun port =>
      if port == (oracle path).branch n.id first then [first] else []) }
  | .coalesce => some { outputs := ports n (fun _ =>
      ((inputs.find? (fun p => !p.2.isEmpty)).map (·.2)).getD []) }
  | .collect => some { outputs := ports n (fun _ =>
      [derivedItem "list" path n.id (sortedItems ((inputs.head?.map (·.2)).getD []))]) }
  | .filter => some { outputs := ports n (fun _ =>
      ((inputs.head?.map (·.2)).getD []).filter ((oracle path).filter n.id)) }
  | .merge => some { outputs := ports n (fun _ => inputs.flatMap fun (port, items) =>
      items.map fun item => derivedItem "merge" path n.id [inputChannel g path n.id port, item]) }
  | .loop .. | .subworkflow .. | .forEach .. => none

def assemble (g : Graph) (path : Path) (inputs : List Input) (values : Values) : Result :=
  let channels := ({ path, graph := g : Frame }).channels.map fun c =>
    (c.id, canonical (if c.entry then ((inputs.find? (·.entry == c.edge.dst)).map (·.items)).getD []
      else outputItems (values c.edge.src.node).outputs c.edge.src.port))
  { outputs := g.exits.map fun p => outputItems (values p.node).outputs p.port
    channels := (channels ++ g.nodes.flatMap (fun n => (values n.id).children)).mergeSort (fun a b => a.1 ≤ b.1) }

/-- A structural DAG certificate. A validator theorem supplies this certificate;
    it contains graph facts only, never a determinism assumption. --/
structure Topology (g : Graph) where
  rank : NodeId → Nat
  sources : ∀ e ∈ g.edges, e.src.node ∈ g.nodes.map (·.id)
  exits : ∀ p ∈ g.exits, p.node ∈ g.nodes.map (·.id)
  increasing : ∀ e ∈ g.edges, rank e.src.node < rank e.dst.node

mutual
/-- Completed dataflow equations, independent of leases, attempts and schedules. --/
inductive GraphEval (oracle : ScopedOracle) : Graph → Path → List Input → Result → Prop
  | graph {g path inputs values}
      (topology : Topology g)
      (nodes : ∀ n ∈ g.nodes, NodeEval oracle g path n (inputData g inputs values n) (values n.id)) :
      GraphEval oracle g path inputs (assemble g path inputs values)

inductive NodeEval (oracle : ScopedOracle) : Graph → Path → Node → PortData → NodeResult → Prop
  | primitive {g path n inputs result} (computed : primitive oracle g path n inputs = some result) :
      NodeEval oracle g path n inputs result
  | sub {g path n inputs body result}
      (kind : n.kind = .subworkflow body) (awake : suppressed n inputs = false)
      (child : GraphEval oracle body (childPath path n.id none 0)
        (bodyInputs body ((plainValues inputs).map (·.2))) result) :
      NodeEval oracle g path n inputs {
        outputs := (n.outputs.zip result.outputs).map (fun (p, items) => { port := p.name, items })
        children := result.channels }
  | forEach {g path n inputs body} {results : ItemId → Result}
      (kind : n.kind = .forEach body) (awake : suppressed n inputs = false)
      (children : ∀ item ∈ ((inputs.head?.map (·.2)).getD []),
        GraphEval oracle body (childPath path n.id (some item) 0) (bodyInputs body [item]) (results item)) :
      NodeEval oracle g path n inputs {
        outputs := ports n (fun _ => ((inputs.head?.map (·.2)).getD []).flatMap (fun item => (results item).outputs.flatten))
        children := ((inputs.head?.map (·.2)).getD []).flatMap (fun item => (results item).channels) }
  | loop {g path n inputs body limit result channels}
      (kind : n.kind = .loop body limit) (awake : suppressed n inputs = false)
      (iterations : LoopEval oracle body path n.id 1
        (((plainValues inputs).head?.map (·.2)).getD "") result channels) :
      NodeEval oracle g path n inputs { outputs := ports n (fun _ => [result]), children := channels }

inductive LoopEval (oracle : ScopedOracle) : Graph → Path → NodeId → Nat → ItemId → ItemId → ChannelData → Prop
  | stop {body path node iteration input result item}
      (child : GraphEval oracle body (childPath path node none iteration) (bodyInputs body [input]) result)
      (output : result.outputs = [[item]]) (done : (oracle path).loop node iteration item = true) :
      LoopEval oracle body path node iteration input item result.channels
  | next {body path node iteration input result item last channels}
      (child : GraphEval oracle body (childPath path node none iteration) (bodyInputs body [input]) result)
      (output : result.outputs = [[item]]) (again : (oracle path).loop node iteration item = false)
      (tail : LoopEval oracle body path node (iteration + 1) item last channels) :
      LoopEval oracle body path node iteration input last (result.channels ++ channels)
end

end Suimon.Semantics
