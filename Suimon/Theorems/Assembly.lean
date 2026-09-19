import Suimon.Theorems.Loop

namespace Suimon
open Semantics Effects

theorem node_output_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (c : Channel) (memberC : c ∈ last.channels)
    (pathC : c.path = P) (entryC : c.entry = false) (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  cases kind : n.kind with
  | leaf retry concurrency => exact leaf_value oracle run fs finished n memberN retry concurrency kind c memberC pathC entryC srcC
  | waitAll => exact waitAll_value oracle run fs finished n memberN kind c memberC pathC entryC srcC
  | branch arms => exact branch_value oracle run fs finished n memberN arms kind c memberC pathC entryC srcC
  | coalesce => exact coalesce_value oracle run fs finished n memberN kind c memberC pathC entryC srcC
  | collect => exact collect_value oracle run fs finished n memberN kind c memberC pathC entryC srcC
  | filter => exact filter_value oracle run fs finished n memberN kind c memberC pathC entryC srcC
  | merge => exact merge_value oracle run fs finished n memberN kind c memberC pathC entryC srcC
  | subworkflow body => exact sub_value oracle run fs finished n memberN body kind c memberC pathC entryC srcC
  | forEach body => exact forEach_value oracle run fs finished n memberN body kind c memberC pathC entryC srcC
  | loop body limit => exact loop_value oracle run fs finished n memberN body limit kind c memberC pathC entryC srcC

theorem frameValues_node (oracle : ScopedOracle) {s : State} {g : Graph} {P : Path}
    (sc : Scope s P g) (n : Node) (member : n ∈ g.nodes) :
    frameValues oracle s g P n.id = nodeValue oracle s g P n := by
  simp only [frameValues, g.node?_of_mem sc.nodes_nodup n member]

theorem FrameStart.entry_bag {allows : State → Op → Prop} {s0 last : State} {ops : List Op}
    {P : Path} {g : Graph} {inputs : List Input} (run : ConformingSteps allows s0 ops last)
    (fs : FrameStart s0 P g inputs) (c : Channel) (memberC : c ∈ last.channels)
    (pathC : c.path = P) (entryC : c.entry = true) :
    bag c = canonical (((inputs.find? (·.entry == c.edge.dst)).map (·.items)).getD []) := by
  obtain ⟨c0, member0, id0, edge0, path0, entry0, _, _, _⟩ := fs.origin run c memberC pathC
  obtain ⟨closed0, items0⟩ := fs.seeded c0 member0 (path0.trans pathC) (entry0.trans entryC)
  obtain ⟨d, memberD, idD, placedD⟩ := run.retains_closed_channel fs.scope.safe c0 member0 closed0
  have same := unique_channel (run.invariants fs.scope.safe) memberD memberC (idD.trans id0)
  subst d
  have itemsEq : c.items = c0.items := by simp only [Channel.items, placedD]
  change sortedItems c.items = _
  rw [itemsEq]
  change bag c0 = _
  rw [items0, edge0]

/-- The state supplies precisely the input bags used by the graph equations. --/
theorem frame_input_equations (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) :
    inputData g inputs0 (frameValues oracle last g P) n = stateInputs last P n := by
  have sc := fs.scope.persist run
  obtain ⟨isBody, valid⟩ := sc.valid
  unfold inputData stateInputs
  apply List.map_congr_left
  intro p memberP
  obtain ⟨c, memberC, found, pathC, exitC, dstC, entrySource, edgeSource, _⟩ := sc.input_channel n memberN p memberP
  dsimp only
  rw [found]
  simp only [Option.map_some, Option.getD_some]
  cases entry : c.entry with
  | true =>
    rw [entrySource entry]
    simp only [↓reduceIte]
    have seeded := fs.entry_bag run c memberC pathC entry
    rw [dstC] at seeded
    rw [seeded]
  | false =>
    obtain ⟨noEntry, memberEdge, onlyEdge⟩ := edgeSource entry
    have findEdge : g.edges.find? (fun e => e.dst == ⟨n.id, p.name⟩) = some c.edge := by
      rw [← List.head?_filter, onlyEdge]
      rfl
    rw [noEntry]
    simp only [Bool.false_eq_true, ↓reduceIte, findEdge]
    obtain ⟨source, memberSource, sourceId⟩ := List.mem_map.mp
      (g.validateEdge_nodes c.edge (g.validate_edges isBody valid c.edge memberEdge)).1
    have value := node_output_value oracle run fs finished source memberSource c memberC pathC entry sourceId.symm
    rw [← sourceId, frameValues_node oracle sc source memberSource]
    exact congrArg (fun items => (p.name, items)) value.symm

def CanonicalOutputs (outputs : List Output) : Prop := ∀ out ∈ outputs, canonical out.items = out.items

theorem ports_canonical (n : Node) (items : PortName → List ItemId) : CanonicalOutputs (ports n items) := by
  intro out member
  obtain ⟨p, _, eq⟩ := List.mem_map.mp member
  subst out
  exact canonical_idem _

theorem exitItems_canonical {s : State} (safe : Invariants s) (P : Path) (g : Graph) :
    ∀ items ∈ exitItems s P g, canonical items = items := by
  intro items member
  obtain ⟨p, _, eq⟩ := List.mem_map.mp member
  subst items
  cases found : exitChannel? s P p with
  | none => simp [found, canonical, sortedItems]
  | some c =>
    simp only [found, Option.map_some, Option.getD_some]
    have memberC := List.mem_of_find?_eq_some found
    exact canonical_sortedItems (items_nodup_of_invariants safe memberC)

theorem primitive_canonical (oracle : ScopedOracle) (g : Graph) (P : Path) (n : Node) (inputs : PortData)
    (result : NodeResult) (computed : primitive oracle g P n inputs = some result) : CanonicalOutputs result.outputs := by
  unfold primitive at computed
  split at computed
  · cases computed
    intro out member
    obtain ⟨p, _, same⟩ := List.mem_map.mp member
    subst out
    exact canonical_idem _
  · cases kind : n.kind <;> simp only [kind] at computed <;> first
    | contradiction
    | (cases computed
       intro out member
       obtain ⟨p, _, same⟩ := List.mem_map.mp member
       subst out
       exact canonical_idem _)

theorem compound_canonical (s : State) (safe : Invariants s) (P : Path) (n : Node) :
    CanonicalOutputs (compoundValue s P n).outputs := by
  cases kind : n.kind <;> simp only [compoundValue, kind]
  case subworkflow body =>
    intro out member
    obtain ⟨⟨p, items⟩, pairMember, same⟩ := List.mem_map.mp member
    subst out
    exact exitItems_canonical safe _ body items (List.of_mem_zip pairMember).2
  case forEach body => exact ports_canonical n _
  case loop body limit => exact ports_canonical n _
  all_goals intro out member; contradiction

theorem nodeValue_canonical (oracle : ScopedOracle) (s : State) (safe : Invariants s) (g : Graph) (P : Path) (n : Node) :
    CanonicalOutputs (nodeValue oracle s g P n).outputs := by
  unfold nodeValue
  cases computed : primitive oracle g P n (stateInputs s P n) with
  | none => exact compound_canonical s safe P n
  | some result => exact primitive_canonical oracle g P n _ result computed

theorem outputItems_canonical (outputs : List Output) (canonical : CanonicalOutputs outputs) (port : PortName) :
    Semantics.canonical (outputItems outputs port) = outputItems outputs port := by
  unfold outputItems
  cases found : outputs.find? (·.port == port) with
  | none => simp [Semantics.canonical, sortedItems]
  | some out => exact canonical out (List.mem_of_find?_eq_some found)

/-- The exit projection of the assembly is the exit projection of the state. --/
theorem frame_exit_equations (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true) :
    (assemble g P inputs0 (frameValues oracle last g P)).outputs = exitItems last P g := by
  have sc := fs.scope.persist run
  obtain ⟨isBody, valid⟩ := sc.valid
  apply List.map_congr_left
  intro p memberP
  obtain ⟨c, memberC, found, pathC, _, entryC, srcC, _⟩ := sc.exit_channel p memberP
  obtain ⟨n, memberN, nodeEq⟩ := List.mem_map.mp (g.validateExit_node p (g.validate_exits isBody valid p memberP))
  have value := node_output_value oracle run fs finished n memberN c memberC pathC entryC (by rw [srcC, nodeEq])
  rw [srcC, outputItems_canonical _ (nodeValue_canonical oracle last sc.safe g P n) p.port] at value
  change outputItems (frameValues oracle last g P p.node).outputs p.port = ((exitChannel? last P p).map bag).getD []
  rw [found, ← nodeEq, frameValues_node oracle sc n memberN]
  exact value.symm

end Suimon
