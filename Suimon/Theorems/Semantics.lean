import Suimon.Semantics
import Suimon.Theorems.Graph

namespace Suimon.Semantics

theorem topology_of_validate (g : Graph) (body : Bool) (checked : g.validate body = .ok ()) :
    Nonempty (Topology g) := by
  obtain ⟨rank, increasing⟩ := acyclicAux_rank g.edges g.nodes.length (g.nodes.map (·.id))
    (g.validate_acyclic body checked)
  refine ⟨{ rank := rank, sources := ?_, exits := ?_, increasing := ?_ }⟩
  · intro e member
    exact (g.validateEdge_nodes e (g.validate_edges body checked e member)).1
  · intro p member
    exact g.validateExit_node p (g.validate_exits body checked p member)
  · intro e member
    have endpoints := g.validateEdge_nodes e (g.validate_edges body checked e member)
    exact increasing e member endpoints.1 endpoints.2

private theorem flatMap_congr_on {α β : Type} (xs : List α) (f g : α → List β)
    (same : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [same x (by simp), ih (fun y hy => same y (by simp [hy]))]

theorem Topology.induction (g : Graph) (topology : Topology g) (P : NodeId → Prop)
    (stepCase : ∀ n ∈ g.nodes, (∀ e ∈ g.edges, e.dst.node = n.id → P e.src.node) → P n.id) :
    ∀ n ∈ g.nodes, P n.id := by
  have ranked : ∀ rank, ∀ n ∈ g.nodes, topology.rank n.id = rank → P n.id := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro n member level
      apply stepCase n member
      intro e edge target
      obtain ⟨source, sourceMember, sourceName⟩ := List.mem_map.mp (topology.sources e edge)
      have lower : topology.rank source.id < rank := by
        simpa [sourceName, target, level] using topology.increasing e edge
      simpa [sourceName] using ih (topology.rank source.id) lower source sourceMember rfl
  intro n member
  exact ranked _ n member rfl

theorem inputData_congr (g : Graph) (inputs : List Input) (left right : Values) (n : Node)
    (same : ∀ e ∈ g.edges, e.dst.node = n.id → left e.src.node = right e.src.node) :
    inputData g inputs left n = inputData g inputs right n := by
  apply List.map_congr_left
  intro p member
  dsimp
  split
  · rfl
  · cases found : g.edges.find? (fun e => e.dst == ⟨n.id, p.name⟩) with
    | none => rfl
    | some e =>
      have target := List.find?_some found
      have node : e.dst.node = n.id := by
        cases e with
        | mk src dst =>
          cases dst
          simpa [BEq.beq, instBEqPortRef] using (Bool.and_eq_true_iff.mp target).1
      dsimp
      rw [same e (List.mem_of_find?_eq_some found) node]

theorem Topology.channel_source (g : Graph) (topology : Topology g) (path : Path)
    (c : Channel) (member : c ∈ ({ path, graph := g : Frame }).channels)
    (notEntry : c.entry = false) : c.edge.src.node ∈ g.nodes.map (·.id) := by
  simp only [Frame.channels, List.mem_append] at member
  rcases member with (edge | entry) | exit
  · obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp edge
    exact topology.sources pair.1 (List.fst_mem_of_mem_zipIdx inPairs)
  · obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp entry
    contradiction
  · obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp exit
    exact topology.exits pair.1 (List.fst_mem_of_mem_zipIdx inPairs)

theorem assemble_congr (g : Graph) (topology : Topology g) (path : Path) (inputs : List Input)
    (left right : Values) (same : ∀ n ∈ g.nodes, left n.id = right n.id) :
    assemble g path inputs left = assemble g path inputs right := by
  have byName : ∀ name ∈ g.nodes.map (·.id), left name = right name := by
    intro name member
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp member
    exact same n hn
  have outputs : (g.exits.map fun p => outputItems (left p.node).outputs p.port) =
      (g.exits.map fun p => outputItems (right p.node).outputs p.port) := by
    apply List.map_congr_left
    intro p hp
    rw [byName p.node (topology.exits p hp)]
  have channels : (({ path, graph := g : Frame }).channels.map fun c =>
      (c.id, canonical (if c.entry then ((inputs.find? (·.entry == c.edge.dst)).map (·.items)).getD []
        else outputItems (left c.edge.src.node).outputs c.edge.src.port))) =
      (({ path, graph := g : Frame }).channels.map fun c =>
      (c.id, canonical (if c.entry then ((inputs.find? (·.entry == c.edge.dst)).map (·.items)).getD []
        else outputItems (right c.edge.src.node).outputs c.edge.src.port))) := by
    apply List.map_congr_left
    intro c hc
    cases entry : c.entry with
    | true => simp
    | false => simp [byName c.edge.src.node (topology.channel_source g path c hc entry)]
  have children : (g.nodes.flatMap fun n => (left n.id).children) =
      (g.nodes.flatMap fun n => (right n.id).children) :=
    flatMap_congr_on _ _ _ (fun n hn => congrArg NodeResult.children (same n hn))
  simp only [assemble, outputs, channels, children]

/-- Completed equations have one result, including every nested frame. The DAG
    case uses topological induction; ForEach uses each trigger's child proof;
    Loop compares successive body results and the same oracle decision. --/
theorem GraphEval.functional {oracle : ScopedOracle} {g : Graph} {path : Path}
    {inputs : List Input} {result : Result} (evaluation : GraphEval oracle g path inputs result) :
    ∀ other, GraphEval oracle g path inputs other → result = other := by
  induction evaluation using GraphEval.rec
    (motive_2 := fun g path n inputs result _ =>
      ∀ other, NodeEval oracle g path n inputs other → result = other)
    (motive_3 := fun body path node iteration input last channels _ =>
      ∀ other otherChannels, LoopEval oracle body path node iteration input other otherChannels →
        last = other ∧ channels = otherChannels) with
  | @graph g path inputs values topology nodes ih =>
    intro other evaluation
    cases evaluation with
    | @graph _ _ _ otherValues otherTopology otherNodes =>
      apply assemble_congr g topology path inputs values otherValues
      apply topology.induction g (fun id => values id = otherValues id)
      intro n member earlier
      have inputEq := inputData_congr g inputs values otherValues n earlier
      apply ih n member
      rw [inputEq]
      exact otherNodes n member
  | @primitive g path n inputs result computed =>
    rename_i other evaluation
    cases evaluation with
    | primitive computed' => exact Option.some.inj (computed.symm.trans computed')
    | sub kind awake child => simp [primitive, kind, awake] at computed
    | forEach kind awake children => simp [primitive, kind, awake] at computed
    | loop kind awake iterations => simp [primitive, kind, awake] at computed
  | @sub g path n inputs body result kind awake child ih =>
    rename_i other evaluation
    cases evaluation with
    | primitive computed => simp [primitive, kind, awake] at computed
    | sub kind' awake' child' =>
      have bodyEq := kind.symm.trans kind'
      cases bodyEq
      have same := ih _ child'
      cases same
      rfl
    | forEach kind' awake' children' => simp [kind] at kind'
    | loop kind' awake' iterations' => simp [kind] at kind'
  | @forEach g path n inputs body results kind awake children ih =>
    rename_i other evaluation
    cases evaluation with
    | primitive computed => simp [primitive, kind, awake] at computed
    | sub kind' awake' child' => simp [kind] at kind'
    | @forEach _ _ _ _ body' results' kind' awake' children' =>
      have bodyEq := kind.symm.trans kind'
      cases bodyEq
      have same : ∀ item ∈ ((inputs.head?.map (·.2)).getD []), results item = results' item :=
        fun item member => ih item member _ (children' item member)
      have outputs := flatMap_congr_on ((inputs.head?.map (·.2)).getD [])
        (fun item => (results item).outputs.flatten) (fun item => (results' item).outputs.flatten)
        (fun item member => congrArg (fun r : Result => r.outputs.flatten) (same item member))
      have channels := flatMap_congr_on ((inputs.head?.map (·.2)).getD [])
        (fun item => (results item).channels) (fun item => (results' item).channels)
        (fun item member => congrArg Result.channels (same item member))
      simp only [outputs, channels]
    | loop kind' awake' iterations' => simp [kind] at kind'
  | @loop g path n inputs body limit result channels kind awake iterations ih =>
    rename_i other evaluation
    cases evaluation with
    | primitive computed => simp [primitive, kind, awake] at computed
    | sub kind' awake' child' => simp [kind] at kind'
    | forEach kind' awake' children' => simp [kind] at kind'
    | loop kind' awake' iterations' =>
      have bodyEq := kind.symm.trans kind'
      cases bodyEq
      obtain ⟨sameResult, sameChannels⟩ := ih _ _ iterations'
      cases sameResult
      cases sameChannels
      rfl
  | @stop body path node iteration input result item child output done ih =>
    rename_i other otherChannels evaluation
    cases evaluation with
    | stop child' output' done' =>
      have resultEq := ih _ child'
      cases resultEq
      have itemEq : item = other := by simpa using output.symm.trans output'
      exact ⟨itemEq, rfl⟩
    | next child' output' again' tail' =>
      have resultEq := ih _ child'
      cases resultEq
      have itemEq := output.symm.trans output'
      simp only [List.cons.injEq, and_true] at itemEq
      cases itemEq
      simp [done] at again'
  | @next body path node iteration input result item last channels child output again tail ihChild ihTail =>
    rename_i other otherChannels evaluation
    cases evaluation with
    | stop child' output' done' =>
      have resultEq := ihChild _ child'
      cases resultEq
      have itemEq : item = other := by simpa using output.symm.trans output'
      subst other
      simp [again] at done'
    | next child' output' again' tail' =>
      have resultEq := ihChild _ child'
      cases resultEq
      have itemEq := output.symm.trans output'
      simp only [List.cons.injEq, and_true] at itemEq
      cases itemEq
      obtain ⟨lastEq, channelsEq⟩ := ihTail _ _ tail'
      exact ⟨lastEq, congrArg (result.channels ++ ·) channelsEq⟩

end Suimon.Semantics
