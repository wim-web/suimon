import Suimon.Theorems.NodeEval

namespace Suimon
open Semantics Effects

def childPaths (s : State) (P : Path) (n : Node) : List Path :=
  match n.kind with
  | .subworkflow _ => [childPath P n.id none 0]
  | .forEach _ => (((stateInputs s P n).head?.map (·.2)).getD []).map fun y => childPath P n.id (some y) 0
  | .loop _ _ => (List.range (loopCount s P n.id)).map fun k => childPath P n.id none (k + 1)
  | _ => []

def ChildShape (s : State) (P : Path) (n : Node) (i : Instance) (f : Frame) : Prop :=
  (∃ body, n.kind = .subworkflow body ∧ i.trigger = none ∧ f.path = childPath P n.id none 0 ∧ f.graph = body) ∨
  (∃ body y, n.kind = .forEach body ∧ i.trigger = some y ∧ f.path = childPath P n.id (some y) 0 ∧ f.graph = body ∧
    y ∈ (((stateInputs s P n).head?.map (·.2)).getD [])) ∨
  (∃ body limit k, n.kind = .loop body limit ∧ i.trigger = none ∧ f.path = childPath P n.id none k ∧ f.graph = body ∧
    1 ≤ k ∧ k ≤ i.iteration)

theorem forEach_item_input {s : State} {P : Path} {g : Graph} (sc : Scope s P g)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (c : Channel) (memberC : c ∈ s.channels) (pathC : c.path = P) (exitC : c.exit = false)
    (nodeC : c.edge.dst.node = n.id) (y : ItemId) (memberY : y ∈ c.items) :
    y ∈ (((stateInputs s P n).head?.map (·.2)).getD []) := by
  obtain ⟨p, q, ins, _, _⟩ := forEach_ports sc n memberN body kind
  obtain ⟨p', memberP', portC, _⟩ := sc.input_port n memberN c memberC pathC exitC nodeC
  have pp : p' = p := by simpa only [ins, List.mem_singleton] using memberP'
  subst p'
  obtain ⟨d, _, found, _, _, _, _, _, uniqueD⟩ := sc.input_channel n memberN p (by simp [ins])
  have same := uniqueD c memberC pathC exitC (PortRef.ext_of nodeC portC)
  subst d
  simp only [stateInputs, ins, List.map_cons, List.map_nil, List.head?_cons, found, Option.map_some, Option.getD_some]
  exact (sortedItems_perm c.items).mem_iff.mpr memberY

/-- Every immediate child in a completed frame is owned by an actual retained
    instance of its parent node, at the trigger/iteration that opened it. --/
theorem immediate_child_owner (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : last.status = .succeeded) (f : Frame) (memberF : f ∈ last.frames)
    (segment : String) (immediate : f.path = P ++ [segment]) :
    ∃ n ∈ g.nodes, ∃ i ∈ last.instances, i.path = P ∧ i.node = n.id ∧ i.status ≠ .cancelled ∧
      f.owner = some i.id ∧ ChildShape last P n i f := by
  have scL := fs.scope.persist run
  have absent0 : ∀ old ∈ s0.frames, old.path ≠ f.path := by
    intro old memberOld eq
    have same := fs.noDescendants old memberOld (by rw [eq, immediate]; exact List.prefix_append _ _)
    have lengths := congrArg List.length (eq.symm.trans same)
    simp only [immediate, List.length_append, List.length_singleton] at lengths
    omega
  obtain ⟨pre, op, post, t, t', child, _, head, allowed, accepted, rest, safeT, _, memberChild, pathChild, opened⟩ :=
    frame_origin run fs.scope.safe f memberF absent0
  have safeNext := preserves_invariants t t' op safeT accepted
  have definitions := rest.frame_definition child memberChild scL.distinct f memberF pathChild.symm
  have scT := fs.scope.persist head
  have parentPath : ∀ (parent : Path) (id : String) (iteration : Nat), child.path = parent ++ [identity [id, toString iteration]] → parent = P := by
    intro parent id iteration path
    have eq := path.symm.trans (pathChild.trans immediate)
    simpa only [List.dropLast_concat] using congrArg List.dropLast eq
  have resolve : ∀ N n, getNode t P N = .ok n → n ∈ g.nodes := by
    intro N n got
    have found := getNode_node? t P N n got
    rw [scT.node?] at found
    exact List.mem_of_find?_eq_some found
  have retain : ∀ i ∈ t'.instances, i.path = P → i.status ≠ .cancelled → child.owner = some i.id →
      ∃ j ∈ last.instances, j.binding = i.binding ∧ j.path = P ∧ j.node = i.node ∧ j.status ≠ .cancelled ∧ f.owner = some j.id := by
    intro i memberI pathI notCancelled owner
    obtain ⟨j, memberJ, bindingJ⟩ := rest.retains_binding safeNext i memberI
    have idJ := congrArg Prod.fst bindingJ
    exact ⟨j, memberJ, bindingJ, (Instance.binding_path bindingJ).trans pathI, Instance.binding_node bindingJ,
      rest.nonCancelled safeNext finished i memberI notCancelled j memberJ idJ,
      definitions.2.1.trans (owner.trans (congrArg some idJ).symm)⟩
  rcases opened with
      ⟨R, N, n, inputs, body, iteration, _, got, plain, kinds, shape, _, _, instances⟩ |
      ⟨R, N, y, n, body, c, _, got, kind, incoming, pending, shape, _, _, instances, _⟩ |
      ⟨inst, old, n, body, limit, prior, items, y, _, found, waiting, got, kind, _, _, _, _, shape, _, _, instances⟩ |
      ⟨inst, old, n, body, limit, prior, items, _, found, failed, got, kind, _, _, _, shape, _, _, instances⟩
  · obtain ⟨path, graph, owner, _⟩ := shape
    have eqR := parentPath R _ iteration path
    subst R
    have memberN := resolve N n got
    let initial := { makeInstance P n .waitingInputs inputs with iteration }
    obtain ⟨j, memberJ, bindingJ, pathJ, nodeJ, notCancelled, ownerJ⟩ := retain initial
      (by rw [instances]; simp [initial]) rfl (by change InstanceStatus.waitingInputs ≠ .cancelled; decide) owner
    refine ⟨n, memberN, j, memberJ, pathJ, nodeJ, notCancelled, ownerJ, ?_⟩
    have triggerJ : j.trigger = none := Instance.binding_trigger bindingJ
    have pathF : f.path = childPath P n.id none iteration := by rw [← pathChild, path]; rfl
    rcases kinds with ⟨kind, zero⟩ | ⟨limit, kind, one⟩
    · exact .inl ⟨body, kind, triggerJ, by simpa only [zero] using pathF, definitions.1.trans graph⟩
    · have bound := (rest.iteration_evolves safeNext initial (by rw [instances]; simp [initial]) j memberJ
        (congrArg Prod.fst bindingJ)).1
      exact .inr (.inr ⟨body, limit, iteration, kind, triggerJ, pathF, definitions.1.trans graph, by omega, bound⟩)
  · obtain ⟨path, graph, owner, _⟩ := shape
    have eqR := parentPath R _ 0 path
    subst R
    have memberN := resolve N n got
    let initial := makeInstance P n .waitingInputs [("item", y)] (some y)
    obtain ⟨j, memberJ, bindingJ, pathJ, nodeJ, notCancelled, ownerJ⟩ := retain initial
      (by rw [instances]; simp [initial]) rfl (by change InstanceStatus.waitingInputs ≠ .cancelled; decide) owner
    refine ⟨n, memberN, j, memberJ, pathJ, nodeJ, notCancelled, ownerJ, .inr (.inl ⟨body, y, kind,
      Instance.binding_trigger bindingJ, by rw [← pathChild, path]; rfl, definitions.1.trans graph, ?_⟩)⟩
    have inChannels : c ∈ t.channels := (List.mem_filter.mp (List.mem_of_mem_head? incoming)).1
    have fields := (List.mem_filter.mp (List.mem_of_mem_head? incoming)).2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
    have full : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (op :: post) last := .cons allowed accepted rest
    obtain ⟨d, memberD, _, layoutD, tokens⟩ := run_image full safeT c inChannels
    obtain ⟨_, edgeD, pathD, _, exitD, _⟩ := Channel.layout_fields layoutD
    have present : y ∈ d.items := by
      rw [Effects.item_mem]
      exact tokens.subset (List.drop_subset _ _ (List.mem_of_mem_head? pending))
    have nodeC : c.edge.dst.node = n.id := fields.2.trans (getNode_id t P N n got).symm
    exact forEach_item_input scL n memberN body kind d memberD (pathD.trans fields.1.1) (exitD.trans fields.1.2)
      (by rw [edgeD]; exact nodeC) y present
  · obtain ⟨path, graph, owner, _⟩ := shape
    have pathOld := parentPath old.path _ (old.iteration + 1) path
    rw [pathOld] at got
    have memberN := resolve old.node n got
    have nodeOld := (getNode_id t P old.node n got).symm
    obtain ⟨idOld, triggerOld, _, _⟩ := loop_instance_shape oracle head fs n memberN body limit kind
      old (instance?_mem found) pathOld nodeOld (by rw [waiting]; decide)
    let initial := { old with iteration := old.iteration + 1 }
    have memberInitial : initial ∈ t'.instances := by rw [instances]; exact setInstance_self_mem t old initial (instance?_mem found) rfl
    obtain ⟨j, memberJ, bindingJ, pathJ, nodeJ, notCancelled, ownerJ⟩ := retain initial memberInitial pathOld
      (by change old.status ≠ .cancelled; rw [waiting]; decide) owner
    have bound := (rest.iteration_evolves safeNext initial memberInitial j memberJ (congrArg Prod.fst bindingJ)).1
    refine ⟨n, memberN, j, memberJ, pathJ, nodeJ.trans nodeOld, notCancelled, ownerJ,
      .inr (.inr ⟨body, limit, old.iteration + 1, kind, (Instance.binding_trigger bindingJ).trans triggerOld, ?_,
      definitions.1.trans graph, by omega, bound⟩)⟩
    rw [← pathChild, path, pathOld, idOld]; rfl
  · obtain ⟨path, graph, owner, _⟩ := shape
    have pathOld := parentPath old.path _ (old.iteration + 1) path
    rw [pathOld] at got
    have memberN := resolve old.node n got
    have nodeOld := (getNode_id t P old.node n got).symm
    obtain ⟨idOld, triggerOld, _, _⟩ := loop_instance_shape oracle head fs n memberN body limit kind
      old (instance?_mem found) pathOld nodeOld (by rw [failed]; decide)
    let initial := { old with status := .waitingInputs, extraIterations := old.extraIterations + 1, iteration := old.iteration + 1 }
    have memberInitial : initial ∈ t'.instances := by rw [instances]; exact setInstance_self_mem t old initial (instance?_mem found) rfl
    obtain ⟨j, memberJ, bindingJ, pathJ, nodeJ, notCancelled, ownerJ⟩ := retain initial memberInitial pathOld
      (by change InstanceStatus.waitingInputs ≠ .cancelled; decide) owner
    have bound := (rest.iteration_evolves safeNext initial memberInitial j memberJ (congrArg Prod.fst bindingJ)).1
    refine ⟨n, memberN, j, memberJ, pathJ, nodeJ.trans nodeOld, notCancelled, ownerJ,
      .inr (.inr ⟨body, limit, old.iteration + 1, kind, (Instance.binding_trigger bindingJ).trans triggerOld, ?_,
      definitions.1.trans graph, by omega, bound⟩)⟩
    rw [← pathChild, path, pathOld, idOld]; rfl

end Suimon
