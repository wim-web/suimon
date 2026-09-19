import Suimon.Theorems.SubEval

namespace Suimon
open Semantics Effects

theorem forEach_controller_event (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph)
    (kind : n.kind = .forEach body) (i : Instance) (memberI : i ∈ last.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) (triggerI : i.trigger = none) (succeeded : i.status = .succeeded) :
    ∃ pre post u u', ops = pre ++ .propagateEos P n.id :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre u ∧
      oracleConforms oracle u (.propagateEos P n.id) = true ∧ step u (.propagateEos P n.id) = .ok u' ∧
      transition u (.propagateEos P n.id) = .ok u' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) u' post last := by
  have safe0 := fs.scope.safe
  have safeLast := run.invariants safe0
  have absent0 : ∀ j ∈ s0.instances, j.id ≠ i.id := by
    intro j memberJ eq
    obtain ⟨_, pathEq, _, _⟩ := run.input_snapshot safe0 j i memberJ memberI eq
    exact fs.noInstances j memberJ (by rw [← pathEq, pathI]; exact List.prefix_refl _)
  obtain ⟨pre, op, post, u, u', j, schedule, head, allowed, accepted, rest, safeU, absentU, memberJ, idJ, bindJ, created⟩ :=
    instance_created run safe0 i memberI absent0
  have nodeU := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  have pathJ := (Instance.binding_path bindJ).trans pathI
  have nodeJ := (Instance.binding_node bindJ).trans nodeI
  rcases created with
      ⟨P', N', n', inputs, opEq, hn, hi, ⟨r, cc, kind', eq⟩ | ⟨body', iteration, kinds, eq⟩⟩
    | ⟨P', N', n', inputs, _, hn, kind', hi, eq⟩
    | ⟨P', N', arm, n', arms, inputs, _, hn, kind', hi, eq⟩
    | ⟨P', N', n', c, _, hn, kind', hc, eq⟩
    | ⟨P', N', e, x, n', c, _, hn, kind', hc, eq⟩
    | ⟨P', N', n', ⟨x, k, _, kind'⟩ | ⟨e, x, _, kind'⟩, hn, eq⟩
    | ⟨P', N', n', opEq, hn, kind', eq⟩
    | ⟨P', N', n', _, hn, eq⟩
    | ⟨P', N', x, n', body', _, hn, kind', eq⟩
  all_goals
    have pathEq : P' = P := by rw [eq] at pathJ; exact pathJ
    have idEq : n'.id = n.id := by rw [eq] at nodeJ; exact nodeJ
    subst P'
    have NEq : N' = n.id := (getNode_id u P N' n' hn).symm.trans idEq
    subst N'
    have sameN : n' = n := node?_of_getNode nodeU hn
    subst n'
  · rw [kind] at kind'; cases kind'
  · rcases kinds with ⟨sub, _⟩ | ⟨m, loop, _⟩
    · rw [kind] at sub; cases sub
    · rw [kind] at loop; cases loop
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · subst op
    exact ⟨pre, post, u, u', schedule, head, allowed, accepted,
      transition_of_created accepted (by simp) j memberJ absentU, rest⟩
  · have cancelled : j.status = .cancelled := by rw [eq]; rfl
    obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status (preserves_invariants u u' op safeU accepted) j memberJ (.inr cancelled)
    have same := unique_instance safeLast memberK memberI (idK.trans idJ)
    subst k
    rw [succeeded, cancelled] at statusK; cases statusK
  · have triggerJ := Instance.binding_trigger bindJ
    rw [eq, triggerI] at triggerJ
    cases triggerJ


theorem forEach_child_eval (oracle : ScopedOracle) {s0 closing last : State} {ops tailOps : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops closing)
    (tail : ConformingSteps (fun s op => oracleConforms oracle s op = true) closing tailOps last)
    (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (bodyAdequacy : FrameAdequacy oracle body)
    (input : Channel) (memberIn : input ∈ closing.channels) (pathIn : input.path = P) (exitIn : input.exit = false)
    (nodeIn : input.edge.dst.node = n.id) (drained : input.pendingItems = [])
    (children : (closing.instances.filter (fun i => i.path == P && i.node == n.id && i.trigger.isSome)).all (·.status == .succeeded) = true)
    (y : ItemId) (present : y ∈ input.items) :
    GraphEval oracle body (childPath P n.id (some y) 0) (bodyInputs body [y])
      (observedResult last (childPath P n.id (some y) 0) body) := by
  obtain ⟨pre, post, u, u', _, head, allowed, accepted, rest, safeU, executed, memberStart⟩ :=
    forEach_input_spawn oracle run fs n memberN body kind input memberIn pathIn exitIn nodeIn drained y present
  have scU := fs.scope.persist head
  obtain ⟨_, m, b, c, got, kindM, _, _, f, opened, absent, arity, view, _, frames, _⟩ :=
    effect_spawn u u' P n.id y safeU.channelIds executed
  have sameN := node?_of_getNode (head.node P n.id n (fs.scope.node?_of_mem n memberN)) got
  subst m
  have bodyEq := NodeKind.forEach.inj (kindM.symm.trans kind)
  subst b
  obtain ⟨pathF, graphF, _, _⟩ := opened
  have validBody := g.validateNode_child n body (.inr (.inr kind)) (fs.scope.checked n memberN)
  have started := seeded_frameStart safeU scU.layout scU.distinct (head.frameAncestors fs.scope.safe ancestors)
    (head.frameOwners fs.scope.safe fs.scope.distinct fs.owners)
    accepted f (by rw [frames]; simp)
    (fun old member eq => by rw [← eq, frame?_of_mem scU.distinct old member] at absent; contradiction)
    (by simpa only [graphF] using validBody) [y] (by simpa only [graphF, List.length_cons, List.length_nil] using arity)
    (by simpa only [graphF] using view)
  have childStart : FrameStart u' (childPath P n.id (some y) 0) body (bodyInputs body [y]) := by
    simpa only [pathF, graphF, makeInstance, childPath] using started
  let initial := makeInstance P n .waitingInputs [("item", y)] (some y)
  have safeNext := preserves_invariants u u' _ safeU accepted
  obtain ⟨j, memberJ, bindingJ⟩ := rest.retains_binding safeNext initial memberStart
  have pathJ : j.path = P := Instance.binding_path bindingJ
  have nodeJ : j.node = n.id := Instance.binding_node bindingJ
  have triggerJ : j.trigger = some y := Instance.binding_trigger bindingJ
  have succeededJ : j.status = .succeeded := by
    have h := List.all_eq_true.mp children j (List.mem_filter.mpr ⟨memberJ, by simp [pathJ, nodeJ, triggerJ]⟩)
    simpa using h
  have headNext := head.append (ConformingSteps.cons allowed accepted (.nil u'))
  obtain ⟨pre2, post2, t, t', a, b', _, before, allowedT, acceptedT, after, memberA, _, _, _, pathA, nodeA, triggerA, active⟩ :=
    sub_success_event oracle headNext rest fs n memberN body initial memberStart (.inr ⟨kind, rfl⟩) rfl rfl
      (by change InstanceStatus.waitingInputs ≠ .succeeded; decide) j memberJ (congrArg Prod.fst bindingJ) succeededJ
  have headT := headNext.append before
  have safeT := headT.invariants fs.scope.safe
  obtain ⟨a', m, frame, outputs, found, waiting, _, current, results, _⟩ :=
    effect_finishSubworkflow t t' a.id (transition_of_active acceptedT active (by simp))
  rw [instance?_of_mem safeT a memberA] at found
  have sameA := Option.some.inj found
  subst a'
  obtain ⟨z, triggerZ, idA, iterA, ⟨witness, memberWitness, pathWitness, graphWitness, _⟩, _⟩ :=
    forEach_child_shape oracle headT fs n memberN body kind a memberA pathA nodeA waiting
  have zy : z = y := Option.some.inj (triggerZ.symm.trans triggerA)
  subst z
  obtain ⟨memberFrame, pathFrame⟩ := currentFrame_spec t a frame current
  have childPathEq : frame.path = childPath P n.id (some y) 0 := by rw [pathFrame, pathA, idA, iterA]; rfl
  have sameFrame := eq_of_mapped_nodup Frame.path t.frames (headT.unique_frames fs.scope.distinct)
    frame witness memberFrame memberWitness (childPathEq.trans pathWitness.symm)
  subst witness
  have complete : FrameCompletes oracle u' last (childPath P n.id (some y) 0) body :=
    ⟨t, pre2, _, frame, before, (ConformingSteps.cons allowedT acceptedT after).append tail, memberFrame, childPathEq, graphWitness,
      (bodyResults_spec t frame outputs results).1⟩
  exact bodyAdequacy u' last _ _ _ childStart (headNext.frameAncestors fs.scope.safe ancestors)
    (rest.append tail) complete finished

theorem forEach_node_eval (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (bodyAdequacy : FrameAdequacy oracle body)
    (i : Instance) (memberI : i ∈ last.instances) (pathI : i.path = P) (nodeI : i.node = n.id)
    (triggerI : i.trigger = none) (succeeded : i.status = .succeeded) :
    NodeEval oracle g P n (stateInputs last P n) (nodeValue oracle last g P n) := by
  have scL := fs.scope.persist run
  obtain ⟨p, q, ins, outs, stream⟩ := forEach_ports fs.scope n memberN body kind
  have notPlain := allKind_plain_false_of_stream n.inputs p (by simp [ins]) stream
  have awake : suppressed n (stateInputs last P n) = false := by simp [suppressed, notPlain]
  obtain ⟨pre, post, t, t', _, head, allowed, accepted, executed, rest⟩ :=
    forEach_controller_event oracle run fs n memberN body kind i memberI pathI nodeI triggerI succeeded
  have scT := fs.scope.persist head
  have tail : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (.propagateEos P n.id :: post) last :=
    .cons allowed accepted rest
  obtain ⟨_, _, _, drained, children, _⟩ := effect_propagateEos t t' P n.id executed
  obtain ⟨c, memberC, foundC, pathC, exitC, dstC, _, _, uniqueC⟩ := scT.input_channel n memberN p (by simp [ins])
  have incoming : c ∈ t.incoming P n.id := List.mem_filter.mpr ⟨memberC, by simp [pathC, exitC, dstC]⟩
  have ready := List.all_eq_true.mp drained c incoming
  simp only [Bool.and_eq_true, List.isEmpty_iff] at ready
  obtain ⟨d, memberD, idD, placedD⟩ := tail.retains_closed_channel scT.safe c memberC ready.1
  obtain ⟨d', memberD', idD', layoutD', _⟩ := run_image tail scT.safe c memberC
  have sameD := unique_channel scL.safe memberD' memberD (idD'.trans idD.symm)
  subst d'
  obtain ⟨_, edgeD, pathD, _, exitD, _⟩ := Channel.layout_fields layoutD'
  obtain ⟨e, _, foundE, _, _, _, _, _, uniqueE⟩ := scL.input_channel n memberN p (by simp [ins])
  have sameE := uniqueE d memberD (pathD.trans pathC) (exitD.trans exitC) (edgeD ▸ dstC)
  subst e
  have inputEq : ((stateInputs last P n).head?.map (·.2)).getD [] = bag c := by
    simp only [stateInputs, ins, List.map_cons, List.map_nil, List.head?_cons, foundE,
      Option.map_some, Option.getD_some]
    simp only [bag, Channel.items, placedD]
  have evaluated := NodeEval.forEach (g := g) (results := fun y => observedResult last (childPath P n.id (some y) 0) body)
    kind awake (fun y memberY => forEach_child_eval oracle fs ancestors head tail finished n memberN body kind bodyAdequacy
      c memberC pathC exitC (congrArg PortRef.node dstC) ready.2 children y (by
        rw [inputEq] at memberY
        exact (sortedItems_perm c.items).mem_iff.mp memberY))
  simpa only [nodeValue, primitive, awake, Bool.false_eq_true, ↓reduceIte, kind, compoundValue, observedResult] using evaluated

end Suimon
