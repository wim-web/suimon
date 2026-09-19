import Suimon.Theorems.LoopChain

namespace Suimon
open Semantics Effects

theorem activate_body_start (oracle : ScopedOracle) {s0 t next : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops t)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (iteration : Nat)
    (kind : (n.kind = .subworkflow body ∧ iteration = 0) ∨ ∃ limit, n.kind = .loop body limit ∧ iteration = 1)
    (inputs : List (PortName × ItemId)) (got : getNode t P n.id = .ok n)
    (plain : plainInputs t P n = .ok inputs)
    (accepted : step t (.activate P n.id) = .ok next)
    (executed : transition t (.activate P n.id) = .ok next) :
    FrameStart next (childPath P n.id none iteration) body (bodyInputs body (inputs.map (·.2))) := by
  have scT := fs.scope.persist head
  obtain ⟨_, m, items, gotM, plainM, cases⟩ := effect_activate t next P n.id executed
  have same := Except.ok.inj (gotM.symm.trans got)
  subst m
  have itemsEq := Except.ok.inj (plainM.symm.trans plain)
  subst items
  rcases cases with ⟨r, c, leaf, _⟩ | ⟨b, k, kinds, f, opened, absent, arity, view, _, frames, _⟩
  · rcases kind with ⟨sub, _⟩ | ⟨limit, loop, _⟩ <;> (rw [leaf] at *; contradiction)
  · have bodyEq : b = body := by
      rcases kind with ⟨sub, _⟩ | ⟨limit, loop, _⟩ <;>
      rcases kinds with ⟨sub', _⟩ | ⟨limit', loop', _⟩
      · exact NodeKind.subworkflow.inj (sub'.symm.trans sub)
      · rw [sub] at loop'; cases loop'
      · rw [loop] at sub'; cases sub'
      · exact (NodeKind.loop.inj (loop'.symm.trans loop)).1
    subst b
    have iterEq : k = iteration := by
      rcases kind with ⟨sub, value⟩ | ⟨limit, loop, value⟩ <;>
      rcases kinds with ⟨sub', value'⟩ | ⟨limit', loop', value'⟩
      · omega
      · rw [sub] at loop'; cases loop'
      · rw [loop] at sub'; cases sub'
      · omega
    subst k
    have valid := g.validateNode_child n body (by
      rcases kind with ⟨sub, _⟩ | ⟨limit, loop, _⟩
      · exact .inr (.inl sub)
      · exact .inl ⟨limit, loop⟩) (fs.scope.checked n memberN)
    obtain ⟨pathF, graphF, _, _⟩ := opened
    have started := seeded_frameStart scT.safe scT.layout scT.distinct
      (head.frameAncestors fs.scope.safe ancestors) (head.frameOwners fs.scope.safe fs.scope.distinct fs.owners)
      accepted f (by rw [frames]; simp)
      (fun old member eq => by rw [← eq, frame?_of_mem scT.distinct old member] at absent; contradiction)
      (by simpa only [graphF] using valid) (inputs.map (·.2))
      (by simpa only [graphF] using arity) (by simpa only [graphF] using view)
    simpa only [pathF, graphF, makeInstance, childPath] using started

theorem loop_node_eval (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (bodyAdequacy : FrameAdequacy oracle body)
    (i : Instance) (memberI : i ∈ last.instances) (pathI : i.path = P) (nodeI : i.node = n.id)
    (succeeded : i.status = .succeeded) :
    NodeEval oracle g P n (stateInputs last P n) (nodeValue oracle last g P n) := by
  have scL := fs.scope.persist run
  obtain ⟨f, inputsI, channels⟩ := plain_instance_inputs oracle run fs n memberN
    (.inr (.inr (.inr (.inr ⟨body, limit, kind⟩)))) i memberI pathI nodeI succeeded
  have inputEq := stateInputs_of_singletons scL n memberN f channels
  have awake : suppressed n (stateInputs last P n) = false := by
    rw [inputEq]; exact suppressed_singletons n f (by rw [kind]; simp)
  obtain ⟨pre, post, t, t', items, _, head, allowed, accepted, executed, rest, got, plain, memberJ, idJ, bindingJ⟩ :=
    loop_instance_origin oracle run fs n memberN body limit kind i memberI pathI nodeI (by rw [succeeded]; decide)
  let j := { makeInstance P n .waitingInputs items with iteration := 1 }
  have childStart := activate_body_start oracle fs ancestors head n memberN body 1 (.inr ⟨limit, kind, rfl⟩)
    items got plain accepted executed
  have itemsEq : items = plainValues (stateInputs last P n) := by
    rw [inputEq, plainValues_singletons]
    exact (Instance.binding_inputs bindingJ).trans inputsI
  have oneInput : n.inputs.length = 1 := by
    have shape := g.validateNode_shape n (fs.scope.checked n memberN)
    simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
    grind only []
  have itemsLen : items.length = 1 := by rw [itemsEq, plainValues, stateInputs, List.length_map, List.length_map, oneInput]
  obtain ⟨pair, singleton⟩ := List.length_eq_one_iff.mp itemsLen
  have inputItem : ((plainValues (stateInputs last P n)).head?.map (·.2)).getD "" = pair.2 := by
    rw [← itemsEq, singleton]; rfl
  have headNext := head.append (ConformingSteps.cons allowed accepted (.nil t'))
  have chain := loop_eval_active oracle fs ancestors headNext rest finished n memberN body limit kind bodyAdequacy
    j i memberJ rfl rfl rfl memberI idJ.symm succeeded pair.2
    (by simpa only [singleton, List.map_cons, List.map_nil] using childStart)
  have triggerI : i.trigger = none := (Instance.binding_trigger bindingJ).symm
  have count : loopCount last P n.id = i.iteration := by
    have found := nodeInstance?_of_mem scL.safe i memberI triggerI
    rw [pathI, nodeI] at found
    simp [loopCount, found]
  have positive : 1 ≤ i.iteration := (loop_instance_shape oracle run fs n memberN body limit kind
    i memberI pathI nodeI (by rw [succeeded]; decide)).2.2.1
  have len : i.iteration - 1 + 1 = i.iteration := by omega
  change LoopEval oracle body P n.id 1 pair.2 _ (loopChannels last P n.id 1 (i.iteration - 1 + 1)) at chain
  rw [len, ← count, ← inputItem] at chain
  have evaluated := NodeEval.loop (g := g) kind awake chain
  simpa only [nodeValue, primitive, awake, Bool.false_eq_true, ↓reduceIte, kind, compoundValue] using evaluated

end Suimon
