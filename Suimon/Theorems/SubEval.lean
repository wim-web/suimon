import Suimon.Theorems.CompoundEval

namespace Suimon
open Semantics Effects

theorem sub_instance_origin (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph)
    (kind : n.kind = .subworkflow body) (i : Instance) (memberI : i ∈ last.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) (notCancelled : i.status ≠ .cancelled) :
    ∃ pre post u u' inputs, ops = pre ++ .activate P n.id :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre u ∧
      oracleConforms oracle u (.activate P n.id) = true ∧ step u (.activate P n.id) = .ok u' ∧
      transition u (.activate P n.id) = .ok u' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) u' post last ∧
      getNode u P n.id = .ok n ∧ plainInputs u P n = .ok inputs ∧
      let j := { makeInstance P n .waitingInputs inputs with iteration := 0 }
      j ∈ u'.instances ∧ j.id = i.id ∧ j.binding = i.binding := by
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
    | ⟨P', N', n', _, hn, kind', eq⟩
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
  · rcases kinds with ⟨sub, _⟩ | ⟨m, loop, iter⟩
    · subst iteration op
      have executed := transition_of_created accepted (by simp) j memberJ absentU
      rw [eq] at memberJ idJ bindJ
      exact ⟨pre, post, u, u', inputs, schedule, head, allowed, accepted, executed, rest, hn, hi, memberJ, idJ, bindJ⟩
    · rw [kind] at loop; cases loop
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; simp at kind'
  · have cancelled : j.status = .cancelled := by rw [eq]; rfl
    obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status (preserves_invariants u u' op safeU accepted) j memberJ (.inr cancelled)
    have same := unique_instance safeLast memberK memberI (idK.trans idJ)
    subst k
    exact False.elim (notCancelled (statusK.trans cancelled))
  · rw [kind] at kind'; cases kind'


theorem sub_success_event (oracle : ScopedOracle) {s0 start last : State} {headOps ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 headOps start)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) start ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph)
    (i : Instance) (memberI : i ∈ start.instances)
    (kind : n.kind = .subworkflow body ∨ (n.kind = .forEach body ∧ i.trigger.isSome = true))
    (pathI : i.path = P) (nodeI : i.node = n.id) (before : i.status ≠ .succeeded)
    (j : Instance) (memberJ : j ∈ last.instances) (sameId : j.id = i.id) (succeeded : j.status = .succeeded) :
    ∃ pre post t t' a b, ops = pre ++ .finishSubworkflow a.id :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) start pre t ∧
      oracleConforms oracle t (.finishSubworkflow a.id) = true ∧ step t (.finishSubworkflow a.id) = .ok t' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last ∧
      a ∈ t.instances ∧ b ∈ t'.instances ∧ a.id = i.id ∧ b.id = i.id ∧
      a.path = P ∧ a.node = n.id ∧ a.trigger = i.trigger ∧
      absorbed t (.finishSubworkflow a.id) = false := by
  have safeStart := head.invariants fs.scope.safe
  obtain ⟨pre, op, post, t, t', a, b, schedule, headT, allowed, accepted, rest, safeT,
    memberA, memberB, idA, idB, bindingA, notA, yesB, evolution⟩ :=
    run.reached safeStart (fun i => i.status = .succeeded) i memberI before j memberJ sameId succeeded
  have pathA := (Instance.binding_path bindingA).trans pathI
  have nodeA := (Instance.binding_node bindingA).trans nodeI
  have triggerA := Instance.binding_trigger bindingA
  have nodeT := (head.append headT).node P n.id n (fs.scope.node?_of_mem n memberN)
  have active := active_of_status_change safeT accepted a memberA b memberB (idB.trans idA.symm)
    (fun equal => notA (equal ▸ yesB))
  have reason :
      (∃ auth outputs, op = .complete auth outputs ∧ ∃ m r c, getNode t a.path a.node = .ok m ∧ m.kind = .leaf r c) ∨
      op = .finishSubworkflow a.id ∨ op = .loopIterate a.id true ∨
      (op = .propagateEos a.path a.node ∧ a.trigger = none) := by
    rcases evolution.2 with same | ⟨_, bad⟩ | ⟨_, why⟩ | ⟨bad, _⟩ | bad | bad | bad | ⟨bad, _⟩
    · exact False.elim (notA (same ▸ yesB))
    · rw [yesB] at bad; cases bad
    · exact why
    all_goals rw [yesB] at bad; cases bad
  have opEq : op = .finishSubworkflow a.id := by
    rcases reason with ⟨_, _, _, m, r, c, got, leaf⟩ | finish | loop | ⟨eos, noTrigger⟩
    · rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rcases kind with sub | ⟨each, _⟩ <;> (rw [leaf] at *; contradiction)
    · exact finish
    · rw [loop] at accepted active
      obtain ⟨a', m, _, _, _, _, _, found, _, got, loopKind, _⟩ :=
        effect_loopIterate t t' a.id true (transition_of_active accepted active (by simp))
      rw [instance?_of_mem safeT a memberA] at found
      have same := Option.some.inj found
      subst a'
      rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rcases kind with sub | ⟨each, _⟩ <;> (rw [loopKind] at *; contradiction)
    · rcases kind with sub | ⟨_, hasTrigger⟩
      · rw [eos] at accepted active
        obtain ⟨m, got, stream, _⟩ := effect_propagateEos t t' a.path a.node (transition_of_active accepted active (by simp))
        rw [pathA, nodeA] at got
        have sameN := node?_of_getNode nodeT got
        subst m
        rw [sub] at stream
        contradiction
      · rw [← triggerA, noTrigger] at hasTrigger; contradiction
  subst op
  exact ⟨pre, post, t, t', a, b, schedule, headT, allowed, accepted, rest, memberA, memberB, idA, idB,
    pathA, nodeA, triggerA, active⟩

theorem sub_node_eval (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .subworkflow body)
    (bodyAdequacy : FrameAdequacy oracle body)
    (i : Instance) (memberI : i ∈ last.instances) (pathI : i.path = P) (nodeI : i.node = n.id)
    (succeeded : i.status = .succeeded) :
    NodeEval oracle g P n (stateInputs last P n) (nodeValue oracle last g P n) := by
  have scL := fs.scope.persist run
  obtain ⟨values, inputsI, channels⟩ := plain_instance_inputs oracle run fs n memberN
    (.inr (.inr (.inr (.inl ⟨body, kind⟩)))) i memberI pathI nodeI succeeded
  have inputEq := stateInputs_of_singletons scL n memberN values channels
  have awake : suppressed n (stateInputs last P n) = false := by
    rw [inputEq]; exact suppressed_singletons n values (by rw [kind]; simp)
  obtain ⟨pre, post, u, u', items, _, head, allowed, accepted, executed, rest, got, plain, memberJ, idJ, bindingJ⟩ :=
    sub_instance_origin oracle run fs n memberN body kind i memberI pathI nodeI (by rw [succeeded]; decide)
  let j := { makeInstance P n .waitingInputs items with iteration := 0 }
  have childStart := activate_body_start oracle fs ancestors head n memberN body 0 (.inl ⟨kind, rfl⟩)
    items got plain accepted executed
  have itemsEq : items = plainValues (stateInputs last P n) := by
    rw [inputEq, plainValues_singletons]
    exact (Instance.binding_inputs bindingJ).trans inputsI
  have headNext := head.append (ConformingSteps.cons allowed accepted (.nil u'))
  obtain ⟨pre2, post2, t, t', a, b, _, before, allowedT, acceptedT, after, memberA, _, _, _, pathA, nodeA, _, active⟩ :=
    sub_success_event oracle headNext rest fs n memberN body j memberJ (.inl kind) rfl rfl
      (by change InstanceStatus.waitingInputs ≠ .succeeded; decide) i memberI idJ.symm succeeded
  have headT := headNext.append before
  have safeT := headT.invariants fs.scope.safe
  obtain ⟨a', m, f, outputs, found, waiting, gotM, current, results, _⟩ :=
    effect_finishSubworkflow t t' a.id (transition_of_active acceptedT active (by simp))
  rw [instance?_of_mem safeT a memberA] at found
  have sameA := Option.some.inj found
  subst a'
  obtain ⟨idA, _, iterA, witness, memberWitness, pathWitness, graphWitness, _⟩ :=
    sub_instance_shape oracle headT fs n memberN body kind a memberA pathA nodeA (by rw [waiting]; decide)
  obtain ⟨memberF, pathF⟩ := currentFrame_spec t a f current
  have childPathEq : f.path = childPath P n.id none 0 := by rw [pathF, pathA, idA, iterA]; rfl
  have sameF := eq_of_mapped_nodup Frame.path t.frames (headT.unique_frames fs.scope.distinct)
    f witness memberF memberWitness (childPathEq.trans pathWitness.symm)
  subst witness
  have complete : FrameCompletes oracle u' last (childPath P n.id none 0) body :=
    ⟨t, pre2, _, f, before, .cons allowedT acceptedT after, memberF, childPathEq, graphWitness,
      (bodyResults_spec t f outputs results).1⟩
  have evaluated := bodyAdequacy u' last post _ _ childStart
    (headNext.frameAncestors fs.scope.safe ancestors) rest complete finished
  rw [itemsEq] at evaluated
  have result := NodeEval.sub (g := g) kind awake evaluated
  simpa only [nodeValue, primitive, awake, Bool.false_eq_true, ↓reduceIte, kind, compoundValue, observedResult] using result

end Suimon
