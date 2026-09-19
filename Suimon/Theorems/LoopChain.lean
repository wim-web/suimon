import Suimon.Theorems.FrameCompletion

namespace Suimon
open Semantics Effects

/-- The body result and oracle decision at any loop boundary, including a
    boundary which reaches the configured iteration limit. --/
theorem loop_body_step (oracle : ScopedOracle) {s0 t t' last : State} {pre post : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} {inst : InstanceId} {done : Bool} (fs : FrameStart s0 P g inputs0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t)
    (allowed : oracleConforms oracle t (.loopIterate inst done) = true)
    (accepted : step t (.loopIterate inst done) = .ok t')
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last)
    (active : absorbed t (.loopIterate inst done) = false)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (target : opTarget t (.loopIterate inst done) = some (P, n.id)) :
    ∃ i f item, t.instance? inst = some i ∧ i.status = .waitingInputs ∧ i.path = P ∧ i.node = n.id ∧
      i.id = instanceId P n.id none ∧ i.trigger = none ∧ f ∈ t.frames ∧
      f.path = childPath P n.id none i.iteration ∧ f.graph = body ∧
      currentFrame t i = .ok f ∧ bodyResults t f = .ok [item] ∧
      exitItems last (childPath P n.id none i.iteration) body = [[item]] ∧
      (oracle P).loop n.id i.iteration item = done := by
  have safeT := head.invariants fs.scope.safe
  have full : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (.loopIterate inst done :: post) last :=
    .cons allowed accepted rest
  have scL := fs.scope.persist (head.append full)
  obtain ⟨i, n', body', limit', f, items, item, foundI, waiting, got, loopKind, current, results, headItem, _, _⟩ :=
    effect_loopIterate t t' inst done (transition_of_active accepted active (by simp))
  obtain ⟨i', foundI', pathI, nodeI⟩ := opTarget_id (inst := inst) rfl target
  rw [foundI] at foundI'
  have sameI := Option.some.inj foundI'
  subst i'
  rw [pathI, nodeI] at got
  have nodeT := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  have sameN := node?_of_getNode nodeT got
  subst n'
  obtain ⟨bodyEq, limitEq⟩ := NodeKind.loop.inj (loopKind.symm.trans kind)
  subst body' limit'
  obtain ⟨idI, triggerI, _, f0, memberF0, pathF0, graphF0, _⟩ :=
    loop_instance_shape oracle head fs n memberN body limit kind i (instance?_mem foundI) pathI nodeI
      (by rw [waiting]; decide)
  obtain ⟨memberF, pathF⟩ := currentFrame_spec t i f current
  have sameF := eq_of_mapped_nodup Frame.path t.frames (head.unique_frames fs.scope.distinct)
    f f0 memberF memberF0 (pathF.trans pathF0.symm)
  subst f0
  have pathChild : f.path = childPath P n.id none i.iteration := by rw [pathF, pathI, idI]; rfl
  have validBody := g.validateNode_child n body (.inl ⟨limit, kind⟩) (fs.scope.checked n memberN)
  have childScope := Scope.child full scL f memberF (by rw [graphF0]; exact validBody)
  have exits := exitItems_of_bodyResults full safeT f items results childScope
  have oneExit : body.exits.length = 1 := by
    have shape := g.validateNode_shape n (fs.scope.checked n memberN)
    simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
    grind only []
  have itemLen : items.length = 1 := by
    have spec := (frameOutputItems_spec t f items (bodyResults_spec t f items results).2).1
    rw [spec, List.length_map, graphF0, oneExit]
  obtain ⟨value, singleton⟩ := List.length_eq_one_iff.mp itemLen
  have valueEq : value = item := by simpa [singleton] using headItem
  have itemsEq : items = [item] := by rw [singleton, valueEq]
  have conf : (oracle P).loop n.id i.iteration item = done := by
    have output := (bodyResults_spec t f items results).2
    simp only [oracleConforms, active, Bool.false_eq_true, ↓reduceIte, foundI, current,
      Except.toOption, Option.bind_some, output, headItem, Option.any_some, pathI, nodeI] at allowed
    exact (beq_iff_eq.mp allowed).symm
  exact ⟨i, f, item, foundI, waiting, pathI, nodeI, idI, triggerI, memberF, pathChild, graphF0, current,
    by simpa only [itemsEq] using results, by simpa [pathChild, graphF0, itemsEq] using exits, conf⟩

theorem loop_success_event (oracle : ScopedOracle) {s0 start last : State} {headOps ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 headOps start)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) start ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat)
    (kind : n.kind = .loop body limit) (i : Instance) (memberI : i ∈ start.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) (before : i.status ≠ .succeeded)
    (j : Instance) (memberJ : j ∈ last.instances) (sameId : j.id = i.id) (succeeded : j.status = .succeeded) :
    ∃ pre post t t' a b, ops = pre ++ .loopIterate a.id true :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) start pre t ∧
      oracleConforms oracle t (.loopIterate a.id true) = true ∧ step t (.loopIterate a.id true) = .ok t' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last ∧
      a ∈ t.instances ∧ b ∈ t'.instances ∧ a.id = i.id ∧ b.id = i.id ∧
      a.path = P ∧ a.node = n.id ∧ a.status ≠ .succeeded ∧ b.status = .succeeded ∧
      absorbed t (.loopIterate a.id true) = false := by
  have safeStart := head.invariants fs.scope.safe
  obtain ⟨pre, op, post, t, t', a, b, schedule, headT, allowed, accepted, rest, safeT,
    memberA, memberB, idA, idB, bindingA, notA, yesB, evolution⟩ :=
    run.reached safeStart (fun i => i.status = .succeeded) i memberI before j memberJ sameId succeeded
  have pathA := (Instance.binding_path bindingA).trans pathI
  have nodeA := (Instance.binding_node bindingA).trans nodeI
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
  have opEq : op = .loopIterate a.id true := by
    rcases reason with ⟨_, _, _, m, r, c, got, leaf⟩ | finish | loop | ⟨eos, _⟩
    · rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at leaf; cases leaf
    · rw [finish] at accepted active
      obtain ⟨a', m, _, _, found, _, got, _, _, _, _, _, _, cases⟩ :=
        effect_finishSubworkflow t t' a.id (transition_of_active accepted active (by simp))
      rw [instance?_of_mem safeT a memberA] at found
      have same := Option.some.inj found
      subst a'
      rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rcases cases with ⟨_, sub, _⟩ | ⟨_, each, _⟩
      · rw [kind] at sub; cases sub
      · rw [kind] at each; cases each
    · exact loop
    · rw [eos] at accepted active
      obtain ⟨m, got, stream, _⟩ := effect_propagateEos t t' a.path a.node (transition_of_active accepted active (by simp))
      rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at stream
      contradiction
  subst op
  exact ⟨pre, post, t, t', a, b, schedule, headT, allowed, accepted, rest, memberA, memberB, idA, idB,
    pathA, nodeA, notA, yesB, active⟩

theorem loop_failure_event (oracle : ScopedOracle) {s0 start last : State} {headOps ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 headOps start)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) start ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat)
    (kind : n.kind = .loop body limit) (i : Instance) (memberI : i ∈ start.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) (before : i.status ≠ .failed)
    (j : Instance) (memberJ : j ∈ last.instances) (sameId : j.id = i.id) (failed : j.status = .failed) :
    ∃ pre post t t' a b, ops = pre ++ .loopIterate a.id false :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) start pre t ∧
      oracleConforms oracle t (.loopIterate a.id false) = true ∧ step t (.loopIterate a.id false) = .ok t' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last ∧
      a ∈ t.instances ∧ b ∈ t'.instances ∧ a.id = i.id ∧ b.id = i.id ∧
      a.path = P ∧ a.node = n.id ∧ a.status ≠ .failed ∧ b.status = .failed ∧
      absorbed t (.loopIterate a.id false) = false := by
  have safeStart := head.invariants fs.scope.safe
  obtain ⟨pre, op, post, t, t', a, b, schedule, headT, allowed, accepted, rest, safeT,
    memberA, memberB, idA, idB, bindingA, notA, yesB, evolution⟩ :=
    run.reached safeStart (fun i => i.status = .failed) i memberI before j memberJ sameId failed
  have pathA := (Instance.binding_path bindingA).trans pathI
  have nodeA := (Instance.binding_node bindingA).trans nodeI
  have nodeT := (head.append headT).node P n.id n (fs.scope.node?_of_mem n memberN)
  have active := active_of_status_change safeT accepted a memberA b memberB (idB.trans idA.symm)
    (fun equal => notA (equal ▸ yesB))
  have reason : (∃ m r c, getNode t a.path a.node = .ok m ∧ m.kind = .leaf r c) ∨ op = .loopIterate a.id false := by
    rcases evolution.2 with same | ⟨_, bad⟩ | ⟨bad, _⟩ | ⟨_, why⟩ | bad | bad | bad | ⟨bad, _⟩
    · exact False.elim (notA (same ▸ yesB))
    · rw [yesB] at bad; cases bad
    · rw [yesB] at bad; cases bad
    · exact why
    all_goals rw [yesB] at bad; cases bad
  have opEq : op = .loopIterate a.id false := by
    rcases reason with ⟨m, r, c, got, leaf⟩ | loop
    · rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at leaf; cases leaf
    · exact loop
  subst op
  exact ⟨pre, post, t, t', a, b, schedule, headT, allowed, accepted, rest, memberA, memberB, idA, idB,
    pathA, nodeA, notA, yesB, active⟩

theorem exitItems_of_frameOutputItems (s : State) (f : Frame) (scope : Scope s f.path f.graph)
    (items : List ItemId) (outputs : frameOutputItems s f = .ok items) :
    exitItems s f.path f.graph = items.map (fun x => [x]) := by
  obtain ⟨itemsEq, channels⟩ := frameOutputItems_spec s f items outputs
  rw [itemsEq, List.map_map]
  unfold exitItems
  apply List.map_congr_left
  intro p memberP
  obtain ⟨c, memberC, pathC, exitC, srcC, itemsC⟩ := channels p memberP
  obtain ⟨d, _, found, _, _, _, _, uniqueD⟩ := scope.exit_channel p memberP
  have same := uniqueD c memberC pathC exitC srcC
  subst d
  rw [found]
  simp [bag, itemsC, sortedItems]

theorem loop_continue_birth (oracle : ScopedOracle) {s0 t next last : State} {pre post : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t)
    (i j : Instance)
    (allowed : oracleConforms oracle t (.loopIterate i.id false) = true)
    (accepted : step t (.loopIterate i.id false) = .ok next)
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) next post last)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (memberI : i ∈ t.instances) (memberJ : j ∈ next.instances)
    (sameId : j.id = i.id) (pathI : i.path = P) (nodeI : i.node = n.id)
    (iteration : j.iteration = i.iteration + 1) :
    ∃ item, j.status = .waitingInputs ∧
      FrameStart next (childPath P n.id none j.iteration) body (bodyInputs body [item]) ∧
      exitItems last (childPath P n.id none i.iteration) body = [[item]] ∧
      (oracle P).loop n.id i.iteration item = false := by
  have safeT := head.invariants fs.scope.safe
  have safeNext := preserves_invariants t next _ safeT accepted
  have active := active_of_iteration_change safeT accepted i j memberI memberJ sameId (by omega)
  have target : opTarget t (.loopIterate i.id false) = some (P, n.id) := by
    simp [opTarget, instance?_of_mem safeT i memberI, pathI, nodeI]
  obtain ⟨old, f, item, foundOld, waiting, _, _, idOld, _, _, _, _, current, results, exits, decision⟩ :=
    loop_body_step oracle fs head allowed accepted rest active n memberN body limit kind target
  rw [instance?_of_mem safeT i memberI] at foundOld
  have sameOld := Option.some.inj foundOld
  subst old
  obtain ⟨i', n', body', limit', f', items, value, found, _, got, kind', current', results', headItem, _, outcomes⟩ :=
    effect_loopIterate t next i.id false (transition_of_active accepted active (by simp))
  rw [instance?_of_mem safeT i memberI] at found
  have sameI := Option.some.inj found
  subst i'
  rw [pathI, nodeI] at got
  have sameN := node?_of_getNode (head.node P n.id n (fs.scope.node?_of_mem n memberN)) got
  subst n'
  obtain ⟨bodyEq, limitEq⟩ := NodeKind.loop.inj (kind'.symm.trans kind)
  subst body' limit'
  rw [current] at current'
  have sameF := Except.ok.inj current'
  subst f'
  rw [results] at results'
  have itemsEq := Except.ok.inj results'
  rw [← itemsEq] at headItem
  have sameItem : item = value := by simpa using headItem
  subst value
  rcases outcomes with ⟨bad, _⟩ | ⟨_, _, _, instances, _⟩ | ⟨_, _, child, opened, absent, arity, view, instances, frames⟩
  · cases bad
  · have updated : {i with status := .failed} ∈ next.instances := by
      rw [instances]
      exact setInstance_self_mem t i _ memberI rfl
    have same := unique_instance safeNext updated memberJ sameId.symm
    have equal : i.iteration = j.iteration := by simpa only using congrArg Instance.iteration same
    omega
  · have updated : {i with iteration := i.iteration + 1} ∈ next.instances := by
      rw [instances]
      exact setInstance_self_mem t i _ memberI rfl
    have same := unique_instance safeNext updated memberJ sameId.symm
    have statusJ : j.status = .waitingInputs := by rw [← same]; exact waiting
    obtain ⟨pathChild, graphChild, _, _⟩ := opened
    have childPathEq : child.path = childPath P n.id none j.iteration := by
      rw [pathChild, iteration, pathI, idOld]
      rfl
    have scopeT := fs.scope.persist head
    have started := seeded_frameStart safeT scopeT.layout scopeT.distinct (head.frameAncestors fs.scope.safe ancestors)
      (head.frameOwners fs.scope.safe fs.scope.distinct fs.owners)
      accepted child (by rw [frames]; simp) absent
      (by rw [graphChild]; exact g.validateNode_child n body (.inl ⟨limit, kind⟩) (fs.scope.checked n memberN))
      [item] (by simpa only [graphChild, List.length_singleton] using arity) (by simpa only [graphChild] using view)
    exact ⟨item, statusJ, by simpa only [childPathEq, graphChild] using started, exits, decision⟩

theorem loop_retry_birth (oracle : ScopedOracle) {s0 start t next last : State} {headOps pre post : List Op}
    {P : Path} {g : Graph} {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 headOps start)
    (prior : ConformingSteps (fun s op => oracleConforms oracle s op = true) start pre t)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (initial old j : Instance) (memberInitial : initial ∈ start.instances) (waiting : initial.status = .waitingInputs)
    (pathInitial : initial.path = P) (nodeInitial : initial.node = n.id)
    (memberOld : old ∈ t.instances) (sameOld : old.id = initial.id) (sameIteration : old.iteration = initial.iteration)
    (memberJ : j ∈ next.instances) (sameId : j.id = old.id) (iteration : j.iteration = old.iteration + 1)
    (allowed : oracleConforms oracle t (.manualRetry old.id) = true)
    (accepted : step t (.manualRetry old.id) = .ok next)
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) next post last) :
    ∃ item, j.status = .waitingInputs ∧
      FrameStart next (childPath P n.id none j.iteration) body (bodyInputs body [item]) ∧
      exitItems last (childPath P n.id none old.iteration) body = [[item]] ∧
      (oracle P).loop n.id old.iteration item = false ∧
      FrameCompletes oracle start last (childPath P n.id none old.iteration) body := by
  have safeStart := head.invariants fs.scope.safe
  have headT := head.append prior
  have scT := fs.scope.persist headT
  have safeT := scT.safe
  have safeNext := preserves_invariants t next _ safeT accepted
  obtain ⟨nodeOld, pathOld, _, _⟩ := prior.input_snapshot safeStart initial old memberInitial memberOld sameOld.symm
  have pathO : old.path = P := pathOld.trans pathInitial
  have nodeO : old.node = n.id := nodeOld.trans nodeInitial
  have nodeT := headT.node P n.id n (fs.scope.node?_of_mem n memberN)
  have active := active_of_iteration_change safeT accepted old j memberOld memberJ sameId (by omega)
  obtain ⟨i', n', found, failed, got, outcomes⟩ := effect_manualRetry t next old.id (transition_of_active accepted active (by simp))
  rw [instance?_of_mem safeT old memberOld] at found
  have sameI := Option.some.inj found
  subst i'
  rw [pathO, nodeO] at got
  have sameN := node?_of_getNode nodeT got
  subst n'
  rcases outcomes with ⟨_, _, leaf, _⟩ | ⟨body', limit', frame, items, loopKind, current, _, outputs,
      child, opened, absent, arity, view, instances, frames, _⟩
  · rw [kind] at leaf; cases leaf
  · obtain ⟨bodyEq, limitEq⟩ := NodeKind.loop.inj (loopKind.symm.trans kind)
    subst body' limit'
    obtain ⟨preFail, postFail, u, u', a, b, _, beforeFail, allowedFail, acceptedFail, afterFail,
      memberA, memberB, idA, idB, pathA, nodeA, _, _, activeFail⟩ :=
      loop_failure_event oracle head prior fs n memberN body limit kind initial memberInitial pathInitial nodeInitial
        (by rw [waiting]; decide) old memberOld sameOld failed
    have safeU := beforeFail.invariants safeStart
    have target : opTarget u (.loopIterate a.id false) = some (P, n.id) := by
      simp [opTarget, instance?_of_mem safeU a memberA, pathA, nodeA]
    have failureToT : ConformingSteps (fun s op => oracleConforms oracle s op = true) u (.loopIterate a.id false :: postFail) t :=
      .cons allowedFail acceptedFail afterFail
    have toLast : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (.manualRetry old.id :: post) last :=
      .cons allowed accepted rest
    obtain ⟨observed, bodyFrame, item, foundA, _, _, _, _, _, memberBodyFrame, pathBodyFrame, graphBodyFrame,
      _, bodyResult, exitsLast, decision⟩ :=
      loop_body_step oracle fs (head.append beforeFail) allowedFail acceptedFail (afterFail.append toLast)
        activeFail n memberN body limit kind target
    rw [instance?_of_mem safeU a memberA] at foundA
    have sameA := Option.some.inj foundA
    subst observed
    have low := (beforeFail.iteration_evolves safeStart initial memberInitial a memberA idA).1
    have high := (failureToT.iteration_evolves safeU a memberA old memberOld (sameOld.trans idA.symm)).1
    have iterationA : a.iteration = old.iteration := by omega
    have validBody := g.validateNode_child n body (.inl ⟨limit, kind⟩) (fs.scope.checked n memberN)
    have scopeAtT := Scope.child failureToT scT bodyFrame memberBodyFrame (by rw [graphBodyFrame]; exact validBody)
    have exitsT := exitItems_of_bodyResults failureToT safeU bodyFrame [item] bodyResult scopeAtT
    simp only [pathBodyFrame, graphBodyFrame, List.map_cons, List.map_nil, iterationA] at exitsT
    obtain ⟨idOld, _, _, witness, memberWitness, pathWitness, graphWitness, _⟩ :=
      loop_instance_shape oracle headT fs n memberN body limit kind old memberOld pathO nodeO (by rw [failed]; decide)
    obtain ⟨memberFrame, pathFrame⟩ := currentFrame_spec t old frame current
    have sameFrame := eq_of_mapped_nodup Frame.path t.frames scT.distinct frame witness memberFrame memberWitness
      (pathFrame.trans pathWitness.symm)
    subst witness
    have bodyPath : frame.path = childPath P n.id none old.iteration := by rw [pathFrame, pathO, idOld]; rfl
    have nilRun : ConformingSteps (fun s op => oracleConforms oracle s op = true) t [] t := .nil t
    have scopeBody := Scope.child nilRun scT frame memberFrame (by rw [graphWitness]; exact validBody)
    have outputItemsEq := exitItems_of_frameOutputItems t frame scopeBody items outputs
    rw [bodyPath, graphWitness, exitsT] at outputItemsEq
    have itemsEq : items = [item] := by
      have lengths := congrArg List.length outputItemsEq
      simp only [List.length_cons, List.length_nil, List.length_map] at lengths
      obtain ⟨value, singleton⟩ := List.length_eq_one_iff.mp lengths.symm
      rw [singleton] at outputItemsEq
      have valueEq : item = value := by simpa using outputItemsEq
      rw [singleton, valueEq]
    have updated : {old with
        status := .waitingInputs
        extraIterations := old.extraIterations + 1
        iteration := old.iteration + 1} ∈ next.instances := by
      rw [instances]
      exact setInstance_self_mem t old _ memberOld rfl
    have sameJ := unique_instance safeNext updated memberJ sameId.symm
    have statusJ : j.status = .waitingInputs := by rw [← sameJ]
    obtain ⟨pathChild, graphChild, _, _⟩ := opened
    have childPathEq : child.path = childPath P n.id none j.iteration := by
      rw [pathChild, pathO, idOld, iteration]
      rfl
    have started := seeded_frameStart safeT scT.layout scT.distinct (headT.frameAncestors fs.scope.safe ancestors)
      (headT.frameOwners fs.scope.safe fs.scope.distinct fs.owners)
      accepted child (by rw [frames]; simp) absent (by rw [graphChild]; exact validBody)
      items (by simpa only [graphChild] using arity) (by simpa only [graphChild] using view)
    refine ⟨item, statusJ, by simpa only [childPathEq, graphChild, itemsEq] using started,
      by simpa only [iterationA] using exitsLast, by simpa only [iterationA] using decision, ?_⟩
    exact ⟨u, preFail, _, bodyFrame, beforeFail, failureToT.append toLast, memberBodyFrame,
      by simpa only [iterationA] using pathBodyFrame, graphBodyFrame, (bodyResults_spec u bodyFrame [item] bodyResult).1⟩

theorem loop_eval_active (oracle : ScopedOracle) {s0 start last : State} {headOps ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (fs : FrameStart s0 P g inputs0) (ancestors : FrameAncestors s0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 headOps start)
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) start ops last)
    (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (bodyAdequacy : FrameAdequacy oracle body)
    (i j : Instance) (memberI : i ∈ start.instances) (waiting : i.status = .waitingInputs)
    (pathI : i.path = P) (nodeI : i.node = n.id) (memberJ : j ∈ last.instances)
    (sameId : j.id = i.id) (succeeded : j.status = .succeeded) (input : ItemId)
    (bodyStart : FrameStart start (childPath P n.id none i.iteration) body (bodyInputs body [input])) :
    LoopEval oracle body P n.id i.iteration input
      ((exitItems last (childPath P n.id none j.iteration) body).flatten.headD "")
      (loopChannels last P n.id i.iteration (j.iteration - i.iteration + 1)) := by
  have safeStart := head.invariants fs.scope.safe
  have ancestorsStart := head.frameAncestors fs.scope.safe ancestors
  have bound := (run.iteration_evolves safeStart i memberI j memberJ sameId).1
  by_cases sameIteration : j.iteration = i.iteration
  · obtain ⟨pre, post, t, t', a, b, _, before, allowed, accepted, after, memberA, memberB, idA, idB,
      pathA, nodeA, _, _, active⟩ :=
      loop_success_event oracle head run fs n memberN body limit kind i memberI pathI nodeI
        (by rw [waiting]; decide) j memberJ sameId succeeded
    have safeT := before.invariants safeStart
    have tail : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (.loopIterate a.id true :: post) last :=
      .cons allowed accepted after
    have lower := (before.iteration_evolves safeStart i memberI a memberA idA).1
    have upper := (tail.iteration_evolves safeT a memberA j memberJ (sameId.trans idA.symm)).1
    have iterationA : a.iteration = i.iteration := by omega
    have target : opTarget t (.loopIterate a.id true) = some (P, n.id) := by
      simp [opTarget, instance?_of_mem safeT a memberA, pathA, nodeA]
    obtain ⟨observed, f, item, found, _, _, _, _, _, memberF, pathF, graphF, _, results, exits, decision⟩ :=
      loop_body_step oracle fs (head.append before) allowed accepted after active n memberN body limit kind target
    rw [instance?_of_mem safeT a memberA] at found
    have same := Option.some.inj found
    subst observed
    rw [iterationA] at pathF exits decision
    have complete : FrameCompletes oracle start last (childPath P n.id none i.iteration) body :=
      ⟨t, pre, _, f, before, tail, memberF, pathF, graphF, (bodyResults_spec t f [item] results).1⟩
    have child := bodyAdequacy start last ops _ _ bodyStart ancestorsStart run complete finished
    have result : LoopEval oracle body P n.id i.iteration input item
        (subtreeBags last (childPath P n.id none i.iteration)) :=
      .stop child exits decision
    simpa [sameIteration, exits, loopChannels] using result
  · have later : i.iteration < j.iteration := by omega
    obtain ⟨pre, op, post, t, t', a, b, schedule, before, allowed, accepted, after, safeT,
      memberA, memberB, idA, idB, bindingA, notA, yesB, evolution⟩ :=
      run.reached safeStart (fun k => i.iteration < k.iteration) i memberI (by omega) j memberJ sameId later
    have lower := (before.iteration_evolves safeStart i memberI a memberA idA).1
    have iterationA : a.iteration = i.iteration := by omega
    have pathA := (Instance.binding_path bindingA).trans pathI
    have nodeA := (Instance.binding_node bindingA).trans nodeI
    rcases evolution.1 with unchanged | ⟨increment, operation, _⟩
    · omega
    · have iterationB : b.iteration = i.iteration + 1 := by omega
      have safeNext := preserves_invariants t t' op safeT accepted
      have one : ConformingSteps (fun s op => oracleConforms oracle s op = true) t [op] t' := .cons allowed accepted (.nil t')
      obtain ⟨nodeB, pathB, _, _⟩ := one.input_snapshot safeT a b memberA memberB (idA.trans idB.symm)
      have headNext := head.append (before.append one)
      have continuation : ∃ item, b.status = .waitingInputs ∧
          FrameStart t' (childPath P n.id none b.iteration) body (bodyInputs body [item]) ∧
          exitItems last (childPath P n.id none i.iteration) body = [[item]] ∧
          (oracle P).loop n.id i.iteration item = false ∧
          FrameCompletes oracle start last (childPath P n.id none i.iteration) body := by
        rcases operation with ⟨_, opEq⟩ | ⟨_, opEq⟩
        · subst op
          obtain ⟨item, statusB, startB, exits, decision⟩ :=
            loop_continue_birth oracle fs ancestors (head.append before) a b allowed accepted after n memberN body limit kind
              memberA memberB (idB.trans idA.symm) pathA nodeA increment
          have active := active_of_iteration_change safeT accepted a b memberA memberB (idB.trans idA.symm) (by omega)
          have target : opTarget t (.loopIterate a.id false) = some (P, n.id) := by
            simp [opTarget, instance?_of_mem safeT a memberA, pathA, nodeA]
          obtain ⟨observed, f, value, found, _, _, _, _, _, memberF, pathF, graphF, _, results, _, _⟩ :=
            loop_body_step oracle fs (head.append before) allowed accepted after active n memberN body limit kind target
          rw [instance?_of_mem safeT a memberA] at found
          have same := Option.some.inj found
          subst observed
          refine ⟨item, statusB, startB, by simpa only [iterationA] using exits,
            by simpa only [iterationA] using decision, ?_⟩
          exact ⟨t, pre, _, f, before, .cons allowed accepted after, memberF,
            by simpa only [iterationA] using pathF, graphF, (bodyResults_spec t f [value] results).1⟩
        · subst op
          obtain ⟨item, statusB, startB, exits, decision, complete⟩ :=
            loop_retry_birth oracle fs ancestors head before n memberN body limit kind i a b memberI waiting pathI nodeI
              memberA idA iterationA memberB (idB.trans idA.symm) increment allowed accepted after
          exact ⟨item, statusB, startB, by simpa only [iterationA] using exits,
            by simpa only [iterationA] using decision, by simpa only [iterationA] using complete⟩
      obtain ⟨item, statusB, startB, exits, decision, complete⟩ := continuation
      have child := bodyAdequacy start last ops _ _ bodyStart ancestorsStart run complete finished
      have tail := loop_eval_active oracle fs ancestors headNext after finished n memberN body limit kind bodyAdequacy
        b j memberB statusB (pathB.trans pathA) (nodeB.trans nodeA) memberJ (sameId.trans idB.symm) succeeded item startB
      have tailLength : j.iteration - b.iteration + 1 = j.iteration - i.iteration := by omega
      rw [tailLength, iterationB] at tail
      exact .next child exits decision tail
termination_by j.iteration - i.iteration
decreasing_by omega

end Suimon
