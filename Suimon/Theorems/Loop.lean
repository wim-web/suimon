import Suimon.Theorems.ForEach

namespace Suimon
open Semantics Effects

def CurrentBody (s : State) (i : Instance) (body : Graph) : Prop :=
  ∃ f ∈ s.frames, f.path = i.path ++ [identity [i.id, toString i.iteration]] ∧
    f.graph = body ∧ f.owner = some i.id

theorem CurrentBody.persist_same {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s)
    (i j : Instance) (memberI : i ∈ s.instances) (memberJ : j ∈ last.instances)
    (sameId : j.id = i.id) (iteration : j.iteration = i.iteration) (body : Graph)
    (current : CurrentBody s i body) : CurrentBody last j body := by
  obtain ⟨f, memberF, pathF, graphF, ownerF⟩ := current
  obtain ⟨_, pathJ, _, _⟩ := run.input_snapshot safe i j memberI memberJ sameId.symm
  have retained : f.definitionView ∈ last.frameDefinitions :=
    run.frameDefinitions.subset (List.mem_map.mpr ⟨f, memberF, rfl⟩)
  obtain ⟨h, memberH, viewH⟩ := List.mem_map.mp retained
  have pathH : h.path = f.path := by simpa [Frame.definitionView] using congrArg Frame.path viewH
  have graphH : h.graph = f.graph := by simpa [Frame.definitionView] using congrArg Frame.graph viewH
  have ownerH : h.owner = f.owner := by simpa [Frame.definitionView] using congrArg Frame.owner viewH
  exact ⟨h, memberH, by rw [pathH, pathF, pathJ, sameId, iteration], graphH.trans graphF,
    by rw [ownerH, ownerF, sameId]⟩

theorem active_of_iteration_change {s next : State} {op : Op} (safe : Invariants s)
    (accepted : step s op = .ok next) (i j : Instance) (memberI : i ∈ s.instances)
    (memberJ : j ∈ next.instances) (sameId : j.id = i.id) (changed : j.iteration ≠ i.iteration) :
    absorbed s op = false := by
  cases active : absorbed s op with
  | false => rfl
  | true =>
    rcases step_ok_cases s op next accepted with ⟨_, same⟩ | ⟨no, _⟩
    · subst next
      exact False.elim (changed (congrArg Instance.iteration (unique_instance safe memberJ memberI sameId)))
    · rw [active] at no; contradiction

theorem step_currentBody (s next : State) (op : Op) (safe : Invariants s)
    (accepted : step s op = .ok next) (i j : Instance) (memberI : i ∈ s.instances)
    (memberJ : j ∈ next.instances) (sameId : j.id = i.id)
    (n : Node) (body : Graph) (limit : Nat) (node : s.node? i.path i.node = some n)
    (kind : n.kind = .loop body limit) (current : CurrentBody s i body) : CurrentBody next j body := by
  have safeNext := preserves_invariants s next op safe accepted
  have one : ConformingSteps (fun _ _ => True) s [op] next := .cons trivial accepted (.nil next)
  obtain ⟨nodeJ, pathJ, _, _⟩ := one.input_snapshot safe i j memberI memberJ sameId.symm
  rcases (step_instance_evolves s next op safe accepted i j memberI memberJ sameId).1 with same | ⟨iteration, event, _⟩
  · exact current.persist_same one safe i j memberI memberJ sameId same body
  · have active := active_of_iteration_change safe accepted i j memberI memberJ sameId (by omega)
    rcases event with ⟨_, opEq⟩ | ⟨_, opEq⟩
    · subst op
      have executed := transition_of_active accepted active (by simp)
      obtain ⟨i', n', body', limit', f, items, item, found, _, got, kind', _, _, _, _, outcomes⟩ :=
        effect_loopIterate s next i.id false executed
      rw [instance?_of_mem safe i memberI] at found
      have sameI := Option.some.inj found
      subst i'
      have sameN := node?_of_getNode node got
      subst n'
      have kinds := NodeKind.loop.inj (kind'.symm.trans kind)
      obtain ⟨bodyEq, limitEq⟩ := kinds
      subst body' limit'
      rcases outcomes with done | blocked | continuing
      · exact Bool.noConfusion done.1
      · obtain ⟨_, _, _, instances, _⟩ := blocked
        have memberUpdated : { i with status := .failed } ∈ next.instances := by
          rw [instances]
          exact setInstance_self_mem s i _ memberI rfl
        have same := unique_instance safeNext memberUpdated memberJ sameId.symm
        have unchanged : i.iteration = j.iteration := by simpa only using congrArg Instance.iteration same
        omega
      · obtain ⟨_, _, f', opened, _, _, _, _, frames⟩ := continuing
        obtain ⟨pathF, graphF, ownerF, _⟩ := opened
        exact ⟨f', by rw [frames]; simp, by rw [pathF, pathJ, sameId, iteration], graphF,
          by rw [ownerF, sameId]⟩
    · subst op
      have executed := transition_of_active accepted active (by simp)
      obtain ⟨i', n', found, _, got, leaf | ⟨body', limit', _, _, kind', _, _, _, f', opened, _, _, _, _, frames, _⟩⟩ :=
        effect_manualRetry s next i.id executed
      all_goals
        rw [instance?_of_mem safe i memberI] at found
        have sameI := Option.some.inj found
        subst i'
        have sameN := node?_of_getNode node got
        subst n'
      · obtain ⟨_, _, leafKind, _⟩ := leaf
        rw [kind] at leafKind; cases leafKind
      · have kinds := NodeKind.loop.inj (kind'.symm.trans kind)
        obtain ⟨bodyEq, limitEq⟩ := kinds
        subst body' limit'
        obtain ⟨pathF, graphF, ownerF, _⟩ := opened
        exact ⟨f', by rw [frames]; simp, by rw [pathF, pathJ, sameId, iteration], graphF,
          by rw [ownerF, sameId]⟩

theorem ConformingSteps.currentBody {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s)
    (i j : Instance) (memberI : i ∈ s.instances) (memberJ : j ∈ last.instances) (sameId : j.id = i.id)
    (n : Node) (body : Graph) (limit : Nat) (node : s.node? i.path i.node = some n)
    (kind : n.kind = .loop body limit) (current : CurrentBody s i body) : CurrentBody last j body := by
  induction run generalizing i with
  | nil =>
    have same := unique_instance safe memberJ memberI sameId
    simpa [same] using current
  | @cons s middle last op ops allowed accepted tail ih =>
    have one : ConformingSteps allows s [op] middle := .cons allowed accepted (.nil middle)
    obtain ⟨k, memberK, bindingK⟩ := one.retains_binding safe i memberI
    have idK : k.id = i.id := congrArg Prod.fst bindingK
    have pathK : k.path = i.path := Instance.binding_path bindingK
    have nodeK : k.node = i.node := Instance.binding_node bindingK
    have currentK := step_currentBody s middle op safe accepted i k memberI memberK idK n body limit node kind current
    have foundK : middle.node? k.path k.node = some n := by
      rw [pathK, nodeK]
      exact one.node _ _ n node
    exact ih (preserves_invariants s middle op safe accepted) k memberK memberJ (sameId.trans idK.symm) foundK currentK

theorem loop_instance_origin (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat)
    (kind : n.kind = .loop body limit) (i : Instance) (memberI : i ∈ last.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) (notCancelled : i.status ≠ .cancelled) :
    ∃ pre post u u' inputs, ops = pre ++ .activate P n.id :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre u ∧
      oracleConforms oracle u (.activate P n.id) = true ∧ step u (.activate P n.id) = .ok u' ∧
      transition u (.activate P n.id) = .ok u' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) u' post last ∧
      getNode u P n.id = .ok n ∧ plainInputs u P n = .ok inputs ∧
      let j := { makeInstance P n .waitingInputs inputs with iteration := 1 }
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
    · rw [kind] at sub; cases sub
    · subst iteration op
      have executed := transition_of_created accepted (by simp) j memberJ absentU
      rw [eq] at memberJ idJ bindJ
      exact ⟨pre, post, u, u', inputs, schedule, head, allowed, accepted, executed, rest, hn, hi, memberJ, idJ, bindJ⟩
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

theorem loop_instance_shape (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat)
    (kind : n.kind = .loop body limit) (i : Instance) (memberI : i ∈ last.instances)
    (pathI : i.path = P) (nodeI : i.node = n.id) (notCancelled : i.status ≠ .cancelled) :
    i.id = instanceId P n.id none ∧ i.trigger = none ∧ 1 ≤ i.iteration ∧ CurrentBody last i body := by
  obtain ⟨pre, post, u, u', inputs, _, head, allowed, accepted, executed, rest, hn, hi, memberJ, idJ, bindJ⟩ :=
    loop_instance_origin oracle run fs n memberN body limit kind i memberI pathI nodeI notCancelled
  let j := { makeInstance P n .waitingInputs inputs with iteration := 1 }
  have safeU := head.invariants fs.scope.safe
  have safeU' := preserves_invariants u u' _ safeU accepted
  have nodeU : u.node? P n.id = some n := getNode_node? u P n.id n hn
  obtain ⟨_, n', inputs', got, plain, leaf | ⟨body', iteration, kinds, f, opened, _, _, _, _, frames, _⟩⟩ :=
    effect_activate u u' P n.id executed
  all_goals
    have sameN := node?_of_getNode nodeU got
    subst n'
  · obtain ⟨_, _, leafKind, _⟩ := leaf
    rw [kind] at leafKind; cases leafKind
  · have inputsEq : inputs' = inputs := Except.ok.inj (plain.symm.trans hi)
    subst inputs'
    rcases kinds with ⟨sub, _⟩ | ⟨m, loop, iterationEq⟩
    · rw [kind] at sub; cases sub
    · subst iteration
      have bodies := (NodeKind.loop.inj (loop.symm.trans kind)).1
      subst body'
      obtain ⟨pathF, graphF, ownerF, _⟩ := opened
      have startFrame : CurrentBody u' j body := ⟨f, by rw [frames]; simp, pathF, graphF, ownerF⟩
      have nodeU' : u'.node? j.path j.node = some n :=
        retained_node u u' P n.id n (step_frameDefinitions u u' _ accepted) nodeU
      exact ⟨idJ.symm, (Instance.binding_trigger bindJ).symm,
        (rest.iteration_evolves safeU' j memberJ i memberI idJ.symm).1,
        rest.currentBody safeU' j i memberJ memberI idJ.symm n body limit nodeU' kind startFrame⟩

theorem nodeInstance?_of_mem {s : State} (safe : Invariants s) (i : Instance) (member : i ∈ s.instances)
    (trigger : i.trigger = none) : s.nodeInstance? i.path i.node = some i := by
  have keys : (s.instances.map instanceKey).Nodup := by
    simp only [Invariants, invariants, Bool.and_eq_true] at safe
    exact unique_nodup _ safe.1.1.1.1.2
  have present : (s.nodeInstance? i.path i.node).isSome :=
    List.find?_isSome.mpr ⟨i, member, by simp [trigger]⟩
  cases found : s.nodeInstance? i.path i.node with
  | none => rw [found] at present; contradiction
  | some j =>
    obtain ⟨memberJ, pathJ, nodeJ, triggerJ⟩ := nodeInstance?_mem found
    have same := eq_of_mapped_nodup instanceKey s.instances keys j i memberJ member (by simp [instanceKey, pathJ, nodeJ, triggerJ, trigger])
    subst j
    rfl

theorem loop_success_step (oracle : ScopedOracle) {s0 t t' last : State} {pre post : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} {inst : InstanceId} (fs : FrameStart s0 P g inputs0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t)
    (allowed : oracleConforms oracle t (.loopIterate inst true) = true)
    (accepted : step t (.loopIterate inst true) = .ok t')
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last)
    (active : absorbed t (.loopIterate inst true) = false)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (target : opTarget t (.loopIterate inst true) = some (P, n.id)) :
    ∃ item q, n.outputs.head? = some q ∧
      t'.placedView = (applyWrites (.out P n.id q.name (.item item) :: eosWrites P n) t).placedView ∧
      exitItems last (childPath P n.id none (loopCount last P n.id)) body = [[item]] ∧
      (oracle P).loop n.id (loopCount last P n.id) item = true ∧
      ∃ i ∈ last.instances, i.path = P ∧ i.node = n.id ∧ i.status = .succeeded := by
  have safeT := head.invariants fs.scope.safe
  have safeT' := preserves_invariants t t' _ safeT accepted
  have full : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (.loopIterate inst true :: post) last :=
    .cons allowed accepted rest
  have scL := fs.scope.persist (head.append full)
  obtain ⟨i, n', body', limit', f, items, item, foundI, waiting, got, loopKind, current, results, headItem, _, outcomes⟩ :=
    effect_loopIterate t t' inst true (transition_of_active accepted active (by simp))
  obtain ⟨i', foundI', pathI, nodeI⟩ := opTarget_id (inst := inst) rfl target
  rw [foundI] at foundI'
  have ii := Option.some.inj foundI'
  subst i'
  rw [pathI, nodeI] at got
  have nodeT := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  have sameN := node?_of_getNode nodeT got
  subst n'
  have kinds := NodeKind.loop.inj (loopKind.symm.trans kind)
  obtain ⟨bodyEq, limitEq⟩ := kinds
  subst body' limit'
  rcases outcomes with ⟨_, q, headQ, view, instances, _⟩ | ⟨bad, _⟩ | ⟨bad, _⟩
  · obtain ⟨idI, triggerI, _, f0, memberF0, pathF0, graphF0, ownerF0⟩ :=
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
    have memberUpdated : { i with status := .succeeded } ∈ t'.instances := by
      rw [instances]
      exact setInstance_self_mem t i _ (instance?_mem foundI) rfl
    obtain ⟨iL, memberIL, idIL, statusIL⟩ := rest.retains_status safeT' _ memberUpdated (.inl rfl)
    obtain ⟨nodeIL, pathIL, triggerIL, _⟩ := rest.input_snapshot safeT' _ iL memberUpdated memberIL idIL.symm
    have iterIL := rest.iteration_of_succeeded safeT' _ memberUpdated rfl iL memberIL idIL
    have lookup := nodeInstance?_of_mem scL.safe iL memberIL (triggerIL.trans triggerI)
    rw [pathIL, nodeIL, pathI, nodeI] at lookup
    have count : loopCount last P n.id = i.iteration := by simp [loopCount, lookup, iterIL]
    have conf : (oracle P).loop n.id i.iteration item = true := by
      have output := (bodyResults_spec t f items results).2
      simp only [oracleConforms, active, Bool.false_eq_true, ↓reduceIte, foundI, current,
        Except.toOption, Option.bind_some, output, headItem, Option.any_some, pathI, nodeI] at allowed
      simpa using allowed
    refine ⟨item, q, headQ, by simpa [pathI] using view, ?_, by rw [count]; exact conf,
      iL, memberIL, pathIL.trans pathI, nodeIL.trans nodeI, statusIL⟩
    simpa [pathChild, graphF0, itemsEq, count] using exits
  all_goals cases bad

theorem seed_step_untouched {s next : State} (f : Frame) (items : List ItemId)
    (view : next.placedView = (applyWrites (seedWrites f.path f.graph.entries items)
      { s with channels := s.channels ++ f.channels }).placedView) (safeNext : Invariants next)
    (c : Channel) (member : c ∈ s.channels) (entry : c.entry = false) :
    ∃ d ∈ next.channels, d.core = c.core := by
  have distinct := StepView.base_distinct f.channels _ view safeNext
  have inBase : c ∈ ({s with channels := s.channels ++ f.channels} : State).channels := List.mem_append_left _ member
  have unchanged := applyWrites_untouched _ _ c inBase distinct entry (by
    intro w memberW token equal
    have impossible := seedWrites_target f.path f.graph.entries items none w memberW c.path c.edge.src.node c.edge.src.port token equal
    cases impossible)
  have inView : c.core ∈ next.placedView := by rw [view]; exact placedView_member unchanged
  exact List.mem_map.mp inView

theorem loop_false_untouched (s next : State) (inst : InstanceId) (safe : Invariants s)
    (accepted : step s (.loopIterate inst false) = .ok next) (active : absorbed s (.loopIterate inst false) = false)
    (c : Channel) (member : c ∈ s.channels) (entry : c.entry = false) :
    ∃ d ∈ next.channels, d.core = c.core := by
  have safeNext := preserves_invariants s next _ safe accepted
  obtain ⟨_, _, _, _, _, _, item, _, _, _, _, _, _, _, _, outcomes⟩ :=
    effect_loopIterate s next inst false (transition_of_active accepted active (by simp))
  rcases outcomes with ⟨bad, _⟩ | ⟨_, _, view, _⟩ | ⟨_, _, f, opened, _, _, view, _⟩
  · cases bad
  · have inView : c.core ∈ next.placedView := by rw [view]; exact placedView_member member
    exact List.mem_map.mp inView
  · have graphF := opened.2.1
    exact seed_step_untouched f [item] (by simpa only [graphF] using view) safeNext c member entry

theorem loop_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (limit : Nat) (kind : n.kind = .loop body limit)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have safe0 := fs.scope.safe
  have scL := fs.scope.persist run
  have checked := fs.scope.checked n memberN
  have names := (g.validate_port_names n checked).2
  have shape := g.validateNode_shape n checked
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
  have plainIn : allKind n.inputs .plain = true := by grind only []
  have plainOut : allKind n.outputs .plain = true := by grind only []
  have oneOutput : n.outputs.length = 1 := by grind only []
  obtain ⟨q, memberQ, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  have qPlain : q.kind = .plain := by simpa using List.all_eq_true.mp plainOut q memberQ
  have plainC : c.kind = .plain := kindC.trans qPlain
  obtain ⟨c0, member0, id0, edge0, path0, entry0, _, _, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have absent : Token.eos ∉ c0.placed := by simp [empty0]
  have present : Token.eos ∈ c.placed := by simpa [Channel.closed] using closed_of_drained finished memberC
  obtain ⟨pre, op, post, t, t', d, d', _, head, allowed, accepted, rest, safeT, active,
    memberD, idD, layoutD, absentD, memberD', idD', _, presentD', _, target⟩ :=
    token_step run safe0 .eos c0 member0 absent (entry0.trans entryC) c memberC id0.symm present
  have safeT' := preserves_invariants t t' op safeT accepted
  have nodeT := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  obtain ⟨_, edgeD, pathD, entryD, _, _⟩ := Channel.layout_fields layoutD
  rw [path0, pathC, edge0, srcC] at target
  rcases target_shape t t' op safeT active accepted P n.id target n nodeT with
      ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
    | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, kinds⟩ | ⟨inst, done, _, _, eq, _⟩ | ⟨eq, _⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; simp at k
  · rcases kinds with sub | each <;> (rw [kind] at *; contradiction)
  · subst op
    cases done with
    | false =>
      obtain ⟨e, memberE, coreE⟩ := loop_false_untouched t t' inst safeT accepted active d memberD (entryD.trans (entry0.trans entryC))
      have idE : e.id = d.id := by simpa only [Channel.core_id] using congrArg Channel.id coreE
      have same := unique_channel safeT' memberE memberD' (idE.trans (idD.trans idD'.symm))
      have placed : e.placed = d.placed := by simpa only [Channel.core_placed] using congrArg Channel.placed coreE
      rw [same] at placed
      exact False.elim (absentD (placed ▸ presentD'))
    | true =>
      obtain ⟨item, q', headQ, view, exits, _, i, memberI, pathI, nodeI, statusI⟩ :=
        loop_success_step oracle fs head allowed accepted rest active n memberN body limit kind target
      have sameQ := head_of_singleton oneOutput headQ memberQ
      subst q'
      obtain ⟨values, _, channels⟩ := plain_instance_inputs oracle run fs n memberN
        (.inr (.inr (.inr (.inr ⟨body, limit, kind⟩)))) i memberI pathI nodeI statusI
      have inputValues := stateInputs_of_singletons scL n memberN values channels
      have notSup : suppressed n (stateInputs last P n) = false := by
        rw [inputValues]
        exact suppressed_singletons n values (by rw [kind]; simp)
      have valueEq : nodeValue oracle last g P n = compoundValue last P n := by
        unfold nodeValue primitive
        rw [notSup]
        simp only [kind, Bool.false_eq_true, ↓reduceIte]
      have emitted : item ∈ c.items := by
        apply written_item_final rest safeT safeT' _ view d memberD (entryD.trans (entry0.trans entryC))
          c memberC (id0.symm.trans idD.symm) item
        rw [pathD, path0, pathC, edgeD, edge0, srcC, portC]
        exact List.mem_cons_self
      have singleton := plain_items_singleton c (channelOK_of_invariants scL.safe memberC) plainC item emitted
      rw [valueEq]
      simp only [compoundValue, kind, exits]
      rw [portC, outputItems_ports n names _ q memberQ]
      simp [bag, singleton, canonical_idem, canonical_singleton]
  · subst op
    have closedD' : d'.closed = true := by simpa [Channel.closed] using presentD'
    obtain ⟨emptyC, _, din, memberDin, pathDin, exitDin, nodeDin, _, emptyDin⟩ :=
      skip_closing_final oracle head allowed accepted rest safe0 safeT active n (fs.scope.node?_of_mem n memberN) (by rw [kind]; simp)
        c0 member0 empty0 (entry0.trans entryC) (path0.trans pathC) (by rw [edge0]; exact srcC)
        d memberD idD d' memberD' idD' closedD' c memberC id0.symm
    have sup := suppressed_of_empty scL n memberN plainIn (by rw [kind]; simp)
      din memberDin pathDin exitDin nodeDin emptyDin
    rw [nodeValue_suppressed oracle last g P n sup, portC, outputItems_ports n names _ q memberQ]
    simp [bag, emptyC]

end Suimon
