import Suimon.Theorems.Compound

namespace Suimon
open Semantics Effects

theorem forEach_ports {s : State} {P : Path} {g : Graph} (sc : Scope s P g)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body) :
    ∃ p q, n.inputs = [p] ∧ n.outputs = [q] ∧ p.kind = .stream := by
  have shape := g.validateNode_shape n (sc.checked n memberN)
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
  have lenIn : n.inputs.length = 1 := by grind only []
  have lenOut : n.outputs.length = 1 := by grind only []
  obtain ⟨p, input⟩ := List.length_eq_one_iff.mp lenIn
  obtain ⟨q, output⟩ := List.length_eq_one_iff.mp lenOut
  have stream : allKind n.inputs .stream = true := by grind only []
  exact ⟨p, q, input, output, by simpa [allKind, input] using stream⟩

/-- Every consumed ForEach input was consumed by a spawn, which records that
    very item as the new instance's trigger. --/
theorem forEach_input_spawn (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (input : Channel) (memberIn : input ∈ last.channels) (pathIn : input.path = P) (exitIn : input.exit = false)
    (nodeIn : input.edge.dst.node = n.id) (drained : input.pendingItems = []) (y : ItemId) (present : y ∈ input.items) :
    ∃ pre post t t', ops = pre ++ .spawn P n.id y :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t ∧
      oracleConforms oracle t (.spawn P n.id y) = true ∧ step t (.spawn P n.id y) = .ok t' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last ∧
      Invariants t ∧ transition t (.spawn P n.id y) = .ok t' ∧
      (makeInstance P n .waitingInputs [("item", y)] (some y)) ∈ t'.instances := by
  have safe0 := fs.scope.safe
  have safeLast := run.invariants safe0
  obtain ⟨p, q, ins, outs, stream⟩ := forEach_ports fs.scope n memberN body kind
  have notPlain := allKind_plain_false_of_stream n.inputs p (by simp [ins]) stream
  obtain ⟨r, memberR, channelR, itemR⟩ := safeLast.drained_item_receipt input memberIn drained y present
  obtain ⟨in0, memberIn0, idIn0, edgeIn0, pathIn0, entryIn0, exitIn0, kindIn0, _⟩ := fs.origin run input memberIn pathIn
  have absent0 : r ∉ s0.consumed := fun h =>
    fs.noRecords0 r h in0 memberIn0 (pathIn0.trans pathIn) (exitIn0.trans exitIn) (channelR.trans idIn0.symm)
  obtain ⟨pre, op, post, t, t', splitRun, head, allowed, accepted, rest, safeT, absentT, presentT, origin⟩ :=
    record_origin run safe0 r memberR absent0
  have changed : ∃ r' ∈ t'.consumed, r' ∉ t.consumed := ⟨r, presentT, absentT⟩
  have nodeT := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  obtain ⟨inT, memberInT, idInT, layoutInT, _⟩ := run_image head safe0 in0 memberIn0
  obtain ⟨_, edgeInT, pathInT, _, exitInT, _⟩ := Channel.layout_fields layoutInT
  rcases origin with ⟨P', N', incoming, shapes⟩ | ⟨inst, i, f, foundI, hf, shapes, inExit⟩
  · obtain ⟨d, memberD, idD⟩ := List.mem_map.mp incoming
    have fields := (List.mem_filter.mp memberD).2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
    have same : d = inT := unique_channel safeT (List.mem_filter.mp memberD).1 memberInT
      (idD.trans (channelR.trans (idIn0.symm.trans idInT.symm)))
    subst d
    have peq : P' = P := fields.1.1.symm.trans (pathInT.trans (pathIn0.trans pathIn))
    have neq : N' = n.id := fields.2.symm.trans (by rw [edgeInT, edgeIn0]; exact nodeIn)
    subst P' N'
    rcases shapes with eq | ⟨x, eq, item⟩ | eq | ⟨arm, eq⟩ | eq | ⟨e, x, eq, _, _⟩ | ⟨x, keep, eq, _⟩
      | ⟨e, x, eq, _, _⟩ | eq | eq
    · subst op
      have executed := transition_of_record accepted (by simp) changed
      obtain ⟨_, m, _, got, _, cases⟩ := effect_activate t t' P n.id executed
      have sameN := node?_of_getNode nodeT got
      subst m
      rcases cases with ⟨_, _, k, _⟩ | ⟨_, _, ⟨k, _⟩ | ⟨_, k, _⟩, _⟩ <;> (rw [kind] at k; cases k)
    · have xy : x = y := item.symm.trans itemR
      rw [xy] at eq
      subst op
      have executed := transition_of_record accepted (by simp) changed
      obtain ⟨_, m, _, _, got, _, _, _, _, _, _, _, _, instances, _⟩ := effect_spawn t t' P n.id y safeT.channelIds executed
      have sameN := node?_of_getNode nodeT got
      subst m
      exact ⟨pre, post, t, t', splitRun, head, allowed, accepted, rest, safeT, executed, by rw [instances]; simp⟩
    · subst op
      obtain ⟨m, _, got, k, _⟩ := effect_fireWaitAll t t' P n.id (transition_of_record accepted (by simp) changed)
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at k; cases k
    · subst op
      obtain ⟨m, _, _, _, got, k, _⟩ := effect_fireBranch t t' P n.id arm (transition_of_record accepted (by simp) changed)
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at k; cases k
    · subst op
      obtain ⟨m, _, got, k, _⟩ := effect_fireCollect t t' P n.id (transition_of_record accepted (by simp) changed)
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at k; cases k
    · subst op
      obtain ⟨m, _, _, got, k, _⟩ := effect_fireCoalesce t t' P n.id e x safeT.channelIds (transition_of_record accepted (by simp) changed)
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at k; cases k
    · subst op
      obtain ⟨m, _, got, k, _⟩ := effect_fireFilter t t' P n.id x keep safeT.channelIds (transition_of_record accepted (by simp) changed)
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at k; cases k
    · subst op
      obtain ⟨m, _, _, got, k, _⟩ := effect_fireMerge t t' P n.id e x safeT.channelIds (transition_of_record accepted (by simp) changed)
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at k; cases k
    · subst op
      have same := effect_propagateEos_records t t' P n.id safeT (transition_of_record accepted (by simp) changed)
      rw [same] at presentT
      exact absurd presentT absentT
    · subst op
      obtain ⟨m, got, cond, _⟩ := effect_skip t t' P n.id (transition_of_record accepted (by simp) changed)
      have sameN := node?_of_getNode nodeT got
      subst m
      have plain := (Bool.and_eq_true_iff.mp cond).1
      rw [notPlain] at plain
      contradiction
  · obtain ⟨d, memberD, idD⟩ := List.mem_map.mp inExit
    have fields := (List.mem_filter.mp memberD).2
    simp only [Bool.and_eq_true, beq_iff_eq] at fields
    have same : d = inT := unique_channel safeT (List.mem_filter.mp memberD).1 memberInT
      (idD.trans (channelR.trans (idIn0.symm.trans idInT.symm)))
    subst d
    have notExit : inT.exit = false := exitInT.trans (exitIn0.trans exitIn)
    rw [notExit] at fields
    exact Bool.noConfusion fields.2

/-- Once a ForEach is ready to close, each of its consumed triggers has passed
    through an actual finishSubworkflow transition. --/
theorem forEach_input_finished (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (input : Channel) (memberIn : input ∈ last.channels) (pathIn : input.path = P) (exitIn : input.exit = false)
    (nodeIn : input.edge.dst.node = n.id) (drained : input.pendingItems = [])
    (children : (last.instances.filter (fun i => i.path == P && i.node == n.id && i.trigger.isSome)).all (·.status == .succeeded) = true)
    (y : ItemId) (present : y ∈ input.items) :
    ∃ pre post t t' inst, ops = pre ++ .finishSubworkflow inst :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t ∧
      oracleConforms oracle t (.finishSubworkflow inst) = true ∧ step t (.finishSubworkflow inst) = .ok t' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last ∧
      absorbed t (.finishSubworkflow inst) = false ∧
      opTarget t (.finishSubworkflow inst) = some (P, n.id) ∧
      ((t.instance? inst).bind (·.trigger)) = some y := by
  obtain ⟨pre, post, u, u', schedule, headU, allowedU, acceptedU, restU, safeU, _, memberStart⟩ :=
    forEach_input_spawn oracle run fs n memberN body kind input memberIn pathIn exitIn nodeIn drained y present
  let start := makeInstance P n .waitingInputs [("item", y)] (some y)
  have safeU' := preserves_invariants u u' _ safeU acceptedU
  have safeLast := run.invariants fs.scope.safe
  obtain ⟨j, memberJ, bindingJ⟩ := restU.retains_binding safeU' start memberStart
  have pathJ : j.path = P := Instance.binding_path bindingJ
  have nodeJ : j.node = n.id := Instance.binding_node bindingJ
  have triggerJ : j.trigger = some y := Instance.binding_trigger bindingJ
  have statusJ : j.status = .succeeded := by
    have h := List.all_eq_true.mp children j (List.mem_filter.mpr ⟨memberJ, by simp [pathJ, nodeJ, triggerJ]⟩)
    simpa using h
  obtain ⟨pre2, op, post2, t, t', a, b, split2, head2, allowed, accepted, rest, safeT,
    memberA, memberB, idA, idB, bindingA, notA, yesB, evolution⟩ :=
    restU.reached safeU' (fun i => i.status = .succeeded) start memberStart (by change InstanceStatus.waitingInputs ≠ .succeeded; decide)
      j memberJ (congrArg Prod.fst bindingJ) statusJ
  have pathA : a.path = P := Instance.binding_path bindingA
  have nodeA : a.node = n.id := Instance.binding_node bindingA
  have triggerA : a.trigger = some y := Instance.binding_trigger bindingA
  have headT := headU.append (.cons allowedU acceptedU head2)
  have nodeT := headT.node P n.id n (fs.scope.node?_of_mem n memberN)
  have active := active_of_status_change safeT accepted a memberA b memberB (idB.trans idA.symm)
    (fun same => notA (same ▸ yesB))
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
    rcases reason with ⟨auth, outputs, _, m, r, c, got, leaf⟩ | finish | loop | ⟨_, noTrigger⟩
    · rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at leaf; cases leaf
    · exact finish
    · rw [loop] at accepted active
      have executed := transition_of_active accepted active (by simp)
      obtain ⟨i, m, body', limit, _, _, _, found, _, got, loopKind, _⟩ := effect_loopIterate t t' a.id true executed
      rw [instance?_of_mem safeT a memberA] at found
      have sameA := Option.some.inj found
      subst i
      rw [pathA, nodeA] at got
      have sameN := node?_of_getNode nodeT got
      subst m
      rw [kind] at loopKind; cases loopKind
    · rw [triggerA] at noTrigger; cases noTrigger
  subst op
  refine ⟨pre ++ .spawn P n.id y :: pre2, post2, t, t', a.id, ?_, headT, allowed, accepted, rest, active, ?_, ?_⟩
  · rw [schedule, split2]
    simp only [List.append_assoc, List.cons_append]
  · simp [opTarget, instance?_of_mem safeT a memberA, pathA, nodeA]
  · simp [instance?_of_mem safeT a memberA, triggerA]

theorem bodyWrites_item (P : Path) (n : Node) (items : List ItemId) (w : Write)
    (member : w ∈ bodyWrites P n items) : ∃ x, w.token = .item x := by
  obtain ⟨⟨p, x⟩, _, same⟩ := List.mem_map.mp member
  subst w
  exact ⟨x, rfl⟩

/-- ForEach output EOS can only originate in propagateEos, whose guard checks
    that every trigger has finished and every input is drained. --/
theorem forEach_closing_step (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    ∃ pre post t t', ops = pre ++ .propagateEos P n.id :: post ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t ∧
      oracleConforms oracle t (.propagateEos P n.id) = true ∧ step t (.propagateEos P n.id) = .ok t' ∧
      ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last ∧
      (t.incoming P n.id).all (fun c => c.closed && c.pendingItems.isEmpty) = true ∧
      (t.instances.filter (fun i => i.path == P && i.node == n.id && i.trigger.isSome)).all (·.status == .succeeded) = true := by
  obtain ⟨p, q, ins, _, stream⟩ := forEach_ports fs.scope n memberN body kind
  have notPlain := allKind_plain_false_of_stream n.inputs p (by simp [ins]) stream
  obtain ⟨c0, member0, id0, edge0, path0, entry0, _, _, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have absent : Token.eos ∉ c0.placed := by simp [empty0]
  have present : Token.eos ∈ c.placed := by simpa [Channel.closed] using closed_of_drained finished memberC
  obtain ⟨pre, op, post, t, t', d, d', schedule, head, allowed, accepted, rest, safeT, active,
    memberD, idD, layoutD, absentD, memberD', idD', _, presentD', _, target⟩ :=
    token_step run fs.scope.safe .eos c0 member0 absent (entry0.trans entryC) c memberC id0.symm present
  have nodeT := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  rw [path0, pathC, edge0, srcC] at target
  rcases target_shape t t' op safeT active accepted P n.id target n nodeT with
      ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
    | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨eq, _⟩ | ⟨inst, _, eq, _⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, plain⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · subst op
    obtain ⟨_, _, _, drained, children, _⟩ := effect_propagateEos t t' P n.id (transition_of_active accepted active (by simp))
    exact ⟨pre, post, t, t', schedule, head, allowed, accepted, rest, drained, children⟩
  · subst op
    obtain ⟨y, items, _, _, view, _⟩ := forEach_finish_step oracle fs head allowed accepted rest active n memberN body kind target
    obtain ⟨w, memberW, tokenW, _⟩ := gained_token view safeT.channelIds d memberD d' memberD'
      (idD'.trans idD.symm) .eos presentD' absentD
    obtain ⟨x, itemW⟩ := bodyWrites_item P n items w memberW
    rw [itemW] at tokenW
    cases tokenW
  · rw [kind] at k; cases k
  · rw [notPlain] at plain; contradiction

theorem written_item_final {allows : State → Op → Prop} {t t' last : State} {post : List Op}
    (rest : ConformingSteps allows t' post last) (safeT : Invariants t) (safeT' : Invariants t')
    (ws : List Write) (view : t'.placedView = (applyWrites ws t).placedView)
    (d : Channel) (memberD : d ∈ t.channels) (entryD : d.entry = false)
    (c : Channel) (memberC : c ∈ last.channels) (idC : c.id = d.id) (x : ItemId)
    (hit : Write.out d.path d.edge.src.node d.edge.src.port (.item x) ∈ ws) : x ∈ c.items := by
  obtain ⟨d', memberD', idD', _, presentD'⟩ := applyWrites_token ws t d memberD entryD safeT.channelIds (.item x) hit
  have inView : d'.core ∈ t'.placedView := by rw [view]; exact placedView_member memberD'
  obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
  have idE : e.id = d.id := (congrArg Channel.id coreE).trans idD'
  have placedE : Token.item x ∈ e.placed := by
    have placed := congrArg Channel.placed coreE
    simp only [Channel.core_placed] at placed
    rw [placed]
    exact presentD'
  exact (Effects.item_mem c x).mpr (token_persists rest safeT' e memberE c memberC (idC.trans idE.symm) _ placedE)

theorem forEach_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have safe0 := fs.scope.safe
  have scL := fs.scope.persist run
  obtain ⟨p, q, ins, outs, stream⟩ := forEach_ports fs.scope n memberN body kind
  have notPlain := allKind_plain_false_of_stream n.inputs p (by simp [ins]) stream
  have notSup : suppressed n (stateInputs last P n) = false := by simp [suppressed, notPlain]
  have outNames := (g.validate_port_names n (fs.scope.checked n memberN)).2
  obtain ⟨q', memberQ', portC, _⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  have qq : q' = q := by simpa [outs] using memberQ'
  subst q'
  obtain ⟨input, memberIn, foundIn, pathIn, exitIn, dstIn, _, _, uniqueIn⟩ :=
    scL.input_channel n memberN p (by simp [ins])
  have nodeIn : input.edge.dst.node = n.id := congrArg PortRef.node dstIn
  have inputEq : ∀ d ∈ last.channels, d.path = P → d.exit = false → d.edge.dst.node = n.id → d = input := by
    intro d memberD pathD exitD nodeD
    obtain ⟨p', memberP', portD, _⟩ := scL.input_port n memberN d memberD pathD exitD nodeD
    have pp : p' = p := by simpa [ins] using memberP'
    subst p'
    exact uniqueIn d memberD pathD exitD (PortRef.ext_of nodeD portD)
  have inputsL : stateInputs last P n = [(p.name, bag input)] := by
    simp [stateInputs, ins, foundIn]
  have valueEq : nodeValue oracle last g P n = {
      outputs := ports n (fun _ =>
      (bag input).flatMap fun y => (exitItems last (childPath P n.id (some y) 0) body).flatten)
      children := (bag input).flatMap fun y => subtreeBags last (childPath P n.id (some y) 0) } := by
    unfold nodeValue primitive
    rw [notSup]
    simp only [kind, Bool.false_eq_true, ↓reduceIte, compoundValue, inputsL]
    rfl
  rw [valueEq, portC, outputItems_ports n outNames _ q (by simp [outs]),
    canonical_idem, bag_eq_canonical scL.safe memberC]
  apply canonical_eq_of_mem_iff
  intro x
  rw [List.mem_flatMap]
  obtain ⟨c0, member0, id0, edge0, path0, entry0, _, _, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  constructor
  · intro presentX
    have absent : Token.item x ∉ c0.placed := by simp [empty0]
    obtain ⟨pre, op, post, t, t', d, d', _, head, allowed, accepted, rest, safeT, active,
      memberD, idD, layoutD, absentD, memberD', idD', _, presentD', _, target⟩ :=
      token_step run safe0 (.item x) c0 member0 absent (entry0.trans entryC) c memberC id0.symm ((Effects.item_mem c x).mp presentX)
    have nodeT := head.node P n.id n (fs.scope.node?_of_mem n memberN)
    rw [path0, pathC, edge0, srcC] at target
    rcases target_shape t t' op safeT active accepted P n.id target n nodeT with
        ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
      | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨eq, _⟩ | ⟨inst, _, eq, _⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, plain⟩
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · subst op
      obtain ⟨_, _, _, _, _, _, _, _, view⟩ := effect_propagateEos t t' P n.id (transition_of_active accepted active (by simp))
      obtain ⟨w, memberW, tokenW, _⟩ := gained_token view safeT.channelIds d memberD d' memberD'
        (idD'.trans idD.symm) (.item x) presentD' absentD
      rw [eosWrites_eos _ _ w memberW] at tokenW
      cases tokenW
    · subst op
      obtain ⟨y, items, _, _, view, exits, din, memberDin, pathDin, exitDin, nodeDin, presentY⟩ :=
        forEach_finish_step oracle fs head allowed accepted rest active n memberN body kind target
      obtain ⟨w, memberW, tokenW, _⟩ := gained_token view safeT.channelIds d memberD d' memberD'
        (idD'.trans idD.symm) (.item x) presentD' absentD
      obtain ⟨⟨p', value⟩, pairMember, sameW⟩ := List.mem_map.mp memberW
      subst w
      simp only [Write.token, Token.item.injEq] at tokenW
      have valueMember : x ∈ items := tokenW ▸ (List.of_mem_zip pairMember).2
      have dinEq := inputEq din memberDin pathDin exitDin nodeDin
      refine ⟨y, mem_bag.mpr (dinEq ▸ presentY), ?_⟩
      rw [exits]
      change x ∈ items.flatMap (fun y => [y])
      simpa only [List.flatMap_singleton'] using valueMember
    · rw [kind] at k; cases k
    · rw [notPlain] at plain; contradiction
  · rintro ⟨y, inputY, outputX⟩
    obtain ⟨preClose, postClose, closing, closed, _, headClose, allowedClose, acceptedClose, restClose, drained, children⟩ :=
      forEach_closing_step oracle run fs finished n memberN body kind c memberC pathC entryC srcC
    have scClosing := fs.scope.persist headClose
    have tailClose : ConformingSteps (fun s op => oracleConforms oracle s op = true)
        closing (.propagateEos P n.id :: postClose) last := .cons allowedClose acceptedClose restClose
    obtain ⟨din, memberDin, _, pathDin, exitDin, dstDin, _, _, _⟩ :=
      scClosing.input_channel n memberN p (by simp [ins])
    have inIncoming : din ∈ closing.incoming P n.id := List.mem_filter.mpr ⟨memberDin, by simp [pathDin, exitDin, dstDin]⟩
    have ready := List.all_eq_true.mp drained din inIncoming
    have closedDin : din.closed = true := (Bool.and_eq_true_iff.mp ready).1
    have drainedDin : din.pendingItems = [] := by simpa using (Bool.and_eq_true_iff.mp ready).2
    obtain ⟨dinL, memberDinL, idDinL, layoutDinL, _⟩ := run_image tailClose scClosing.safe din memberDin
    obtain ⟨_, edgeDinL, pathDinL, _, exitDinL, _⟩ := Channel.layout_fields layoutDinL
    have dinLEq := inputEq dinL memberDinL (pathDinL.trans pathDin) (exitDinL.trans exitDin) (by rw [edgeDinL, dstDin])
    obtain ⟨fixed, memberFixed, idFixed, placedFixed⟩ := tailClose.retains_closed_channel scClosing.safe din memberDin closedDin
    have fixedEq := unique_channel scL.safe memberFixed memberIn (idFixed.trans (idDinL.symm.trans (congrArg Channel.id dinLEq)))
    have itemsEq : input.items = din.items := by
      subst fixed
      exact congrArg (fun placed => placed.filterMap fun t => match t with | .item v => some v | .eos => none) placedFixed
    obtain ⟨pre, post, t, t', inst, _, head, allowed, accepted, rest, active, target, trigger⟩ :=
      forEach_input_finished oracle headClose fs n memberN body kind din memberDin pathDin exitDin
        (congrArg PortRef.node dstDin) drainedDin children y (itemsEq ▸ mem_bag.mp inputY)
    have tail := rest.append tailClose
    have safeT := head.invariants safe0
    have safeT' := preserves_invariants t t' _ safeT accepted
    obtain ⟨y', items, arity, trigger', view, exits, _⟩ :=
      forEach_finish_step oracle fs head allowed accepted tail active n memberN body kind target
    have yy : y' = y := Option.some.inj (trigger'.symm.trans trigger)
    rw [yy] at exits
    have itemMember : x ∈ items := by
      rw [exits] at outputX
      change x ∈ items.flatMap (fun y => [y]) at outputX
      simpa only [List.flatMap_singleton'] using outputX
    have itemLen : items.length = 1 := by rw [← arity, outs]; rfl
    obtain ⟨z, single⟩ := List.length_eq_one_iff.mp itemLen
    have xz : x = z := by simpa [single] using itemMember
    have itemsEq' : items = [x] := by rw [single, xz]
    obtain ⟨d, memberD, idD, layoutD, _⟩ := run_image head safe0 c0 member0
    obtain ⟨_, edgeD, pathD, entryD, _, _⟩ := Channel.layout_fields layoutD
    apply written_item_final tail safeT safeT' (bodyWrites P n items) view d memberD
      (entryD.trans (entry0.trans entryC)) c memberC (id0.symm.trans idD.symm) x
    simp only [bodyWrites, outs, itemsEq', List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    rw [pathD, path0, pathC, edgeD, edge0, srcC, portC]

end Suimon
