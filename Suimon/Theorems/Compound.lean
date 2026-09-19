import Suimon.Theorems.NodeValues

/-! Channel equations of compound nodes (subworkflow, forEach, loop), read from child frames. -/

namespace Suimon
open Semantics Effects

/-- Tokens gained across writes come from a write whose id group contained the channel. -/
theorem applyWrites_tokens_targeted (ws : List Write) (st : State) (d : Channel)
    (member : d ∈ (applyWrites ws st).channels) :
    ∃ c ∈ st.channels, c.id = d.id ∧ ∀ t ∈ d.placed, t ∈ c.placed ∨
      ∃ w ∈ ws, w.token = t ∧ (w.ids st).contains c.id = true := by
  induction ws generalizing st with
  | nil => exact ⟨d, member, rfl, fun t ht => .inl ht⟩
  | cons w ws ih =>
    simp only [applyWrites_cons] at member
    obtain ⟨c, memberC, idC, tokens⟩ := ih _ member
    simp only [applyWrite, write, List.mem_map] at memberC
    obtain ⟨e, memberE, eq⟩ := memberC
    have idE : e.id = c.id := by
      rw [← eq]
      split <;> simp [insertToken_id]
    refine ⟨e, memberE, idE.trans idC, ?_⟩
    intro t ht
    rcases tokens t ht with old | ⟨v, hv, tv, hits⟩
    · rw [← eq] at old
      split at old
      · rename_i selected
        rcases (insertToken_mem e w.token t).mp old with older | fresh
        · exact .inl older
        · exact .inr ⟨w, by simp, fresh.symm, selected⟩
      · exact .inl old
    · refine .inr ⟨v, by simp [hv], tv, ?_⟩
      rw [← idE] at hits
      rwa [applyWrite_ids_after] at hits

theorem out_ids_port (st : State) (distinct : (st.channels.map (·.id)).Nodup) (P : Path) (N : NodeId) (port : PortName)
    (t : Token) (c : Channel) (memberC : c ∈ st.channels)
    (hits : ((Write.out P N port t).ids st).contains c.id = true) :
    c.path = P ∧ c.entry = false ∧ c.edge.src = ⟨N, port⟩ := by
  simp only [Write.ids, List.contains_iff_mem, List.mem_map] at hits
  obtain ⟨c', memberC', idC'⟩ := hits
  have inChannels : c' ∈ st.channels := (List.mem_filter.mp memberC').1
  have props := (List.mem_filter.mp memberC').2
  have same : c' = c := eq_of_mapped_nodup (·.id) st.channels distinct c' c inChannels memberC idC'
  subst same
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at props
  exact ⟨props.1.1, props.1.2, props.2⟩

/-- The single item of an exit channel, as read by `frameOutputItems`. -/
def exitValue (s : State) (f : Frame) (p : PortRef) : ItemId :=
  (((s.channels.find? (fun c => c.path == f.path && c.exit && c.edge.src == p)).map (·.items)).getD []).headD ""

theorem frameOutputItems_spec (s : State) (f : Frame) (items : List ItemId)
    (h : frameOutputItems s f = .ok items) :
    items = f.graph.exits.map (exitValue s f) ∧
    ∀ p ∈ f.graph.exits, ∃ ch ∈ s.channels, ch.path = f.path ∧ ch.exit = true ∧ ch.edge.src = p ∧
      ch.items = [exitValue s f p] := by
  unfold frameOutputItems at h
  have single : ∀ p ∈ f.graph.exits, ∀ y, (do
      let c ← (s.channels.find? (fun c => c.path == f.path && c.exit && c.edge.src == p)).toExcept
        { code := "MISSING_EXIT", message := p.port }
      match c.items with
      | [item] => return item
      | _ => throw { code := "BODY_RESULT_ARITY", message := p.port } : Result ItemId) = .ok y →
      ∃ ch ∈ s.channels, s.channels.find? (fun c => c.path == f.path && c.exit && c.edge.src == p) = some ch ∧
        ch.items = [y] ∧ y = exitValue s f p := by
    intro p _ y hy
    cases found : s.channels.find? (fun c => c.path == f.path && c.exit && c.edge.src == p) with
    | none => simp [found, Option.toExcept, bind, Except.bind] at hy
    | some ch =>
      simp only [found, Option.toExcept, bind, Except.bind] at hy
      refine ⟨ch, List.mem_of_find?_eq_some found, rfl, ?_⟩
      split at hy
      · rename_i item eqItems
        simp only [pure, Except.pure, Except.ok.injEq] at hy
        subst hy
        exact ⟨eqItems, by simp [exitValue, found, eqItems]⟩
      · contradiction
  refine ⟨?_, ?_⟩
  · apply mapM_eq_map _ (exitValue s f) f.graph.exits items _ h
    intro p member y hy
    obtain ⟨_, _, _, _, value⟩ := single p member y hy
    exact value
  · intro p member
    obtain ⟨y, hy⟩ := mapM_ok_members _ f.graph.exits items h p member
    obtain ⟨ch, memberCh, found, itemsCh, value⟩ := single p member y hy
    have props := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq] at props
    exact ⟨ch, memberCh, props.1.1, props.1.2, props.2, by rw [itemsCh, value]⟩

theorem bodyResults_spec (s : State) (f : Frame) (items : List ItemId) (h : bodyResults s f = .ok items) :
    frameDone s f = true ∧ frameOutputItems s f = .ok items := by
  simp only [bodyResults, bind, Except.bind] at h
  cases done : require (frameDone s f) "BODY_NOT_FINISHED" with
  | error e => rw [done] at h; contradiction
  | ok u =>
    rw [done] at h
    exact ⟨require_ok _ _ _ u done, h⟩

theorem frameDone_exits_closed (s : State) (f : Frame) (done : frameDone s f = true) :
    ∀ c ∈ s.channels, c.path = f.path → c.exit = true → c.closed = true := by
  intro c memberC pathC exitC
  simp only [frameDone, Bool.and_eq_true] at done
  exact List.all_eq_true.mp done.1.1.1.2 c (List.mem_filter.mpr ⟨memberC, by simp [pathC, exitC]⟩)

theorem frameDone_instances (s : State) (f : Frame) (done : frameDone s f = true) :
    ∀ i ∈ s.instances, i.path = f.path → i.status = .succeeded ∨ i.status = .cancelled := by
  intro i memberI pathI
  simp only [frameDone, Bool.and_eq_true] at done
  have := List.all_eq_true.mp done.1.2 i (List.mem_filter.mpr ⟨memberI, by simp [pathI]⟩)
  simpa using this

/-- Exit items read at a body-result step persist to the end of the run. -/
theorem exitItems_of_bodyResults {allows : State → Op → Prop} {t last : State} {ops : List Op}
    (run : ConformingSteps allows t ops last) (safeT : Invariants t) (f : Frame) (items : List ItemId)
    (h : bodyResults t f = .ok items) (scope : Scope last f.path f.graph) :
    exitItems last f.path f.graph = items.map fun x => [x] := by
  obtain ⟨done, outputs⟩ := bodyResults_spec t f items h
  obtain ⟨itemsEq, channels⟩ := frameOutputItems_spec t f items outputs
  have safeLast := run.invariants safeT
  rw [itemsEq, List.map_map]
  unfold exitItems
  apply List.map_congr_left
  intro p memberP
  obtain ⟨ch, memberCh, pathCh, exitCh, srcCh, itemsCh⟩ := channels p memberP
  have closedCh := frameDone_exits_closed t f done ch memberCh pathCh exitCh
  obtain ⟨d, memberD, idD, placedD⟩ := run.retains_closed_channel safeT ch memberCh closedCh
  obtain ⟨d', memberD', idD', layoutD', _⟩ := run_image run safeT ch memberCh
  have same : d' = d := unique_channel safeLast memberD' memberD (idD'.trans idD.symm)
  subst same
  obtain ⟨_, edgeD, pathD, _, exitD, _⟩ := Channel.layout_fields layoutD'
  obtain ⟨e, _, found, _, _, _, _, uniqueE⟩ := scope.exit_channel p memberP
  have de : d' = e := uniqueE d' memberD' (pathD.trans pathCh) (exitD.trans exitCh) (by rw [edgeD, srcCh])
  subst de
  rw [found]
  simp only [Option.map_some, Option.getD_some, Function.comp_def]
  have itemsD : d'.items = [exitValue t f p] := by
    simp only [Channel.items, placedD]
    exact itemsCh
  simp [bag, itemsD]

theorem outputItems_zip (n : Node) (names : (n.outputs.map (·.name)).Nodup) (l : List (List ItemId))
    (len : l.length = n.outputs.length) (q : Port) (k : Nat) (hk : n.outputs[k]? = some q) (v : List ItemId)
    (hv : l[k]? = some v) :
    outputItems ((n.outputs.zip l).map fun (p, items) => ({ port := p.name, items } : Output)) q.name = v := by
  have memberQ : q ∈ n.outputs := List.mem_of_getElem? hk
  have found : (n.outputs.zip l).find? (fun pair => pair.1.name == q.name) = some (q, v) := by
    have memberPair : (q, v) ∈ n.outputs.zip l := List.mem_iff_getElem?.mpr ⟨k, List.getElem?_zip_eq_some.mpr ⟨hk, hv⟩⟩
    have exists_ : ((n.outputs.zip l).find? (fun pair => pair.1.name == q.name)).isSome :=
      List.find?_isSome.mpr ⟨(q, v), memberPair, by simp⟩
    cases h : (n.outputs.zip l).find? (fun pair => pair.1.name == q.name) with
    | none => rw [h] at exists_; contradiction
    | some pair =>
      have memberP := List.mem_of_find?_eq_some h
      have nameP : pair.1.name = q.name := by simpa using List.find?_some h
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp memberP
      obtain ⟨hi1, hi2⟩ := List.getElem?_zip_eq_some.mp hi
      have sameQ : pair.1 = q := eq_of_mapped_nodup (·.name) n.outputs names pair.1 q (List.mem_of_getElem? hi1) memberQ nameP
      have sameIndex : i = k := by
        rw [sameQ] at hi1
        have hi' : (n.outputs.map (·.name))[i]? = some q.name := by simp [hi1]
        have hk' : (n.outputs.map (·.name))[k]? = some q.name := by simp [hk]
        have bound : i < (n.outputs.map (·.name)).length := by
          rw [List.length_map]
          exact (List.getElem?_eq_some_iff.mp hi1).1
        exact (List.Nodup.getElem?_inj bound names).mp (hi'.trans hk'.symm)
      subst sameIndex
      rw [hv] at hi2
      cases pair
      simp only at sameQ hi2
      rw [sameQ, Option.some.inj hi2]
  unfold outputItems
  rw [List.find?_map]
  have : ((fun (o : Output) => o.port == q.name) ∘ fun (pair : Port × List ItemId) => ({ port := pair.1.name, items := pair.2 } : Output)) =
      fun pair => pair.1.name == q.name := by
    funext pair; rfl
  rw [this, found]
  rfl


/-- A step that creates an instance is an executed (non-idle, non-absorbed) transition. -/
theorem transition_of_created {s next : State} {op : Op} (h : step s op = .ok next) (notIdle : op ≠ .idle)
    (j : Instance) (memberJ : j ∈ next.instances) (absent : ∀ k ∈ s.instances, k.id ≠ j.id) :
    transition s op = .ok next := by
  rcases step_ok_cases s op next h with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst same; exact absurd rfl (absent j memberJ)
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle => exact absurd rfl notIdle
    | _ => simpa only [transitionOrIdle] using executed

theorem setInstance_self_mem (s : State) (i i' : Instance) (member : i ∈ s.instances) (same : i'.id = i.id) :
    i' ∈ (setInstance s i').instances := by
  simp only [setInstance, List.mem_map]
  exact ⟨i, member, by simp [same]⟩

/-- The scope of a body frame at the end of a run, from the frame at an earlier state. -/
theorem Scope.child {allows : State → Op → Prop} {t last : State} {ops : List Op} {P : Path} {g : Graph}
    (run : ConformingSteps allows t ops last) (scL : Scope last P g) (f : Frame) (memberF : f ∈ t.frames)
    (valid : f.graph.validate true = .ok ()) : Scope last f.path f.graph := by
  refine ⟨scL.safe, scL.layout, scL.distinct, ?_, ⟨true, valid⟩⟩
  have inDefs : f.definitionView ∈ last.frameDefinitions :=
    run.frameDefinitions.subset (List.mem_map.mpr ⟨f, memberF, rfl⟩)
  obtain ⟨h, memberH, viewH⟩ := List.mem_map.mp inDefs
  refine ⟨h, memberH, ?_, ?_⟩
  · have := congrArg Frame.path viewH
    simpa [Frame.definitionView] using this
  · have := congrArg Frame.graph viewH
    simpa [Frame.definitionView] using this

theorem currentFrame_spec (s : State) (i : Instance) (f : Frame) (h : currentFrame s i = .ok f) :
    f ∈ s.frames ∧ f.path = i.path ++ [identity [i.id, toString i.iteration]] := by
  unfold currentFrame at h
  simp only [Option.toExcept] at h
  split at h
  · rename_i f' found
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩
  · contradiction

/-- A non-cancelled instance of a subworkflow node was made by `activate`, at iteration 0, and
    owns a frame with the body graph at the child path. -/
theorem sub_instance_shape (oracle : ScopedOracle) {s0 t : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input}
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops t)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph)
    (kind : n.kind = .subworkflow body)
    (i : Instance) (memberI : i ∈ t.instances) (pathI : i.path = P) (nodeI : i.node = n.id)
    (notCancelled : i.status ≠ .cancelled) :
    i.id = instanceId P n.id none ∧ i.trigger = none ∧ i.iteration = 0 ∧
      ∃ f ∈ t.frames, f.path = childPath P n.id none 0 ∧ f.graph = body ∧ f.owner = some i.id := by
  have safe0 := fs.scope.safe
  have safeT := head.invariants safe0
  have absent0 : ∀ j ∈ s0.instances, j.id ≠ i.id := by
    intro j memberJ eq
    obtain ⟨_, pathEq, _, _⟩ := head.input_snapshot safe0 j i memberJ memberI eq
    exact fs.noInstances j memberJ (by rw [← pathEq, pathI]; exact List.prefix_refl _)
  obtain ⟨pre, op, post, u, u', j, _, headU, allowed, accepted, rest, safeU, absentU, memberJ, idJ, bindJ, created⟩ :=
    instance_created head safe0 i memberI absent0
  have safeU' := preserves_invariants u u' op safeU accepted
  have nodeU : u.node? P n.id = some n := headU.node P n.id n (fs.scope.node?_of_mem n memberN)
  have pathJ : j.path = P := (Instance.binding_path bindJ).trans pathI
  have nodeJ : j.node = n.id := (Instance.binding_node bindJ).trans nodeI
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
  · -- activate of a subworkflow: the frame is opened here
    rcases kinds with ⟨kindSub, iter0⟩ | ⟨m, kindLoop, _⟩
    · subst iter0
      have bodyEq : body' = body := by rw [kind] at kindSub; exact (NodeKind.subworkflow.inj kindSub).symm
      subst bodyEq
      subst opEq
      have executed := transition_of_created accepted (by simp) j memberJ absentU
      obtain ⟨_, n2, inputs2, hn2, hi2, ⟨_, _, kind2, _⟩ | ⟨body2, iteration2, kinds2, f, opened, _, _, _, _, frames', _⟩⟩ :=
        effect_activate u u' P n.id executed
      · have sameN2 := node?_of_getNode nodeU hn2; subst n2; rw [kind] at kind2; cases kind2
      · have sameN2 := node?_of_getNode nodeU hn2; subst n2
        have inputsEq : inputs2 = inputs := Except.ok.inj (hi2.symm.trans hi)
        subst inputsEq
        rcases kinds2 with ⟨kindSub2, iter2⟩ | ⟨_, kindLoop2, _⟩
        · subst iter2
          obtain ⟨pathF, graphF, ownerF, _⟩ := opened
          have idI : i.id = instanceId P n.id none := by rw [← idJ, eq]; rfl
          have triggerI : i.trigger = none := by rw [← Instance.binding_trigger bindJ, eq]; rfl
          have iterI : i.iteration = 0 := by
            have := (rest.iteration_evolves safeU' j memberJ i memberI idJ.symm).2
            rw [this, eq]
            intro n3 b m found3
            rw [eq] at found3
            simp only [makeInstance] at found3
            have kept := headU.node P n.id n (fs.scope.node?_of_mem n memberN)
            have kept' := retained_node u u' P n.id n (step_frameDefinitions u u' _ accepted) kept
            rw [kept'] at found3
            have same := Option.some.inj found3
            subst same
            rw [kind]
            intro h; cases h
          refine ⟨idI, triggerI, iterI, ?_⟩
          have memberF : f ∈ u'.frames := by rw [frames']; simp
          have inDefs : f.definitionView ∈ t.frameDefinitions :=
            rest.frameDefinitions.subset (List.mem_map.mpr ⟨f, memberF, rfl⟩)
          obtain ⟨h, memberH, viewH⟩ := List.mem_map.mp inDefs
          refine ⟨h, memberH, ?_, ?_, ?_⟩
          · have := congrArg Frame.path viewH
            simp only [Frame.definitionView] at this
            rw [this, pathF]
            rfl
          · have := congrArg Frame.graph viewH
            simp only [Frame.definitionView] at this
            rw [this, graphF]
            exact NodeKind.subworkflow.inj (kindSub2.symm.trans kind)
          · have := congrArg Frame.owner viewH
            simp only [Frame.definitionView] at this
            rw [this, ownerF, idI]
            rfl
        · rw [kind] at kindLoop2; cases kindLoop2
    · rw [kind] at kindLoop; cases kindLoop
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; simp at kind'
  · -- skip: cancelled for good
    exfalso
    have cancelledJ : j.status = .cancelled := by rw [eq]; rfl
    obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeU' j memberJ (.inr cancelledJ)
    have same : k = i := unique_instance safeT memberK memberI (idK.trans idJ)
    subst same
    exact notCancelled (statusK.trans cancelledJ)
  · rw [kind] at kind'; cases kind'


theorem ConformingSteps.append {allows : State → Op → Prop} {s m last : State} {ops1 ops2 : List Op}
    (first : ConformingSteps allows s ops1 m) (second : ConformingSteps allows m ops2 last) :
    ConformingSteps allows s (ops1 ++ ops2) last := by
  induction first with
  | nil => exact second
  | cons allowed accepted tail ih => exact .cons allowed accepted (ih second)

/-- A token gained by a channel across a step described by writes comes from a write hitting it. -/
theorem gained_token {t t' : State} {ws : List Write} (view : t'.placedView = (applyWrites ws t).placedView)
    (distinct : (t.channels.map (·.id)).Nodup) (d : Channel) (memberD : d ∈ t.channels)
    (d' : Channel) (memberD' : d' ∈ t'.channels) (same : d'.id = d.id) (tok : Token)
    (present : tok ∈ d'.placed) (absent : tok ∉ d.placed) :
    ∃ w ∈ ws, w.token = tok ∧ (w.ids t).contains d.id = true := by
  have inView : d'.core ∈ (applyWrites ws t).placedView := by rw [← view]; exact placedView_member memberD'
  obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
  obtain ⟨c, memberC, idC, tokens⟩ := applyWrites_tokens_targeted ws t e memberE
  have idE : e.id = d'.id := by simpa using congrArg Channel.id coreE
  have sameC : c = d := eq_of_mapped_nodup (·.id) t.channels distinct c d memberC memberD (idC.trans (idE.trans same))
  subst sameC
  have placedE : tok ∈ e.placed := by
    have := congrArg Channel.placed coreE
    simp only [Channel.core_placed] at this
    rw [this]; exact present
  rcases tokens tok placedE with old | hit
  · exact absurd old absent
  · exact hit

theorem mem_zip_of_index {α β : Type} {xs : List α} {ys : List β} {k : Nat} {x : α} {y : β}
    (hx : xs[k]? = some x) (hy : ys[k]? = some y) : (x, y) ∈ xs.zip ys :=
  List.mem_iff_getElem?.mpr ⟨k, List.getElem?_zip_eq_some.mpr ⟨hx, hy⟩⟩

theorem zip_index_of_names (n : Node) (names : (n.outputs.map (·.name)).Nodup) {β : Type} (l : List β)
    (q : Port) (k : Nat) (hk : n.outputs[k]? = some q) (y : β) (mem : (q, y) ∈ n.outputs.zip l) : l[k]? = some y := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mem
  obtain ⟨hi1, hi2⟩ := List.getElem?_zip_eq_some.mp hi
  have hi' : (n.outputs.map (·.name))[i]? = some q.name := by simp [hi1]
  have hk' : (n.outputs.map (·.name))[k]? = some q.name := by simp [hk]
  have bound : i < (n.outputs.map (·.name)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hi1).1
  have sameIndex : i = k := (List.Nodup.getElem?_inj bound names).mp (hi'.trans hk'.symm)
  subst sameIndex
  exact hi2

/-- A `finishSubworkflow` step on a subworkflow node writes its body results, which persist. -/
theorem sub_finish_step (oracle : ScopedOracle) {s0 t t' last : State} {pre post : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} {inst : InstanceId}
    (fs : FrameStart s0 P g inputs0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t)
    (allowed : oracleConforms oracle t (.finishSubworkflow inst) = true)
    (accepted : step t (.finishSubworkflow inst) = .ok t')
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last)
    (active : absorbed t (.finishSubworkflow inst) = false)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .subworkflow body)
    (target : opTarget t (.finishSubworkflow inst) = some (P, n.id)) :
    ∃ items, n.outputs.length = items.length ∧
      t'.placedView = (applyWrites (bodyWrites P n items ++ eosWrites P n) t).placedView ∧
      exitItems last (childPath P n.id none 0) body = items.map (fun x => [x]) ∧
      ∃ i ∈ last.instances, i.path = P ∧ i.node = n.id ∧ i.status = .succeeded := by
  have safeT := head.invariants fs.scope.safe
  have safeT' := preserves_invariants t t' _ safeT accepted
  have executed := transition_of_active accepted active (by simp)
  obtain ⟨i, n', f, items, foundI, waitingI, hn', hf, hbody, arity, _, _, instances', branch⟩ :=
    effect_finishSubworkflow t t' inst executed
  obtain ⟨i2, foundI2, pathI, nodeI⟩ := opTarget_id (inst := inst) rfl target
  rw [foundI] at foundI2
  have sameI : i = i2 := Option.some.inj foundI2
  subst i2
  have nodeT : t.node? P n.id = some n := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  rw [pathI, nodeI] at hn'
  have sameN : n' = n := node?_of_getNode nodeT hn'
  subst sameN
  rcases branch with ⟨body', kindSub, view⟩ | ⟨body', kindFE, _⟩
  · have bodyEq : body' = body := NodeKind.subworkflow.inj (kindSub.symm.trans kind)
    subst bodyEq
    obtain ⟨idI, _, iterI, f0, memberF0, pathF0, graphF0, _⟩ :=
      sub_instance_shape oracle head fs n' memberN body' kind i (instance?_mem foundI) pathI nodeI (by rw [waitingI]; decide)
    obtain ⟨memberF, pathF⟩ := currentFrame_spec t i f hf
    have pathF' : f.path = childPath P n'.id none 0 := by rw [pathF, pathI, idI, iterI]; rfl
    have distinctT := head.unique_frames fs.scope.distinct
    have sameF : f = f0 := eq_of_mapped_nodup Frame.path t.frames distinctT f f0 memberF memberF0 (pathF'.trans pathF0.symm)
    subst sameF
    have full : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (_ :: post) last := .cons allowed accepted rest
    have scL := fs.scope.persist (head.append full)
    have validBody : f.graph.validate true = .ok () := by
      rw [graphF0]
      exact g.validateNode_child n' body' (.inr (.inl kind)) (fs.scope.checked n' memberN)
    have scopeChild := Scope.child full scL f memberF validBody
    have exits := exitItems_of_bodyResults full safeT f items hbody scopeChild
    rw [pathF', graphF0] at exits
    refine ⟨items, arity, by rw [view, pathI], exits, ?_⟩
    have memberUpdated : { i with status := .succeeded } ∈ t'.instances := by
      rw [instances']
      exact setInstance_self_mem t i _ (instance?_mem foundI) rfl
    obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeT' _ memberUpdated (.inl rfl)
    obtain ⟨nodeK, pathK, _, _⟩ := rest.input_snapshot safeT' _ k memberUpdated memberK idK.symm
    exact ⟨k, memberK, pathK.trans pathI, nodeK.trans nodeI, statusK⟩
  · rw [kind] at kindFE; cases kindFE


theorem active_of_change {t t' : State} {op : Op} (safe : Invariants t) (accepted : step t op = .ok t')
    (d : Channel) (memberD : d ∈ t.channels) (d' : Channel) (memberD' : d' ∈ t'.channels) (same : d'.id = d.id)
    (changed : d'.closed ≠ d.closed) : absorbed t op = false := by
  cases ha : absorbed t op with
  | false => rfl
  | true =>
    exfalso
    rcases step_ok_cases t op t' accepted with ⟨_, eq⟩ | ⟨notAbs, _⟩
    · subst eq
      exact changed (by rw [unique_channel safe memberD' memberD same])
    · rw [ha] at notAbs; contradiction

theorem PortRef.ext_of {r : PortRef} {N : NodeId} {port : PortName} (node : r.node = N) (p : r.port = port) :
    r = ⟨N, port⟩ := by
  cases r
  simp only at node p
  rw [node, p]

/-- The channel equation of a subworkflow output: the single item of the corresponding body exit. -/
theorem sub_value (oracle : ScopedOracle) {s0 last : State} {ops : List Op} {P : Path} {g : Graph} {inputs0 : List Input}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (fs : FrameStart s0 P g inputs0) (finished : succeededDrained last = true)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .subworkflow body)
    (c : Channel) (memberC : c ∈ last.channels) (pathC : c.path = P) (entryC : c.entry = false)
    (srcC : c.edge.src.node = n.id) :
    bag c = canonical (outputItems (nodeValue oracle last g P n).outputs c.edge.src.port) := by
  have safe0 := fs.scope.safe
  have scL := fs.scope.persist run
  have checkedN := fs.scope.checked n memberN
  obtain ⟨inNames, outNames⟩ := g.validate_port_names n checkedN
  have shape := g.validateNode_shape n checkedN
  simp only [Node.shapeOK, kind, Bool.and_eq_true, beq_iff_eq] at shape
  have plain : allKind n.inputs .plain = true := shape.1.1.1.1.1
  obtain ⟨q, port, portC, kindC⟩ := scL.output_port n memberN c memberC pathC entryC srcC
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp port
  have srcEq : c.edge.src = ⟨n.id, q.name⟩ := PortRef.ext_of srcC portC
  obtain ⟨c0, member0, id0, edge0, path0, entry0, exit0, kind0, emptyOf⟩ := fs.origin run c memberC pathC
  have empty0 := emptyOf entryC
  have found0 : s0.node? c0.path c0.edge.src.node = some n := by
    rw [path0, pathC, edge0, srcC]; exact fs.scope.node?_of_mem n memberN
  have open0 : c0.closed = false := by simp [Channel.closed, empty0]
  have closedC := closed_of_drained finished memberC
  obtain ⟨pre, op, post, t, t', d, d', _, head, allowed, accepted, rest, safeT, memberD, idD, layoutD, openD,
    memberD', idD', layoutD', closedD', placedD', target⟩ :=
    closing_step run safe0 c0 member0 open0 (entry0.trans entryC) c memberC id0.symm closedC
  have active : absorbed t op = false :=
    active_of_change safeT accepted d memberD d' memberD' (idD'.trans idD.symm) (by rw [closedD', openD]; decide)
  have nodeT : t.node? P n.id = some n := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  have safeT' := preserves_invariants t t' op safeT accepted
  obtain ⟨_, edgeD, pathD, entryD, _, _⟩ := Channel.layout_fields layoutD
  rw [path0, pathC, edge0, srcC] at target
  rcases target_shape t t' op safeT active accepted _ _ target n nodeT with
      ⟨_, _, _, _, _, _, k'⟩ | ⟨_, _, _, _, _, k'⟩ | ⟨_, k'⟩ | ⟨_, _, _, k'⟩ | ⟨_, _, _, k'⟩ | ⟨_, k'⟩
    | ⟨_, _, _, k'⟩ | ⟨_, _, _, k'⟩ | ⟨_, k'⟩ | ⟨inst, body', eq, kinds⟩ | ⟨_, _, _, _, _, k'⟩ | ⟨eq, _⟩
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; cases k'
  · rw [kind] at k'; simp at k'
  · -- the body finished: the output holds the corresponding exit item
    subst eq
    obtain ⟨items, arity, view, exits, iL, memberIL, pathIL, nodeIL, statusIL⟩ :=
      sub_finish_step oracle fs head allowed accepted rest active n memberN body kind target
    obtain ⟨f, inputsIL, chans⟩ := plain_instance_inputs oracle run fs n memberN (.inr (.inr (.inr (.inl ⟨body, kind⟩))))
      iL memberIL pathIL nodeIL statusIL
    have inputsL := stateInputs_of_singletons scL n memberN f chans
    have notSup : suppressed n (stateInputs last P n) = false := by
      rw [inputsL]; exact suppressed_singletons n f (by rw [kind]; simp)
    have valueEq : nodeValue oracle last g P n = compoundValue last P n := by
      unfold nodeValue primitive
      rw [notSup]
      simp only [kind, Bool.false_eq_true, ↓reduceIte]
    have outputsEq : (compoundValue last P n).outputs =
        (n.outputs.zip (exitItems last (childPath P n.id none 0) body)).map fun (p, items) => ({ port := p.name, items } : Output) := by
      unfold compoundValue
      rw [kind]
    have bound : k < items.length := by rw [← arity]; exact (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨item, hitem⟩ : ∃ item, items[k]? = some item := ⟨items[k], List.getElem?_eq_getElem bound⟩
    have exitsK : (exitItems last (childPath P n.id none 0) body)[k]? = some [item] := by
      rw [exits, List.getElem?_map, hitem]; rfl
    have lenExits : (exitItems last (childPath P n.id none 0) body).length = n.outputs.length := by
      rw [exits, List.length_map, arity]
    rw [valueEq, outputsEq, portC, outputItems_zip n outNames _ lenExits q k hk [item] exitsK, canonical_singleton,
      bag_eq_canonical scL.safe memberC]
    -- the output channel holds exactly `item`
    have present : item ∈ c.items := by
      have hit : Write.out d.path d.edge.src.node d.edge.src.port (.item item) ∈ bodyWrites P n items ++ eosWrites P n := by
        apply List.mem_append_left
        unfold bodyWrites
        apply List.mem_map.mpr
        refine ⟨(q, item), mem_zip_of_index hk hitem, ?_⟩
        rw [pathD, path0, pathC, edgeD, edge0, srcEq]
      obtain ⟨d2, memberD2, idD2, _, presentD2⟩ :=
        applyWrites_token _ t d memberD (entryD.trans (entry0.trans entryC)) safeT.channelIds (.item item) hit
      have inView : d2.core ∈ t'.placedView := by rw [view]; exact placedView_member memberD2
      obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
      have idE : e.id = c0.id := by simpa using (congrArg Channel.id coreE).trans (idD2.trans idD)
      have placedE : Token.item item ∈ e.placed := by
        have := congrArg Channel.placed coreE
        simp only [Channel.core_placed] at this
        rw [this]; exact presentD2
      exact (Effects.item_mem c item).mpr (token_persists rest safeT' e memberE c memberC (id0.symm.trans idE.symm) _ placedE)
    have only : ∀ x ∈ c.items, x = item := by
      intro x presentX
      have presentTok : Token.item x ∈ c.placed := (Effects.item_mem c x).mp presentX
      have absent : Token.item x ∉ c0.placed := by rw [empty0]; simp
      obtain ⟨pre2, op2, post2, t2, t2', d2, d2', _, head2, allowed2, accepted2, rest2, safeT2, active2,
        memberD2, idD2, layoutD2, absentD2, memberD2', idD2', layoutD2', presentD2', _, target2⟩ :=
        token_step run safe0 (.item x) c0 member0 absent (entry0.trans entryC) c memberC id0.symm presentTok
      have nodeT2 : t2.node? P n.id = some n := head2.node P n.id n (fs.scope.node?_of_mem n memberN)
      rw [path0, pathC, edge0, srcC] at target2
      obtain ⟨_, edgeD2, pathD2, _, _, _⟩ := Channel.layout_fields layoutD2
      rcases target_shape t2 t2' op2 safeT2 active2 accepted2 _ _ target2 n nodeT2 with
          ⟨_, _, _, _, _, _, k'⟩ | ⟨_, _, _, _, _, k'⟩ | ⟨_, k'⟩ | ⟨_, _, _, k'⟩ | ⟨_, _, _, k'⟩ | ⟨_, k'⟩
        | ⟨_, _, _, k'⟩ | ⟨_, _, _, k'⟩ | ⟨_, k'⟩ | ⟨inst2, body2, eq2, kinds2⟩ | ⟨_, _, _, _, _, k'⟩ | ⟨eq2, _⟩
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; cases k'
      · rw [kind] at k'; simp at k'
      · subst eq2
        obtain ⟨items2, arity2, view2, exits2, _⟩ :=
          sub_finish_step oracle fs head2 allowed2 accepted2 rest2 active2 n memberN body kind target2
        obtain ⟨w, memberW, tokenW, hits⟩ :=
          gained_token view2 safeT2.channelIds d2 memberD2 d2' memberD2' (idD2'.trans idD2.symm) (.item x) presentD2' absentD2
        rcases List.mem_append.mp memberW with inBody | inEos
        · unfold bodyWrites at inBody
          obtain ⟨⟨p, y⟩, memberPair, eqW⟩ := List.mem_map.mp inBody
          subst eqW
          simp only [Write.token, Token.item.injEq] at tokenW
          subst y
          obtain ⟨_, _, srcD2⟩ := out_ids_port t2 safeT2.channelIds P n.id p.name _ d2 memberD2 hits
          rw [edgeD2, edge0, srcEq] at srcD2
          simp only [PortRef.mk.injEq] at srcD2
          have sameP : p = q := eq_of_mapped_nodup (·.name) n.outputs outNames p q (List.of_mem_zip memberPair).1 port srcD2.2.symm
          subst sameP
          have indexed := zip_index_of_names n outNames items2 p k hk x memberPair
          have exitsK2 : (exitItems last (childPath P n.id none 0) body)[k]? = some [x] := by
            rw [exits2, List.getElem?_map, indexed]; rfl
          rw [exitsK] at exitsK2
          exact (by simpa using exitsK2 : item = x).symm
        · have := eosWrites_eos _ _ w inEos
          rw [this] at tokenW
          cases tokenW
      · rw [kind] at k'; cases k'
      · -- a skip writes no item
        subst eq2
        exfalso
        have executed := transition_of_active accepted2 active2 (by simp)
        obtain ⟨n2, hn2, _, _, _, _, _, _, view2⟩ := effect_skip t2 t2' _ _ executed
        obtain ⟨w, memberW, tokenW, _⟩ :=
          gained_token view2 safeT2.channelIds d2 memberD2 d2' memberD2' (idD2'.trans idD2.symm) (.item x) presentD2' absentD2
        have := eosWrites_eos _ _ w memberW
        rw [this] at tokenW
        cases tokenW
    have itemsC : c.items = [item] :=
      singleton_of_subset (items_nodup_of_invariants scL.safe memberC) (fun x hx => by simp [only x hx]) present
    rw [itemsC]
    exact canonical_singleton item
  · rw [kind] at k'; cases k'
  · -- skipped: the output stays empty and the node is suppressed
    subst eq
    obtain ⟨emptyC, _, dIn, memberDIn, pathDIn, exitDIn, nodeDIn, _, emptyDIn⟩ :=
      skip_closing_final oracle head allowed accepted rest safe0 safeT active n (fs.scope.node?_of_mem n memberN) (by rw [kind]; simp)
        c0 member0 empty0 (entry0.trans entryC) (path0.trans pathC) (by rw [edge0]; exact srcC)
        d memberD idD d' memberD' idD' closedD' c memberC id0.symm
    have sup : suppressed n (stateInputs last P n) = true :=
      suppressed_of_empty scL n memberN plain (by rw [kind]; simp) dIn memberDIn pathDIn exitDIn nodeDIn emptyDIn
    rw [nodeValue_suppressed oracle last g P n sup, portC, outputItems_ports n outNames _ q port]
    simp [bag, emptyC]


/-! ### ForEach -/

theorem instance?_of_mem {s : State} (safe : Invariants s) (i : Instance) (member : i ∈ s.instances) :
    s.instance? i.id = some i := by
  have exists_ : (s.instances.find? (·.id == i.id)).isSome := List.find?_isSome.mpr ⟨i, member, by simp⟩
  cases found : s.instances.find? (·.id == i.id) with
  | none => rw [found] at exists_; contradiction
  | some j =>
    have memberJ := List.mem_of_find?_eq_some found
    have idJ : j.id = i.id := by simpa using List.find?_some found
    have same := unique_instance safe memberJ member idJ
    unfold State.instance?
    rw [found, same]

theorem active_of_status_change {t t' : State} {op : Op} (safe : Invariants t) (accepted : step t op = .ok t')
    (a : Instance) (memberA : a ∈ t.instances) (b : Instance) (memberB : b ∈ t'.instances) (same : b.id = a.id)
    (changed : b.status ≠ a.status) : absorbed t op = false := by
  cases ha : absorbed t op with
  | false => rfl
  | true =>
    exfalso
    rcases step_ok_cases t op t' accepted with ⟨_, eq⟩ | ⟨notAbs, _⟩
    · subst eq
      exact changed (by rw [unique_instance safe memberB memberA same])
    · rw [ha] at notAbs; contradiction

theorem Invariants.record_instance {s : State} (safe : Invariants s) (r : Consumption) (member : r ∈ s.consumed) :
    ∃ k ∈ s.instances, k.id = r.byInstance := by
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  have accounting := safe.1.2
  simp only [accountingOK, Bool.and_eq_true] at accounting
  have all := List.all_eq_true.mp accounting.2 r member
  simp only [Bool.and_eq_true] at all
  cases found : s.instance? r.byInstance with
  | none => rw [found] at all; simp at all
  | some k => exact ⟨k, instance?_mem found, instance?_id found⟩

/-- A waiting instance of a forEach node was spawned for one input item, at iteration 0, owns a
    frame with the body at the child path, and its trigger item sits on the node's input channel. -/
theorem forEach_child_shape (oracle : ScopedOracle) {s0 t : State} {ops : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input}
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops t)
    (fs : FrameStart s0 P g inputs0) (n : Node) (memberN : n ∈ g.nodes) (body : Graph)
    (kind : n.kind = .forEach body)
    (i : Instance) (memberI : i ∈ t.instances) (pathI : i.path = P) (nodeI : i.node = n.id)
    (waiting : i.status = .waitingInputs) :
    ∃ y, i.trigger = some y ∧ i.id = instanceId P n.id (some y) ∧ i.iteration = 0 ∧
      (∃ f ∈ t.frames, f.path = childPath P n.id (some y) 0 ∧ f.graph = body ∧ f.owner = some i.id) ∧
      (∃ c ∈ t.channels, c.path = P ∧ c.exit = false ∧ c.edge.dst.node = n.id ∧ y ∈ c.items) := by
  have safe0 := fs.scope.safe
  have safeT := head.invariants safe0
  have absent0 : ∀ j ∈ s0.instances, j.id ≠ i.id := by
    intro j memberJ eq
    obtain ⟨_, pathEq, _, _⟩ := head.input_snapshot safe0 j i memberJ memberI eq
    exact fs.noInstances j memberJ (by rw [← pathEq, pathI]; exact List.prefix_refl _)
  obtain ⟨pre, op, post, u, u', j, _, headU, allowed, accepted, rest, safeU, absentU, memberJ, idJ, bindJ, created⟩ :=
    instance_created head safe0 i memberI absent0
  have safeU' := preserves_invariants u u' op safeU accepted
  have nodeU : u.node? P n.id = some n := headU.node P n.id n (fs.scope.node?_of_mem n memberN)
  have pathJ : j.path = P := (Instance.binding_path bindJ).trans pathI
  have nodeJ : j.node = n.id := (Instance.binding_node bindJ).trans nodeI
  have notCreatedFinal : j.status ≠ .succeeded ∧ j.status ≠ .cancelled := by
    constructor <;> intro st
    · obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeU' j memberJ (.inl st)
      have same : k = i := unique_instance safeT memberK memberI (idK.trans idJ)
      subst same
      rw [waiting] at statusK; rw [st] at statusK; cases statusK
    · obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeU' j memberJ (.inr st)
      have same : k = i := unique_instance safeT memberK memberI (idK.trans idJ)
      subst same
      rw [waiting] at statusK; rw [st] at statusK; cases statusK
  rcases created with
      ⟨P', N', n', inputs, opEq, hn, hi, ⟨r, cc, kind', eq⟩ | ⟨body', iteration, kinds, eq⟩⟩
    | ⟨P', N', n', inputs, _, hn, kind', hi, eq⟩
    | ⟨P', N', arm, n', arms, inputs, _, hn, kind', hi, eq⟩
    | ⟨P', N', n', c, _, hn, kind', hc, eq⟩
    | ⟨P', N', e, x, n', c, _, hn, kind', hc, eq⟩
    | ⟨P', N', n', ⟨x, k, _, kind'⟩ | ⟨e, x, _, kind'⟩, hn, eq⟩
    | ⟨P', N', n', _, hn, kind', eq⟩
    | ⟨P', N', n', _, hn, eq⟩
    | ⟨P', N', x, n', body', opEq, hn, kind', eq⟩
  all_goals
    have pathEq : P' = P := by rw [eq] at pathJ; exact pathJ
    have idEq : n'.id = n.id := by rw [eq] at nodeJ; exact nodeJ
    subst P'
    have NEq : N' = n.id := (getNode_id u P N' n' hn).symm.trans idEq
    subst N'
    have sameN : n' = n := node?_of_getNode nodeU hn
    subst n'
  · rw [kind] at kind'; cases kind'
  · rcases kinds with ⟨kindSub, _⟩ | ⟨m, kindLoop, _⟩
    · rw [kind] at kindSub; cases kindSub
    · rw [kind] at kindLoop; cases kindLoop
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · rw [kind] at kind'; cases kind'
  · exact absurd (by rw [eq]; rfl) notCreatedFinal.1
  · exact absurd (by rw [eq]; rfl) notCreatedFinal.2
  · -- spawned for `x`
    have bodyEq : body' = body := by rw [kind] at kind'; exact (NodeKind.forEach.inj kind').symm
    subst bodyEq
    subst opEq
    have executed := transition_of_created accepted (by simp) j memberJ absentU
    obtain ⟨_, n2, body2, c, hn2, kind2, hc, pending, f, opened, _, _, _, _, frames', _⟩ :=
      effect_spawn u u' P n.id x safeU.channelIds executed
    have sameN2 := node?_of_getNode nodeU hn2
    subst n2
    have bodyEq2 : body2 = body' := by rw [kind] at kind2; exact (NodeKind.forEach.inj kind2).symm
    subst bodyEq2
    obtain ⟨pathF, graphF, ownerF, _⟩ := opened
    have triggerI : i.trigger = some x := by rw [← Instance.binding_trigger bindJ, eq]; rfl
    have idI : i.id = instanceId P n.id (some x) := by rw [← idJ, eq]; rfl
    have iterI : i.iteration = 0 := by
      have notLoop : ∀ n3 b m, u'.node? j.path j.node = some n3 → n3.kind ≠ .loop b m := by
        intro n3 b m found3
        rw [eq] at found3
        simp only [makeInstance] at found3
        have kept := headU.node P n.id n (fs.scope.node?_of_mem n memberN)
        have kept' := retained_node u u' P n.id n (step_frameDefinitions u u' _ accepted) kept
        rw [kept'] at found3
        have same := Option.some.inj found3
        subst same
        rw [kind]
        intro h; cases h
      have := (rest.iteration_evolves safeU' j memberJ i memberI idJ.symm).2 notLoop
      rw [this, eq]
      rfl
    refine ⟨x, triggerI, idI, iterI, ?_, ?_⟩
    · have memberF : f ∈ u'.frames := by rw [frames']; simp
      have inDefs : f.definitionView ∈ t.frameDefinitions :=
        rest.frameDefinitions.subset (List.mem_map.mpr ⟨f, memberF, rfl⟩)
      obtain ⟨h, memberH, viewH⟩ := List.mem_map.mp inDefs
      refine ⟨h, memberH, ?_, ?_, ?_⟩
      · have := congrArg Frame.path viewH
        simp only [Frame.definitionView] at this
        rw [this, pathF]
        rfl
      · have := congrArg Frame.graph viewH
        simp only [Frame.definitionView] at this
        rw [this, graphF]
      · have := congrArg Frame.owner viewH
        simp only [Frame.definitionView] at this
        rw [this, ownerF, idI]
        rfl
    · have memberC : c ∈ u.channels := (List.mem_filter.mp (List.mem_of_mem_head? hc)).1
      have fields := (List.mem_filter.mp (List.mem_of_mem_head? hc)).2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
      have presentX : Token.item x ∈ c.placed := List.drop_subset _ _ (List.mem_of_mem_head? pending)
      have full : ConformingSteps (fun s op => oracleConforms oracle s op = true) u (_ :: post) t := .cons allowed accepted rest
      obtain ⟨d, memberD, idD, layoutD, prefixD⟩ := run_image full safeU c memberC
      obtain ⟨_, edgeD, pathD, _, exitD, _⟩ := Channel.layout_fields layoutD
      refine ⟨d, memberD, pathD.trans fields.1.1, exitD.trans fields.1.2, by rw [edgeD]; exact fields.2, ?_⟩
      exact (Effects.item_mem d x).mpr (prefixD.subset presentX)

/-- A `finishSubworkflow` step on a forEach node writes the child's results to the output. -/
theorem forEach_finish_step (oracle : ScopedOracle) {s0 t t' last : State} {pre post : List Op} {P : Path} {g : Graph}
    {inputs0 : List Input} {inst : InstanceId}
    (fs : FrameStart s0 P g inputs0)
    (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t)
    (allowed : oracleConforms oracle t (.finishSubworkflow inst) = true)
    (accepted : step t (.finishSubworkflow inst) = .ok t')
    (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) t' post last)
    (active : absorbed t (.finishSubworkflow inst) = false)
    (n : Node) (memberN : n ∈ g.nodes) (body : Graph) (kind : n.kind = .forEach body)
    (target : opTarget t (.finishSubworkflow inst) = some (P, n.id)) :
    ∃ y items, n.outputs.length = items.length ∧
      ((t.instance? inst).bind (·.trigger)) = some y ∧
      t'.placedView = (applyWrites (bodyWrites P n items) t).placedView ∧
      exitItems last (childPath P n.id (some y) 0) body = items.map (fun x => [x]) ∧
      (∃ c ∈ last.channels, c.path = P ∧ c.exit = false ∧ c.edge.dst.node = n.id ∧ y ∈ c.items) := by
  have safeT := head.invariants fs.scope.safe
  have safeT' := preserves_invariants t t' _ safeT accepted
  have executed := transition_of_active accepted active (by simp)
  obtain ⟨i, n', f, items, foundI, waitingI, hn', hf, hbody, arity, _, _, instances', branch⟩ :=
    effect_finishSubworkflow t t' inst executed
  obtain ⟨i2, foundI2, pathI, nodeI⟩ := opTarget_id (inst := inst) rfl target
  rw [foundI] at foundI2
  have sameI : i = i2 := Option.some.inj foundI2
  subst i2
  have nodeT : t.node? P n.id = some n := head.node P n.id n (fs.scope.node?_of_mem n memberN)
  rw [pathI, nodeI] at hn'
  have sameN : n' = n := node?_of_getNode nodeT hn'
  subst sameN
  rcases branch with ⟨body', kindSub, _⟩ | ⟨body', kindFE, view⟩
  · rw [kind] at kindSub; cases kindSub
  · have bodyEq : body' = body := NodeKind.forEach.inj (kindFE.symm.trans kind)
    subst bodyEq
    obtain ⟨y, triggerI, idI, iterI, ⟨f0, memberF0, pathF0, graphF0, _⟩, c, memberC, pathC, exitC, nodeC, presentY⟩ :=
      forEach_child_shape oracle head fs n' memberN body' kind i (instance?_mem foundI) pathI nodeI waitingI
    obtain ⟨memberF, pathF⟩ := currentFrame_spec t i f hf
    have pathF' : f.path = childPath P n'.id (some y) 0 := by rw [pathF, pathI, idI, iterI]; rfl
    have distinctT := head.unique_frames fs.scope.distinct
    have sameF : f = f0 := eq_of_mapped_nodup Frame.path t.frames distinctT f f0 memberF memberF0 (pathF'.trans pathF0.symm)
    subst sameF
    have full : ConformingSteps (fun s op => oracleConforms oracle s op = true) t (_ :: post) last := .cons allowed accepted rest
    have scL := fs.scope.persist (head.append full)
    have validBody : f.graph.validate true = .ok () := by
      rw [graphF0]
      exact g.validateNode_child n' body' (.inr (.inr kind)) (fs.scope.checked n' memberN)
    have scopeChild := Scope.child full scL f memberF validBody
    have exits := exitItems_of_bodyResults full safeT f items hbody scopeChild
    rw [pathF', graphF0] at exits
    refine ⟨y, items, arity, by simp [foundI, triggerI], by rw [view, pathI], exits, ?_⟩
    obtain ⟨d, memberD, idD, layoutD, prefixD⟩ := run_image full safeT c memberC
    obtain ⟨_, edgeD, pathD, _, exitD, _⟩ := Channel.layout_fields layoutD
    refine ⟨d, memberD, pathD.trans pathC, exitD.trans exitC, by rw [edgeD]; exact nodeC, ?_⟩
    exact (Effects.item_mem d y).mpr (prefixD.subset ((Effects.item_mem c y).mp presentY))

end Suimon
