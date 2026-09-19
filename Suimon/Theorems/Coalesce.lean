import Suimon.Theorems.Records

/-! Final contents of a Coalesce node's output and inputs. -/

namespace Suimon
open Effects

theorem head_of_singleton {α : Type} {l : List α} {x q : α} (len : l.length = 1) (hd : l.head? = some x) (mem : q ∈ l) :
    q = x := by
  match l, len, hd, mem with
  | [y], _, hd, mem =>
    simp only [List.head?_cons, Option.some.injEq] at hd
    simp only [List.mem_singleton] at mem
    exact mem.trans hd

/-- A step that creates a record is an executed (non-idle, non-absorbed) transition. -/
theorem transition_of_record {s next : State} {op : Op} (h : step s op = .ok next) (notIdle : op ≠ .idle)
    (changed : ∃ r ∈ next.consumed, r ∉ s.consumed) : transition s op = .ok next := by
  obtain ⟨r, present, absent⟩ := changed
  rcases step_ok_cases s op next h with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst same; exact absurd present absent
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle => exact absurd rfl notIdle
    | _ => simpa only [transitionOrIdle] using executed

theorem unique_instance {s : State} (safe : Invariants s) {i j : Instance}
    (hi : i ∈ s.instances) (hj : j ∈ s.instances) (same : i.id = j.id) : i = j :=
  eq_of_mapped_nodup (·.id) s.instances safe.instanceIds i j hi hj same

theorem instanceId_none (path : Path) (n : Node) (status : InstanceStatus) (inputs : List (PortName × ItemId)) :
    (makeInstance path n status inputs).id = instanceId path n.id none := rfl

/-- Final contents of the (single) output channel of a Coalesce node. -/
theorem coalesce_output_final (oracle : ScopedOracle) {s0 last : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (safe0 : Invariants s0) (layout0 : LayoutOK s0) (distinct0 : (s0.frames.map Frame.path).Nodup)
    (finished : succeededDrained last = true)
    (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n) (kind : n.kind = .coalesce)
    (singleOut : n.outputs.length = 1)
    (frame0 : ∃ f ∈ s0.frames, f.path = c0.path)
    (fresh0 : ∀ j ∈ s0.instances, ¬ (j.path = c0.path ∧ j.node = c0.edge.src.node))
    (noRecords0 : ∀ r ∈ s0.consumed, ∀ c ∈ s0.channels, c.path = c0.path → c.exit = false → r.channel ≠ c.id)
    (inputKinds : ∀ c ∈ s0.channels, c.path = c0.path → c.exit = false → c.edge.dst.node = c0.edge.src.node → c.kind = .plain)
    (uniqueDst : ∀ c ∈ s0.channels, ∀ d ∈ s0.channels, c.path = c0.path → d.path = c0.path → c.exit = false → d.exit = false →
      c.edge.dst = d.edge.dst → c.id = d.id)
    (q : Port) (port : q ∈ n.outputs) (portC : c0.edge.src.port = q.name)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) :
    (∃ item selected, selected ∈ last.channels ∧ selected.path = c0.path ∧ selected.exit = false ∧
        selected.edge.dst.node = c0.edge.src.node ∧ selected.items = [item] ∧
        (∀ d ∈ last.channels, d.path = c0.path → d.exit = false → d.edge.dst.node = c0.edge.src.node →
          d.id ≠ selected.id → d.items = []) ∧
        cl.items = [item] ∧
        ∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .succeeded) ∨
    (cl.items = [] ∧ (∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .cancelled) ∧
        ∀ d ∈ last.channels, d.path = c0.path → d.exit = false → d.edge.dst.node = c0.edge.src.node → d.items = []) := by
  have closedL := closed_of_drained finished memberL
  have open0 : Token.eos ∉ c0.placed := by rw [empty0]; simp
  have present : Token.eos ∈ cl.placed := by simpa [Channel.closed] using closedL
  obtain ⟨pre, op, post, s, s', c, c', _, head, allowed, accepted, rest, safeS, active,
    memberC, idC, layoutC, absentC, memberC', idC', layoutC', presentC', _, target⟩ :=
    token_step run safe0 .eos c0 member0 open0 entry0 cl memberL idL present
  have nodeS := head.node c0.path c0.edge.src.node n found
  have safeS' := preserves_invariants s s' op safeS accepted
  have safeLast : Invariants last := rest.invariants safeS'
  obtain ⟨_, edgeC, pathC, entryC, _, kindC⟩ := Channel.layout_fields layoutC
  have closedC' : c'.closed = true := by simpa [Channel.closed] using presentC'
  have finalPlaced : cl.placed = c'.placed := by
    obtain ⟨e, memberE, idE, placedE⟩ := rest.retains_closed_channel safeS' c' memberC' closedC'
    have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idC'.trans idL.symm))
    subst same
    exact placedE
  obtain ⟨f0, memberF0, pathF0⟩ := frame0
  -- every channel of this frame at `last` descends from a channel at `s0`
  have originL : ∀ d ∈ last.channels, d.path = c0.path → ∃ d00 ∈ s0.channels, d00.layout = d.layout :=
    fun d memberD pathD => channel_origin_layout run layout0 distinct0 f0 memberF0 d memberD (pathD.trans pathF0.symm)
  rcases target_shape s s' op safeS active accepted _ _ target n nodeS with
      ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨edge, item, eq, _⟩ | ⟨_, k⟩
    | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨eq, _⟩
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · -- fireCoalesce
    subst eq
    left
    rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [active] at a; contradiction
    · have executed := prepareWith_body transitionOrIdle s s' _ prepared
      have ready := prepare_preconditions s _ s' prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨n', c1, p0, hn, _, hc1, head1, hp0, view, instances, _, consumed⟩ :=
        effect_fireCoalesce s s' _ _ edge item safeS.channelIds executed
      have sameN := node?_of_getNode nodeS hn
      subst n'
      have nid := getNode_id s _ _ n hn
      have qEq : q = p0 := head_of_singleton singleOut hp0 port
      subst qEq
      have member1 : c1 ∈ s.incoming c0.path c0.edge.src.node := List.mem_of_find?_eq_some hc1
      have inChannels1 : c1 ∈ s.channels := (List.mem_filter.mp member1).1
      have fields1 := (List.mem_filter.mp member1).2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields1
      have id1 : c1.id = edge := by simpa using List.find?_some hc1
      -- the selected input is closed (readiness) and plain
      have closed1 : c1.closed = true := by
        simp only [preconditions, coalesceReady, hc1, Option.any_some, Bool.and_eq_true, plainChannelReady] at ready
        exact ready.1.1.1.2
      obtain ⟨c100, member100, layout100⟩ := channel_origin_layout head layout0 distinct0 f0 memberF0 c1 inChannels1
        (fields1.1.1.trans pathF0.symm)
      obtain ⟨id100, edge100, path100, _, exit100, kind100⟩ := Channel.layout_fields layout100
      have plain1 : c1.kind = .plain := by
        rw [← kind100]
        exact inputKinds c100 member100 (path100.trans fields1.1.1) (exit100.trans fields1.1.2) (by rw [edge100]; exact fields1.2)
      have items1 : c1.items = [item] := by
        apply plain_items_singleton c1 (channelOK_of_invariants safeS inChannels1) plain1
        exact (Effects.item_mem c1 _).mpr (List.drop_subset _ _ (List.mem_of_mem_head? head1))
      have runS : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.fireCoalesce c0.path c0.edge.src.node edge item :: post) last :=
        .cons allowed accepted rest
      -- the selected input at the end
      obtain ⟨e1, memberE1, idE1, placedE1⟩ := runS.retains_closed_channel safeS c1 inChannels1 closed1
      obtain ⟨e1', memberE1', idE1', layoutE1', _⟩ := run_image runS safeS c1 inChannels1
      have sameE1 : e1' = e1 := unique_channel safeLast memberE1' memberE1 (idE1'.trans idE1.symm)
      subst sameE1
      obtain ⟨_, edgeE1, pathE1, _, exitE1, _⟩ := Channel.layout_fields layoutE1'
      -- the created instance persists as succeeded
      let j := makeInstance c0.path n .succeeded [(c1.edge.dst.port, item)]
      have memberJ : j ∈ s'.instances := by rw [instances]; simp [j]
      obtain ⟨kFinal, memberK, idK, statusK⟩ := rest.retains_status safeS' j memberJ (.inl rfl)
      obtain ⟨nodeK, pathK, _, inputsK⟩ := rest.input_snapshot safeS' j kFinal memberJ memberK idK.symm
      refine ⟨item, e1', memberE1, pathE1.trans fields1.1.1, exitE1.trans fields1.1.2, by rw [edgeE1]; exact fields1.2,
        by simp only [Channel.items, placedE1]; exact items1, ?_, ?_, ⟨kFinal, memberK, pathK, nodeK.trans nid, statusK⟩⟩
      · -- every other input is empty at the end
        intro d memberD pathD exitD nodeD notSel
        cases hd : d.items with
        | nil => rfl
        | cons x xs =>
          exfalso
          -- the item was consumed: find its record and the operation that created it
          have drainedD : (d.path.isEmpty && d.exit) = false := by simp [exitD]
          obtain ⟨r, memberR, channelR, itemR⟩ := succeededDrained_input_receipt last safeLast finished d memberD drainedD x (by rw [hd]; simp)
          obtain ⟨d00, member00, layout00⟩ := originL d memberD pathD
          obtain ⟨id00, edge00, path00, _, exit00, _⟩ := Channel.layout_fields layout00
          have absent0 : r ∉ s0.consumed := fun h =>
            noRecords0 r h d00 member00 (path00.trans pathD) (exit00.trans exitD) (channelR.trans id00.symm)
          obtain ⟨pre2, op2, post2, t, t', _, head2, allowed2, accepted2, rest2, safeT, _, presentT, origin⟩ :=
            record_origin run safe0 r memberR absent0
          have safeT' := preserves_invariants t t' op2 safeT accepted2
          -- the channel at `t`
          obtain ⟨dt, memberDt, idDt, layoutDt, _⟩ := run_image head2 safe0 d00 member00
          obtain ⟨_, edgeDt, pathDt, _, exitDt, _⟩ := Channel.layout_fields layoutDt
          have nodeT := head2.node c0.path c0.edge.src.node n found
          rcases origin with ⟨P', N', inIncoming, shapes⟩ | ⟨inst, i, f, foundI, hf, shapes, inExit⟩
          · -- the record consumed an input of the target node (P', N') = (P, N)
            obtain ⟨dt', memberDt', idDt'⟩ := List.mem_map.mp inIncoming
            have inChannelsDt' : dt' ∈ t.channels := (List.mem_filter.mp memberDt').1
            have fieldsDt' := (List.mem_filter.mp memberDt').2
            simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fieldsDt'
            have sameDt : dt' = dt := unique_channel safeT inChannelsDt' memberDt (idDt'.trans (channelR.trans (id00.symm.trans idDt.symm)))
            subst dt'
            have PEq : P' = c0.path := fieldsDt'.1.1.symm.trans (pathDt.trans (path00.trans pathD))
            have NEq : N' = c0.edge.src.node := fieldsDt'.2.symm.trans (by rw [edgeDt, edge00]; exact nodeD)
            subst PEq NEq
            have changed : ∃ r' ∈ t'.consumed, r' ∉ t.consumed := ⟨r, presentT, by assumption⟩
            -- the created instance of the closing step, seen at the end
            have finalId : kFinal.id = instanceId c0.path n.id none := idK
            rcases shapes with eq2 | ⟨x', eq2, _⟩ | eq2 | ⟨a, eq2⟩ | eq2 | ⟨e', x', eq2, itemR', channelR'⟩ | ⟨x', k', eq2, _⟩
              | ⟨e', x', eq2, _, _⟩ | eq2 | eq2
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨_, n2, _, hn2, _, kinds⟩ := effect_activate t t' _ _ executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rcases kinds with ⟨_, _, k2, _⟩ | ⟨_, _, ⟨k2, _⟩ | ⟨_, k2, _⟩, _⟩ <;> (rw [kind] at k2; cases k2)
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨_, n2, _, _, hn2, k2, _⟩ := effect_spawn t t' _ _ x' safeT.channelIds executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rw [kind] at k2; cases k2
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireWaitAll t t' _ _ executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rw [kind] at k2; cases k2
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, _, _, _, hn2, k2, _⟩ := effect_fireBranch t t' _ _ a executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rw [kind] at k2; cases k2
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireCollect t t' _ _ executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rw [kind] at k2; cases k2
            · -- a second Coalesce firing on another input: the same instance would carry two inputs
              subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, c2, _, hn2, _, hc2, _, _, _, instances2, _, _⟩ :=
                effect_fireCoalesce t t' _ _ e' x' safeT.channelIds executed
              have := node?_of_getNode nodeT hn2
              subst n2
              have member2 : c2 ∈ t.incoming c0.path c0.edge.src.node := List.mem_of_find?_eq_some hc2
              have inChannels2 : c2 ∈ t.channels := (List.mem_filter.mp member2).1
              have id2 : c2.id = e' := by simpa using List.find?_some hc2
              -- c2 is the channel of the record, i.e. `dt`
              have same2 : c2 = dt := unique_channel safeT inChannels2 memberDt (id2.trans (channelR'.symm.trans (channelR.trans (id00.symm.trans idDt.symm))))
              have fields2 := (List.mem_filter.mp member2).2
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields2
              let j2 := makeInstance c0.path n .succeeded [(c2.edge.dst.port, x')]
              have memberJ2 : j2 ∈ t'.instances := by rw [instances2]; simp [j2]
              obtain ⟨k2, memberK2, idK2, _⟩ := rest2.retains_status safeT' j2 memberJ2 (.inl rfl)
              obtain ⟨_, _, _, inputsK2⟩ := rest2.input_snapshot safeT' j2 k2 memberJ2 memberK2 idK2.symm
              have sameK : k2 = kFinal := unique_instance safeLast memberK2 memberK (idK2.trans finalId.symm)
              subst sameK
              have portsEq : c2.edge.dst.port = c1.edge.dst.port := by
                have := inputsK2.symm.trans inputsK
                simp [j2, j, makeInstance] at this
                exact this.1
              -- the two input channels share their destination, hence coincide
              obtain ⟨c200, member200, layout200⟩ := channel_origin_layout head2 layout0 distinct0 f0 memberF0 c2 inChannels2
                (fields2.1.1.trans pathF0.symm)
              obtain ⟨id200, edge200, path200, _, exit200, _⟩ := Channel.layout_fields layout200
              have dstEq : c200.edge.dst = c100.edge.dst := by
                rw [edge200, edge100]
                have nodeEq : c2.edge.dst.node = c1.edge.dst.node := fields2.2.trans fields1.2.symm
                cases hA : c2.edge.dst with
                | mk nodeA portA =>
                  cases hB : c1.edge.dst with
                  | mk nodeB portB =>
                    rw [hA, hB] at nodeEq portsEq
                    simp only at nodeEq portsEq
                    rw [nodeEq, portsEq]
              have idsEq := uniqueDst c200 member200 c100 member100 (path200.trans fields2.1.1)
                (path100.trans fields1.1.1) (exit200.trans fields2.1.2) (exit100.trans fields1.1.2) dstEq
              apply notSel
              rw [← id00, ← idDt, ← same2, ← id200, idsEq, id100]
              exact idE1'.symm
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireFilter t t' _ _ x' k' safeT.channelIds executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rw [kind] at k2; cases k2
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, _, _, hn2, k2, _⟩ := effect_fireMerge t t' _ _ e' x' safeT.channelIds executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rw [kind] at k2; cases k2
            · subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, hn2, k2, _⟩ := effect_propagateEos t t' _ _ executed
              have := node?_of_getNode nodeT hn2
              subst n2
              rw [kind] at k2; simp at k2
            · -- a skip would leave a cancelled instance with the same identifier
              subst eq2
              have executed := transition_of_record accepted2 (by simp) changed
              obtain ⟨n2, hn2, _, _, _, instances2, _, _, _⟩ := effect_skip t t' _ _ executed
              have := node?_of_getNode nodeT hn2
              subst n2
              let j2 := makeInstance c0.path n .cancelled
              have memberJ2 : j2 ∈ t'.instances := by rw [instances2]; simp [j2]
              obtain ⟨k2, memberK2, idK2, statusK2⟩ := rest2.retains_status safeT' j2 memberJ2 (.inr rfl)
              have sameK : k2 = kFinal := unique_instance safeLast memberK2 memberK (idK2.trans finalId.symm)
              subst sameK
              rw [statusK] at statusK2
              cases statusK2
          · -- an exit channel of a frame cannot be an input channel
            obtain ⟨dx, memberDx, idDx⟩ := List.mem_map.mp inExit
            have inChannelsDx : dx ∈ t.channels := (List.mem_filter.mp memberDx).1
            have fieldsDx := (List.mem_filter.mp memberDx).2
            simp only [Bool.and_eq_true, beq_iff_eq] at fieldsDx
            have sameDx : dx = dt := unique_channel safeT inChannelsDx memberDt (idDx.trans (channelR.trans (id00.symm.trans idDt.symm)))
            subst sameDx
            have : dx.exit = false := exitDt.trans (exit00.trans exitD)
            rw [this] at fieldsDx
            exact absurd fieldsDx.2 (by decide)
      · -- the output holds exactly the selected item
        have emptyC : c.items = [] := by
          cases hi : c.items with
          | nil => rfl
          | cons x xs =>
            exfalso
            obtain ⟨j', memberJ', pathJ', nodeJ'⟩ := items_imply_instance oracle head safe0 n c0 found member0 empty0 entry0
              c memberC idC x (by rw [hi]; simp)
            have triggerJ' := instance_trigger_none oracle head safe0 _ _ n found (fun body h => by rw [kind] at h; cases h)
              fresh0 j' memberJ' pathJ' nodeJ'
            have fresh := fresh_of_append safeS' _ instances j' memberJ'
            apply fresh
            simp only [instanceKey, makeInstance, pathJ', nodeJ', triggerJ', nid]
        have srcC : c.edge.src = ⟨c0.edge.src.node, q.name⟩ := by
          rw [edgeC]
          cases hsrc : c0.edge.src with
          | mk a b =>
            rw [hsrc] at portC
            simp only at portC
            simp [portC]
        have hit : Write.out c.path c.edge.src.node c.edge.src.port (.item item) ∈
            Write.out c0.path c0.edge.src.node q.name (.item item) :: eosWrites c0.path n := by
          rw [pathC, srcC]
          exact List.mem_cons_self ..
        obtain ⟨d', memberD', idD', _, presentD'⟩ :=
          applyWrites_token _ s c memberC (entryC.trans entry0) safeS.channelIds (.item item) hit
        have inView : d'.core ∈ s'.placedView := by rw [view]; exact placedView_member memberD'
        obtain ⟨f, memberF, coreF⟩ := List.mem_map.mp inView
        have idF : f.id = d'.id := by simpa using congrArg Channel.id coreF
        have sameF : f = c' := unique_channel safeS' memberF memberC' (idF.trans (idD'.trans (idC.trans idC'.symm)))
        subst sameF
        have itemIn : item ∈ f.items := by
          rw [Effects.item_mem]
          have := congrArg Channel.placed coreF
          simp only [Channel.core_placed] at this
          rw [this]; exact presentD'
        have tokens := view_tokens s' s _ safeS.channelIds view c memberC f memberF (idC'.trans idC.symm)
        have subset : f.items ⊆ [item] := by
          intro x hx
          rcases tokens (.item x) ((Effects.item_mem f x).mp hx) with old | ⟨w, hw, tw⟩
          · exact absurd ((Effects.item_mem c x).mpr old) (by rw [emptyC]; simp)
          · rcases List.mem_cons.mp hw with rfl | eos
            · cases tw; simp
            · have := eosWrites_eos _ _ w eos
              rw [this] at tw; cases tw
        have itemsF : f.items = [item] := singleton_of_subset (items_nodup_of_invariants safeS' memberF) subset itemIn
        rw [show cl.items = f.items from by simp only [Channel.items, finalPlaced], itemsF]
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; cases k
  · rw [kind] at k; simp at k
  · rcases k with k | k <;> (rw [kind] at k; cases k)
  · rw [kind] at k; cases k
  · -- skip: all inputs were closed and empty
    subst eq
    right
    rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [active] at a; contradiction
    · have executed := prepareWith_body transitionOrIdle s s' _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨n', hn, cond, _, noInstance, instances, _, _, _⟩ := effect_skip s s' _ _ executed
      have sameN := node?_of_getNode nodeS hn
      subst n'
      have emptyC : c.items = [] := by
        cases hi : c.items with
        | nil => rfl
        | cons x xs =>
          exfalso
          obtain ⟨j, memberJ, pathJ, nodeJ⟩ := items_imply_instance oracle head safe0 n c0 found member0 empty0 entry0
            c memberC idC x (by rw [hi]; simp)
          exact noInstance j memberJ ⟨pathJ, nodeJ⟩
      have itemsL : cl.items = [] := by
        have same := skip_no_items s s' _ _ safeS safeS' active accepted c memberC c' memberC' (idC'.trans idC.symm)
        simp only [Channel.items, finalPlaced]
        exact same.trans emptyC
      refine ⟨itemsL, ?_, ?_⟩
      · let j := makeInstance c0.path n .cancelled
        have memberJ : j ∈ s'.instances := by rw [instances]; simp [j]
        obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeS' j memberJ (.inr rfl)
        obtain ⟨nodeK, pathK, _, _⟩ := rest.input_snapshot safeS' j k memberJ memberK idK.symm
        refine ⟨k, memberK, pathK, ?_, statusK⟩
        rw [nodeK]
        exact getNode_id s _ _ n hn
      · intro d memberD pathD exitD nodeD
        have allEmpty : (s.incoming c0.path c0.edge.src.node).all (fun c => c.closed && c.items.isEmpty) = true := by
          simp only [Bool.and_eq_true] at cond
          have raw := cond.2
          rw [kind] at raw
          simp only [Bool.and_eq_true] at raw
          exact raw.2
        obtain ⟨d00, member00, layout00⟩ := originL d memberD pathD
        obtain ⟨id00, edge00, path00, _, exit00, _⟩ := Channel.layout_fields layout00
        obtain ⟨ds, memberDs, idDs, layoutDs, _⟩ := run_image head safe0 d00 member00
        obtain ⟨_, edgeDs, pathDs, _, exitDs, _⟩ := Channel.layout_fields layoutDs
        have inIncoming : ds ∈ s.incoming c0.path c0.edge.src.node := by
          refine List.mem_filter.mpr ⟨memberDs, ?_⟩
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
          exact ⟨⟨pathDs.trans (path00.trans pathD), exitDs.trans (exit00.trans exitD)⟩, by rw [edgeDs, edge00]; exact nodeD⟩
        have props := List.all_eq_true.mp allEmpty ds inIncoming
        simp only [Bool.and_eq_true, List.isEmpty_iff] at props
        have runS : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.skip c0.path c0.edge.src.node :: post) last :=
          .cons allowed accepted rest
        obtain ⟨e, memberE, idE, placedE⟩ := runS.retains_closed_channel safeS ds memberDs props.1
        have sameE : e = d := unique_channel safeLast memberE memberD (idE.trans (idDs.trans id00))
        subst sameE
        simp only [Channel.items, placedE]
        exact props.2

end Suimon
