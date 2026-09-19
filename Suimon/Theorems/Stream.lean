import Suimon.Theorems.Coalesce

/-! Final contents of Filter and Merge outputs, via consumption records. -/

namespace Suimon
open Effects

/-- A consumption record at a state points at an item actually placed on its channel. -/
theorem record_item_placed {s : State} (safe : Invariants s) (r : Consumption) (member : r ∈ s.consumed) :
    ∃ c ∈ s.channels, c.id = r.channel ∧ r.item ∈ c.items := by
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  have accounting := safe.1.2
  simp only [accountingOK, Bool.and_eq_true] at accounting
  have all := List.all_eq_true.mp accounting.2 r member
  simp only [Bool.and_eq_true] at all
  obtain ⟨c, memberC, props⟩ := List.any_eq_true.mp all.2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at props
  refine ⟨c, memberC, props.1.1, ?_⟩
  rw [Effects.item_mem]
  exact List.mem_of_getElem? props.2

/-- A token present after a step, on a channel whose history is later fixed, persists to the end. -/
theorem token_persists {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (c : Channel) (member : c ∈ s.channels)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c.id) (t : Token) (present : t ∈ c.placed) :
    t ∈ cl.placed := by
  obtain ⟨d, memberD, idD, _, prefixD⟩ := run_image run safe c member
  have same : d = cl := unique_channel (run.invariants safe) memberD memberL (idD.trans idL.symm)
  subst same
  exact prefixD.subset present

/-- Records persist along a run. -/
theorem ConformingSteps.records_persist {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (r : Consumption) (member : r ∈ s.consumed) :
    r ∈ last.consumed := by
  induction run with
  | nil => exact member
  | @cons s middle final op ops allowed accepted tail ih =>
    exact ih (preserves_invariants s middle op safe accepted) ((step_records s middle op safe accepted).1 r member)

/-- The executed transition behind a non-absorbed, non-idle accepted step. -/
theorem transition_of_active {s next : State} {op : Op} (h : step s op = .ok next) (active : absorbed s op = false)
    (notIdle : op ≠ .idle) : transition s op = .ok next := by
  rcases step_ok_cases s op next h with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
  · rw [active] at a; contradiction
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle => exact absurd rfl notIdle
    | _ => simpa only [transitionOrIdle] using executed

/-- Final contents of the (single) output channel of a Filter node: the kept items of its
    (single) input channel. -/
theorem filter_output_final (oracle : ScopedOracle) {s0 last : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (safe0 : Invariants s0) (layout0 : LayoutOK s0) (distinct0 : (s0.frames.map Frame.path).Nodup)
    (finished : succeededDrained last = true)
    (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n) (kind : n.kind = .filter)
    (singleOut : n.outputs.length = 1) (streamInput : allKind n.inputs .plain = false)
    (frame0 : ∃ f ∈ s0.frames, f.path = c0.path)
    (noRecords0 : ∀ r ∈ s0.consumed, ∀ c ∈ s0.channels, c.path = c0.path → c.exit = false → r.channel ≠ c.id)
    (uniqueInput : ∀ c ∈ s0.channels, ∀ d ∈ s0.channels, c.path = c0.path → d.path = c0.path → c.exit = false → d.exit = false →
      c.edge.dst.node = c0.edge.src.node → d.edge.dst.node = c0.edge.src.node → c.id = d.id)
    (q : Port) (port : q ∈ n.outputs) (portC : c0.edge.src.port = q.name)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id)
    (input : Channel) (memberIn : input ∈ last.channels) (pathIn : input.path = c0.path) (exitIn : input.exit = false)
    (nodeIn : input.edge.dst.node = c0.edge.src.node) :
    ∀ x, x ∈ cl.items ↔ (x ∈ input.items ∧ (oracle c0.path).filter c0.edge.src.node x = true) := by
  have safeLast : Invariants last := run.invariants safe0
  obtain ⟨f0, memberF0, pathF0⟩ := frame0
  have qEq : ∀ p0, n.outputs.head? = some p0 → q = p0 := fun p0 hp0 => head_of_singleton singleOut hp0 port
  -- the input channel at any intermediate state: the unique channel into the node
  have inputAt : ∀ {t : State} {pre : List Op} (head : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 pre t)
      {ops' : List Op} (rest : ConformingSteps (fun s op => oracleConforms oracle s op = true) t ops' last)
      (c1 : Channel), c1 ∈ t.incoming c0.path c0.edge.src.node →
      ∃ e ∈ last.channels, e.id = c1.id ∧ e = input := by
    intro t pre head ops' rest c1 memberC1
    have safeT : Invariants t := head.invariants safe0
    have inChannels : c1 ∈ t.channels := (List.mem_filter.mp memberC1).1
    have fields := (List.mem_filter.mp memberC1).2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
    obtain ⟨e, memberE, idE, layoutE, _⟩ := run_image rest safeT c1 inChannels
    obtain ⟨_, edgeE, pathE, _, exitE, _⟩ := Channel.layout_fields layoutE
    refine ⟨e, memberE, idE, ?_⟩
    exact unique_input_channel run safe0 layout0 distinct0 c0.path c0.edge.src.node ⟨f0, memberF0, pathF0⟩ uniqueInput
      e input memberE memberIn (pathE.trans fields.1.1) pathIn (exitE.trans fields.1.2) exitIn
      (by rw [edgeE]; exact fields.2) nodeIn
  intro x
  constructor
  · intro present
    have presentTok : Token.item x ∈ cl.placed := (Effects.item_mem cl x).mp present
    have absent : Token.item x ∉ c0.placed := by rw [empty0]; simp
    obtain ⟨pre, op, post, t, t', d, d', _, head, allowed, accepted, rest, safeT, active,
      memberD, idD, layoutD, absentD, memberD', idD', layoutD', presentD', _, target⟩ :=
      token_step run safe0 (.item x) c0 member0 absent entry0 cl memberL idL presentTok
    have nodeT := head.node c0.path c0.edge.src.node n found
    have safeT' := preserves_invariants t t' op safeT accepted
    rcases target_shape t t' op safeT active accepted _ _ target n nodeT with
        ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
      | ⟨x', keep, eq, _⟩ | ⟨_, _, _, k⟩ | ⟨eq, _⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, plainK⟩
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · -- fireFilter x' keep wrote the item
      subst eq
      have executed := transition_of_active accepted active (by simp)
      obtain ⟨n', c1, hn, _, hc1, head1, _, _, consumed, kept | ⟨_, view⟩⟩ :=
        effect_fireFilter t t' _ _ x' keep safeT.channelIds executed
      · obtain ⟨keepTrue, p0, hp0, view⟩ := kept
        have tokens := view_tokens t' t _ safeT.channelIds view d memberD d' memberD' (idD'.trans idD.symm) (.item x) presentD'
        rcases tokens with old | ⟨w, hw, tw⟩
        · exact absurd old absentD
        · simp only [List.mem_singleton] at hw
          subst hw
          cases tw
          have conf : keep = (oracle c0.path).filter c0.edge.src.node x := by
            have h := allowed
            simp only [oracleConforms, active, Bool.false_eq_true, ↓reduceIte] at h
            exact beq_iff_eq.mp h
          refine ⟨?_, by rw [← conf]; exact keepTrue⟩
          have memberC1 : c1 ∈ t.incoming c0.path c0.edge.src.node := List.mem_of_mem_head? hc1
          have memberR : ({ channel := c1.id, index := c1.consumed, item := x, byInstance := instanceId c0.path c0.edge.src.node } : Consumption) ∈ t'.consumed := by
            rw [consumed]; simp
          have memberRL := rest.records_persist safeT' _ memberR
          obtain ⟨ch, memberCh, idCh, itemCh⟩ := record_item_placed safeLast _ memberRL
          obtain ⟨e, memberE, idE, eIn⟩ := inputAt head (.cons allowed accepted rest) c1 memberC1
          have same : ch = e := unique_channel safeLast memberCh memberE (idCh.trans idE.symm)
          subst same
          rw [eIn] at itemCh
          exact itemCh
      · exfalso
        have tokens := view_tokens t' t [] safeT.channelIds (by simpa using view) d memberD d' memberD' (idD'.trans idD.symm) (.item x) presentD'
        rcases tokens with old | ⟨w, hw, _⟩
        · exact absentD old
        · simp at hw
    · rw [kind] at k; cases k
    · -- propagateEos writes only EOS
      subst eq
      exfalso
      have executed := transition_of_active accepted active (by simp)
      obtain ⟨n', hn, _, _, _, _, _, _, view⟩ := effect_propagateEos t t' _ _ executed
      have tokens := view_tokens t' t _ safeT.channelIds view d memberD d' memberD' (idD'.trans idD.symm) (.item x) presentD'
      rcases tokens with old | ⟨w, hw, tw⟩
      · exact absentD old
      · have := eosWrites_eos _ _ w hw
        rw [this] at tw; cases tw
    · rcases k with k | k <;> (rw [kind] at k; cases k)
    · rw [kind] at k; cases k
    · rw [plainK] at streamInput; contradiction
  · -- every kept input item was filtered through and written to the output
    rintro ⟨presentIn, keepX⟩
    have drainedIn : (input.path.isEmpty && input.exit) = false := by simp [exitIn]
    obtain ⟨r, memberR, channelR, itemR⟩ := succeededDrained_input_receipt last safeLast finished input memberIn drainedIn x presentIn
    obtain ⟨in00, memberIn00, layoutIn00⟩ := channel_origin_layout run layout0 distinct0 f0 memberF0 input memberIn (pathIn.trans pathF0.symm)
    obtain ⟨idIn00, edgeIn00, pathIn00, _, exitIn00, _⟩ := Channel.layout_fields layoutIn00
    have absent0 : r ∉ s0.consumed := fun h =>
      noRecords0 r h in00 memberIn00 (pathIn00.trans pathIn) (exitIn00.trans exitIn) (channelR.trans idIn00.symm)
    obtain ⟨pre, op, post, t, t', _, head, allowed, accepted, rest, safeT, absentT, presentT, origin⟩ :=
      record_origin run safe0 r memberR absent0
    have safeT' := preserves_invariants t t' op safeT accepted
    have changed : ∃ r' ∈ t'.consumed, r' ∉ t.consumed := ⟨r, presentT, absentT⟩
    have nodeT := head.node c0.path c0.edge.src.node n found
    -- the input channel at `t`
    obtain ⟨inT, memberInT, idInT, layoutInT, _⟩ := run_image head safe0 in00 memberIn00
    obtain ⟨_, edgeInT, pathInT, _, exitInT, _⟩ := Channel.layout_fields layoutInT
    -- the output channel at `t`
    obtain ⟨outT, memberOutT, idOutT, layoutOutT, _⟩ := run_image head safe0 c0 member0
    obtain ⟨_, edgeOutT, pathOutT, entryOutT, _, _⟩ := Channel.layout_fields layoutOutT
    rcases origin with ⟨P', N', inIncoming, shapes⟩ | ⟨inst, i, f, foundI, hf, shapes, inExit⟩
    · obtain ⟨dt, memberDt, idDt⟩ := List.mem_map.mp inIncoming
      have inChannelsDt : dt ∈ t.channels := (List.mem_filter.mp memberDt).1
      have fieldsDt := (List.mem_filter.mp memberDt).2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fieldsDt
      have sameDt : dt = inT := unique_channel safeT inChannelsDt memberInT (idDt.trans (channelR.trans (idIn00.symm.trans idInT.symm)))
      subst sameDt
      have PEq : P' = c0.path := fieldsDt.1.1.symm.trans (pathInT.trans (pathIn00.trans pathIn))
      have NEq : N' = c0.edge.src.node := fieldsDt.2.symm.trans (by rw [edgeInT, edgeIn00]; exact nodeIn)
      subst PEq NEq
      rcases shapes with eq2 | ⟨x', eq2, _⟩ | eq2 | ⟨a, eq2⟩ | eq2 | ⟨e', x', eq2, _, _⟩ | ⟨x', k', eq2, itemR'⟩
        | ⟨e', x', eq2, _, _⟩ | eq2 | eq2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨_, n2, _, hn2, _, kinds⟩ := effect_activate t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rcases kinds with ⟨_, _, k2, _⟩ | ⟨_, _, ⟨k2, _⟩ | ⟨_, k2, _⟩, _⟩ <;> (rw [kind] at k2; cases k2)
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨_, n2, _, _, hn2, k2, _⟩ := effect_spawn t t' _ _ x' safeT.channelIds executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireWaitAll t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, _, _, hn2, k2, _⟩ := effect_fireBranch t t' _ _ a executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireCollect t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, _, hn2, k2, _⟩ := effect_fireCoalesce t t' _ _ e' x' safeT.channelIds executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · -- the filter firing on `x` wrote `x` to the output
        subst eq2
        subst itemR'
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, c1, hn2, _, _, _, _, _, _, kept | ⟨keepFalse, _⟩⟩ :=
          effect_fireFilter t t' _ _ r.item k' safeT.channelIds executed
        · obtain ⟨_, p0, hp0, view⟩ := kept
          have := node?_of_getNode nodeT hn2
          subst n2
          have qp := qEq p0 hp0
          subst qp
          have hit : Write.out outT.path outT.edge.src.node outT.edge.src.port (.item r.item) ∈
              [Write.out c0.path c0.edge.src.node q.name (.item r.item)] := by
            rw [pathOutT, edgeOutT]
            have : c0.edge.src = ⟨c0.edge.src.node, q.name⟩ := by
              cases hsrc : c0.edge.src with
              | mk a b => rw [hsrc] at portC; simp only at portC; simp [portC]
            rw [this]
            simp
          obtain ⟨d', memberD', idD', _, presentD'⟩ :=
            applyWrites_token _ t outT memberOutT (entryOutT.trans entry0) safeT.channelIds (.item r.item) hit
          have inView : d'.core ∈ t'.placedView := by rw [view]; exact placedView_member memberD'
          obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
          have idE : e.id = c0.id := by simpa using (congrArg Channel.id coreE).trans (idD'.trans idOutT)
          have placedE : Token.item r.item ∈ e.placed := by
            have := congrArg Channel.placed coreE
            simp only [Channel.core_placed] at this
            rw [this]; exact presentD'
          have final := token_persists rest safeT' e memberE cl memberL (idL.trans idE.symm) _ placedE
          rw [itemR] at final
          exact (Effects.item_mem cl x).mpr final
        · -- keep = false contradicts conformance with the kept oracle answer
          exfalso
          have conf : k' = (oracle c0.path).filter c0.edge.src.node r.item := by
            have h := allowed
            have active : absorbed t (.fireFilter c0.path c0.edge.src.node r.item k') = false := by
              cases ha : absorbed t (.fireFilter c0.path c0.edge.src.node r.item k') with
              | false => rfl
              | true =>
                exfalso
                rcases step_ok_cases t _ t' accepted with ⟨_, same⟩ | ⟨notAbs, _, _, _, _⟩
                · subst same; exact absentT presentT
                · rw [ha] at notAbs; contradiction
            simp only [oracleConforms, active, Bool.false_eq_true, ↓reduceIte] at h
            exact beq_iff_eq.mp h
          rw [itemR] at conf
          rw [keepX] at conf
          rw [conf] at keepFalse
          cases keepFalse
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, _, hn2, k2, _⟩ := effect_fireMerge t t' _ _ e' x' safeT.channelIds executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · -- propagateEos creates no record
        subst eq2
        have executed := transition_of_record accepted (by simp) changed
        have same := effect_propagateEos_records t t' _ _ safeT executed
        rw [same] at presentT
        exact absurd presentT absentT
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, hn2, cond, _⟩ := effect_skip t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        simp only [Bool.and_eq_true] at cond
        rw [cond.1] at streamInput
        contradiction
    · obtain ⟨dx, memberDx, idDx⟩ := List.mem_map.mp inExit
      have inChannelsDx : dx ∈ t.channels := (List.mem_filter.mp memberDx).1
      have fieldsDx := (List.mem_filter.mp memberDx).2
      simp only [Bool.and_eq_true, beq_iff_eq] at fieldsDx
      have sameDx : dx = inT := unique_channel safeT inChannelsDx memberInT (idDx.trans (channelR.trans (idIn00.symm.trans idInT.symm)))
      subst sameDx
      have : dx.exit = false := exitInT.trans (exitIn00.trans exitIn)
      rw [this] at fieldsDx
      exact absurd fieldsDx.2 (by decide)

/-- Final contents of the (single) output channel of a Merge node: every item of every
    input channel, tagged with the input channel's id. -/
theorem merge_output_final (oracle : ScopedOracle) {s0 last : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (safe0 : Invariants s0) (layout0 : LayoutOK s0) (distinct0 : (s0.frames.map Frame.path).Nodup)
    (finished : succeededDrained last = true)
    (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n) (kind : n.kind = .merge)
    (singleOut : n.outputs.length = 1) (streamInput : allKind n.inputs .plain = false)
    (frame0 : ∃ f ∈ s0.frames, f.path = c0.path)
    (noRecords0 : ∀ r ∈ s0.consumed, ∀ c ∈ s0.channels, c.path = c0.path → c.exit = false → r.channel ≠ c.id)
    (q : Port) (port : q ∈ n.outputs) (portC : c0.edge.src.port = q.name)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) :
    ∀ x, x ∈ cl.items ↔ ∃ input ∈ last.channels, input.path = c0.path ∧ input.exit = false ∧
      input.edge.dst.node = c0.edge.src.node ∧
      ∃ y ∈ input.items, x = derivedItem "merge" c0.path c0.edge.src.node [input.id, y] := by
  have safeLast : Invariants last := run.invariants safe0
  obtain ⟨f0, memberF0, pathF0⟩ := frame0
  have qEq : ∀ p0, n.outputs.head? = some p0 → q = p0 := fun p0 hp0 => head_of_singleton singleOut hp0 port
  intro x
  constructor
  · intro present
    have presentTok : Token.item x ∈ cl.placed := (Effects.item_mem cl x).mp present
    have absent : Token.item x ∉ c0.placed := by rw [empty0]; simp
    obtain ⟨pre, op, post, t, t', d, d', _, head, allowed, accepted, rest, safeT, active,
      memberD, idD, layoutD, absentD, memberD', idD', layoutD', presentD', _, target⟩ :=
      token_step run safe0 (.item x) c0 member0 absent entry0 cl memberL idL presentTok
    have nodeT := head.node c0.path c0.edge.src.node n found
    have safeT' := preserves_invariants t t' op safeT accepted
    rcases target_shape t t' op safeT active accepted _ _ target n nodeT with
        ⟨_, _, _, _, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
      | ⟨_, _, _, k⟩ | ⟨e, y, eq, _⟩ | ⟨eq, _⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨_, plainK⟩
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · rw [kind] at k; cases k
    · -- fireMerge e y wrote the tagged item
      subst eq
      have executed := transition_of_active accepted active (by simp)
      obtain ⟨n', c1, p0, hn, _, memberC1, idC1, _, hp0, _, _, consumed, view⟩ :=
        effect_fireMerge t t' _ _ e y safeT.channelIds executed
      have tokens := view_tokens t' t _ safeT.channelIds view d memberD d' memberD' (idD'.trans idD.symm) (.item x) presentD'
      rcases tokens with old | ⟨w, hw, tw⟩
      · exact absurd old absentD
      · simp only [List.mem_singleton] at hw
        subst hw
        cases tw
        have inChannels : c1 ∈ t.channels := (List.mem_filter.mp memberC1).1
        have fields := (List.mem_filter.mp memberC1).2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
        have memberR : ({ channel := e, index := c1.consumed, item := y, byInstance := instanceId c0.path c0.edge.src.node } : Consumption) ∈ t'.consumed := by
          rw [consumed]; simp
        have memberRL := rest.records_persist safeT' _ memberR
        obtain ⟨ch, memberCh, idCh, itemCh⟩ := record_item_placed safeLast _ memberRL
        obtain ⟨e1, memberE1, idE1, layoutE1, _⟩ := run_image (.cons allowed accepted rest) safeT c1 inChannels
        obtain ⟨_, edgeE1, pathE1, _, exitE1, _⟩ := Channel.layout_fields layoutE1
        have same : ch = e1 := unique_channel safeLast memberCh memberE1 (idCh.trans (idC1.symm.trans idE1.symm))
        subst same
        refine ⟨ch, memberCh, pathE1.trans fields.1.1, exitE1.trans fields.1.2, by rw [edgeE1]; exact fields.2, y, itemCh, ?_⟩
        rw [idE1, idC1]
    · -- propagateEos writes only EOS
      subst eq
      exfalso
      have executed := transition_of_active accepted active (by simp)
      obtain ⟨n', hn, _, _, _, _, _, _, view⟩ := effect_propagateEos t t' _ _ executed
      have tokens := view_tokens t' t _ safeT.channelIds view d memberD d' memberD' (idD'.trans idD.symm) (.item x) presentD'
      rcases tokens with old | ⟨w, hw, tw⟩
      · exact absentD old
      · have := eosWrites_eos _ _ w hw
        rw [this] at tw; cases tw
    · rcases k with k | k <;> (rw [kind] at k; cases k)
    · rw [kind] at k; cases k
    · rw [plainK] at streamInput; contradiction
  · -- every input item was merged through and written to the output
    rintro ⟨input, memberIn, pathIn, exitIn, nodeIn, y, presentIn, eqX⟩
    subst eqX
    have drainedIn : (input.path.isEmpty && input.exit) = false := by simp [exitIn]
    obtain ⟨r, memberR, channelR, itemR⟩ := succeededDrained_input_receipt last safeLast finished input memberIn drainedIn y presentIn
    obtain ⟨in00, memberIn00, layoutIn00⟩ := channel_origin_layout run layout0 distinct0 f0 memberF0 input memberIn (pathIn.trans pathF0.symm)
    obtain ⟨idIn00, edgeIn00, pathIn00, _, exitIn00, _⟩ := Channel.layout_fields layoutIn00
    have absent0 : r ∉ s0.consumed := fun h =>
      noRecords0 r h in00 memberIn00 (pathIn00.trans pathIn) (exitIn00.trans exitIn) (channelR.trans idIn00.symm)
    obtain ⟨pre, op, post, t, t', _, head, allowed, accepted, rest, safeT, absentT, presentT, origin⟩ :=
      record_origin run safe0 r memberR absent0
    have safeT' := preserves_invariants t t' op safeT accepted
    have changed : ∃ r' ∈ t'.consumed, r' ∉ t.consumed := ⟨r, presentT, absentT⟩
    have nodeT := head.node c0.path c0.edge.src.node n found
    obtain ⟨inT, memberInT, idInT, layoutInT, _⟩ := run_image head safe0 in00 memberIn00
    obtain ⟨_, edgeInT, pathInT, _, exitInT, _⟩ := Channel.layout_fields layoutInT
    obtain ⟨outT, memberOutT, idOutT, layoutOutT, _⟩ := run_image head safe0 c0 member0
    obtain ⟨_, edgeOutT, pathOutT, entryOutT, _, _⟩ := Channel.layout_fields layoutOutT
    rcases origin with ⟨P', N', inIncoming, shapes⟩ | ⟨inst, i, f, foundI, hf, shapes, inExit⟩
    · obtain ⟨dt, memberDt, idDt⟩ := List.mem_map.mp inIncoming
      have inChannelsDt : dt ∈ t.channels := (List.mem_filter.mp memberDt).1
      have fieldsDt := (List.mem_filter.mp memberDt).2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fieldsDt
      have sameDt : dt = inT := unique_channel safeT inChannelsDt memberInT (idDt.trans (channelR.trans (idIn00.symm.trans idInT.symm)))
      subst sameDt
      have PEq : P' = c0.path := fieldsDt.1.1.symm.trans (pathInT.trans (pathIn00.trans pathIn))
      have NEq : N' = c0.edge.src.node := fieldsDt.2.symm.trans (by rw [edgeInT, edgeIn00]; exact nodeIn)
      subst PEq NEq
      rcases shapes with eq2 | ⟨x', eq2, _⟩ | eq2 | ⟨a, eq2⟩ | eq2 | ⟨e', x', eq2, _, _⟩ | ⟨x', k', eq2, _⟩
        | ⟨e', x', eq2, itemR', channelR'⟩ | eq2 | eq2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨_, n2, _, hn2, _, kinds⟩ := effect_activate t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rcases kinds with ⟨_, _, k2, _⟩ | ⟨_, _, ⟨k2, _⟩ | ⟨_, k2, _⟩, _⟩ <;> (rw [kind] at k2; cases k2)
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨_, n2, _, _, hn2, k2, _⟩ := effect_spawn t t' _ _ x' safeT.channelIds executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireWaitAll t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, _, _, hn2, k2, _⟩ := effect_fireBranch t t' _ _ a executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireCollect t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, _, hn2, k2, _⟩ := effect_fireCoalesce t t' _ _ e' x' safeT.channelIds executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, _, hn2, k2, _⟩ := effect_fireFilter t t' _ _ x' k' safeT.channelIds executed
        have := node?_of_getNode nodeT hn2
        subst n2
        rw [kind] at k2; cases k2
      · -- the merge firing on `y` from `input` wrote the tagged item
        subst eq2
        subst itemR'
        subst channelR'
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, c1, p0, hn2, _, _, _, _, hp0, _, _, _, view⟩ :=
          effect_fireMerge t t' _ _ r.channel r.item safeT.channelIds executed
        have := node?_of_getNode nodeT hn2
        subst n2
        have qp := qEq p0 hp0
        subst qp
        have hit : Write.out outT.path outT.edge.src.node outT.edge.src.port
            (.item (derivedItem "merge" c0.path c0.edge.src.node [r.channel, r.item])) ∈
            [Write.out c0.path c0.edge.src.node q.name (.item (derivedItem "merge" c0.path c0.edge.src.node [r.channel, r.item]))] := by
          rw [pathOutT, edgeOutT]
          have : c0.edge.src = ⟨c0.edge.src.node, q.name⟩ := by
            cases hsrc : c0.edge.src with
            | mk a b => rw [hsrc] at portC; simp only at portC; simp [portC]
          rw [this]
          simp
        obtain ⟨d', memberD', idD', _, presentD'⟩ :=
          applyWrites_token _ t outT memberOutT (entryOutT.trans entry0) safeT.channelIds _ hit
        have inView : d'.core ∈ t'.placedView := by rw [view]; exact placedView_member memberD'
        obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
        have idE : e.id = c0.id := by simpa using (congrArg Channel.id coreE).trans (idD'.trans idOutT)
        have placedE : Token.item (derivedItem "merge" c0.path c0.edge.src.node [r.channel, r.item]) ∈ e.placed := by
          have := congrArg Channel.placed coreE
          simp only [Channel.core_placed] at this
          rw [this]; exact presentD'
        have final := token_persists rest safeT' e memberE cl memberL (idL.trans idE.symm) _ placedE
        rw [itemR, channelR] at final
        exact (Effects.item_mem cl _).mpr final
      · -- propagateEos creates no record
        subst eq2
        have executed := transition_of_record accepted (by simp) changed
        have same := effect_propagateEos_records t t' _ _ safeT executed
        rw [same] at presentT
        exact absurd presentT absentT
      · subst eq2
        have executed := transition_of_record accepted (by simp) changed
        obtain ⟨n2, hn2, cond, _⟩ := effect_skip t t' _ _ executed
        have := node?_of_getNode nodeT hn2
        subst n2
        simp only [Bool.and_eq_true] at cond
        rw [cond.1] at streamInput
        contradiction
    · obtain ⟨dx, memberDx, idDx⟩ := List.mem_map.mp inExit
      have inChannelsDx : dx ∈ t.channels := (List.mem_filter.mp memberDx).1
      have fieldsDx := (List.mem_filter.mp memberDx).2
      simp only [Bool.and_eq_true, beq_iff_eq] at fieldsDx
      have sameDx : dx = inT := unique_channel safeT inChannelsDx memberInT (idDx.trans (channelR.trans (idIn00.symm.trans idInT.symm)))
      subst sameDx
      have : dx.exit = false := exitInT.trans (exitIn00.trans exitIn)
      rw [this] at fieldsDx
      exact absurd fieldsDx.2 (by decide)

end Suimon
