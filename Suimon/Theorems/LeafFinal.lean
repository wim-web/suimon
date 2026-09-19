import Suimon.Theorems.FrameOrigin

/-! Final contents of a leaf's output channels in a successful, drained run. -/

namespace Suimon
open Effects

theorem Instance.binding_path {i j : Instance} (h : j.binding = i.binding) : j.path = i.path := by
  simp only [Instance.binding, Prod.mk.injEq] at h
  exact h.2.2.1
theorem Instance.binding_node {i j : Instance} (h : j.binding = i.binding) : j.node = i.node := by
  simp only [Instance.binding, Prod.mk.injEq] at h
  exact h.2.1
theorem Instance.binding_inputs {i j : Instance} (h : j.binding = i.binding) : j.inputs = i.inputs := by
  simp only [Instance.binding, Prod.mk.injEq] at h
  exact h.2.2.2.2
theorem Instance.binding_trigger {i j : Instance} (h : j.binding = i.binding) : j.trigger = i.trigger := by
  simp only [Instance.binding, Prod.mk.injEq] at h
  exact h.2.2.2.1

/-- Tokens gained by a channel across writes come from the channel before or from the writes. -/
theorem view_tokens (next base : State) (ws : List Write) (baseDistinct : (base.channels.map (·.id)).Nodup)
    (view : next.placedView = (applyWrites ws base).placedView)
    (c : Channel) (member : c ∈ base.channels) (d : Channel) (memberD : d ∈ next.channels) (same : d.id = c.id) :
    ∀ t ∈ d.placed, t ∈ c.placed ∨ ∃ w ∈ ws, w.token = t := by
  have inView : d.core ∈ (applyWrites ws base).placedView := by
    rw [← view]; exact placedView_member memberD
  obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
  obtain ⟨f, memberF, idF, tokens⟩ := applyWrites_tokens ws _ e memberE
  have idE : e.id = d.id := by simpa using congrArg Channel.id coreE
  have sameF : f = c := by
    apply eq_of_mapped_nodup (·.id) base.channels baseDistinct f c memberF member
    show f.id = c.id
    rw [idF, idE, same]
  subst sameF
  have placedE : e.placed = d.placed := by simpa using congrArg Channel.placed coreE
  intro t ht
  rw [← placedE] at ht
  exact tokens t ht

/-- Writes of EOS only never change the items of a channel. -/
theorem applyWrites_eos_items (ws : List Write) (eosOnly : ∀ w ∈ ws, w.token = .eos) (st : State)
    (c : Channel) (member : c ∈ st.channels) :
    ∃ d ∈ (applyWrites ws st).channels, d.id = c.id ∧ d.items = c.items := by
  induction ws generalizing st c with
  | nil => exact ⟨c, member, rfl, rfl⟩
  | cons w ws ih =>
    simp only [applyWrites_cons]
    have one : ∃ d ∈ (applyWrite st w).channels, d.id = c.id ∧ d.items = c.items := by
      unfold applyWrite
      refine ⟨_, write_member st _ _ c member, ?_⟩
      have tok : w.token = .eos := eosOnly w (by simp)
      split
      · rw [tok]
        exact ⟨insertToken_id _ _, insertToken_eos_items _⟩
      · exact ⟨rfl, rfl⟩
    obtain ⟨d, memberD, idD, itemsD⟩ := one
    obtain ⟨e, memberE, idE, itemsE⟩ := ih (fun v hv => eosOnly v (by simp [hv])) _ d memberD
    exact ⟨e, memberE, idE.trans idD, itemsE.trans itemsD⟩

theorem eosWrites_eos (path : Path) (n : Node) : ∀ w ∈ eosWrites path n, w.token = .eos := by
  intro w hw
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hw
  rfl

/-- An accepted emit never closes a channel. -/
theorem emit_keeps_open (s next : State) (auth : Credentials) (port : PortName) (item : ItemId)
    (safe : Invariants s) (active : absorbed s (.emit auth port item) = false)
    (h : step s (.emit auth port item) = .ok next) (c : Channel) (member : c ∈ s.channels) (openC : c.closed = false)
    (d : Channel) (memberD : d ∈ next.channels) (same : d.id = c.id) : d.closed = false := by
  rcases step_ok_cases s _ next h with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
  · rw [active] at a; contradiction
  · have executed := prepareWith_body transitionOrIdle s next _ prepared
    simp only [transitionOrIdle] at executed
    obtain ⟨i, n, _, _, _, _, view, _⟩ := effect_emit s next auth port item executed
    have tokens := view_tokens next s [.out i.path i.node port (.item item)] safe.channelIds view c member d memberD same
    cases hd : d.closed with
    | false => rfl
    | true =>
      exfalso
      have eos : Token.eos ∈ d.placed := by simpa [Channel.closed] using hd
      rcases tokens .eos eos with old | ⟨w, hw, tw⟩
      · have : c.closed = true := by simpa [Channel.closed] using old
        rw [this] at openC; contradiction
      · simp only [List.mem_singleton] at hw
        subst hw
        cases tw

/-- An accepted skip adds no items to any channel. -/
theorem skip_no_items (s next : State) (path : Path) (node : NodeId)
    (safe : Invariants s) (safeNext : Invariants next) (active : absorbed s (.skip path node) = false)
    (h : step s (.skip path node) = .ok next) (c : Channel) (member : c ∈ s.channels)
    (d : Channel) (memberD : d ∈ next.channels) (same : d.id = c.id) : d.items = c.items := by
  rcases step_ok_cases s _ next h with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
  · rw [active] at a; contradiction
  · have executed := prepareWith_body transitionOrIdle s next _ prepared
    simp only [transitionOrIdle] at executed
    obtain ⟨n, _, _, _, _, _, _, _, view⟩ := effect_skip s next path node executed
    obtain ⟨e, memberE, idE, itemsE⟩ := applyWrites_eos_items (eosWrites path n) (eosWrites_eos path n) s c member
    have inView : e.core ∈ next.placedView := by rw [view]; exact placedView_member memberE
    obtain ⟨f, memberF, coreF⟩ := List.mem_map.mp inView
    have idF : f.id = c.id := by simpa using (congrArg Channel.id coreF).trans idE
    have sameF : f = d := unique_channel safeNext memberF memberD (idF.trans same.symm)
    subst sameF
    have itemsF : f.items = e.items := by simpa using congrArg Channel.items coreF
    exact itemsF.trans itemsE


theorem Channel.layout_fields {c d : Channel} (h : d.layout = c.layout) :
    d.id = c.id ∧ d.edge = c.edge ∧ d.path = c.path ∧ d.entry = c.entry ∧ d.exit = c.exit ∧ d.kind = c.kind := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Channel.id h
  · simpa using congrArg Channel.edge h
  · simpa using congrArg Channel.path h
  · simpa using congrArg Channel.entry h
  · simpa using congrArg Channel.exit h
  · simpa using congrArg Channel.kind h

theorem closed_of_drained {s : State} (finished : succeededDrained s = true) {c : Channel} (member : c ∈ s.channels) :
    c.closed = true := by
  simp only [succeededDrained, Bool.and_eq_true] at finished
  have := List.all_eq_true.mp finished.1.2 c member
  simp only [Bool.and_eq_true] at this
  exact this.1

theorem open_of_not_eos {c : Channel} (h : Token.eos ∉ c.placed) : c.closed = false := by
  cases hc : c.closed with
  | false => rfl
  | true => exact absurd (by simpa [Channel.closed] using hc) h

/-- No item reaches an output channel of a leaf before an instance of that node exists. -/
theorem items_need_instance (oracle : ScopedOracle) {s0 s : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops s)
    (safe0 : Invariants s0) (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n)
    (r : RetryPolicy) (cc : Nat) (leaf : n.kind = .leaf r cc)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (c : Channel) (memberC : c ∈ s.channels) (idC : c.id = c0.id)
    (noInstance : ∀ j ∈ s.instances, ¬ (j.path = c0.path ∧ j.node = c0.edge.src.node)) :
    c.items = [] := by
  cases hi : c.items with
  | nil => rfl
  | cons x xs =>
    exfalso
    have present : Token.item x ∈ c.placed := (Effects.item_mem c x).mp (by rw [hi]; simp)
    have absent : Token.item x ∉ c0.placed := by rw [empty0]; simp
    obtain ⟨pre, op, post, t, t', d, d', _, head, allowed, accepted, rest, safeT, active,
      memberD, idD, layoutD, absentD, memberD', idD', layoutD', presentD', _, target⟩ :=
      token_step run safe0 (.item x) c0 member0 absent entry0 c memberC idC present
    have nodeT := head.node c0.path c0.edge.src.node n found
    have safeT' := preserves_invariants t t' op safeT accepted
    have persist : ∀ i ∈ t.instances, i.path = c0.path → i.node = c0.edge.src.node → False := by
      intro i memberI pathI nodeI
      obtain ⟨j, memberJ, bindJ⟩ := (ConformingSteps.cons allowed accepted rest).retains_binding safeT i memberI
      exact noInstance j memberJ ⟨(Instance.binding_path bindJ).trans pathI, (Instance.binding_node bindJ).trans nodeI⟩
    rcases target_shape t t' op safeT active accepted _ _ target n nodeT with
        ⟨auth, _, _, _, _, eq, _⟩ | ⟨auth, _, _, _, eq, _⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
      | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨eq, _⟩
    · subst eq
      obtain ⟨i, foundI, pathI, nodeI⟩ := opTarget_instance rfl target
      exact persist i (instance?_mem foundI) pathI nodeI
    · subst eq
      obtain ⟨i, foundI, pathI, nodeI⟩ := opTarget_instance rfl target
      exact persist i (instance?_mem foundI) pathI nodeI
    · rw [leaf] at k; cases k
    · rw [leaf] at k; cases k
    · rw [leaf] at k; cases k
    · rw [leaf] at k; cases k
    · rw [leaf] at k; cases k
    · rw [leaf] at k; cases k
    · rw [leaf] at k; simp at k
    · rcases k with k | k <;> (rw [leaf] at k; cases k)
    · rw [leaf] at k; cases k
    · subst eq
      have same := skip_no_items t t' _ _ safeT safeT' active accepted d memberD d' memberD' (idD'.trans idD.symm)
      have xIn : x ∈ d'.items := (Effects.item_mem d' x).mpr presentD'
      rw [same] at xIn
      exact absentD ((Effects.item_mem d x).mp xIn)

/-- Final contents of one output channel of a leaf node, in a successful drained run. -/
theorem leaf_output_final (oracle : ScopedOracle) {s0 last : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops last)
    (safe0 : Invariants s0) (finished : succeededDrained last = true)
    (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n)
    (r : RetryPolicy) (cc : Nat) (leaf : n.kind = .leaf r cc) (names : (n.outputs.map (·.name)).Nodup)
    (q : Port) (port : q ∈ n.outputs) (portC : c0.edge.src.port = q.name) (kind0 : c0.kind = q.kind)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) :
    (∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .succeeded ∧
        (q.kind = .stream → cl.items.Perm (outputItems ((oracle c0.path).leaf c0.edge.src.node i.inputs) q.name)) ∧
        (q.kind = .plain → cl.items = outputItems ((oracle c0.path).leaf c0.edge.src.node i.inputs) q.name)) ∨
    (cl.items = [] ∧ (∃ i ∈ last.instances, i.path = c0.path ∧ i.node = c0.edge.src.node ∧ i.status = .cancelled) ∧
        ∃ d ∈ last.channels, d.path = c0.path ∧ d.exit = false ∧ d.edge.dst.node = c0.edge.src.node ∧
          d.closed = true ∧ d.items = []) := by
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
  -- the final channel keeps the history fixed at the closing step
  have finalPlaced : cl.placed = c'.placed := by
    obtain ⟨e, memberE, idE, placedE⟩ := rest.retains_closed_channel safeS' c' memberC' closedC'
    have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idC'.trans idL.symm))
    subst same
    exact placedE
  rcases target_shape s s' op safeS active accepted _ _ target n nodeS with
      ⟨auth, port', item, _, _, eq, _⟩ | ⟨auth, outputs, _, _, eq, _⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩
    | ⟨_, _, _, k⟩ | ⟨_, _, _, k⟩ | ⟨_, k⟩ | ⟨_, _, _, k⟩ | ⟨_, _, _, _, _, k⟩ | ⟨eq, _⟩
  · -- emit cannot close
    subst eq
    exfalso
    have openC := open_of_not_eos absentC
    have := emit_keeps_open s s' auth port' item safeS active accepted c memberC openC c' memberC' (idC'.trans idC.symm)
    rw [closedC'] at this; contradiction
  · -- complete: the oracle's outputs
    subst eq
    left
    rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [active] at a; contradiction
    · have executed := prepareWith_body transitionOrIdle s s' _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨i, n', foundI, hn, _, _, _, instances, _, _⟩ := effect_complete s s' auth outputs executed
      obtain ⟨i2, foundI2, pathI, nodeI⟩ := opTarget_instance rfl target
      rw [foundI] at foundI2
      cases foundI2
      have hnP : getNode s c0.path c0.edge.src.node = .ok n' := by rw [← pathI, ← nodeI]; exact hn
      have sameN := node?_of_getNode nodeS hnP
      subst n'
      have runC : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.complete auth outputs :: post) last :=
        .cons allowed accepted rest
      have outgoingC : c ∈ s.outgoing i.path i.node q.name := by
        refine List.mem_filter.mpr ⟨memberC, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
        refine ⟨⟨pathC.trans pathI.symm, entryC.trans entry0⟩, ?_⟩
        rw [edgeC]
        cases h : c0.edge.src with
        | mk node port'' =>
          rw [h] at nodeI portC
          simp only at nodeI portC
          rw [nodeI, portC]
      -- the instance that completed persists as succeeded with the same inputs
      let j : Instance := { i with status := .succeeded, lease := none }
      have memberJ : j ∈ s'.instances := by
        rw [instances]
        exact List.mem_map.mpr ⟨i, instance?_mem foundI, by simp [j]⟩
      obtain ⟨k, memberK, idK, statusK⟩ := rest.retains_status safeS' j memberJ (.inl rfl)
      obtain ⟨nodeK, pathK, _, inputsK⟩ := rest.input_snapshot safeS' j k memberJ memberK idK.symm
      have inputsK' : k.inputs = i.inputs := inputsK
      refine ⟨k, memberK, pathK.trans pathI, nodeK.trans nodeI, statusK, ?_, ?_⟩
      · intro stream
        obtain ⟨d, memberD, idD, _, permD⟩ :=
          complete_stream_output_final oracle runC safeS active i foundI n hn names q port stream c outgoingC
        have same : d = cl := unique_channel safeLast memberD memberL (idD.trans (idC.trans idL.symm))
        subst same
        rw [pathI, nodeI] at permD
        rw [inputsK']
        exact permD
      · intro plain
        have kindPlain : c.kind = .plain := kindC.trans (kind0.trans plain)
        obtain ⟨d, memberD, idD, _, itemsD⟩ :=
          complete_plain_output_final oracle runC safeS active i foundI n hn names q port plain c outgoingC kindPlain
        have same : d = cl := unique_channel safeLast memberD memberL (idD.trans (idC.trans idL.symm))
        subst same
        rw [pathI, nodeI] at itemsD
        rw [inputsK']
        exact itemsD
  · rw [leaf] at k; cases k
  · rw [leaf] at k; cases k
  · rw [leaf] at k; cases k
  · rw [leaf] at k; cases k
  · rw [leaf] at k; cases k
  · rw [leaf] at k; cases k
  · rw [leaf] at k; simp at k
  · rcases k with k | k <;> (rw [leaf] at k; cases k)
  · rw [leaf] at k; cases k
  · -- skip: never started, outputs empty
    subst eq
    right
    rcases step_ok_cases s _ s' accepted with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [active] at a; contradiction
    · have executed := prepareWith_body transitionOrIdle s s' _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨n', hn, cond, _, noInstance, instances, _, _, _⟩ := effect_skip s s' _ _ executed
      have sameN := node?_of_getNode nodeS hn
      subst n'
      have emptyC : c.items = [] :=
        items_need_instance oracle head safe0 n c0 found r cc leaf member0 empty0 entry0 c memberC idC noInstance
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
      · rw [leaf] at cond
        simp only [Bool.and_eq_true] at cond
        obtain ⟨d, memberD, props⟩ := List.any_eq_true.mp cond.2
        simp only [Bool.and_eq_true, List.isEmpty_iff] at props
        have inChannels : d ∈ s.channels := (List.mem_filter.mp memberD).1
        have fields := (List.mem_filter.mp memberD).2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at fields
        have runS : ConformingSteps (fun s op => oracleConforms oracle s op = true) s (.skip c0.path c0.edge.src.node :: post) last :=
          .cons allowed accepted rest
        obtain ⟨e, memberE, idE, placedE⟩ := runS.retains_closed_channel safeS d inChannels props.1
        obtain ⟨e', memberE', idE', layoutE', _⟩ := run_image runS safeS d inChannels
        have same : e' = e := unique_channel safeLast memberE' memberE (idE'.trans idE.symm)
        subst same
        obtain ⟨_, edgeE, pathE, _, exitE, _⟩ := Channel.layout_fields layoutE'
        refine ⟨e', memberE, pathE.trans fields.1.1, exitE.trans fields.1.2, ?_, ?_, ?_⟩
        · rw [edgeE]; exact fields.2
        · simpa [Channel.closed, placedE] using props.1
        · simp only [Channel.items, placedE]; exact props.2

end Suimon
