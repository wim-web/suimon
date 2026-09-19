import Suimon.Theorems.Locality

/-! Every channel that ends closed was closed by exactly one step, and that step
    targets the channel's producing node. The closed history is final. -/

namespace Suimon
open Effects

@[simp] theorem Channel.layout_id (c : Channel) : c.layout.id = c.id := rfl
@[simp] theorem Channel.layout_edge (c : Channel) : c.layout.edge = c.edge := rfl
@[simp] theorem Channel.layout_path (c : Channel) : c.layout.path = c.path := rfl
@[simp] theorem Channel.layout_entry (c : Channel) : c.layout.entry = c.entry := rfl
@[simp] theorem Channel.layout_exit (c : Channel) : c.layout.exit = c.exit := rfl
@[simp] theorem Channel.layout_kind (c : Channel) : c.layout.kind = c.kind := rfl
theorem Channel.core_layout (c : Channel) : c.core.layout = c.layout := rfl

theorem insertToken_prefix (c : Channel) (t : Token) : c.placed.IsPrefix (insertToken c t).placed := by
  unfold insertToken
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem applyWrites_image (ws : List Write) (st : State) (c : Channel) (member : c ∈ st.channels) :
    ∃ d ∈ (applyWrites ws st).channels, d.id = c.id ∧ d.layout = c.layout ∧ c.placed.IsPrefix d.placed := by
  induction ws generalizing st c with
  | nil => exact ⟨c, member, rfl, rfl, List.prefix_refl _⟩
  | cons w ws ih =>
    simp only [applyWrites_cons]
    have one : ∃ d ∈ (applyWrite st w).channels, d.id = c.id ∧ d.layout = c.layout ∧ c.placed.IsPrefix d.placed := by
      unfold applyWrite
      refine ⟨_, write_member st _ _ c member, ?_⟩
      split
      · exact ⟨insertToken_id _ _, insertToken_layout _ _, insertToken_prefix _ _⟩
      · exact ⟨rfl, rfl, List.prefix_refl _⟩
    obtain ⟨d, memberD, idD, layoutD, prefixD⟩ := one
    obtain ⟨e, memberE, idE, layoutE, prefixE⟩ := ih _ d memberD
    exact ⟨e, memberE, idE.trans idD, layoutE.trans layoutD, prefixD.trans prefixE⟩

theorem Invariants.channelIds {s : State} (safe : Invariants s) : (s.channels.map (·.id)).Nodup := by
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  exact unique_nodup _ safe.1.1.1.1.1.1.2

/-- The image of a channel after an accepted step: same identity and layout, extended history. -/
theorem step_image (s next : State) (op : Op) (c : Channel) (member : c ∈ s.channels)
    (safe : Invariants s) (h : step s op = .ok next) :
    ∃ d ∈ next.channels, d.id = c.id ∧ d.layout = c.layout ∧ c.placed.IsPrefix d.placed := by
  obtain ⟨added, ws, view, _⟩ := step_view s next op safe.channelIds h
  have memberBase : c ∈ ({ s with channels := s.channels ++ added } : State).channels :=
    List.mem_append_left _ member
  obtain ⟨d, memberD, idD, layoutD, prefixD⟩ := applyWrites_image ws _ c memberBase
  have inView : d.core ∈ next.placedView := by
    rw [view]
    exact placedView_member memberD
  obtain ⟨e, memberE, eq⟩ := List.mem_map.mp inView
  refine ⟨e, memberE, ?_, ?_, ?_⟩
  · have := congrArg Channel.id eq
    simpa using this.trans idD
  · have := congrArg Channel.layout eq
    simpa [Channel.core_layout] using this.trans layoutD
  · have := congrArg Channel.placed eq
    simp only [Channel.core_placed] at this
    rw [this]
    exact prefixD

theorem unique_channel {s : State} (safe : Invariants s) {c d : Channel}
    (hc : c ∈ s.channels) (hd : d ∈ s.channels) (same : c.id = d.id) : c = d :=
  eq_of_mapped_nodup (·.id) s.channels safe.channelIds c d hc hd same

/-- Decomposition of a run at the step that closes a channel. -/
theorem closing_step {allows : State → Op → Prop} {s0 last : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops last) (safe0 : Invariants s0)
    (c0 : Channel) (member0 : c0 ∈ s0.channels) (open0 : c0.closed = false) (nonEntry : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) (closedL : cl.closed = true) :
    ∃ pre op post s s' c c', ops = pre ++ op :: post ∧
      ConformingSteps allows s0 pre s ∧ allows s op ∧ step s op = .ok s' ∧
      ConformingSteps allows s' post last ∧ Invariants s ∧
      c ∈ s.channels ∧ c.id = c0.id ∧ c.layout = c0.layout ∧ c.closed = false ∧
      c' ∈ s'.channels ∧ c'.id = c0.id ∧ c'.layout = c0.layout ∧ c'.closed = true ∧ c'.placed = cl.placed ∧
      opTarget s op = some (c0.path, c0.edge.src.node) := by
  induction run generalizing c0 with
  | nil =>
    have same := unique_channel safe0 memberL member0 idL
    subst same
    rw [open0] at closedL
    contradiction
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid : Invariants middle := preserves_invariants s middle op safe0 accepted
    obtain ⟨d, memberD, idD, layoutD, prefixD⟩ := step_image s middle op c0 member0 safe0 accepted
    have entryD : d.entry = false := by
      have := congrArg Channel.entry layoutD
      simpa using this.trans nonEntry
    cases closedD : d.closed with
    | true =>
      -- this step closed the channel
      have safeLast : Invariants final := tail.invariants safeMid
      obtain ⟨e, memberE, idE, placedE⟩ := tail.retains_closed_channel safeMid d memberD closedD
      have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idD.trans idL.symm))
      subst same
      refine ⟨[], op, ops, s, middle, c0, d, rfl, .nil s, allowed, accepted, tail, safe0,
        member0, rfl, rfl, open0, memberD, idD, layoutD, closedD, placedE.symm, ?_⟩
      apply Classical.byContradiction
      intro miss
      obtain ⟨f, memberF, coreF⟩ := step_untouched s middle op c0 member0 nonEntry safe0 safeMid accepted miss
      have idF : f.id = c0.id := by simpa using congrArg Channel.id coreF
      have sameF : f = d := unique_channel safeMid memberF memberD (idF.trans idD.symm)
      subst sameF
      have closedF : f.closed = c0.closed := by simpa using congrArg Channel.closed coreF
      rw [closedD, open0] at closedF
      contradiction
    | false =>
      obtain ⟨pre, op', post, t, t', c, c', split, head, allowed', accepted', rest, safeT,
        memberC, idC, layoutC, openC, memberC', idC', layoutC', closedC', placedC', target⟩ :=
        ih safeMid d memberD closedD entryD memberL (idL.trans idD.symm)
      refine ⟨op :: pre, op', post, t, t', c, c', by simp [split], .cons allowed accepted head, allowed', accepted',
        rest, safeT, memberC, idC.trans idD, layoutC.trans layoutD, openC, memberC', idC'.trans idD,
        layoutC'.trans layoutD, closedC', placedC', ?_⟩
      rw [target]
      have pathD : d.path = c0.path := by simpa using congrArg Channel.path layoutD
      have edgeD : d.edge = c0.edge := by simpa using congrArg Channel.edge layoutD
      rw [pathD, edgeD]


/-- Along a run, every channel keeps its identity and layout and only extends its history. -/
theorem run_image {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (c : Channel) (member : c ∈ s.channels) :
    ∃ d ∈ last.channels, d.id = c.id ∧ d.layout = c.layout ∧ c.placed.IsPrefix d.placed := by
  induction run generalizing c with
  | nil => exact ⟨c, member, rfl, rfl, List.prefix_refl _⟩
  | @cons s middle final op ops allowed accepted tail ih =>
    obtain ⟨d, memberD, idD, layoutD, prefixD⟩ := step_image s middle op c member safe accepted
    obtain ⟨e, memberE, idE, layoutE, prefixE⟩ := ih (preserves_invariants s middle op safe accepted) d memberD
    exact ⟨e, memberE, idE.trans idD, layoutE.trans layoutD, prefixD.trans prefixE⟩

/-- Decomposition of a run at the step that first places token `tok` on a channel. -/
theorem token_step {allows : State → Op → Prop} {s0 last : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops last) (safe0 : Invariants s0) (tok : Token)
    (c0 : Channel) (member0 : c0 ∈ s0.channels) (absent0 : tok ∉ c0.placed) (nonEntry : c0.entry = false)
    (cl : Channel) (memberL : cl ∈ last.channels) (idL : cl.id = c0.id) (present : tok ∈ cl.placed) :
    ∃ pre op post s s' c c', ops = pre ++ op :: post ∧
      ConformingSteps allows s0 pre s ∧ allows s op ∧ step s op = .ok s' ∧
      ConformingSteps allows s' post last ∧ Invariants s ∧ absorbed s op = false ∧
      c ∈ s.channels ∧ c.id = c0.id ∧ c.layout = c0.layout ∧ tok ∉ c.placed ∧
      c' ∈ s'.channels ∧ c'.id = c0.id ∧ c'.layout = c0.layout ∧ tok ∈ c'.placed ∧ c'.placed.IsPrefix cl.placed ∧
      opTarget s op = some (c0.path, c0.edge.src.node) := by
  induction run generalizing c0 with
  | nil =>
    have same := unique_channel safe0 memberL member0 idL
    subst same
    exact absurd present absent0
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid : Invariants middle := preserves_invariants s middle op safe0 accepted
    obtain ⟨d, memberD, idD, layoutD, prefixD⟩ := step_image s middle op c0 member0 safe0 accepted
    have entryD : d.entry = false := by
      have := congrArg Channel.entry layoutD
      simpa using this.trans nonEntry
    by_cases presentD : tok ∈ d.placed
    · have safeLast : Invariants final := tail.invariants safeMid
      obtain ⟨e, memberE, idE, layoutE, prefixE⟩ := run_image tail safeMid d memberD
      have same : e = cl := unique_channel safeLast memberE memberL (idE.trans (idD.trans idL.symm))
      subst same
      have active : absorbed s op = false := by
        cases h : absorbed s op with
        | false => rfl
        | true =>
          exfalso
          rcases step_ok_cases s op middle accepted with ⟨_, same⟩ | ⟨notAbs, _, _, _, _⟩
          · subst same
            have := unique_channel safe0 memberD member0 idD
            subst this
            exact absent0 presentD
          · rw [h] at notAbs; contradiction
      refine ⟨[], op, ops, s, middle, c0, d, rfl, .nil s, allowed, accepted, tail, safe0, active,
        member0, rfl, rfl, absent0, memberD, idD, layoutD, presentD, prefixE, ?_⟩
      apply Classical.byContradiction
      intro miss
      obtain ⟨f, memberF, coreF⟩ := step_untouched s middle op c0 member0 nonEntry safe0 safeMid accepted miss
      have idF : f.id = c0.id := by simpa using congrArg Channel.id coreF
      have sameF : f = d := unique_channel safeMid memberF memberD (idF.trans idD.symm)
      subst sameF
      have placedF : f.placed = c0.placed := by simpa using congrArg Channel.placed coreF
      rw [placedF] at presentD
      exact absent0 presentD
    · obtain ⟨pre, op', post, t, t', c, c', split, head, allowed', accepted', rest, safeT, active',
        memberC, idC, layoutC, absentC, memberC', idC', layoutC', presentC', prefixC', target⟩ :=
        ih safeMid d memberD presentD entryD memberL (idL.trans idD.symm)
      refine ⟨op :: pre, op', post, t, t', c, c', by simp [split], .cons allowed accepted head, allowed', accepted',
        rest, safeT, active', memberC, idC.trans idD, layoutC.trans layoutD, absentC, memberC', idC'.trans idD,
        layoutC'.trans layoutD, presentC', prefixC', ?_⟩
      rw [target]
      have pathD : d.path = c0.path := by simpa using congrArg Channel.path layoutD
      have edgeD : d.edge = c0.edge := by simpa using congrArg Channel.edge layoutD
      rw [pathD, edgeD]

/-- A targeted write leaves its token on every channel of the group. -/
theorem applyWrites_token (ws : List Write) (st : State) (c : Channel) (member : c ∈ st.channels)
    (nonEntry : c.entry = false) (distinct : (st.channels.map (·.id)).Nodup) (t : Token)
    (hit : Write.out c.path c.edge.src.node c.edge.src.port t ∈ ws) :
    ∃ d ∈ (applyWrites ws st).channels, d.id = c.id ∧ d.layout = c.layout ∧ t ∈ d.placed := by
  obtain ⟨pre, post, split⟩ := List.append_of_mem hit
  subst split
  rw [applyWrites_append, applyWrites_cons]
  obtain ⟨d, memberD, idD, layoutD, _⟩ := applyWrites_image pre st c member
  have distinctPre : ((applyWrites pre st).channels.map (·.id)).Nodup := by rw [applyWrites_ids]; exact distinct
  have pathD : d.path = c.path := by simpa using congrArg Channel.path layoutD
  have edgeD : d.edge = c.edge := by simpa using congrArg Channel.edge layoutD
  have entryD : d.entry = false := by simpa using (congrArg Channel.entry layoutD).trans nonEntry
  have selected : ((Write.out c.path c.edge.src.node c.edge.src.port t).ids (applyWrites pre st)).contains d.id = true := by
    simp only [Write.ids]
    exact (outgoing_ids_of_follows d (applyWrites pre st) c.path c.edge.src.node c.edge.src.port distinctPre
      (Follows.refl d _ memberD)).mpr ⟨pathD, entryD, by rw [edgeD]⟩
  have written : insertToken d t ∈ (applyWrite (applyWrites pre st) (.out c.path c.edge.src.node c.edge.src.port t)).channels := by
    unfold applyWrite
    have selMem : d.id ∈ (Write.out c.path c.edge.src.node c.edge.src.port t).ids (applyWrites pre st) :=
      List.contains_iff_mem.mp selected
    have := write_member (applyWrites pre st) ((Write.out c.path c.edge.src.node c.edge.src.port t).ids (applyWrites pre st)) t d memberD
    simpa [selMem, Write.token] using this
  obtain ⟨e, memberE, idE, layoutE, prefixE⟩ := applyWrites_image post _ _ written
  refine ⟨e, memberE, ?_, ?_, ?_⟩
  · rw [idE, insertToken_id, idD]
  · rw [layoutE, insertToken_layout, layoutD]
  · have : t ∈ (insertToken d t).placed := (insertToken_mem d t t).mpr (.inr rfl)
    exact prefixE.subset this

end Suimon
