import Suimon.Theorems.FrameTree

namespace Suimon
open Semantics Effects

theorem applyWrites_selected_token (ws : List Write) (st : State) (c : Channel) (member : c ∈ st.channels)
    (w : Write) (hit : w ∈ ws) (selected : (w.ids st).contains c.id = true) :
    ∃ d ∈ (applyWrites ws st).channels, d.id = c.id ∧ w.token ∈ d.placed := by
  obtain ⟨pre, post, split⟩ := List.append_of_mem hit
  subst ws
  rw [applyWrites_append, applyWrites_cons]
  obtain ⟨d, memberD, idD, _, _⟩ := applyWrites_image pre st c member
  have selectedD : (w.ids (applyWrites pre st)).contains d.id = true := by
    rw [idD, Write.ids_layout w (applyWrites pre st) st (applyWrites_channelLayout pre st)]
    exact selected
  have written : insertToken d w.token ∈ (applyWrite (applyWrites pre st) w).channels := by
    have value := write_member (applyWrites pre st) (w.ids (applyWrites pre st)) w.token d memberD
    simpa only [selectedD, ↓reduceIte, applyWrite] using value
  obtain ⟨e, memberE, idE, _, prefixE⟩ := applyWrites_image post _ _ written
  exact ⟨e, memberE, by rw [idE, insertToken_id, idD],
    prefixE.subset ((insertToken_mem d w.token w.token).mpr (.inr rfl))⟩

/-- Exact membership across a batch of writes, including entry seeding. --/
theorem writes_on_channel (base next : State) (ws : List Write)
    (distinct : (base.channels.map (·.id)).Nodup) (safeNext : Invariants next)
    (view : next.placedView = (applyWrites ws base).placedView)
    (before : Channel) (memberBefore : before ∈ base.channels)
    (after : Channel) (memberAfter : after ∈ next.channels) (sameId : after.id = before.id) (token : Token) :
    token ∈ after.placed ↔ token ∈ before.placed ∨
      ∃ w ∈ ws, w.token = token ∧ (w.ids base).contains before.id = true := by
  constructor
  · intro present
    have inView : after.core ∈ (applyWrites ws base).placedView := by rw [← view]; exact placedView_member memberAfter
    obtain ⟨image, memberImage, sameCore⟩ := List.mem_map.mp inView
    have imageId : image.id = after.id := by simpa only [Channel.core_id] using congrArg Channel.id sameCore
    have imageTokens : image.placed = after.placed := by simpa only [Channel.core_placed] using congrArg Channel.placed sameCore
    obtain ⟨origin, memberOrigin, idOrigin, tokens⟩ := applyWrites_tokens_targeted ws base image memberImage
    have same := eq_of_mapped_nodup Channel.id base.channels distinct origin before memberOrigin memberBefore
      (idOrigin.trans (imageId.trans sameId))
    subst origin
    exact tokens token (imageTokens ▸ present)
  · intro source
    have image : ∃ image ∈ (applyWrites ws base).channels, image.id = before.id ∧ token ∈ image.placed := by
      rcases source with old | ⟨w, memberW, tokenW, hit⟩
      · obtain ⟨image, memberImage, idImage, _, past⟩ := applyWrites_image ws base before memberBefore
        exact ⟨image, memberImage, idImage, past.subset old⟩
      · obtain ⟨image, memberImage, idImage, presentImage⟩ := applyWrites_selected_token ws base before memberBefore w memberW hit
        exact ⟨image, memberImage, idImage, tokenW ▸ presentImage⟩
    obtain ⟨image, memberImage, idImage, presentImage⟩ := image
    have inView : image.core ∈ next.placedView := by rw [view]; exact placedView_member memberImage
    obtain ⟨actual, memberActual, sameCore⟩ := List.mem_map.mp inView
    have actualId : actual.id = image.id := by simpa only [Channel.core_id] using congrArg Channel.id sameCore
    have actualTokens : actual.placed = image.placed := by simpa only [Channel.core_placed] using congrArg Channel.placed sameCore
    have same := unique_channel safeNext memberActual memberAfter (actualId.trans (idImage.trans sameId.symm))
    subst actual
    exact actualTokens ▸ presentImage

theorem seed_ids_on_entry (s : State) (distinct : (s.channels.map (·.id)).Nodup) (c : Channel)
    (member : c ∈ s.channels) (P : Path) (pathC : c.path = P) (entryC : c.entry = true)
    (exitC : c.exit = false) (ref : PortRef) (token : Token) :
    ((Write.seed P ref token).ids s).contains c.id = true ↔ ref = c.edge.dst := by
  simp only [Write.ids, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨d, memberD, idD⟩
    have inState : d ∈ s.channels := (List.mem_filter.mp (List.mem_filter.mp memberD).1).1
    have same := eq_of_mapped_nodup Channel.id s.channels distinct d c inState member idD
    subst d
    have fields := (List.mem_filter.mp memberD).2
    have dst : c.edge.dst = ref := by simpa using (Bool.and_eq_true_iff.mp fields).2
    exact dst.symm
  · intro refEq
    subst ref
    exact ⟨c, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨member, by simp [pathC, exitC]⟩,
      by simp [entryC]⟩, rfl⟩

theorem root_ids_on_entry (s : State) (distinct : (s.channels.map (·.id)).Nodup) (c : Channel)
    (member : c ∈ s.channels) (pathC : c.path = []) (entryC : c.entry = true)
    (ref : PortRef) (token : Token) :
    ((Write.root ref token).ids s).contains c.id = true ↔ ref = c.edge.dst := by
  simp only [Write.ids, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨d, memberD, idD⟩
    have same := eq_of_mapped_nodup Channel.id s.channels distinct d c (List.mem_filter.mp memberD).1 member idD
    subst d
    have fields := (List.mem_filter.mp memberD).2
    have dst : c.edge.dst = ref := by simpa using (Bool.and_eq_true_iff.mp fields).2
    exact dst.symm
  · intro refEq
    subst ref
    exact ⟨c, List.mem_filter.mpr ⟨member, by simp [pathC, entryC]⟩, rfl⟩

theorem rootWrites_hits (s : State) (distinct : (s.channels.map (·.id)).Nodup) (c : Channel)
    (member : c ∈ s.channels) (pathC : c.path = []) (entryC : c.entry = true)
    (inputs : List Input) (names : (inputs.map (·.entry)).Nodup) (input : Input)
    (memberInput : input ∈ inputs) (ref : input.entry = c.edge.dst) (token : Token) :
    (∃ w ∈ rootWrites inputs, w.token = token ∧ (w.ids s).contains c.id = true) ↔
    token = .eos ∨ ∃ item ∈ input.items, token = .item item := by
  constructor
  · rintro ⟨w, memberW, tokenW, hit⟩
    obtain ⟨other, memberOther, writes⟩ := List.mem_flatMap.mp memberW
    rcases List.mem_append.mp writes with items | eos
    · obtain ⟨item, memberItem, eq⟩ := List.mem_map.mp items
      subst w
      have refOther := (root_ids_on_entry s distinct c member pathC entryC other.entry _).mp hit
      have same := eq_of_mapped_nodup Input.entry inputs names other input memberOther memberInput (refOther.trans ref.symm)
      subst other
      exact .inr ⟨item, memberItem, tokenW.symm⟩
    · have eq : w = .root other.entry .eos := by simpa using eos
      subst w
      exact .inl tokenW.symm
  · rintro (eos | ⟨item, memberItem, eq⟩)
    · refine ⟨.root input.entry .eos, ?_, eos.symm, ?_⟩
      · exact List.mem_flatMap.mpr ⟨input, memberInput, List.mem_append_right _ (by simp)⟩
      · exact (root_ids_on_entry s distinct c member pathC entryC input.entry _).mpr ref
    · refine ⟨.root input.entry (.item item), ?_, eq.symm, ?_⟩
      · exact List.mem_flatMap.mpr ⟨input, memberInput, List.mem_append_left _ (List.mem_map.mpr ⟨item, memberItem, rfl⟩)⟩
      · exact (root_ids_on_entry s distinct c member pathC entryC input.entry _).mpr ref

theorem bodyInputs_entries (g : Graph) (items : List ItemId) (arity : items.length = g.entries.length) :
    (bodyInputs g items).map Input.entry = g.entries := by
  simp only [bodyInputs, List.map_map]
  exact List.map_fst_zip (by omega)

theorem seedWrites_hits (s : State) (distinct : (s.channels.map (·.id)).Nodup) (c : Channel)
    (member : c ∈ s.channels) (P : Path) (pathC : c.path = P) (entryC : c.entry = true) (exitC : c.exit = false)
    (g : Graph) (items : List ItemId) (names : ((bodyInputs g items).map (·.entry)).Nodup) (input : Input)
    (memberInput : input ∈ bodyInputs g items) (ref : input.entry = c.edge.dst) (token : Token) :
    (∃ w ∈ seedWrites P g.entries items, w.token = token ∧ (w.ids s).contains c.id = true) ↔
    token = .eos ∨ ∃ item ∈ input.items, token = .item item := by
  constructor
  · rintro ⟨w, memberW, tokenW, hit⟩
    obtain ⟨⟨p, item⟩, pairMember, either⟩ := List.mem_flatMap.mp memberW
    simp only [List.mem_cons, List.not_mem_nil, or_false] at either
    rcases either with eq | eq
    · subst w
      have refOther := (seed_ids_on_entry s distinct c member P pathC entryC exitC p _).mp hit
      have other : ({entry := p, items := [item]} : Input) ∈ bodyInputs g items := List.mem_map.mpr ⟨(p, item), pairMember, rfl⟩
      have same := eq_of_mapped_nodup Input.entry _ names _ input other memberInput (refOther.trans ref.symm)
      refine .inr ⟨item, ?_, tokenW.symm⟩
      rw [← same]
      simp
    · subst w
      exact .inl tokenW.symm
  · obtain ⟨⟨p, item⟩, pairMember, inputEq⟩ := List.mem_map.mp memberInput
    subst input
    intro condition
    rcases condition with eos | ⟨value, memberValue, tokenEq⟩
    · refine ⟨.seed P p .eos, ?_, eos.symm, ?_⟩
      · exact List.mem_flatMap.mpr ⟨(p, item), pairMember, by simp⟩
      · exact (seed_ids_on_entry s distinct c member P pathC entryC exitC p _).mpr ref
    · have same : value = item := by simpa using memberValue
      subst value
      refine ⟨.seed P p (.item item), ?_, tokenEq.symm, ?_⟩
      · exact List.mem_flatMap.mpr ⟨(p, item), pairMember, by simp⟩
      · exact (seed_ids_on_entry s distinct c member P pathC entryC exitC p _).mpr ref

end Suimon
