import Suimon.Theorems.CompletedRun

namespace Suimon

theorem Frame.channel_path (f : Frame) (c : Channel) (member : c ∈ f.channels) : c.path = f.path := by
  simp only [Frame.channels, List.mem_append] at member
  rcases member with (edge | entry) | boundary
  · obtain ⟨pair, _, same⟩ := List.mem_map.mp edge
    subst c
    rfl
  · obtain ⟨pair, _, same⟩ := List.mem_map.mp entry
    subst c
    rfl
  · obtain ⟨pair, _, same⟩ := List.mem_map.mp boundary
    subst c
    rfl

theorem Frame.channel_output (f : Frame) (body : Bool) (valid : f.graph.validate body = .ok ())
    (c : Channel) (member : c ∈ f.channels) (notEntry : c.entry = false) :
    ∃ p, f.graph.output? c.edge.src = some p ∧ c.kind = p.kind := by
  simp only [Frame.channels, List.mem_append] at member
  rcases member with (edge | entry) | boundary
  · obtain ⟨⟨e, index⟩, edgeMember, same⟩ := List.mem_map.mp edge
    subst c
    have checked := f.graph.validate_edges body valid e (List.fst_mem_of_mem_zipIdx edgeMember)
    cases found : f.graph.output? e.src with
    | none => simp [Graph.validateEdge, found] at checked
    | some p => exact ⟨p, rfl, by simp [found]⟩
  · obtain ⟨⟨ref, index⟩, _, same⟩ := List.mem_map.mp entry
    subst c
    contradiction
  · obtain ⟨⟨ref, index⟩, exitMember, same⟩ := List.mem_map.mp boundary
    subst c
    have checked := f.graph.validate_exits body valid ref (List.fst_mem_of_mem_zipIdx exitMember)
    cases found : f.graph.output? ref with
    | none => simp [Graph.validateExit, found] at checked
    | some p => exact ⟨p, rfl, by simp [found]⟩

theorem Frame.channel_input (f : Frame) (body : Bool) (valid : f.graph.validate body = .ok ())
    (c : Channel) (member : c ∈ f.channels) (notExit : c.exit = false) :
    ∃ p, f.graph.input? c.edge.dst = some p ∧ c.kind = p.kind := by
  simp only [Frame.channels, List.mem_append] at member
  rcases member with (edge | entry) | boundary
  · obtain ⟨⟨e, index⟩, edgeMember, same⟩ := List.mem_map.mp edge
    subst c
    have checked := f.graph.validate_edges body valid e (List.fst_mem_of_mem_zipIdx edgeMember)
    cases output : f.graph.output? e.src with
    | none => simp [Graph.validateEdge, output] at checked
    | some p =>
      cases input : f.graph.input? e.dst with
      | none => simp [Graph.validateEdge, output, input] at checked
      | some q =>
        have same : p.kind = q.kind := by
          by_cases kinds : p.kind == q.kind
          · simpa using kinds
          · simp [Graph.validateEdge, output, input, kinds, bind, Except.bind] at checked
        exact ⟨q, rfl, by simpa [output] using same⟩
  · obtain ⟨⟨ref, index⟩, entryMember, same⟩ := List.mem_map.mp entry
    subst c
    have checked : f.graph.validateEntry ref = .ok () := by
      have all : ∃ values, f.graph.entries.mapM f.graph.validateEntry = .ok values := by
        rw [Graph.validate] at valid
        repeat' (first
          | (exact ⟨_, by assumption⟩)
          | split at valid
          | (simp only [bind, Except.bind, pure, Except.pure] at valid)
          | contradiction)
      obtain ⟨values, accepted⟩ := all
      obtain ⟨value, correct⟩ := mapM_ok_members f.graph.validateEntry _ values accepted ref
        (List.fst_mem_of_mem_zipIdx entryMember)
      cases value
      exact correct
    cases found : f.graph.input? ref with
    | none => simp [Graph.validateEntry, found] at checked
    | some p => exact ⟨p, rfl, by simp [found]⟩
  · obtain ⟨⟨ref, index⟩, _, same⟩ := List.mem_map.mp boundary
    subst c
    contradiction

theorem LayoutOK.channel_frame {s : State} (balanced : LayoutOK s) (c : Channel) (member : c ∈ s.channels) :
    ∃ f ∈ s.frames, c.layout ∈ f.channels ∧ c.path = f.path := by
  have mapped : c.layout ∈ s.channelLayout := List.mem_map.mpr ⟨c, member, rfl⟩
  rw [balanced] at mapped
  obtain ⟨f, memberF, channel⟩ := List.mem_flatMap.mp mapped
  exact ⟨f, memberF, channel, f.channel_path c.layout channel⟩

theorem LayoutOK.channel_in_scope {s : State} (balanced : LayoutOK s)
    (distinct : (s.frames.map Frame.path).Nodup) (c : Channel) (f : Frame)
    (member : c ∈ s.channels) (found : s.frame? c.path = some f) : c.layout ∈ f.channels := by
  obtain ⟨origin, originMember, channel, path⟩ := balanced.channel_frame c member
  have frameMember := List.mem_of_find?_eq_some found
  have framePath : f.path = c.path := by simpa using List.find?_some found
  have same : origin = f := eq_of_mapped_nodup Frame.path s.frames distinct origin f originMember frameMember
    (path.symm.trans framePath.symm)
  simpa [same] using channel

theorem CompletedState.channel_output {graph : Graph} {s : State} (completed : CompletedState graph s)
    (c : Channel) (member : c ∈ s.channels) (notEntry : c.entry = false) :
    ∃ f ∈ s.frames, f.path = c.path ∧ ∃ p, f.graph.output? c.edge.src = some p ∧ c.kind = p.kind := by
  obtain ⟨f, memberF, channel, path⟩ := completed.layout.channel_frame c member
  have valid := (completed.frames f.definitionView (List.mem_map.mpr ⟨f, memberF, rfl⟩)).1
  obtain ⟨p, found, kind⟩ := f.channel_output f.owner.isSome valid c.layout channel notEntry
  exact ⟨f, memberF, path.symm, p, found, kind⟩

end Suimon
