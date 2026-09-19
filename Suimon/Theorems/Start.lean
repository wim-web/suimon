import Suimon.Theorems.Seeding
import Suimon.Theorems.FrameOwners

namespace Suimon
open Semantics Effects

theorem subset_reverse_of_length {α : Type} {left right : List α} (distinct : left.Nodup)
    (included : left ⊆ right) (lengths : left.length = right.length) : right ⊆ left := by
  classical
  intro x member
  by_cases missing : x ∈ left
  · exact missing
  apply False.elim
  have more : (x :: left).Nodup := List.nodup_cons.mpr ⟨missing, distinct⟩
  have bound := more.length_le_of_subset (show x :: left ⊆ right from fun y hy => by
    rcases List.mem_cons.mp hy with rfl | old
    · exact member
    · exact included old)
  simp only [List.length_cons] at bound
  omega

theorem find_input {inputs : List Input} (distinct : (inputs.map (·.entry)).Nodup) (input : Input)
    (member : input ∈ inputs) : inputs.find? (·.entry == input.entry) = some input := by
  have exists_ : (inputs.find? (·.entry == input.entry)).isSome := List.find?_isSome.mpr ⟨input, member, by simp⟩
  cases found : inputs.find? (·.entry == input.entry) with
  | none => rw [found] at exists_; contradiction
  | some other =>
    have key : other.entry = input.entry := by simpa using List.find?_some found
    have same := eq_of_mapped_nodup Input.entry inputs distinct other input (List.mem_of_find?_eq_some found) member key
    subst other
    rfl

theorem Scope.entry_ref {s : State} {P : Path} {g : Graph} (sc : Scope s P g) (c : Channel)
    (member : c ∈ s.channels) (path : c.path = P) (entry : c.entry = true) : c.edge.dst ∈ g.entries := by
  rcases template_cases P g c.layout (sc.template c member path) with ⟨e, i, indexed, same⟩ |
    ⟨ref, i, indexed, same⟩ | ⟨ref, i, indexed, same⟩
  · have entryEq := congrArg Channel.entry same
    simp [entry] at entryEq
  · have dstEq : c.edge.dst = ref := by simpa using congrArg (fun ch => ch.edge.dst) same
    rw [dstEq]
    exact List.fst_mem_of_mem_zipIdx indexed
  · have entryEq := congrArg Channel.entry same
    simp [entry] at entryEq

theorem view_untouched {base next : State} (safeNext : Invariants next)
    (distinct : (base.channels.map (·.id)).Nodup) (ws : List Write)
    (view : next.placedView = (applyWrites ws base).placedView) (noOutput : OutTarget ws none)
    (before : Channel) (memberBefore : before ∈ base.channels) (entry : before.entry = false)
    (after : Channel) (memberAfter : after ∈ next.channels) (idAfter : after.id = before.id) : after.placed = before.placed := by
  have same := applyWrites_untouched ws base before memberBefore distinct entry (by
    intro w memberW token equal
    have impossible := noOutput w memberW _ _ _ token equal
    cases impossible)
  have inView : before.core ∈ next.placedView := by rw [view]; exact placedView_member same
  obtain ⟨c, memberC, coreC⟩ := List.mem_map.mp inView
  have idC : c.id = before.id := by simpa only [Channel.core_id] using congrArg Channel.id coreC
  have sameC := unique_channel safeNext memberC memberAfter (idC.trans idAfter.symm)
  subst c
  simpa only [Channel.core_placed] using congrArg Channel.placed coreC

/-- A successful start establishes the root frame's proof interface directly
    from the executed input writes and the commit boundary. --/
theorem start_frameStart (graph : Graph) (inputs : List Input) (next : State)
    (valid : graph.WellFormed) (accepted : step (.initial graph) (.start inputs) = .ok next) :
    FrameStart next [] graph inputs ∧ FrameAncestors next := by
  have active : absorbed (.initial graph) (.start inputs) = false := rfl
  have executed := transition_of_active accepted active (by simp)
  have safeNext : Invariants next := by
    rcases step_ok_cases _ _ _ accepted with ⟨bad, _⟩ | ⟨_, _, _, safe, _⟩
    · rw [active] at bad; contradiction
    · exact safe
  obtain ⟨_, _, ⟨f, found, checked⟩, view, instances, frames, consumed, _⟩ := effect_start _ next inputs executed
  have sameF : f = {path := [], graph := graph} := by simpa [State.initial, State.frame?] using found.symm
  subst f
  simp only [Bool.and_eq_true, beq_iff_eq] at checked
  have names := unique_nodup _ checked.1.1
  have incoming : inputs.map Input.entry ⊆ graph.entries := by
    intro ref member
    obtain ⟨input, memberInput, same⟩ := List.mem_map.mp member
    have present := List.all_eq_true.mp checked.2 input memberInput
    simpa [same] using present
  have covered := subset_reverse_of_length names incoming (by simpa using checked.1.2)
  have sc : Scope next [] graph := {
    safe := safeNext
    layout := step_layout _ _ _ (initial_layout graph) accepted
    distinct := by simp [frames, State.initial]
    frame := ⟨{path := [], graph := graph}, by simp [frames, State.initial], rfl, rfl⟩
    valid := ⟨false, valid⟩ }
  have ids : next.channels.map Channel.id = (State.initial graph).channels.map Channel.id := by
    have equal := congrArg (List.map Channel.id) view
    simpa only [placedView_ids, applyWrites_ids] using equal
  have baseDistinct : ((State.initial graph).channels.map Channel.id).Nodup := by rw [← ids]; exact safeNext.channelIds
  constructor
  · refine ⟨sc, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i member
      simp [instances, State.initial] at member
    · intro r member
      simp [consumed, State.initial] at member
    · intro frame member _
      have same : frame = {path := [], graph := graph} := by simpa [frames, State.initial] using member
      rw [same]
    · intro c member path entry
      have template : c.layout ∈ (State.initial graph).channels := sc.template c member path
      exact view_untouched safeNext baseDistinct (rootWrites inputs) view (rootWrites_target inputs none)
        c.layout template entry c member rfl
    · intro c member path entry
      have template : c.layout ∈ (State.initial graph).channels := sc.template c member path
      obtain ⟨input, memberInput, ref⟩ := List.mem_map.mp (covered (sc.entry_ref c member path entry))
      have tokenEq := writes_on_channel (.initial graph) next (rootWrites inputs) baseDistinct safeNext view
        c.layout template c member rfl
      have hits := rootWrites_hits (.initial graph) baseDistinct c.layout template path entry inputs names input memberInput ref
      have lookup : inputs.find? (·.entry == c.edge.dst) = some input := by rw [← ref]; exact find_input names input memberInput
      refine ⟨?_, ?_⟩
      · apply List.contains_iff_mem.mpr
        exact (tokenEq .eos).mpr (.inr ((hits .eos).mpr (.inl rfl)))
      · rw [lookup]
        simp only [Option.map_some, Option.getD_some, bag_eq_canonical safeNext member]
        apply canonical_eq_of_mem_iff
        intro item
        rw [Effects.item_mem, tokenEq, hits]
        simp [Channel.layout]
    · intro frame member id owner
      have same : frame = {path := [], graph := graph} := by simpa [frames, State.initial] using member
      rw [same] at owner
      contradiction
  · intro frame member P prefixP
    have frameEq : frame = {path := [], graph := graph} := by simpa [frames, State.initial] using member
    subst frame
    have empty : P = [] := List.prefix_nil.mp prefixP
    exact ⟨{path := [], graph := graph}, by simp [frames, State.initial], empty.symm⟩

theorem FrameOpenedBy.seedData {s next : State} {op : Op} {f : Frame} (opened : FrameOpenedBy s next op f) :
    ∃ items, items.length = f.graph.entries.length ∧
      next.placedView = (applyWrites (seedWrites f.path f.graph.entries items)
        {s with channels := s.channels ++ f.channels}).placedView := by
  rcases opened with ⟨P, N, n, inputs, body, iteration, _, _, _, _, shape, arity, view, _⟩ |
    ⟨P, N, item, n, body, c, _, _, _, _, _, shape, arity, view, _⟩ |
    ⟨inst, i, n, body, limit, old, items, item, _, _, _, _, _, _, _, _, _, shape, arity, view, _⟩ |
    ⟨inst, i, n, body, limit, old, items, _, _, _, _, _, _, _, _, shape, arity, view, _⟩
  · exact ⟨inputs.map Prod.snd, by simpa only [shape.2.1] using arity, by simpa only [shape.2.1] using view⟩
  · exact ⟨[item], by simpa only [shape.2.1, List.length_singleton] using arity, by simpa only [shape.2.1] using view⟩
  · exact ⟨[item], by simpa only [shape.2.1, List.length_singleton] using arity, by simpa only [shape.2.1] using view⟩
  · exact ⟨items, by simpa only [shape.2.1] using arity, by simpa only [shape.2.1] using view⟩

theorem Scope.entry_not_exit {s : State} {P : Path} {g : Graph} (sc : Scope s P g)
    (c : Channel) (member : c ∈ s.channels) (path : c.path = P) (entry : c.entry = true) : c.exit = false := by
  rcases template_cases P g c.layout (sc.template c member path) with ⟨e, i, indexed, same⟩ |
    ⟨ref, i, indexed, same⟩ | ⟨ref, i, indexed, same⟩
  · have entryEq := congrArg Channel.entry same
    simp [entry] at entryEq
  · simpa using congrArg Channel.exit same
  · have entryEq := congrArg Channel.entry same
    simp [entry] at entryEq

theorem seeded_frameStart {s next : State} {op : Op} (safe : Invariants s) (layout : LayoutOK s)
    (distinct : (s.frames.map Frame.path).Nodup) (ancestors : FrameAncestors s)
    (owners : FrameOwners s)
    (accepted : step s op = .ok next) (f : Frame) (memberF : f ∈ next.frames)
    (absent : ∀ old ∈ s.frames, old.path ≠ f.path) (valid : f.graph.validate true = .ok ())
    (items : List ItemId) (arity : items.length = f.graph.entries.length)
    (view : next.placedView = (applyWrites (seedWrites f.path f.graph.entries items)
      {s with channels := s.channels ++ f.channels}).placedView) :
    FrameStart next f.path f.graph (bodyInputs f.graph items) := by
  have safeNext := preserves_invariants s next op safe accepted
  have one : ConformingSteps (fun _ _ => True) s [op] next := .cons trivial accepted (.nil next)
  have sc : Scope next f.path f.graph := {
    safe := safeNext
    layout := step_layout s next op layout accepted
    distinct := one.unique_frames distinct
    frame := ⟨f, memberF, rfl, rfl⟩
    valid := ⟨true, valid⟩ }
  let inputs := bodyInputs f.graph items
  have entries : inputs.map Input.entry = f.graph.entries := bodyInputs_entries f.graph items arity
  have names : (inputs.map Input.entry).Nodup := by rw [entries]; exact (f.graph.validate_boundaries true valid).1
  let base : State := {s with channels := s.channels ++ f.channels}
  have baseDistinct : (base.channels.map Channel.id).Nodup := StepView.base_distinct f.channels _ view safeNext
  have template : ∀ c ∈ next.channels, c.path = f.path → c.layout ∈ base.channels := by
    intro c memberC pathC
    apply List.mem_append_right
    rw [Frame.channels_template]
    exact sc.template c memberC pathC
  refine ⟨sc, new_scope_no_instances safe accepted ancestors f.path absent,
    new_scope_no_records safe layout accepted ancestors f.path absent,
    new_scope_no_descendants safe accepted ancestors f memberF absent, ?_, ?_, one.frameOwners safe distinct owners⟩
  · intro c memberC pathC entryC
    exact view_untouched safeNext baseDistinct _ view (seedWrites_target _ _ _ none)
      c.layout (template c memberC pathC) entryC c memberC rfl
  · intro c memberC pathC entryC
    have entryRef := sc.entry_ref c memberC pathC entryC
    rw [← entries] at entryRef
    obtain ⟨input, memberInput, ref⟩ := List.mem_map.mp entryRef
    have exitC := sc.entry_not_exit c memberC pathC entryC
    have tokenEq := writes_on_channel base next _ baseDistinct safeNext view c.layout (template c memberC pathC) c memberC rfl
    have hits := seedWrites_hits base baseDistinct c.layout (template c memberC pathC) f.path pathC entryC exitC
      f.graph items names input memberInput ref
    have lookup : inputs.find? (·.entry == c.edge.dst) = some input := by rw [← ref]; exact find_input names input memberInput
    refine ⟨?_, ?_⟩
    · apply List.contains_iff_mem.mpr
      exact (tokenEq .eos).mpr (.inr ((hits .eos).mpr (.inl rfl)))
    · change bag c = canonical (((inputs.find? _).map (·.items)).getD [])
      rw [lookup]
      simp only [Option.map_some, Option.getD_some, bag_eq_canonical safeNext memberC]
      apply canonical_eq_of_mem_iff
      intro item
      rw [Effects.item_mem, tokenEq, hits]
      simp [Channel.layout]

theorem opened_frameStart {s next : State} {op : Op} (safe : Invariants s) (layout : LayoutOK s)
    (distinct : (s.frames.map Frame.path).Nodup) (ancestors : FrameAncestors s)
    (owners : FrameOwners s)
    (accepted : step s op = .ok next) (f : Frame) (memberF : f ∈ next.frames)
    (absent : ∀ old ∈ s.frames, old.path ≠ f.path) (valid : f.graph.validate true = .ok ())
    (opened : FrameOpenedBy s next op f) :
    ∃ items, items.length = f.graph.entries.length ∧ FrameStart next f.path f.graph (bodyInputs f.graph items) := by
  obtain ⟨items, arity, view⟩ := opened.seedData
  exact ⟨items, arity, seeded_frameStart safe layout distinct ancestors owners accepted f memberF absent valid items arity view⟩

end Suimon
