import Suimon.Theorems.Assembly

namespace Suimon
open Semantics Effects

theorem getNode_parent {s : State} {P : Path} {N : NodeId} {n : Node} (got : getNode s P N = .ok n) :
    ∃ f ∈ s.frames, f.path = P := by
  cases found : s.frame? P with
  | none => simp [getNode, found, Option.toExcept, bind, Except.bind] at got
  | some f => exact ⟨f, List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

theorem FrameOpenedBy.parent {s next : State} {op : Op} {f : Frame} (opened : FrameOpenedBy s next op f) :
    ∃ parent ∈ s.frames, ∃ segment, f.path = parent.path ++ [segment] := by
  rcases opened with ⟨P, N, n, inputs, body, iteration, _, got, _, _, shape, _⟩ |
    ⟨P, N, item, n, body, c, _, got, _, _, _, shape, _⟩ |
    ⟨inst, i, n, body, limit, old, items, item, _, _, _, got, _, _, _, _, _, shape, _⟩ |
    ⟨inst, i, n, body, limit, old, items, _, _, _, got, _, _, _, _, shape, _⟩
  all_goals
    obtain ⟨parent, member, path⟩ := getNode_parent got
    exact ⟨parent, member, _, by rw [shape.1, path] <;> rfl⟩

def FrameAncestors (s : State) : Prop :=
  ∀ f ∈ s.frames, ∀ P, P <+: f.path → ∃ parent ∈ s.frames, parent.path = P

theorem ConformingSteps.frame_path {allows : State → Op → Prop} {s next : State} {ops : List Op}
    (run : ConformingSteps allows s ops next) (f : Frame) (member : f ∈ s.frames) :
    ∃ g ∈ next.frames, g.path = f.path := by
  have inDefs := run.frameDefinitions.subset (List.mem_map.mpr ⟨f, member, rfl⟩)
  obtain ⟨g, memberG, same⟩ := List.mem_map.mp inDefs
  exact ⟨g, memberG, by simpa [Frame.definitionView] using congrArg Frame.path same⟩

theorem step_frameAncestors {s next : State} {op : Op} (safe : Invariants s)
    (accepted : step s op = .ok next) (ancestors : FrameAncestors s) : FrameAncestors next := by
  have one : ConformingSteps (fun _ _ => True) s [op] next := .cons trivial accepted (.nil next)
  intro f memberF P pathP
  rcases step_frames_origin s next op safe accepted f memberF with ⟨old, memberOld, samePath⟩ | opened
  · obtain ⟨parent, memberParent, pathParent⟩ := ancestors old memberOld P (by rw [samePath]; exact pathP)
    obtain ⟨after, memberAfter, pathAfter⟩ := one.frame_path parent memberParent
    exact ⟨after, memberAfter, pathAfter.trans pathParent⟩
  · obtain ⟨parent, memberParent, segment, pathF⟩ := opened.parent
    by_cases shorter : P.length ≤ parent.path.length
    · have parentPrefix : parent.path <+: f.path := by rw [pathF]; exact List.prefix_append _ _
      have prefixParent : P <+: parent.path := List.prefix_of_prefix_length_le pathP parentPrefix shorter
      obtain ⟨ancestor, memberAncestor, pathAncestor⟩ := ancestors parent memberParent P prefixParent
      obtain ⟨after, memberAfter, pathAfter⟩ := one.frame_path ancestor memberAncestor
      exact ⟨after, memberAfter, pathAfter.trans pathAncestor⟩
    · have lengthBound := pathP.length_le
      have fullLength : P.length = f.path.length := by
        rw [pathF, List.length_append, List.length_singleton] at lengthBound ⊢
        omega
      have same : P = f.path := pathP.eq_of_length fullLength
      exact ⟨f, memberF, same.symm⟩

theorem ConformingSteps.frameAncestors {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (ancestors : FrameAncestors s) : FrameAncestors last := by
  induction run with
  | nil => exact ancestors
  | cons allowed accepted tail ih =>
    exact ih (preserves_invariants _ _ _ safe accepted) (step_frameAncestors safe accepted ancestors)

theorem FrameAncestors.fresh_subtree {s : State} (ancestors : FrameAncestors s) (P : Path)
    (absent : ∀ f ∈ s.frames, f.path ≠ P) : ∀ f ∈ s.frames, ¬ P <+: f.path := by
  intro f member prefixP
  obtain ⟨parent, memberParent, pathParent⟩ := ancestors f member P prefixP
  exact absent parent memberParent pathParent

theorem CreatedBy.parent {s : State} {op : Op} {i : Instance} (created : CreatedBy s op i) :
    ∃ f ∈ s.frames, f.path = i.path := by
  rcases created with
      ⟨P, N, n, inputs, _, got, _, ⟨r, c, _, eq⟩ | ⟨body, iteration, _, eq⟩⟩ |
      ⟨P, N, n, inputs, _, got, _, _, eq⟩ |
      ⟨P, N, arm, n, arms, inputs, _, got, _, _, eq⟩ |
      ⟨P, N, n, c, _, got, _, _, eq⟩ |
      ⟨P, N, edge, item, n, c, _, got, _, _, eq⟩ |
      ⟨P, N, n, _, got, eq⟩ |
      ⟨P, N, n, _, got, _, eq⟩ |
      ⟨P, N, n, _, got, eq⟩ |
      ⟨P, N, item, n, body, _, got, _, eq⟩
  all_goals
    obtain ⟨parent, member, path⟩ := getNode_parent got
    exact ⟨parent, member, by rw [eq]; exact path⟩

/-- Even newly created instances run in a frame which existed before the step;
    opening a child frame does not start any node inside it in the same step. --/
theorem step_instance_parent {s next : State} {op : Op} (safe : Invariants s)
    (accepted : step s op = .ok next) (i : Instance) (member : i ∈ next.instances) :
    ∃ f ∈ s.frames, f.path = i.path := by
  classical
  by_cases old : ∃ j ∈ s.instances, j.id = i.id
  · obtain ⟨j, memberJ, idJ⟩ := old
    have one : ConformingSteps (fun _ _ => True) s [op] next := .cons trivial accepted (.nil next)
    obtain ⟨_, pathI, _, _⟩ := one.input_snapshot safe j i memberJ member idJ
    obtain ⟨n, nodeJ⟩ := safe.instance_node j memberJ
    cases frame : s.frame? j.path with
    | none => simp [State.node?, frame] at nodeJ
    | some f =>
      have pathF : f.path = j.path := by simpa using List.find?_some frame
      exact ⟨f, List.mem_of_find?_eq_some frame, pathF.trans pathI.symm⟩
  · have absent : ∀ j ∈ s.instances, j.id ≠ i.id := fun j memberJ equal => old ⟨j, memberJ, equal⟩
    exact (step_instance_created s next op safe accepted i member absent).parent

theorem step_record_old_channel {s next : State} {op : Op} (safe : Invariants s)
    (accepted : step s op = .ok next) (r : Consumption) (member : r ∈ next.consumed) :
    ∃ c ∈ s.channels, c.id = r.channel := by
  classical
  by_cases old : r ∈ s.consumed
  · obtain ⟨c, memberC, idC, _⟩ := record_item_placed safe r old
    exact ⟨c, memberC, idC⟩
  · rcases (step_records s next op safe accepted).2 r member old with ⟨P, N, channels, _⟩ |
      ⟨inst, i, f, _, _, _, channels⟩
    all_goals
      obtain ⟨c, memberC, idC⟩ := List.mem_map.mp channels
      exact ⟨c, (List.mem_filter.mp memberC).1, idC⟩

theorem new_scope_no_instances {s next : State} {op : Op} (safe : Invariants s)
    (accepted : step s op = .ok next) (ancestors : FrameAncestors s) (P : Path)
    (absent : ∀ f ∈ s.frames, f.path ≠ P) : ∀ i ∈ next.instances, ¬ P <+: i.path := by
  intro i memberI prefixP
  obtain ⟨parent, memberParent, pathParent⟩ := step_instance_parent safe accepted i memberI
  exact ancestors.fresh_subtree P absent parent memberParent (by rw [pathParent]; exact prefixP)

theorem new_scope_no_records {s next : State} {op : Op} (safe : Invariants s) (layout : LayoutOK s)
    (accepted : step s op = .ok next) (ancestors : FrameAncestors s) (P : Path)
    (absent : ∀ f ∈ s.frames, f.path ≠ P) :
    ∀ r ∈ next.consumed, ∀ c ∈ next.channels, P <+: c.path → r.channel ≠ c.id := by
  intro r memberR c memberC prefixP equal
  obtain ⟨old, memberOld, idOld⟩ := step_record_old_channel safe accepted r memberR
  obtain ⟨image, memberImage, idImage, layoutImage, _⟩ := step_image s next op old memberOld safe accepted
  have same := unique_channel (preserves_invariants s next op safe accepted) memberImage memberC
    (idImage.trans (idOld.trans equal))
  have pathC : c.path = old.path := by
    rw [same] at layoutImage
    exact (Channel.layout_fields layoutImage).2.2.1
  obtain ⟨frame, memberFrame, _, pathFrame⟩ := layout.channel_frame old memberOld
  exact ancestors.fresh_subtree P absent frame memberFrame (by rw [← pathFrame, ← pathC]; exact prefixP)

theorem new_scope_no_descendants {s next : State} {op : Op} (safe : Invariants s)
    (accepted : step s op = .ok next) (ancestors : FrameAncestors s) (f : Frame) (memberF : f ∈ next.frames)
    (absent : ∀ old ∈ s.frames, old.path ≠ f.path) :
    ∀ k ∈ next.frames, f.path <+: k.path → k.path = f.path := by
  have fresh := ancestors.fresh_subtree f.path absent
  have memberView : f.definitionView ∈ next.frameDefinitions := List.mem_map.mpr ⟨f, memberF, rfl⟩
  rcases step_frameExtension s next op accepted with same | ⟨added, same, _⟩
  · rw [same] at memberView
    obtain ⟨old, memberOld, viewOld⟩ := List.mem_map.mp memberView
    have pathOld : old.path = f.path := by simpa [Frame.definitionView] using congrArg Frame.path viewOld
    exact False.elim (absent old memberOld pathOld)
  · rw [same] at memberView
    have addedEq : f.definitionView = added := by
      rcases List.mem_append.mp memberView with old | new
      · obtain ⟨old, memberOld, viewOld⟩ := List.mem_map.mp old
        have pathOld : old.path = f.path := by simpa [Frame.definitionView] using congrArg Frame.path viewOld
        exact False.elim (absent old memberOld pathOld)
      · simpa using new
    intro k memberK prefixK
    have inView : k.definitionView ∈ next.frameDefinitions := List.mem_map.mpr ⟨k, memberK, rfl⟩
    rw [same] at inView
    rcases List.mem_append.mp inView with old | new
    · obtain ⟨old, memberOld, viewOld⟩ := List.mem_map.mp old
      have pathOld : old.path = k.path := by simpa [Frame.definitionView] using congrArg Frame.path viewOld
      exact False.elim (fresh old memberOld (by rw [pathOld]; exact prefixK))
    · have sameK : k.definitionView = added := by simpa using new
      simpa [Frame.definitionView] using congrArg Frame.path (sameK.trans addedEq.symm)

end Suimon
