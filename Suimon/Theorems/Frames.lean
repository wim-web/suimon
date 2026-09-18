import Suimon.Theorems.Completion
import Suimon.Theorems.Graph

namespace Suimon

/-- Frame closure does not change the graph, its scope, or its owner. --/
def FrameCertified (root : Graph) (f : Frame) : Prop :=
  f.graph.validate f.owner.isSome = .ok () ∧
  (f.path = [] → f.graph = root ∧ f.owner = none ∧ f.definition = [])

def FramesCertified (root : Graph) (s : State) : Prop :=
  ∀ f ∈ s.frameDefinitions, FrameCertified root f

theorem initial_frames_certified (g : Graph) (valid : g.WellFormed) :
    FramesCertified g (.initial g) := by
  intro f member
  simp only [State.initial, State.frameDefinitions, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  subst f
  exact ⟨valid, fun _ => ⟨rfl, rfl, rfl⟩⟩

theorem getNode_certified (root : Graph) (s : State) (path : Path) (id : NodeId) (n : Node)
    (certified : FramesCertified root s) (found : getNode s path id = .ok n) :
    ∃ f ∈ s.frames, f.graph.validate f.owner.isSome = .ok () ∧ n ∈ f.graph.nodes := by
  unfold getNode at found
  cases frame : s.frame? path with
  | none => simp [frame, Option.toExcept, bind, Except.bind] at found
  | some f =>
    have member := List.mem_of_find?_eq_some frame
    have valid := (certified f.definitionView (List.mem_map.mpr ⟨f, member, rfl⟩)).1
    cases closed : f.closed with
    | true => simp [frame, closed, Option.toExcept, require, bind, Except.bind] at found
    | false =>
      cases node : f.graph.node? id with
      | none => simp [frame, closed, node, Option.toExcept, require, bind, Except.bind] at found
      | some value =>
        simp only [frame, closed, node, Option.toExcept, require, Bool.not_false,
          ↓reduceIte, bind, Except.bind, Except.ok.injEq] at found
        subst n
        exact ⟨f, member, valid, List.mem_of_find?_eq_some node⟩

theorem getNode_body_certified (root : Graph) (s : State) (path : Path) (id : NodeId)
    (n : Node) (body : Graph) (certified : FramesCertified root s)
    (found : getNode s path id = .ok n)
    (kind : (∃ limit, n.kind = .loop body limit) ∨ n.kind = .subworkflow body ∨ n.kind = .forEach body) :
    body.validate true = .ok () := by
  obtain ⟨f, _, valid, member⟩ := getNode_certified root s path id n certified found
  exact f.graph.validateNode_child n body kind (f.graph.validate_nodes _ valid n member)

theorem addFrame_certified (root : Graph) (s next : State) (owner : Instance) (body : Graph)
    (items : List ItemId) (certified : FramesCertified root s)
    (valid : body.validate true = .ok ()) (accepted : addFrame s owner body items = .ok next) :
    FramesCertified root next := by
  have effect := congrArg (fun view => view.2.2.1) (addFrame_layoutView s next owner body items accepted)
  simp only [State.layoutView, State.frameDefinitions, List.map_append, List.map_cons,
    List.map_nil] at effect
  intro f member
  rw [show next.frameDefinitions = _ from effect] at member
  rcases List.mem_append.mp member with old | new
  · exact certified f old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at new
    subst f
    refine ⟨valid, ?_⟩
    intro empty
    have length := congrArg List.length empty
    simp [Frame.definitionView] at length

set_option maxHeartbeats 2000000 in
theorem transition_frames_certified (root : Graph) (s next : State) (op : Op)
    (certified : FramesCertified root s) (accepted : transition s op = .ok next) :
    FramesCertified root next := by
  have hPlace := place_layoutView
  have hConsume := consume_layoutView
  have hInputs := consumeInputs_layoutView
  have hClose := closeOutputs_layoutView
  have hFresh := freshInstance_layoutView
  have hDecision := decision_layoutView
  have hFrame := closeFrame_layoutView
  have hControl := finishControl_layoutView
  have hStream := streamController_layoutView
  have hOutputs := placeOutputs_layoutView
  have hBody := placeBodyOutputs_layoutView
  have hChannels := consumeChannels_layoutView
  have hStart := startInputs_layoutView
  have hFailure := expireOrFail_layoutView
  have hAdd := addFrame_certified root
  have hLoop : ∀ path id n body limit, getNode s path id = .ok n →
      n.kind = .loop body limit → body.validate true = .ok () := by
    intro path id n body limit found kind
    exact getNode_body_certified root s path id n body certified found (.inl ⟨limit, kind⟩)
  have hSub : ∀ path id n body, getNode s path id = .ok n →
      n.kind = .subworkflow body → body.validate true = .ok () := by
    intro path id n body found kind
    exact getNode_body_certified root s path id n body certified found (.inr (.inl kind))
  have hEach : ∀ path id n body, getNode s path id = .ok n →
      n.kind = .forEach body → body.validate true = .ok () := by
    intro path id n body found kind
    exact getNode_body_certified root s path id n body certified found (.inr (.inr kind))
  simp only [State.layoutView, Prod.mk.injEq, FramesCertified, State.frameDefinitions]
    at hPlace hConsume hInputs hClose hFresh hDecision hFrame hControl hStream
      hOutputs hBody hChannels hStart hFailure hAdd certified ⊢
  cases op <;>
    simp only [transition, require, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at accepted
  all_goals
    repeat (first
      | split at accepted
      | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
      | contradiction
      | cases accepted)
  all_goals
    try simp only [putOutput, setInstance, setAttempt, State.frameDefinitions] at *
    grind only []

theorem step_frames_certified (root : Graph) (s next : State) (op : Op)
    (certified : FramesCertified root s) (accepted : step s op = .ok next) :
    FramesCertified root next := by
  rcases step_ok_cases s op next accepted with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · simpa [same] using certified
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure] at executed
      cases executed
      unfold idleState
      split <;> exact certified
    | _ =>
      simp only [transitionOrIdle] at executed
      exact transition_frames_certified root s next _ certified executed

theorem ConformingSteps.frames_certified {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (root : Graph) (certified : FramesCertified root s) : FramesCertified root next := by
  induction run with
  | nil => exact certified
  | cons allowed accepted tail ih => exact ih (step_frames_certified root _ _ _ certified accepted)

set_option maxHeartbeats 1600000 in
theorem transition_frameDefinitions (s next : State) (op : Op)
    (accepted : transition s op = .ok next) : s.frameDefinitions.IsPrefix next.frameDefinitions := by
  have hPlace := place_layoutView
  have hConsume := consume_layoutView
  have hInputs := consumeInputs_layoutView
  have hClose := closeOutputs_layoutView
  have hFresh := freshInstance_layoutView
  have hDecision := decision_layoutView
  have hFrame := closeFrame_layoutView
  have hControl := finishControl_layoutView
  have hStream := streamController_layoutView
  have hOutputs := placeOutputs_layoutView
  have hBody := placeBodyOutputs_layoutView
  have hChannels := consumeChannels_layoutView
  have hStart := startInputs_layoutView
  have hFailure := expireOrFail_layoutView
  have hAdd := addFrame_layoutView
  simp only [State.layoutView, Prod.mk.injEq, State.frameDefinitions, List.map_append]
    at hPlace hConsume hInputs hClose hFresh hDecision hFrame hControl hStream
      hOutputs hBody hChannels hStart hFailure hAdd ⊢
  cases op <;>
    simp only [transition, require, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at accepted
  all_goals
    repeat (first
      | split at accepted
      | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
      | contradiction
      | cases accepted)
  all_goals
    try simp only [putOutput, setInstance, setAttempt] at *
    grind only [List.prefix_refl, List.prefix_append]

theorem step_frameDefinitions (s next : State) (op : Op)
    (accepted : step s op = .ok next) : s.frameDefinitions.IsPrefix next.frameDefinitions := by
  rcases step_ok_cases s op next accepted with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst next
    exact List.prefix_refl _
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure] at executed
      cases executed
      unfold idleState
      split <;> exact List.prefix_refl _
    | _ =>
      simp only [transitionOrIdle] at executed
      exact transition_frameDefinitions s next _ executed

theorem ConformingSteps.frameDefinitions {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next) :
    s.frameDefinitions.IsPrefix next.frameDefinitions := by
  induction run with
  | nil => exact List.prefix_refl _
  | cons allowed accepted tail ih => exact (step_frameDefinitions _ _ _ accepted).trans ih

theorem frameDefinition_find (s : State) (path : Path) :
    s.frameDefinitions.find? (·.path == path) = (s.frame? path).map Frame.definitionView := by
  simp only [State.frameDefinitions, List.find?_map, State.frame?]
  rfl

/-- A child addition or closure cannot change the graph of an existing scope. --/
theorem retained_node (s next : State) (path : Path) (node : NodeId) (n : Node)
    (history : s.frameDefinitions.IsPrefix next.frameDefinitions)
    (found : s.node? path node = some n) : next.node? path node = some n := by
  cases before : s.frame? path with
  | none => simp [State.node?, before] at found
  | some f =>
    have old : s.frameDefinitions.find? (·.path == path) = some f.definitionView := by
      rw [frameDefinition_find, before]
      rfl
    have same := history.find?_eq_some old
    rw [frameDefinition_find] at same
    cases after : next.frame? path with
    | none => simp [after] at same
    | some g =>
      have graphs : g.graph = f.graph := by
        have definitions : g.definitionView = f.definitionView := by simpa [after] using same
        simpa only [Frame.definitionView] using congrArg Frame.graph definitions
      simpa [State.node?, before, after, graphs] using found

@[simp] theorem frameDefinitions_paths (s : State) :
    s.frameDefinitions.map Frame.path = s.frames.map Frame.path := by
  simp only [State.frameDefinitions, List.map_map, Function.comp_def, Frame.definitionView]

def FrameExtension (before after : List Frame) : Prop :=
  after = before ∨ ∃ f, after = before ++ [f] ∧ f.path ∉ before.map Frame.path

theorem FrameExtension.refl (frames : List Frame) : FrameExtension frames frames := .inl rfl

theorem addFrame_extension (s next : State) (owner : Instance) (body : Graph) (items : List ItemId)
    (accepted : addFrame s owner body items = .ok next) :
    FrameExtension s.frameDefinitions next.frameDefinitions := by
  let path := owner.path ++ [identity [owner.id, toString owner.iteration]]
  have absent : s.frame? path = none := by
    cases found : s.frame? path with
    | none => rfl
    | some f =>
      have failed : addFrame s owner body items = .error { code := "DUPLICATE_FRAME", message := "DUPLICATE_FRAME" } := by
        have rawFound : s.frame? (owner.path ++ [identity [owner.id, toString owner.iteration]]) = some f := found
        simp only [addFrame, rawFound, Option.isSome_some, Bool.not_true, require,
          Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
      rw [failed] at accepted
      contradiction
  have fresh : path ∉ s.frameDefinitions.map Frame.path := by
    rw [frameDefinitions_paths]
    intro member
    obtain ⟨f, memberF, pathF⟩ := List.mem_map.mp member
    have notFound := List.find?_eq_none.mp absent f memberF
    simpa [pathF] using notFound
  have effect := congrArg (fun view => view.2.2.1) (addFrame_layoutView s next owner body items accepted)
  simp only [State.layoutView, State.frameDefinitions, List.map_append, List.map_cons, List.map_nil] at effect
  exact .inr ⟨_, effect, fresh⟩

set_option maxHeartbeats 1600000 in
theorem transition_frameExtension (s next : State) (op : Op)
    (accepted : transition s op = .ok next) : FrameExtension s.frameDefinitions next.frameDefinitions := by
  have hPlace := place_layoutView
  have hConsume := consume_layoutView
  have hInputs := consumeInputs_layoutView
  have hClose := closeOutputs_layoutView
  have hFresh := freshInstance_layoutView
  have hDecision := decision_layoutView
  have hFrame := closeFrame_layoutView
  have hControl := finishControl_layoutView
  have hStream := streamController_layoutView
  have hOutputs := placeOutputs_layoutView
  have hBody := placeBodyOutputs_layoutView
  have hChannels := consumeChannels_layoutView
  have hStart := startInputs_layoutView
  have hFailure := expireOrFail_layoutView
  have hAdd := addFrame_extension
  simp only [State.layoutView, Prod.mk.injEq, State.frameDefinitions]
    at hPlace hConsume hInputs hClose hFresh hDecision hFrame hControl hStream
      hOutputs hBody hChannels hStart hFailure hAdd ⊢
  cases op <;>
    simp only [transition, require, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, instMonadExceptOfExcept] at accepted
  all_goals
    repeat' (first
      | split at accepted
      | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
      | contradiction
      | cases accepted)
  all_goals
    try simp only [putOutput, setInstance, setAttempt] at *
    grind only [FrameExtension.refl]

theorem step_frameExtension (s next : State) (op : Op)
    (accepted : step s op = .ok next) : FrameExtension s.frameDefinitions next.frameDefinitions := by
  rcases step_ok_cases s op next accepted with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst next
    exact .refl _
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure] at executed
      cases executed
      unfold idleState
      split <;> exact .refl _
    | _ =>
      simp only [transitionOrIdle] at executed
      exact transition_frameExtension s next _ executed

theorem FrameExtension.unique {before after : List Frame} (extension : FrameExtension before after)
    (distinct : (before.map Frame.path).Nodup) : (after.map Frame.path).Nodup := by
  rcases extension with same | ⟨f, same, fresh⟩
  · simpa [same] using distinct
  · simp only [same, List.map_append, List.map_cons, List.map_nil, List.nodup_append,
      List.nodup_cons, List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true, distinct, true_and]
    intro a member b singleton equal
    have bEq : b = f.path := by simpa using singleton
    exact fresh (bEq ▸ equal ▸ member)

theorem ConformingSteps.unique_frames {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (distinct : (s.frames.map Frame.path).Nodup) : (next.frames.map Frame.path).Nodup := by
  induction run with
  | nil => exact distinct
  | cons allowed accepted tail ih =>
    apply ih
    have result := (step_frameExtension _ _ _ accepted).unique (by simpa using distinct)
    simpa using result

end Suimon
