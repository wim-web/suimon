import Suimon.Theorems.History
import Suimon.Theorems.Traversal

namespace Suimon

def Channel.layout (c : Channel) : Channel := { c with placed := [], consumed := 0 }
def State.channelLayout (s : State) : List Channel := s.channels.map Channel.layout
def State.frameChannels (s : State) : List Channel := s.frames.flatMap Frame.channels
def Frame.definitionView (f : Frame) : Frame := { f with closed := false }
def State.frameDefinitions (s : State) : List Frame := s.frames.map Frame.definitionView
def State.layoutView (s : State) : List Channel × List Channel × List Frame × ExecStatus :=
  (s.channelLayout, s.frameChannels, s.frameDefinitions, s.status)
def LayoutOK (s : State) : Prop := s.channelLayout = s.frameChannels

@[simp] theorem Frame.channels_layout (f : Frame) : f.channels.map Channel.layout = f.channels := by
  simp [Frame.channels, Frame.edgeChannels, Frame.entryChannels, Frame.exitChannels,
    List.map_append, List.map_map, Function.comp_def, Channel.layout]

theorem placeToken_layout (c next : Channel) (token : Token)
    (accepted : placeToken c token = .ok next) : next.layout = c.layout := by
  simp only [placeToken, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first | split at accepted | contradiction | (cases accepted; rfl))

theorem place_layout (s next : State) (ids : List String) (token : Token)
    (accepted : place s ids token = .ok next) :
    next.channelLayout = s.channelLayout ∧ next.frames = s.frames ∧ next.status = s.status := by
  change ((s.channels.mapM (fun c => if ids.contains c.id then placeToken c token else .ok c)) >>= fun cs =>
    Except.ok { s with channels := cs }) = .ok next at accepted
  cases result : s.channels.mapM (fun c => if ids.contains c.id then placeToken c token else .ok c) with
  | error e => simp only [result, bind, Except.bind] at accepted; contradiction
  | ok cs =>
    have same := mapM_preserves Channel.layout _ s.channels cs (by
      intro c member d correct
      dsimp at correct
      split at correct
      · exact placeToken_layout c d token correct
      · cases correct; rfl) result
    simp only [result, bind, Except.bind] at accepted
    cases accepted
    exact ⟨same, rfl, rfl⟩

theorem consume_layout (s next : State) (channel who : String) (expected : Option ItemId)
    (accepted : consume s channel who expected = .ok next) :
    next.channelLayout = s.channelLayout ∧ next.frames = s.frames ∧ next.status = s.status := by
  simp only [consume, Option.toExcept, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | split at accepted
    | contradiction
    | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
    | (cases accepted
       constructor
       · simp only [State.channelLayout, List.map_map]
         apply List.map_congr_left
         intro c member
         dsimp
         split <;> rfl
       · exact ⟨rfl, rfl⟩))

theorem place_layoutView (s next : State) (ids : List String) (token : Token)
    (accepted : place s ids token = .ok next) : next.layoutView = s.layoutView := by
  obtain ⟨channels, frames, status⟩ := place_layout s next ids token accepted
  simp only [State.layoutView, channels, State.frameChannels, State.frameDefinitions, frames, status]

theorem consume_layoutView (s next : State) (channel who : String) (expected : Option ItemId)
    (accepted : consume s channel who expected = .ok next) : next.layoutView = s.layoutView := by
  obtain ⟨channels, frames, status⟩ := consume_layout s next channel who expected accepted
  simp only [State.layoutView, channels, State.frameChannels, State.frameDefinitions, frames, status]

theorem consumeRest_layoutView (s next : State) (c : Channel) (who : String)
    (accepted : consumeRest s c who = .ok next) : next.layoutView = s.layoutView := by
  exact foldlM_preserves State.layoutView _ c.pending s next
    (fun state _ _ result valid => consume_layoutView state result c.id who none valid) accepted

theorem consumeInputs_layoutView (s next : State) (path : Path) (node who : String)
    (accepted : consumeInputs s path node who = .ok next) : next.layoutView = s.layoutView := by
  exact foldlM_preserves State.layoutView _ (s.incoming path node) s next
    (fun state c _ result valid => consumeRest_layoutView state result c who valid) accepted

theorem closeOutputs_layoutView (s next : State) (path : Path) (node : Node)
    (accepted : closeOutputs s path node = .ok next) : next.layoutView = s.layoutView := by
  exact foldlM_preserves State.layoutView _ node.outputs s next
    (fun state p _ result valid => place_layoutView state result _ .eos valid) accepted

theorem freshInstance_layoutView (s next : State) (i : Instance)
    (accepted : freshInstance s i = .ok next) : next.layoutView = s.layoutView := by
  simp only [freshInstance, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first | split at accepted | contradiction | (cases accepted; rfl))

theorem decision_layoutView (s next : State) (key value : String)
    (accepted : decision s key value = .ok next) : next.layoutView = s.layoutView := by
  simp only [decision, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first | split at accepted | contradiction | (cases accepted; rfl))

@[simp] theorem setInstance_layoutView (s : State) (i : Instance) :
    (setInstance s i).layoutView = s.layoutView := rfl

@[simp] theorem setAttempt_layoutView (s : State) (id : AttemptId) (status : AttemptStatus) :
    (setAttempt s id status).layoutView = s.layoutView := rfl

theorem initial_layout (g : Graph) : LayoutOK (.initial g) := by
  simp [LayoutOK, State.channelLayout, State.frameChannels, State.initial]

theorem closeFrame_layoutView (s next : State) (f : Frame) (who : InstanceId)
    (accepted : closeFrame s f who = .ok next) : next.layoutView = s.layoutView := by
  unfold closeFrame consumeChannels at accepted
  cases consumed : (s.channels.filter (fun c => c.path == f.path && c.exit)).foldlM
      (fun state c => consumeRest state c who) s with
  | error e => simp [consumed, bind, Except.bind] at accepted
  | ok middle =>
    have same := foldlM_preserves State.layoutView _ _ s middle
      (fun state c _ result valid => consumeRest_layoutView state result c who valid) consumed
    simp only [consumed, bind, Except.bind, pure, Except.pure] at accepted
    cases accepted
    have frames : (middle.frames.map (fun g => if g.path == f.path then { g with closed := true } else g)).flatMap Frame.channels =
        middle.frameChannels := by
      simp only [State.frameChannels, List.flatMap_map]
      apply congrArg (fun fn => middle.frames.flatMap fn)
      funext g
      split <;> rfl
    have definitions : (middle.frames.map (fun g => if g.path == f.path then { g with closed := true } else g)).map Frame.definitionView =
        middle.frameDefinitions := by
      simp only [State.frameDefinitions, List.map_map]
      apply List.map_congr_left
      intro g member
      dsimp
      split <;> rfl
    change (middle.channelLayout,
      (middle.frames.map (fun g => if g.path == f.path then { g with closed := true } else g)).flatMap Frame.channels,
      (middle.frames.map (fun g => if g.path == f.path then { g with closed := true } else g)).map Frame.definitionView,
      middle.status) = s.layoutView
    rw [frames, definitions]
    exact same

theorem routeOutputs_layoutView (s next : State) (path : Path) (n : Node)
    (output : Option ItemId) (arm : Option PortName)
    (accepted : routeOutputs s path n output arm = .ok next) : next.layoutView = s.layoutView := by
  apply foldlM_preserves State.layoutView _ n.outputs s next _ accepted
  intro state p member result valid
  dsimp at valid
  split at valid
  · exact place_layoutView state result _ _ valid
  · cases valid; rfl

theorem finishControl_layoutView (s next : State) (path : Path) (n : Node)
    (inputs : List (PortName × ItemId)) (output : Option ItemId) (arm : Option PortName)
    (accepted : finishControl s path n inputs output arm = .ok next) : next.layoutView = s.layoutView := by
  unfold finishControl at accepted
  cases created : freshInstance s (makeInstance path n .succeeded inputs) with
  | error e => simp [created, bind, Except.bind] at accepted
  | ok a =>
    have first := freshInstance_layoutView s a _ created
    simp only [created, bind, Except.bind] at accepted
    cases consumed : consumeInputs a path n.id (instanceId path n.id) with
    | error e => simp [consumed, bind, Except.bind, makeInstance] at accepted
    | ok b =>
      have second := consumeInputs_layoutView a b path n.id _ consumed
      simp only [makeInstance, consumed, bind, Except.bind] at accepted
      cases emitted : routeOutputs b path n output arm with
      | error e => simp [emitted, bind, Except.bind] at accepted
      | ok c =>
        have third := routeOutputs_layoutView b c path n output arm emitted
        simp only [emitted, bind, Except.bind] at accepted
        exact (closeOutputs_layoutView c next path n accepted).trans (third.trans (second.trans first))

theorem streamController_layoutView (s next : State) (path : Path) (n : Node)
    (accepted : streamController s path n = .ok next) : next.layoutView = s.layoutView := by
  unfold streamController at accepted
  cases found : s.nodeInstance? path n.id with
  | none => exact freshInstance_layoutView s next _ (by simpa [found] using accepted)
  | some i =>
    simp only [found, require, bind, Except.bind, pure, Except.pure] at accepted
    repeat (first | split at accepted | contradiction | (cases accepted; rfl))

theorem seedEntries_layoutView (s next : State) (path : Path) (entries : List PortRef) (items : List ItemId)
    (accepted : seedEntries s path entries items = .ok next) : next.layoutView = s.layoutView := by
  apply foldlM_preserves State.layoutView _ (entries.zip items) s next _ accepted
  intro state pair member out valid
  rcases pair with ⟨p, id⟩
  dsimp at valid
  cases first : place state
      (((state.incoming path p.node).filter (fun c => c.entry && c.edge.dst == p)).map (·.id)) (.item id) with
  | error e => simp [first, bind, Except.bind] at valid
  | ok middle =>
    simp only [first, bind, Except.bind] at valid
    exact (place_layoutView middle out _ .eos valid).trans (place_layoutView state middle _ (.item id) first)

theorem addFrame_layoutView (s next : State) (owner : Instance) (body : Graph) (items : List ItemId)
    (accepted : addFrame s owner body items = .ok next) :
    let path := owner.path ++ [identity [owner.id, toString owner.iteration]]
    let definition := ((s.frame? owner.path).map (·.definition)).getD [] ++ [owner.node]
    let f : Frame := { path, graph := body, definition, owner := some owner.id }
    next.layoutView = ({ s with frames := s.frames ++ [f], channels := s.channels ++ f.channels } : State).layoutView := by
  unfold addFrame at accepted
  simp only [require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | (exact seedEntries_layoutView _ next _ body.entries items accepted)
    | split at accepted
    | contradiction)

theorem addFrame_layout (s next : State) (owner : Instance) (body : Graph) (items : List ItemId)
    (balanced : LayoutOK s) (accepted : addFrame s owner body items = .ok next) : LayoutOK next := by
  let path := owner.path ++ [identity [owner.id, toString owner.iteration]]
  let definition := ((s.frame? owner.path).map (·.definition)).getD [] ++ [owner.node]
  let f : Frame := { path, graph := body, definition, owner := some owner.id }
  let base : State := { s with frames := s.frames ++ [f], channels := s.channels ++ f.channels }
  have baseOK : LayoutOK base := by
    simp only [LayoutOK, base, State.channelLayout, State.frameChannels, List.map_append,
      Frame.channels_layout, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact congrArg (· ++ f.channels) balanced
  have written : next.layoutView = base.layoutView := addFrame_layoutView s next owner body items accepted
  have channels := congrArg Prod.fst written
  have frames := congrArg (fun v => v.2.1) written
  change next.channelLayout = next.frameChannels
  exact channels.trans (baseOK.trans frames.symm)

theorem placeOutputs_layoutView (s next : State) (path : Path) (node : NodeId) (outputs : List Output)
    (accepted : placeOutputs s path node outputs = .ok next) : next.layoutView = s.layoutView := by
  apply foldlM_preserves State.layoutView _ outputs s next _ accepted
  intro state output member result valid
  exact foldlM_preserves State.layoutView _ output.items state result
    (fun current item _ after placed => place_layoutView current after _ (.item item) placed) valid

theorem placeBodyOutputs_layoutView (s next : State) (path : Path) (node : Node) (items : List ItemId)
    (accepted : placeBodyOutputs s path node items = .ok next) : next.layoutView = s.layoutView := by
  exact foldlM_preserves State.layoutView _ (node.outputs.zip items) s next
    (fun state pair _ result valid => place_layoutView state result _ (.item pair.2) valid) accepted

theorem consumeChannels_layoutView (s next : State) (channels : List Channel) (who : InstanceId)
    (accepted : consumeChannels s channels who = .ok next) : next.layoutView = s.layoutView :=
  foldlM_preserves State.layoutView _ channels s next
    (fun state c _ result valid => consumeRest_layoutView state result c who valid) accepted

theorem startInputs_layoutView (s next : State) (inputs : List Input)
    (accepted : startInputs s inputs = .ok next) : next.layoutView = s.layoutView := by
  apply foldlM_preserves State.layoutView _ inputs s next _ accepted
  intro state input member result valid
  let channels : List Channel := state.channels.filter (fun c => c.path.isEmpty && c.entry && c.edge.dst == input.entry)
  have placed : ∀ middle, input.items.foldlM (fun current item => place current (channels.map (·.id)) (.item item)) state = .ok middle →
      middle.layoutView = state.layoutView := by
    intro middle correct
    exact foldlM_preserves State.layoutView _ input.items state middle
      (fun current item _ after yes => place_layoutView current after _ (.item item) yes) correct
  change ((do
    require (unique input.items && channels.all (fun (c : Channel) => c.kind != PortKind.plain || input.items.length == 1)) "INVALID_INPUT"
    let middle ← input.items.foldlM (fun (current : State) (item : ItemId) => place current (channels.map Channel.id) (.item item)) state
    place middle (channels.map Channel.id) .eos) : Result State) = .ok result at valid
  cases ready : require (unique input.items && channels.all (fun c => c.kind != .plain || input.items.length == 1)) "INVALID_INPUT" with
  | error e => rw [ready] at valid; contradiction
  | ok value =>
    rw [ready] at valid
    simp only [bind, Except.bind] at valid
    cases body : input.items.foldlM (fun current item => place current (channels.map (·.id)) (.item item)) state with
    | error e => rw [body] at valid; contradiction
    | ok middle =>
      rw [body] at valid
      simp only [bind, Except.bind] at valid
      exact (place_layoutView middle result _ .eos valid).trans (placed middle body)

theorem expireOrFail_layoutView (s next : State) (i : Instance) (n : Node) (now : Time)
    (outcome : AttemptStatus) (retryable : Bool) (code : String)
    (accepted : expireOrFail s i n now outcome retryable code = .ok next) :
    next.channelLayout = s.channelLayout ∧ next.frameChannels = s.frameChannels ∧
    next.frameDefinitions = s.frameDefinitions ∧ (next.status = .succeeded → s.status = .succeeded) := by
  simp only [expireOrFail, require, Option.toExcept, setInstance, setAttempt,
    bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | split at accepted
    | contradiction
    | (cases accepted; simp [State.channelLayout, State.frameChannels, State.frameDefinitions]))

theorem layout_of_view_eq (s next : State) (balanced : LayoutOK s)
    (same : next.layoutView = s.layoutView) : LayoutOK next := by
  have channels := congrArg Prod.fst same
  have frames := congrArg (fun v => v.2.1) same
  exact channels.trans (balanced.trans frames.symm)

set_option maxHeartbeats 1600000 in
theorem transition_layout (s next : State) (op : Op) (balanced : LayoutOK s)
    (accepted : transition s op = .ok next) : LayoutOK next := by
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
  have hAdd := addFrame_layout
  simp only [LayoutOK, State.layoutView, Prod.mk.injEq, State.channelLayout, State.frameChannels]
    at hPlace hConsume hInputs hClose hFresh hDecision hFrame hControl hStream hOutputs hBody hChannels hStart hFailure hAdd
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
    simp only [putOutput, LayoutOK, State.layoutView, State.channelLayout, State.frameChannels, setInstance, setAttempt] at *
    grind only []

theorem step_layout (s next : State) (op : Op) (balanced : LayoutOK s)
    (accepted : step s op = .ok next) : LayoutOK next := by
  rcases step_ok_cases s op next accepted with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · simpa [same] using balanced
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure] at executed
      cases executed
      unfold idleState
      split <;> exact balanced
    | _ =>
      simp only [transitionOrIdle] at executed
      exact transition_layout s next _ balanced executed

theorem ConformingSteps.layout {allows : State → Op → Prop} {s next : State} {ops : List Op}
    (run : ConformingSteps allows s ops next) (balanced : LayoutOK s) : LayoutOK next := by
  induction run with
  | nil => exact balanced
  | cons allowed accepted tail ih => exact ih (step_layout _ _ _ balanced accepted)

end Suimon
