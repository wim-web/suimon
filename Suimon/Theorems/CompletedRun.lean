import Suimon.Theorems.Bindings
import Suimon.Theorems.Frames

namespace Suimon

@[simp] theorem idleState_channels (s : State) : (idleState s).channels = s.channels := by
  unfold idleState
  split <;> rfl

@[simp] theorem idleState_frames (s : State) : (idleState s).frames = s.frames := by
  unfold idleState
  split <;> rfl

@[simp] theorem idleState_instances (s : State) : (idleState s).instances = s.instances := by
  unfold idleState
  split <;> rfl

@[simp] theorem idleState_frameDone (s : State) (f : Frame) : frameDone (idleState s) f = frameDone s f := by
  simp only [frameDone, State.nodeInstance?, idleState_channels, idleState_instances]

/-- The accepted start boundary supplies invariants even without a separate
    theorem about the serialization of the initial channel identifiers. --/
theorem ConformingSteps.started_invariants {allows : State → Op → Prop}
    (graph : Graph) (inputs : List Input) {ops : List Op} {last : State}
    (run : ConformingSteps allows (.initial graph) (.start inputs :: ops) last) : Invariants last := by
  cases run with
  | cons allowed accepted tail =>
    rcases step_ok_cases _ _ _ accepted with ⟨absorbed, _⟩ | ⟨_, _, _, safe, _⟩
    · simp [Suimon.absorbed, duplicateComplete, State.initial, ExecStatus.terminal] at absorbed
    · exact tail.invariants safe

/-- Facts extracted from an actual successful run, rather than assumed as a
    second execution semantics. The root and every child use validated graphs. --/
structure CompletedState (graph : Graph) (s : State) : Prop where
  safe : Invariants s
  layout : LayoutOK s
  frames : FramesCertified graph s
  uniqueFrames : (s.frames.map Frame.path).Nodup
  root : ∃ f, s.frame? [] = some f ∧ f.path = [] ∧ f.graph = graph ∧ frameDone s f = true

theorem ConformingSteps.completedState {allows : State → Op → Prop}
    (graph : Graph) (inputs : List Input) {ops : List Op} {last : State}
    (valid : graph.WellFormed)
    (run : ConformingSteps allows (.initial graph) (.start inputs :: ops) last)
    (finished : last.status = .succeeded) : CompletedState graph last := by
  have frames := run.frames_certified graph (initial_frames_certified graph valid)
  refine ⟨run.started_invariants graph inputs, run.layout (initial_layout graph), frames,
    run.unique_frames (by simp [State.initial]), ?_⟩
  obtain ⟨headOps, tailOps, before, root, _, _, _, result, _, found, done⟩ :=
    run.completion (by change ExecStatus.running ≠ .succeeded; decide) finished
  have finalFound : last.frame? [] = some root := by
    simpa only [result, State.frame?, idleState_frames] using found
  have member : root ∈ last.frames := List.mem_of_find?_eq_some finalFound
  have path : root.path = [] := by simpa using List.find?_some finalFound
  have certified := frames root.definitionView (List.mem_map.mpr ⟨root, member, rfl⟩)
  have graphEq : root.graph = graph := (certified.2 path).1
  exact ⟨root, finalFound, path, graphEq, by simpa only [result, idleState_frameDone] using done⟩

theorem CompletedState.root_nodes {graph : Graph} {s : State} (completed : CompletedState graph s) :
    ∀ n ∈ graph.nodes, ∃ i ∈ s.instances,
      i.path = [] ∧ i.node = n.id ∧ i.trigger = none ∧
      (i.status == .succeeded || i.status == .cancelled) = true := by
  obtain ⟨root, _, path, graphEq, done⟩ := completed.root
  simp only [frameDone, Bool.and_eq_true] at done
  intro n member
  have nodeDone := List.all_eq_true.mp done.2 n (by simpa [graphEq] using member)
  simp only [Option.any_eq_true] at nodeDone
  obtain ⟨i, found, status⟩ := nodeDone
  have predicate := List.find?_some found
  simp only [State.nodeInstance?, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    path] at predicate
  exact ⟨i, List.mem_of_find?_eq_some found, predicate.1.1, predicate.1.2, predicate.2, status⟩

end Suimon
