import Suimon.Theorems.Effects2

/-! Locality of placements: an accepted step writes tokens only to the output
    groups of the node it targets (plus entry seeds of a frame it opens). -/

namespace Suimon
open Effects

/-- The frame-local node an operation may write outputs for. -/
def opTarget (s : State) : Op → Option (Path × NodeId)
  | .emit a .. | .complete a .. => (s.instance? a.instance).map fun i => (i.path, i.node)
  | .fireWaitAll p n | .fireBranch p n _ | .fireCoalesce p n _ _ | .fireCollect p n
  | .fireFilter p n _ _ | .fireMerge p n _ _ | .propagateEos p n | .skip p n => some (p, n)
  | .finishSubworkflow i | .loopIterate i _ => (s.instance? i).map fun i => (i.path, i.node)
  | _ => none

def OutTarget (ws : List Write) (target : Option (Path × NodeId)) : Prop :=
  ∀ w ∈ ws, ∀ p n q t, w = .out p n q t → target = some (p, n)

theorem OutTarget.nil (target : Option (Path × NodeId)) : OutTarget [] target := by
  intro w hw; simp at hw

theorem OutTarget.append {a b : List Write} {target : Option (Path × NodeId)}
    (ha : OutTarget a target) (hb : OutTarget b target) : OutTarget (a ++ b) target := by
  intro w hw p n q t eq
  rcases List.mem_append.mp hw with h | h
  · exact ha w h p n q t eq
  · exact hb w h p n q t eq

theorem OutTarget.cons {w : Write} {ws : List Write} {target : Option (Path × NodeId)}
    (hw : ∀ p n q t, w = .out p n q t → target = some (p, n)) (hws : OutTarget ws target) :
    OutTarget (w :: ws) target := by
  intro v hv p n q t eq
  rcases List.mem_cons.mp hv with rfl | h
  · exact hw p n q t eq
  · exact hws v h p n q t eq

theorem eosWrites_target (path : Path) (n : Node) : OutTarget (eosWrites path n) (some (path, n.id)) := by
  intro w hw p node q t eq
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp hw
  cases eq; rfl

theorem outputWrites_target (path : Path) (node : NodeId) (outputs : List Output) :
    OutTarget (outputWrites path node outputs) (some (path, node)) := by
  intro w hw p n q t eq
  obtain ⟨o, _, inner⟩ := List.mem_flatMap.mp hw
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp inner
  cases eq; rfl

theorem bodyWrites_target (path : Path) (n : Node) (items : List ItemId) :
    OutTarget (bodyWrites path n items) (some (path, n.id)) := by
  intro w hw p node q t eq
  obtain ⟨pair, _, rfl⟩ := List.mem_map.mp hw
  cases eq; rfl

theorem routeWrites_target (path : Path) (n : Node) (value : Option ItemId) (arm : Option PortName) :
    OutTarget (routeWrites path n value arm) (some (path, n.id)) := by
  intro w hw p node q t eq
  obtain ⟨port, _, inner⟩ := List.mem_filterMap.mp hw
  cases h : routeOutput arm port.name value with
  | none => rw [h] at inner; contradiction
  | some id =>
    rw [h] at inner
    simp only [Option.map_some, Option.some.injEq] at inner
    subst inner
    cases eq; rfl

theorem seedWrites_target (path : Path) (entries : List PortRef) (items : List ItemId)
    (target : Option (Path × NodeId)) : OutTarget (seedWrites path entries items) target := by
  intro w hw p node q t eq
  obtain ⟨pair, _, inner⟩ := List.mem_flatMap.mp hw
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at inner
  rcases inner with rfl | rfl <;> cases eq

theorem rootWrites_target (inputs : List Input) (target : Option (Path × NodeId)) :
    OutTarget (rootWrites inputs) target := by
  intro w hw p node q t eq
  obtain ⟨input, _, inner⟩ := List.mem_flatMap.mp hw
  rcases List.mem_append.mp inner with h | h
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
    cases eq
  · simp only [List.mem_singleton] at h
    subst h
    cases eq

/-- The placed view of an accepted step is the base (with possibly one opened frame)
    written by a list of targeted placements. -/
def StepView (s next : State) (op : Op) : Prop :=
  ∃ added ws, next.placedView = (applyWrites ws { s with channels := s.channels ++ added }).placedView ∧
    OutTarget ws (opTarget s op)

theorem StepView.unchanged {s next : State} {op : Op} (same : next.channels = s.channels) : StepView s next op :=
  ⟨[], [], by simp [State.placedView, same], OutTarget.nil _⟩

theorem StepView.plain {s next : State} {op : Op} (ws : List Write)
    (view : next.placedView = (applyWrites ws s).placedView) (target : OutTarget ws (opTarget s op)) :
    StepView s next op :=
  ⟨[], ws, by simpa using view, target⟩

theorem StepView.opened {s next : State} {op : Op} (f : Frame) (ws : List Write)
    (view : next.placedView = (applyWrites ws { s with channels := s.channels ++ f.channels }).placedView)
    (target : OutTarget ws (opTarget s op)) : StepView s next op :=
  ⟨f.channels, ws, view, target⟩

theorem transition_view (s next : State) (op : Op) (distinct : (s.channels.map (·.id)).Nodup)
    (h : transition s op = .ok next) : StepView s next op := by
  cases op with
  | start inputs =>
    obtain ⟨_, _, _, view, _⟩ := effect_start s next inputs h
    exact StepView.plain _ view (rootWrites_target _ _)
  | activate path node =>
    obtain ⟨_, n, inputs, _, _, leaf | ⟨body, iteration, _, f, _, _, _, view, _⟩⟩ := effect_activate s next path node h
    · obtain ⟨_, _, _, view, _⟩ := leaf
      exact StepView.plain [] (by simpa using view) (OutTarget.nil _)
    · exact StepView.opened f _ view (seedWrites_target _ _ _ _)
  | spawn path node item =>
    obtain ⟨_, n, body, c, _, _, _, _, f, _, _, _, view, _⟩ := effect_spawn s next path node item distinct h
    exact StepView.opened f _ view (seedWrites_target _ _ _ _)
  | claim auth worker => exact StepView.unchanged (effect_claim s next auth worker h).1
  | renew auth => exact StepView.unchanged (effect_renew s next auth h).1
  | expireLease inst now => exact StepView.unchanged (effect_expireLease s next inst now h).1
  | promoteRetry inst now => exact StepView.unchanged (effect_promoteRetry s next inst now h).1
  | fail auth code retryable => exact StepView.unchanged (effect_fail s next auth code retryable h).1
  | emit auth port item =>
    obtain ⟨i, n, found, _, _, _, view, _⟩ := effect_emit s next auth port item h
    refine StepView.plain _ view ?_
    intro w hw p node q t eq
    simp only [List.mem_singleton] at hw
    subst hw
    cases eq
    simp [opTarget, found]
  | complete auth outputs =>
    obtain ⟨i, n, found, hn, _, _, view, _⟩ := effect_complete s next auth outputs h
    refine StepView.plain _ view ?_
    have target : opTarget s (.complete auth outputs) = some (i.path, i.node) := by simp [opTarget, found]
    rw [target]
    refine OutTarget.append (outputWrites_target _ _ _) ?_
    rw [← getNode_id s i.path i.node n hn]
    exact eosWrites_target _ _
  | fireWaitAll path node =>
    obtain ⟨n, inputs, hn, _, _, view, _⟩ := effect_fireWaitAll s next path node h
    refine StepView.plain _ view ?_
    show OutTarget _ (some (path, node))
    rw [← getNode_id s path node n hn]
    exact OutTarget.append (routeWrites_target _ _ _ _) (eosWrites_target _ _)
  | fireBranch path node arm =>
    obtain ⟨n, arms, inputs, item, hn, _, _, _, _, view, _⟩ := effect_fireBranch s next path node arm h
    refine StepView.plain _ view ?_
    show OutTarget _ (some (path, node))
    rw [← getNode_id s path node n hn]
    exact OutTarget.append (routeWrites_target _ _ _ _) (eosWrites_target _ _)
  | fireCollect path node =>
    obtain ⟨n, c, hn, _, _, _, _, view, _⟩ := effect_fireCollect s next path node h
    refine StepView.plain _ view ?_
    show OutTarget _ (some (path, node))
    rw [← getNode_id s path node n hn]
    exact OutTarget.append (routeWrites_target _ _ _ _) (eosWrites_target _ _)
  | fireCoalesce path node edge item =>
    obtain ⟨n, c, p0, hn, _, _, _, _, view, _⟩ := effect_fireCoalesce s next path node edge item distinct h
    refine StepView.plain _ view ?_
    show OutTarget _ (some (path, node))
    refine OutTarget.cons (fun p n' q t eq => by cases eq; rfl) ?_
    rw [← getNode_id s path node n hn]
    exact eosWrites_target _ _
  | fireFilter path node item keep =>
    obtain ⟨n, c, hn, _, _, _, _, _, _, ⟨_, p0, _, view⟩ | ⟨_, view⟩⟩ := effect_fireFilter s next path node item keep distinct h
    · refine StepView.plain _ view ?_
      exact OutTarget.cons (fun p n' q t eq => by cases eq; rfl) (OutTarget.nil _)
    · exact StepView.plain [] (by simpa using view) (OutTarget.nil _)
  | fireMerge path node edge item =>
    obtain ⟨n, c, p0, hn, _, _, _, _, _, _, _, _, view⟩ := effect_fireMerge s next path node edge item distinct h
    refine StepView.plain _ view ?_
    exact OutTarget.cons (fun p n' q t eq => by cases eq; rfl) (OutTarget.nil _)
  | propagateEos path node =>
    obtain ⟨n, hn, _, _, _, _, _, _, view⟩ := effect_propagateEos s next path node h
    refine StepView.plain _ view ?_
    show OutTarget _ (some (path, node))
    rw [← getNode_id s path node n hn]
    exact eosWrites_target _ _
  | finishSubworkflow inst =>
    obtain ⟨i, n, f, items, found, _, hn, _, _, _, _, _, _, ⟨body, _, view⟩ | ⟨body, _, view⟩⟩ :=
      effect_finishSubworkflow s next inst h
    · refine StepView.plain _ view ?_
      have target : opTarget s (.finishSubworkflow inst) = some (i.path, i.node) := by simp [opTarget, found]
      rw [target, ← getNode_id s i.path i.node n hn]
      exact OutTarget.append (bodyWrites_target _ _ _) (eosWrites_target _ _)
    · refine StepView.plain _ view ?_
      have target : opTarget s (.finishSubworkflow inst) = some (i.path, i.node) := by simp [opTarget, found]
      rw [target, ← getNode_id s i.path i.node n hn]
      exact bodyWrites_target _ _ _
  | loopIterate inst done =>
    obtain ⟨i, n, body, limit, f, items, item, found, _, hn, _, _, _, _, _,
      ⟨_, p0, _, view, _, _⟩ | ⟨_, _, view, _, _, _⟩ | ⟨_, _, f', _, _, _, view, _, _⟩⟩ :=
      effect_loopIterate s next inst done h
    · refine StepView.plain _ view ?_
      have target : opTarget s (.loopIterate inst done) = some (i.path, i.node) := by simp [opTarget, found]
      rw [target, ← getNode_id s i.path i.node n hn]
      exact OutTarget.cons (fun p n' q t eq => by cases eq; rfl) (eosWrites_target _ _)
    · exact StepView.plain [] (by simpa using view) (OutTarget.nil _)
    · exact StepView.opened f' _ view (seedWrites_target _ _ _ _)
  | skip path node =>
    obtain ⟨n, hn, _, _, _, _, _, _, view⟩ := effect_skip s next path node h
    refine StepView.plain _ view ?_
    show OutTarget _ (some (path, node))
    rw [← getNode_id s path node n hn]
    exact eosWrites_target _ _
  | idle =>
    rw [effect_idle s next h]
    exact StepView.unchanged rfl
  | cancel => exact StepView.unchanged (effect_cancel s next h).1
  | manualRetry inst =>
    obtain ⟨i, n, found, _, hn, ⟨_, _, _, admin, _⟩ | ⟨body, limit, f, items, _, _, _, _, f', _, _, _, view, _, _, _⟩⟩ :=
      effect_manualRetry s next inst h
    · exact StepView.unchanged admin.1
    · exact StepView.opened f' _ view (seedWrites_target _ _ _ _)

theorem step_view (s next : State) (op : Op) (distinct : (s.channels.map (·.id)).Nodup)
    (h : step s op = .ok next) : StepView s next op := by
  rcases step_ok_cases s op next h with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst same; exact StepView.unchanged rfl
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      exact StepView.unchanged (idleState_channels s)
    | _ =>
      simp only [transitionOrIdle] at executed
      exact transition_view s next _ distinct executed

/-- Channel identifiers of the base are distinct whenever the result satisfies the invariants. -/
theorem StepView.base_distinct {s next : State} (added : List Channel) (ws : List Write)
    (view : next.placedView = (applyWrites ws { s with channels := s.channels ++ added }).placedView)
    (safe : Invariants next) : ((s.channels ++ added).map (·.id)).Nodup := by
  have ids : next.channels.map (·.id) = (s.channels ++ added).map (·.id) := by
    have := congrArg (List.map (·.id)) view
    rw [placedView_ids, placedView_ids, applyWrites_ids] at this
    exact this
  rw [← ids]
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  exact unique_nodup _ safe.1.1.1.1.1.1.2

/-- A channel outside the targeted output group keeps its placed history across a step. -/
theorem step_untouched (s next : State) (op : Op) (c : Channel) (member : c ∈ s.channels)
    (nonEntry : c.entry = false) (safe : Invariants s) (safeNext : Invariants next)
    (h : step s op = .ok next) (miss : opTarget s op ≠ some (c.path, c.edge.src.node)) :
    ∃ d ∈ next.channels, d.core = c.core := by
  have distinct : (s.channels.map (·.id)).Nodup := by
    simp only [Invariants, invariants, Bool.and_eq_true] at safe
    exact unique_nodup _ safe.1.1.1.1.1.1.2
  obtain ⟨added, ws, view, target⟩ := step_view s next op distinct h
  have baseDistinct := StepView.base_distinct added ws view safeNext
  have memberBase : c ∈ ({ s with channels := s.channels ++ added } : State).channels :=
    List.mem_append_left _ member
  have untouched := applyWrites_untouched ws _ c memberBase baseDistinct nonEntry (by
    intro w hw t eq
    have := target w hw c.path c.edge.src.node c.edge.src.port t eq
    exact miss this)
  have inView : c.core ∈ next.placedView := by
    rw [view]
    exact placedView_member untouched
  obtain ⟨d, memberD, eq⟩ := List.mem_map.mp inView
  exact ⟨d, memberD, eq⟩

end Suimon
