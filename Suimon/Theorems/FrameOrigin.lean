import Suimon.Theorems.PlainOutputs

/-! Origins of frames, persistence of nodes along a run, and token provenance. -/

namespace Suimon
open Effects

/-- Tokens on a channel after writes come from the channel before or from a write. -/
theorem applyWrites_tokens (ws : List Write) (st : State) (d : Channel) (member : d ∈ (applyWrites ws st).channels) :
    ∃ c ∈ st.channels, c.id = d.id ∧ ∀ t ∈ d.placed, t ∈ c.placed ∨ ∃ w ∈ ws, w.token = t := by
  induction ws generalizing st with
  | nil => exact ⟨d, member, rfl, fun t ht => .inl ht⟩
  | cons w ws ih =>
    simp only [applyWrites_cons] at member
    obtain ⟨c, memberC, idC, tokens⟩ := ih _ member
    simp only [applyWrite, write, List.mem_map] at memberC
    obtain ⟨e, memberE, eq⟩ := memberC
    refine ⟨e, memberE, ?_, ?_⟩
    · rw [← idC, ← eq]
      split <;> simp [insertToken_id]
    · intro t ht
      rcases tokens t ht with old | ⟨v, hv, tv⟩
      · rw [← eq] at old
        split at old
        · rcases (insertToken_mem e w.token t).mp old with older | fresh
          · exact .inl older
          · exact .inr ⟨w, by simp, fresh.symm⟩
        · exact .inl old
      · exact .inr ⟨v, by simp [hv], tv⟩

theorem cancelled_status_absorbing (status : InstanceStatus)
    (h : allowedStatus .cancelled status = true) : status = .cancelled := by
  cases status <;> first | rfl | (change false = true at h; contradiction)

/-- A retained instance keeps `succeeded` / `cancelled` once reached, along a run. -/
theorem ConformingSteps.retains_status {allows : State → Op → Prop} {s next : State} {ops : List Op}
    (run : ConformingSteps allows s ops next) (safe : Invariants s) (i : Instance) (member : i ∈ s.instances)
    (final : i.status = .succeeded ∨ i.status = .cancelled) :
    ∃ j ∈ next.instances, j.id = i.id ∧ j.status = i.status := by
  induction run generalizing i with
  | nil => exact ⟨i, member, rfl, rfl⟩
  | @cons s middle last op ops allowed accepted tail ih =>
    have safeMid := preserves_invariants s middle op safe accepted
    rcases step_ok_cases s op middle accepted with ⟨_, same⟩ | ⟨_, _, _, _, hist⟩
    · subst same
      exact ih safeMid i member final
    · simp only [historyOK, Bool.and_eq_true] at hist
      have retained := List.all_eq_true.mp hist.1.2 i member
      obtain ⟨j, lookup, properties⟩ := (Option.any_eq_true _ _).mp retained
      simp only [Bool.and_eq_true] at properties
      have memberJ : j ∈ middle.instances := List.mem_of_find?_eq_some lookup
      have idJ : j.id = i.id := by simpa using List.find?_some lookup
      have statusJ : j.status = i.status := by
        rcases final with done | gone
        · rw [done] at properties ⊢
          exact succeeded_status_absorbing _ properties.1.2
        · rw [gone] at properties ⊢
          exact cancelled_status_absorbing _ properties.1.2
      obtain ⟨k, memberK, idK, statusK⟩ := ih safeMid j memberJ (by rw [statusJ]; exact final)
      exact ⟨k, memberK, idK.trans idJ, statusK.trans statusJ⟩

/-- Node definitions of an existing scope persist along a run. -/
theorem ConformingSteps.node {allows : State → Op → Prop} {s next : State} {ops : List Op}
    (run : ConformingSteps allows s ops next) (path : Path) (node : NodeId) (n : Node)
    (found : s.node? path node = some n) : next.node? path node = some n :=
  retained_node s next path node n run.frameDefinitions found

/-- A frame present at the end, with its definition view, seen from an earlier state. -/
theorem ConformingSteps.frame_definition {allows : State → Op → Prop} {s next : State} {ops : List Op}
    (run : ConformingSteps allows s ops next) (f : Frame) (member : f ∈ s.frames)
    (distinctNext : (next.frames.map Frame.path).Nodup) (g : Frame) (memberG : g ∈ next.frames)
    (samePath : g.path = f.path) : g.graph = f.graph ∧ g.owner = f.owner ∧ g.definition = f.definition := by
  have inDefs : f.definitionView ∈ next.frameDefinitions :=
    run.frameDefinitions.subset (List.mem_map.mpr ⟨f, member, rfl⟩)
  obtain ⟨h, memberH, viewH⟩ := List.mem_map.mp inDefs
  have pathH : h.path = f.path := by
    have := congrArg Frame.path viewH
    simpa [Frame.definitionView] using this
  have same : h = g := eq_of_mapped_nodup Frame.path next.frames distinctNext h g memberH memberG (pathH.trans samePath.symm)
  subst same
  have graphs := congrArg Frame.graph viewH
  have owners := congrArg Frame.owner viewH
  have defs := congrArg Frame.definition viewH
  simp only [Frame.definitionView] at graphs owners defs
  exact ⟨graphs, owners, defs⟩

/-- The frame opened by an operation, with the facts needed to seed and evaluate it. -/
def FrameOpenedBy (s next : State) (op : Op) (g : Frame) : Prop :=
  (∃ path node n inputs body iteration, op = .activate path node ∧ getNode s path node = .ok n ∧
      plainInputs s path n = .ok inputs ∧
      ((n.kind = .subworkflow body ∧ iteration = 0) ∨ ∃ m, n.kind = .loop body m ∧ iteration = 1) ∧
      OpenedFrame { makeInstance path n .waitingInputs inputs with iteration } body g ∧
      (inputs.map (·.2)).length = body.entries.length ∧
      next.placedView = (applyWrites (seedWrites g.path body.entries (inputs.map (·.2)))
        { s with channels := s.channels ++ g.channels }).placedView ∧
      next.instances = s.instances ++ [{ makeInstance path n .waitingInputs inputs with iteration }]) ∨
  (∃ path node item n body c, op = .spawn path node item ∧ getNode s path node = .ok n ∧ n.kind = .forEach body ∧
      (s.incoming path node).head? = some c ∧ c.pending.head? = some (.item item) ∧
      OpenedFrame (makeInstance path n .waitingInputs [("item", item)] (some item)) body g ∧
      1 = body.entries.length ∧
      next.placedView = (applyWrites (seedWrites g.path body.entries [item])
        { s with channels := s.channels ++ g.channels }).placedView ∧
      next.instances = s.instances ++ [makeInstance path n .waitingInputs [("item", item)] (some item)] ∧
      next.consumed = s.consumed ++ [({ channel := c.id, index := c.consumed, item := item, byInstance := (makeInstance path n .waitingInputs [("item", item)] (some item)).id } : Consumption)]) ∨
  (∃ inst i n body limit f items item, op = .loopIterate inst false ∧ s.instance? inst = some i ∧
      i.status = .waitingInputs ∧ getNode s i.path i.node = .ok n ∧ n.kind = .loop body limit ∧
      currentFrame s i = .ok f ∧ bodyResults s f = .ok items ∧ items.head? = some item ∧
      i.iteration < limit + i.extraIterations ∧
      OpenedFrame { i with iteration := i.iteration + 1 } body g ∧ 1 = body.entries.length ∧
      next.placedView = (applyWrites (seedWrites g.path body.entries [item])
        { s with channels := s.channels ++ g.channels }).placedView ∧
      next.instances = (setInstance s { i with iteration := i.iteration + 1 }).instances) ∨
  (∃ inst i n body limit f items, op = .manualRetry inst ∧ s.instance? inst = some i ∧ i.status = .failed ∧
      getNode s i.path i.node = .ok n ∧ n.kind = .loop body limit ∧ currentFrame s i = .ok f ∧ f.closed = true ∧
      frameOutputItems s f = .ok items ∧
      OpenedFrame { i with status := .waitingInputs, extraIterations := i.extraIterations + 1, iteration := i.iteration + 1 } body g ∧
      items.length = body.entries.length ∧
      next.placedView = (applyWrites (seedWrites g.path body.entries items)
        { s with channels := s.channels ++ g.channels }).placedView ∧
      next.instances = (setInstance s { i with status := .waitingInputs, extraIterations := i.extraIterations + 1, iteration := i.iteration + 1 }).instances)

theorem closeFrames_paths (frames : List Frame) (path : Path) (g : Frame) (member : g ∈ closeFrames frames path) :
    ∃ k ∈ frames, k.path = g.path := by
  simp only [closeFrames, List.mem_map] at member
  obtain ⟨k, memberK, eq⟩ := member
  refine ⟨k, memberK, ?_⟩
  rw [← eq]
  split <;> rfl

/-- Every frame after a step either existed (by path) or was opened by the step. -/
theorem step_frames_origin (s next : State) (op : Op) (safe : Invariants s) (h : step s op = .ok next)
    (g : Frame) (memberG : g ∈ next.frames) : (∃ k ∈ s.frames, k.path = g.path) ∨ FrameOpenedBy s next op g := by
  have distinct := safe.channelIds
  rcases step_ok_cases s op next h with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst same; exact .inl ⟨g, memberG, rfl⟩
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      rw [idleState_frames] at memberG
      exact .inl ⟨g, memberG, rfl⟩
    | start inputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, frames, _⟩ := effect_start s next inputs executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | activate path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, inputs, hn, plain, leaf | ⟨body, iteration, kinds, f, opened, _, arity, view, instances, frames, _⟩⟩ :=
        effect_activate s next path node executed
      · obtain ⟨_, _, _, _, _, frames, _⟩ := leaf
        rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
      · rw [frames] at memberG
        rcases List.mem_append.mp memberG with old | new
        · exact .inl ⟨g, old, rfl⟩
        · simp only [List.mem_singleton] at new
          subst new
          exact .inr (.inl ⟨path, node, n, inputs, body, iteration, rfl, hn, plain, kinds, opened, arity, view, instances⟩)
    | spawn path node item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, body, c, hn, kind, hc, head, f, opened, _, arity, view, instances, frames, consumed⟩ :=
        effect_spawn s next path node item distinct executed
      rw [frames] at memberG
      rcases List.mem_append.mp memberG with old | new
      · exact .inl ⟨g, old, rfl⟩
      · simp only [List.mem_singleton] at new
        subst new
        exact .inr (.inr (.inl ⟨path, node, item, n, body, c, rfl, hn, kind, hc, head, opened, arity, view, instances, consumed⟩))
    | claim auth worker => rw [(effect_claim s next auth worker executed).2.1] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | renew auth => rw [(effect_renew s next auth executed).2.1] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | expireLease inst now => rw [(effect_expireLease s next inst now executed).2.1] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | promoteRetry inst now => rw [(effect_promoteRetry s next inst now executed).2.1] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | fail auth code retryable => rw [(effect_fail s next auth code retryable executed).2.1] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | emit auth port item =>
      obtain ⟨_, _, _, _, _, _, _, _, frames, _⟩ := effect_emit s next auth port item executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | complete auth outputs =>
      obtain ⟨_, _, _, _, _, _, _, _, frames, _⟩ := effect_complete s next auth outputs executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | fireWaitAll path node =>
      obtain ⟨_, _, _, _, _, _, _, frames, _⟩ := effect_fireWaitAll s next path node executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | fireBranch path node arm =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, frames, _⟩ := effect_fireBranch s next path node arm executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | fireCollect path node =>
      obtain ⟨_, _, _, _, _, _, _, _, _, frames, _⟩ := effect_fireCollect s next path node executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | fireCoalesce path node edge item =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, frames, _⟩ := effect_fireCoalesce s next path node edge item distinct executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | fireFilter path node item keep =>
      obtain ⟨_, _, _, _, _, _, _, frames, _⟩ := effect_fireFilter s next path node item keep distinct executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | fireMerge path node edge item =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, frames, _⟩ := effect_fireMerge s next path node edge item distinct executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | propagateEos path node =>
      obtain ⟨_, _, _, _, _, _, frames, _⟩ := effect_propagateEos s next path node executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | finishSubworkflow inst =>
      obtain ⟨i, _, f, _, _, _, _, _, _, _, frames, _⟩ := effect_finishSubworkflow s next inst executed
      rw [frames] at memberG
      exact .inl (closeFrames_paths _ _ g memberG)
    | loopIterate inst done =>
      obtain ⟨i, n, body, limit, f, items, item, found, waiting, hn, kind, hf, hb, hi, _,
        ⟨_, _, _, _, _, frames⟩ | ⟨_, _, _, _, frames, _⟩ | ⟨notDone, below, f', opened, _, arity, view, instances, frames⟩⟩ :=
        effect_loopIterate s next inst done executed
      · rw [frames] at memberG; exact .inl (closeFrames_paths _ _ g memberG)
      · rw [frames] at memberG; exact .inl (closeFrames_paths _ _ g memberG)
      · rw [frames] at memberG
        rcases List.mem_append.mp memberG with old | new
        · exact .inl (closeFrames_paths _ _ g old)
        · simp only [List.mem_singleton] at new
          subst new
          subst notDone
          exact .inr (.inr (.inr (.inl ⟨inst, i, n, body, limit, f, items, item, rfl, found, waiting, hn, kind, hf, hb, hi, below, opened, arity, view, instances⟩)))
    | skip path node =>
      obtain ⟨_, _, _, _, _, _, frames, _⟩ := effect_skip s next path node executed
      rw [frames] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | cancel => rw [(effect_cancel s next executed).2.1] at memberG; exact .inl ⟨g, memberG, rfl⟩
    | manualRetry inst =>
      obtain ⟨i, n, found, failed, hn, ⟨_, _, _, admin, _⟩ | ⟨body, limit, f, items, kind, hf, closed, hi, f', opened, _, arity, view, instances, frames, _⟩⟩ :=
        effect_manualRetry s next inst executed
      · rw [admin.2.1] at memberG; exact .inl ⟨g, memberG, rfl⟩
      · rw [frames] at memberG
        rcases List.mem_append.mp memberG with old | new
        · exact .inl ⟨g, old, rfl⟩
        · simp only [List.mem_singleton] at new
          subst new
          exact .inr (.inr (.inr (.inr ⟨inst, i, n, body, limit, f, items, rfl, found, failed, hn, kind, hf, closed, hi, opened, arity, view, instances⟩)))

/-- Decomposition of a run at the step that opens a frame (by path). -/
theorem frame_origin {allows : State → Op → Prop} {s0 last : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops last) (safe0 : Invariants s0)
    (f : Frame) (memberL : f ∈ last.frames) (absent0 : ∀ k ∈ s0.frames, k.path ≠ f.path) :
    ∃ pre op post s s' g, ops = pre ++ op :: post ∧
      ConformingSteps allows s0 pre s ∧ allows s op ∧ step s op = .ok s' ∧
      ConformingSteps allows s' post last ∧ Invariants s ∧
      (∀ k ∈ s.frames, k.path ≠ f.path) ∧ g ∈ s'.frames ∧ g.path = f.path ∧ FrameOpenedBy s s' op g := by
  induction run with
  | nil => exact absurd rfl (absent0 f memberL)
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid : Invariants middle := preserves_invariants s middle op safe0 accepted
    cases found : middle.frames.find? (·.path == f.path) with
    | some g =>
      have memberG : g ∈ middle.frames := List.mem_of_find?_eq_some found
      have pathG : g.path = f.path := by simpa using List.find?_some found
      rcases step_frames_origin s middle op safe0 accepted g memberG with ⟨k, memberK, pathK⟩ | opened
      · exact absurd (pathK.trans pathG) (absent0 k memberK)
      · exact ⟨[], op, ops, s, middle, g, rfl, .nil s, allowed, accepted, tail, safe0, absent0, memberG, pathG, opened⟩
    | none =>
      have absentMid : ∀ k ∈ middle.frames, k.path ≠ f.path := by
        intro k hk eq
        have := List.find?_eq_none.mp found k hk
        simp [eq] at this
      obtain ⟨pre, op', post, t, t', g, split, head, allowed', accepted', rest, safeT, absentT, memberG, pathG, opened⟩ :=
        ih safeMid memberL absentMid
      exact ⟨op :: pre, op', post, t, t', g, by simp [split], .cons allowed accepted head, allowed', accepted',
        rest, safeT, absentT, memberG, pathG, opened⟩

end Suimon
