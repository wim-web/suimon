import Suimon.Theorems.Consumption

/-! Origins: the step that creates an instance, and the shapes an operation can
    have when it targets a node of a given kind. -/

namespace Suimon

theorem Instance.binding_eq {i j : Instance} (id : j.id = i.id) (node : j.node = i.node) (path : j.path = i.path)
    (trigger : j.trigger = i.trigger) (inputs : j.inputs = i.inputs) : j.binding = i.binding := by
  simp only [Instance.binding, id, node, path, trigger, inputs]

/-- Decomposition of a run at the step that creates an instance (by identifier). -/
theorem instance_origin {allows : State → Op → Prop} {s0 last : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops last) (safe0 : Invariants s0)
    (i : Instance) (memberL : i ∈ last.instances) (absent0 : ∀ j ∈ s0.instances, j.id ≠ i.id) :
    ∃ pre op post s s' j, ops = pre ++ op :: post ∧
      ConformingSteps allows s0 pre s ∧ allows s op ∧ step s op = .ok s' ∧
      ConformingSteps allows s' post last ∧ Invariants s ∧
      (∀ k ∈ s.instances, k.id ≠ i.id) ∧ j ∈ s'.instances ∧ j.id = i.id ∧ j.binding = i.binding := by
  induction run with
  | nil => exact absurd rfl (absent0 i memberL)
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid : Invariants middle := preserves_invariants s middle op safe0 accepted
    cases found : middle.instances.find? (·.id == i.id) with
    | some j =>
      have memberJ : j ∈ middle.instances := List.mem_of_find?_eq_some found
      have idJ : j.id = i.id := by simpa using List.find?_some found
      obtain ⟨node, path, trigger, inputs⟩ := tail.input_snapshot safeMid j i memberJ memberL idJ
      exact ⟨[], op, ops, s, middle, j, rfl, .nil s, allowed, accepted, tail, safe0, absent0, memberJ, idJ,
        Instance.binding_eq idJ node.symm path.symm trigger.symm inputs.symm⟩
    | none =>
      have absentMid : ∀ k ∈ middle.instances, k.id ≠ i.id := by
        intro k hk eq
        have := List.find?_eq_none.mp found k hk
        simp [eq] at this
      obtain ⟨pre, op', post, t, t', j, split, head, allowed', accepted', rest, safeT, absentT, memberJ, idJ, bindJ⟩ :=
        ih safeMid memberL absentMid
      exact ⟨op :: pre, op', post, t, t', j, by simp [split], .cons allowed accepted head, allowed', accepted',
        rest, safeT, absentT, memberJ, idJ, bindJ⟩

theorem node?_of_getNode {s : State} {P : Path} {N : NodeId} {n m : Node}
    (found : s.node? P N = some n) (got : getNode s P N = .ok m) : m = n := by
  have := getNode_node? s P N m got
  rw [found] at this
  exact (Option.some.inj this).symm

theorem opTarget_instance {s : State} {a : Credentials} {P : Path} {N : NodeId} {op : Op}
    (shape : opTarget s op = (s.instance? a.instance).map fun i => (i.path, i.node))
    (target : opTarget s op = some (P, N)) :
    ∃ i, s.instance? a.instance = some i ∧ i.path = P ∧ i.node = N := by
  rw [shape] at target
  cases found : s.instance? a.instance with
  | none => rw [found] at target; contradiction
  | some i =>
    rw [found] at target
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at target
    exact ⟨i, rfl, target.1, target.2⟩

theorem opTarget_id {s : State} {inst : InstanceId} {P : Path} {N : NodeId} {op : Op}
    (shape : opTarget s op = (s.instance? inst).map fun i => (i.path, i.node))
    (target : opTarget s op = some (P, N)) :
    ∃ i, s.instance? inst = some i ∧ i.path = P ∧ i.node = N := by
  rw [shape] at target
  cases found : s.instance? inst with
  | none => rw [found] at target; contradiction
  | some i =>
    rw [found] at target
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at target
    exact ⟨i, rfl, target.1, target.2⟩

/-- Shapes of an accepted, non-absorbed operation that targets node `n` at `(P, N)`. -/
theorem target_shape (s next : State) (op : Op) (safe : Invariants s) (active : absorbed s op = false)
    (h : step s op = .ok next)
    (P : Path) (N : NodeId) (target : opTarget s op = some (P, N)) (n : Node) (found : s.node? P N = some n) :
    (∃ auth port item r c, op = .emit auth port item ∧ n.kind = .leaf r c) ∨
    (∃ auth outputs r c, op = .complete auth outputs ∧ n.kind = .leaf r c) ∨
    (op = .fireWaitAll P N ∧ n.kind = .waitAll) ∨
    (∃ arm arms, op = .fireBranch P N arm ∧ n.kind = .branch arms) ∨
    (∃ e x, op = .fireCoalesce P N e x ∧ n.kind = .coalesce) ∨
    (op = .fireCollect P N ∧ n.kind = .collect) ∨
    (∃ x k, op = .fireFilter P N x k ∧ n.kind = .filter) ∨
    (∃ e x, op = .fireMerge P N e x ∧ n.kind = .merge) ∨
    (op = .propagateEos P N ∧ (match n.kind with | .filter | .merge | .forEach _ => true | _ => false) = true) ∨
    (∃ inst body, op = .finishSubworkflow inst ∧ (n.kind = .subworkflow body ∨ n.kind = .forEach body)) ∨
    (∃ inst d body limit, op = .loopIterate inst d ∧ n.kind = .loop body limit) ∨
    (op = .skip P N ∧ allKind n.inputs .plain = true) := by
  have distinct := safe.channelIds
  rcases step_ok_cases s op next h with ⟨absorbedTrue, _⟩ | ⟨_, _, prepared, _, _⟩
  · rw [active] at absorbedTrue; contradiction
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | emit auth port item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, n', found', hn, ⟨r, c, kind⟩, _⟩ := effect_emit s next auth port item executed
      obtain ⟨i', found'', pathI, nodeI⟩ := opTarget_instance rfl target
      rw [found'] at found''
      cases found''
      subst pathI nodeI
      have := node?_of_getNode found hn
      subst this
      exact .inl ⟨auth, port, item, r, c, rfl, kind⟩
    | complete auth outputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, found', hn, ⟨r, c, kind⟩, _⟩ := effect_complete s next auth outputs executed
      obtain ⟨i', found'', pathI, nodeI⟩ := opTarget_instance rfl target
      rw [found'] at found''
      cases found''
      subst pathI nodeI
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inl ⟨auth, outputs, r, c, rfl, kind⟩)
    | fireWaitAll path node =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', _, hn, kind, _⟩ := effect_fireWaitAll s next path node executed
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inl ⟨rfl, kind⟩))
    | fireBranch path node arm =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', arms, _, _, hn, kind, _⟩ := effect_fireBranch s next path node arm executed
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inr (.inl ⟨arm, arms, rfl, kind⟩)))
    | fireCoalesce path node edge item =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', _, _, hn, kind, _⟩ := effect_fireCoalesce s next path node edge item distinct executed
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inr (.inr (.inl ⟨edge, item, rfl, kind⟩))))
    | fireCollect path node =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', _, hn, kind, _⟩ := effect_fireCollect s next path node executed
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, kind⟩)))))
    | fireFilter path node item keep =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', _, hn, kind, _⟩ := effect_fireFilter s next path node item keep distinct executed
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨item, keep, rfl, kind⟩))))))
    | fireMerge path node edge item =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', _, _, hn, kind, _⟩ := effect_fireMerge s next path node edge item distinct executed
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨edge, item, rfl, kind⟩)))))))
    | propagateEos path node =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', hn, kind, _⟩ := effect_propagateEos s next path node executed
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, kind⟩))))))))
    | finishSubworkflow inst =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, n', f, items, found', _, hn, _, _, _, _, _, _, kinds⟩ := effect_finishSubworkflow s next inst executed
      obtain ⟨i', found'', pathI, nodeI⟩ := opTarget_id rfl target
      rw [found'] at found''
      cases found''
      subst pathI nodeI
      have := node?_of_getNode found hn
      subst this
      rcases kinds with ⟨body, kind, _⟩ | ⟨body, kind, _⟩
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨inst, body, rfl, .inl kind⟩)))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨inst, body, rfl, .inr kind⟩)))))))))
    | loopIterate inst done =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, n', body, limit, f, items, item, found', _, hn, kind, _⟩ := effect_loopIterate s next inst done executed
      obtain ⟨i', found'', pathI, nodeI⟩ := opTarget_id rfl target
      rw [found'] at found''
      cases found''
      subst pathI nodeI
      have := node?_of_getNode found hn
      subst this
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨inst, done, body, limit, rfl, kind⟩))))))))))
    | skip path node =>
      simp only [transitionOrIdle] at executed
      simp only [opTarget, Option.some.injEq, Prod.mk.injEq] at target
      obtain ⟨rfl, rfl⟩ := target
      obtain ⟨n', hn, cond, _, _, _⟩ := effect_skip s next path node executed
      have := node?_of_getNode found hn
      subst this
      simp only [Bool.and_eq_true] at cond
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, cond.1⟩))))))))))
    | start inputs => simp [opTarget] at target
    | activate path node => simp [opTarget] at target
    | spawn path node item => simp [opTarget] at target
    | claim auth worker => simp [opTarget] at target
    | renew auth => simp [opTarget] at target
    | expireLease inst now => simp [opTarget] at target
    | promoteRetry inst now => simp [opTarget] at target
    | fail auth code retryable => simp [opTarget] at target
    | idle => simp [opTarget] at target
    | cancel => simp [opTarget] at target
    | manualRetry inst => simp [opTarget] at target

end Suimon
