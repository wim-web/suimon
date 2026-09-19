import Suimon.Theorems.LeafFinal

/-! Items on a node's outputs imply an instance of that node; instance creation shapes. -/

namespace Suimon
open Effects

theorem nodeInstance?_mem {s : State} {path : Path} {node : NodeId} {i : Instance}
    (found : s.nodeInstance? path node = some i) : i ∈ s.instances ∧ i.path = path ∧ i.node = node ∧ i.trigger = none := by
  have member := List.mem_of_find?_eq_some found
  have pred := List.find?_some found
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at pred
  exact ⟨member, pred.1.1, pred.1.2, pred.2⟩

/-- Writing an item to an output of `(P, N)` leaves an instance of `(P, N)` in the resulting state. -/
theorem item_write_instance (s next : State) (op : Op) (safe : Invariants s) (active : absorbed s op = false)
    (h : step s op = .ok next) (P : Path) (N : NodeId) (target : opTarget s op = some (P, N))
    (n : Node) (found : s.node? P N = some n)
    (c : Channel) (member : c ∈ s.channels) (d : Channel) (memberD : d ∈ next.channels) (same : d.id = c.id)
    (x : ItemId) (absent : Token.item x ∉ c.placed) (present : Token.item x ∈ d.placed) :
    ∃ j ∈ next.instances, j.path = P ∧ j.node = N := by
  have safeNext := preserves_invariants s next op safe h
  have persist : ∀ i ∈ s.instances, i.path = P → i.node = N → ∃ j ∈ next.instances, j.path = P ∧ j.node = N := by
    intro i memberI pathI nodeI
    obtain ⟨j, memberJ, bindJ⟩ := (ConformingSteps.cons (allows := fun _ _ => True) trivial h (.nil next)).retains_binding safe i memberI
    exact ⟨j, memberJ, (Instance.binding_path bindJ).trans pathI, (Instance.binding_node bindJ).trans nodeI⟩
  have appended : ∀ (i : Instance), next.instances = s.instances ++ [i] → i.path = P → i.node = N →
      ∃ j ∈ next.instances, j.path = P ∧ j.node = N := fun i same hp hn => ⟨i, by rw [same]; simp, hp, hn⟩
  have eosOnlyContra : ∀ ws : List Write, (∀ w ∈ ws, w.token = .eos) →
      next.placedView = (applyWrites ws s).placedView → False := by
    intro ws eosOnly view
    have tokens := view_tokens next s ws safe.channelIds view c member d memberD same (.item x) present
    rcases tokens with old | ⟨w, hw, tw⟩
    · exact absent old
    · have := eosOnly w hw
      rw [this] at tw
      cases tw
  rcases step_ok_cases s op next h with ⟨a, _⟩ | ⟨_, _, prepared, _, _⟩
  · rw [active] at a; contradiction
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    rcases target_shape s next op safe active h P N target n found with
        ⟨auth, _, _, _, _, eq, _⟩ | ⟨auth, _, _, _, eq, _⟩ | ⟨eq, _⟩ | ⟨arm, _, eq, _⟩ | ⟨e, y, eq, _⟩ | ⟨eq, _⟩
      | ⟨y, k, eq, _⟩ | ⟨e, y, eq, _⟩ | ⟨eq, _⟩ | ⟨inst, _, eq, _⟩ | ⟨inst, dn, _, _, eq, _⟩ | ⟨eq, _⟩
    · subst eq
      obtain ⟨i, foundI, pathI, nodeI⟩ := opTarget_instance rfl target
      exact persist i (instance?_mem foundI) pathI nodeI
    · subst eq
      obtain ⟨i, foundI, pathI, nodeI⟩ := opTarget_instance rfl target
      exact persist i (instance?_mem foundI) pathI nodeI
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', _, hn, _, _, _, instances, _⟩ := effect_fireWaitAll s next P N executed
      exact appended _ instances rfl (getNode_id s P N n' hn)
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', _, _, _, hn, _, _, _, _, _, instances, _⟩ := effect_fireBranch s next P N arm executed
      exact appended _ instances rfl (getNode_id s P N n' hn)
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', _, _, hn, _, _, _, _, _, instances, _⟩ := effect_fireCoalesce s next P N e y safe.channelIds executed
      exact appended _ instances rfl (getNode_id s P N n' hn)
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', _, hn, _, _, _, _, _, instances, _⟩ := effect_fireCollect s next P N executed
      exact appended _ instances rfl (getNode_id s P N n' hn)
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', _, hn, _, _, _, controller, _⟩ := effect_fireFilter s next P N y k safe.channelIds executed
      rcases controller with ⟨old, foundOld, _⟩ | ⟨_, instances⟩
      · obtain ⟨memberOld, pathOld, nodeOld, _⟩ := nodeInstance?_mem foundOld
        exact persist old memberOld pathOld (nodeOld.trans (getNode_id s P N n' hn))
      · exact appended _ instances rfl (getNode_id s P N n' hn)
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', _, _, hn, _, _, _, _, _, controller, _⟩ := effect_fireMerge s next P N e y safe.channelIds executed
      rcases controller with ⟨old, foundOld, _⟩ | ⟨_, instances⟩
      · obtain ⟨memberOld, pathOld, nodeOld, _⟩ := nodeInstance?_mem foundOld
        exact persist old memberOld pathOld (nodeOld.trans (getNode_id s P N n' hn))
      · exact appended _ instances rfl (getNode_id s P N n' hn)
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', hn, _, _, _, _, _, _, view⟩ := effect_propagateEos s next P N executed
      exact absurd view (fun v => eosOnlyContra _ (eosWrites_eos P n') v)
    · subst eq
      obtain ⟨i, foundI, pathI, nodeI⟩ := opTarget_id rfl target
      exact persist i (instance?_mem foundI) pathI nodeI
    · subst eq
      obtain ⟨i, foundI, pathI, nodeI⟩ := opTarget_id rfl target
      exact persist i (instance?_mem foundI) pathI nodeI
    · subst eq
      simp only [transitionOrIdle] at executed
      obtain ⟨n', hn, _, _, _, _, _, _, view⟩ := effect_skip s next P N executed
      exact absurd view (fun v => eosOnlyContra _ (eosWrites_eos P n') v)

/-- An item on an output of `(P, N)` implies an instance of `(P, N)`. -/
theorem items_imply_instance (oracle : ScopedOracle) {s0 s : State} {ops : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s0 ops s)
    (safe0 : Invariants s0) (n : Node) (c0 : Channel) (found : s0.node? c0.path c0.edge.src.node = some n)
    (member0 : c0 ∈ s0.channels) (empty0 : c0.placed = []) (entry0 : c0.entry = false)
    (c : Channel) (memberC : c ∈ s.channels) (idC : c.id = c0.id) (x : ItemId) (present : x ∈ c.items) :
    ∃ j ∈ s.instances, j.path = c0.path ∧ j.node = c0.edge.src.node := by
  have presentTok : Token.item x ∈ c.placed := (Effects.item_mem c x).mp present
  have absent : Token.item x ∉ c0.placed := by rw [empty0]; simp
  obtain ⟨pre, op, post, t, t', d, d', _, head, allowed, accepted, rest, safeT, active,
    memberD, idD, _, absentD, memberD', idD', _, presentD', _, target⟩ :=
    token_step run safe0 (.item x) c0 member0 absent entry0 c memberC idC presentTok
  have nodeT := head.node c0.path c0.edge.src.node n found
  obtain ⟨j, memberJ, pathJ, nodeJ⟩ := item_write_instance t t' op safeT active accepted _ _ target n nodeT d memberD d' memberD'
    (idD'.trans idD.symm) x absentD presentD'
  have safeT' := preserves_invariants t t' op safeT accepted
  obtain ⟨k, memberK, bindK⟩ := rest.retains_binding safeT' j memberJ
  exact ⟨k, memberK, (Instance.binding_path bindK).trans pathJ, (Instance.binding_node bindK).trans nodeJ⟩

/-- Every instance after a step existed before (by id) or was created with trigger `none`,
    except children spawned for a forEach node. -/
theorem step_instances_origin (s next : State) (op : Op) (safe : Invariants s) (h : step s op = .ok next)
    (j : Instance) (memberJ : j ∈ next.instances) :
    (∃ k ∈ s.instances, k.id = j.id) ∨ j.trigger = none ∨
    (∃ path node item n body, op = .spawn path node item ∧ getNode s path node = .ok n ∧ n.kind = .forEach body ∧
      j = makeInstance path n .waitingInputs [("item", item)] (some item)) := by
  have distinct := safe.channelIds
  have ofSet : ∀ (a : State) (i : Instance), j ∈ (setInstance a i).instances → (∃ k ∈ a.instances, k.id = j.id) ∨ j = i := by
    intro a i mem
    rcases setInstance_mem a i j mem with eq | old
    · exact .inr eq
    · exact .inl ⟨j, old, rfl⟩
  have ofSame : ∀ (a : State), next.instances = a.instances → a = s → (∃ k ∈ s.instances, k.id = j.id) := by
    intro a same eq
    subst eq
    rw [same] at memberJ
    exact ⟨j, memberJ, rfl⟩
  have ofUpdate : ∀ (i : Instance), i ∈ s.instances → ∀ i', next.instances = (setInstance s i').instances → i'.id = i.id →
      (∃ k ∈ s.instances, k.id = j.id) := by
    intro i memberI i' same idI
    rw [same] at memberJ
    rcases ofSet s i' memberJ with old | eq
    · exact old
    · subst eq
      exact ⟨i, memberI, idI.symm⟩
  have ofAppend : ∀ (i : Instance), next.instances = s.instances ++ [i] → (∃ k ∈ s.instances, k.id = j.id) ∨ j = i := by
    intro i same
    rw [same] at memberJ
    rcases List.mem_append.mp memberJ with old | new
    · exact .inl ⟨j, old, rfl⟩
    · simp only [List.mem_singleton] at new
      exact .inr new
  rcases step_ok_cases s op next h with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst same; exact .inl ⟨j, memberJ, rfl⟩
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      rw [idleState_instances] at memberJ
      exact .inl ⟨j, memberJ, rfl⟩
    | start inputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, instances, _⟩ := effect_start s next inputs executed
      exact .inl (ofSame s instances rfl)
    | activate path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, inputs, _, _, ⟨_, _, _, _, instances, _⟩ | ⟨body, iteration, _, f, _, _, _, _, instances, _⟩⟩ :=
        effect_activate s next path node executed
      · rcases ofAppend _ instances with old | eq
        · exact .inl old
        · subst eq; exact .inr (.inl rfl)
      · rcases ofAppend _ instances with old | eq
        · exact .inl old
        · subst eq; exact .inr (.inl rfl)
    | spawn path node item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, body, c, hn, kind, _, _, f, _, _, _, _, instances, _⟩ := effect_spawn s next path node item distinct executed
      rcases ofAppend _ instances with old | eq
      · exact .inl old
      · exact .inr (.inr ⟨path, node, item, n, body, rfl, hn, kind, eq⟩)
    | claim auth worker =>
      simp only [transitionOrIdle] at executed
      simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
      cases found : s.instance? auth.instance with
      | none => simp [found] at executed
      | some i =>
        simp only [found] at executed
        cases hn : getNode s i.path i.node with
        | error e => simp [hn] at executed
        | ok n =>
          simp only [hn] at executed
          cases hl : leafPolicy n with
          | error e => simp [hl] at executed
          | ok policy =>
            rcases policy with ⟨r, concurrency⟩
            simp only [hl] at executed
            repeat (first | split at executed | contradiction)
            simp only [Except.ok.injEq] at executed
            subst executed
            exact .inl (ofUpdate i (instance?_mem found) _ rfl rfl)
    | renew auth =>
      simp only [transitionOrIdle] at executed
      simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
      cases found : s.instance? auth.instance with
      | none => simp [found] at executed
      | some i =>
        simp only [found] at executed
        cases hn : getNode s i.path i.node with
        | error e => simp [hn] at executed
        | ok n =>
          simp only [hn] at executed
          cases hl : leafPolicy n with
          | error e => simp [hl] at executed
          | ok policy =>
            rcases policy with ⟨r, concurrency⟩
            simp only [hl, Except.ok.injEq] at executed
            subst executed
            exact .inl (ofUpdate i (instance?_mem found) _ rfl rfl)
    | expireLease inst now =>
      simp only [transitionOrIdle] at executed
      simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
      cases found : s.instance? inst with
      | none => simp [found] at executed
      | some i =>
        simp only [found] at executed
        cases hn : getNode s i.path i.node with
        | error e => simp [hn] at executed
        | ok n =>
          simp only [hn] at executed
          split at executed
          · contradiction
          · obtain ⟨_, _, _, retry, retryAt, instances⟩ := expireOrFail_effect s next i n now _ _ _ executed
            exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
    | promoteRetry inst now =>
      simp only [transitionOrIdle] at executed
      simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
      cases found : s.instance? inst with
      | none => simp [found] at executed
      | some i =>
        simp only [found] at executed
        split at executed
        · contradiction
        · simp only [Except.ok.injEq] at executed
          subst executed
          exact .inl (ofUpdate i (instance?_mem found) _ rfl rfl)
    | fail auth code retryable =>
      simp only [transitionOrIdle] at executed
      simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at executed
      cases found : s.instance? auth.instance with
      | none => simp [found] at executed
      | some i =>
        simp only [found] at executed
        cases hn : getNode s i.path i.node with
        | error e => simp [hn] at executed
        | ok n =>
          simp only [hn] at executed
          obtain ⟨_, _, _, retry, retryAt, instances⟩ := expireOrFail_effect s next i n _ _ _ _ executed
          exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
    | emit auth port item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, _, instances, _⟩ := effect_emit s next auth port item executed
      exact .inl (ofSame s instances rfl)
    | complete auth outputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, found, _, _, _, _, instances, _⟩ := effect_complete s next auth outputs executed
      exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
    | fireWaitAll path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, instances, _⟩ := effect_fireWaitAll s next path node executed
      rcases ofAppend _ instances with old | eq
      · exact .inl old
      · subst eq; exact .inr (.inl rfl)
    | fireBranch path node arm =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, instances, _⟩ := effect_fireBranch s next path node arm executed
      rcases ofAppend _ instances with old | eq
      · exact .inl old
      · subst eq; exact .inr (.inl rfl)
    | fireCollect path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, _, _, instances, _⟩ := effect_fireCollect s next path node executed
      rcases ofAppend _ instances with old | eq
      · exact .inl old
      · subst eq; exact .inr (.inl rfl)
    | fireCoalesce path node edge item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, _, _, _, instances, _⟩ := effect_fireCoalesce s next path node edge item distinct executed
      rcases ofAppend _ instances with old | eq
      · exact .inl old
      · subst eq; exact .inr (.inl rfl)
    | fireFilter path node item keep =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, controller, _⟩ := effect_fireFilter s next path node item keep distinct executed
      rcases controller with ⟨_, _, instances⟩ | ⟨_, instances⟩
      · exact .inl (ofSame s instances rfl)
      · rcases ofAppend _ instances with old | eq
        · exact .inl old
        · subst eq; exact .inr (.inl rfl)
    | fireMerge path node edge item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, _, _, _, controller, _⟩ := effect_fireMerge s next path node edge item distinct executed
      rcases controller with ⟨_, _, instances⟩ | ⟨_, instances⟩
      · exact .inl (ofSame s instances rfl)
      · rcases ofAppend _ instances with old | eq
        · exact .inl old
        · subst eq; exact .inr (.inl rfl)
    | propagateEos path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, ⟨_, instances⟩ | ⟨old, foundOld, _, instances⟩, _⟩ := effect_propagateEos s next path node executed
      · rcases ofAppend _ instances with old | eq
        · exact .inl old
        · subst eq; exact .inr (.inl rfl)
      · exact .inl (ofUpdate old (nodeInstance?_mem foundOld).1 _ instances rfl)
    | finishSubworkflow inst =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, _, _, found, _, _, _, _, _, _, _, instances, _⟩ := effect_finishSubworkflow s next inst executed
      exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
    | loopIterate inst done =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, _, _, _, _, _, found, _, _, _, _, _, _, _,
        ⟨_, _, _, _, instances, _⟩ | ⟨_, _, _, instances, _, _⟩ | ⟨_, _, _, _, _, _, _, instances, _⟩⟩ :=
        effect_loopIterate s next inst done executed
      · exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
      · exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
      · exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
    | skip path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, instances, _⟩ := effect_skip s next path node executed
      rcases ofAppend _ instances with old | eq
      · exact .inl old
      · subst eq; exact .inr (.inl rfl)
    | cancel =>
      simp only [transitionOrIdle] at executed
      simp only [transition, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      simp only [List.mem_map] at memberJ
      obtain ⟨i, memberI, eq⟩ := memberJ
      refine .inl ⟨i, memberI, ?_⟩
      rw [← eq]
      split <;> rfl
    | manualRetry inst =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, found, _, _, ⟨_, _, _, _, instances⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, instances, _, _⟩⟩ :=
        effect_manualRetry s next inst executed
      · exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)
      · exact .inl (ofUpdate i (instance?_mem found) _ instances rfl)

end Suimon
