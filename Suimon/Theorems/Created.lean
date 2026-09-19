import Suimon.Theorems.FrameChannels

/-! Which operation created an instance, and with what fields. -/

namespace Suimon

/-- The instance `j` was appended by `op` at `s`, with the fields the operation assigns. -/
def CreatedBy (s : State) (op : Op) (j : Instance) : Prop :=
  (∃ P N n inputs, op = .activate P N ∧ getNode s P N = .ok n ∧ plainInputs s P n = .ok inputs ∧
      ((∃ r c, n.kind = .leaf r c ∧ j = makeInstance P n .ready inputs) ∨
       (∃ body iteration, ((n.kind = .subworkflow body ∧ iteration = 0) ∨ ∃ m, n.kind = .loop body m ∧ iteration = 1) ∧
          j = { makeInstance P n .waitingInputs inputs with iteration }))) ∨
  (∃ P N n inputs, op = .fireWaitAll P N ∧ getNode s P N = .ok n ∧ n.kind = .waitAll ∧
      plainInputs s P n = .ok inputs ∧ j = makeInstance P n .succeeded inputs) ∨
  (∃ P N arm n arms inputs, op = .fireBranch P N arm ∧ getNode s P N = .ok n ∧ n.kind = .branch arms ∧
      plainInputs s P n = .ok inputs ∧ j = makeInstance P n .succeeded inputs) ∨
  (∃ P N n c, op = .fireCollect P N ∧ getNode s P N = .ok n ∧ n.kind = .collect ∧ (s.incoming P N).head? = some c ∧
      j = makeInstance P n .succeeded ((sortedItems c.items).map ("item", ·))) ∨
  (∃ P N e x n c, op = .fireCoalesce P N e x ∧ getNode s P N = .ok n ∧ n.kind = .coalesce ∧
      (s.incoming P N).find? (·.id == e) = some c ∧ j = makeInstance P n .succeeded [(c.edge.dst.port, x)]) ∨
  (∃ P N n, ((∃ x k, op = .fireFilter P N x k ∧ n.kind = .filter) ∨ (∃ e x, op = .fireMerge P N e x ∧ n.kind = .merge)) ∧
      getNode s P N = .ok n ∧ j = makeInstance P n .waitingInputs) ∨
  (∃ P N n, op = .propagateEos P N ∧ getNode s P N = .ok n ∧
      (match n.kind with | .filter | .merge | .forEach _ => true | _ => false) = true ∧ j = makeInstance P n .succeeded) ∨
  (∃ P N n, op = .skip P N ∧ getNode s P N = .ok n ∧ j = makeInstance P n .cancelled) ∨
  (∃ P N x n body, op = .spawn P N x ∧ getNode s P N = .ok n ∧ n.kind = .forEach body ∧
      j = makeInstance P n .waitingInputs [("item", x)] (some x))

theorem step_instance_created (s next : State) (op : Op) (safe : Invariants s) (h : step s op = .ok next)
    (j : Instance) (memberJ : j ∈ next.instances) (absent : ∀ k ∈ s.instances, k.id ≠ j.id) :
    CreatedBy s op j := by
  have distinct := safe.channelIds
  have ofSet : ∀ (a : State) (i : Instance), j ∈ (setInstance a i).instances → (∃ k ∈ a.instances, k.id = j.id) ∨ j = i := by
    intro a i mem
    rcases setInstance_mem a i j mem with eq | old
    · exact .inr eq
    · exact .inl ⟨j, old, rfl⟩
  have ofSame : ∀ (a : State), next.instances = a.instances → a = s → False := by
    intro a same eq
    subst eq
    rw [same] at memberJ
    exact absent j memberJ rfl
  have ofUpdate : ∀ (i : Instance), i ∈ s.instances → ∀ i', next.instances = (setInstance s i').instances → i'.id = i.id → False := by
    intro i memberI i' same idI
    rw [same] at memberJ
    rcases ofSet s i' memberJ with ⟨k, memberK, idK⟩ | eq
    · exact absent k memberK idK
    · subst eq
      exact absent i memberI idI.symm
  have ofAppend : ∀ (i : Instance), next.instances = s.instances ++ [i] → j = i := by
    intro i same
    rw [same] at memberJ
    rcases List.mem_append.mp memberJ with old | new
    · exact absurd rfl (absent j old)
    · simpa using new
  rcases step_ok_cases s op next h with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst same; exact absurd rfl (absent j memberJ)
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      rw [idleState_instances] at memberJ
      exact absurd rfl (absent j memberJ)
    | start inputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, instances, _⟩ := effect_start s next inputs executed
      exact (ofSame s instances rfl).elim
    | activate path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, inputs, hn, hi, ⟨r, c, kind, _, instances, _⟩ | ⟨body, iteration, kinds, f, _, _, _, _, instances, _⟩⟩ :=
        effect_activate s next path node executed
      · exact .inl ⟨path, node, n, inputs, rfl, hn, hi, .inl ⟨r, c, kind, ofAppend _ instances⟩⟩
      · exact .inl ⟨path, node, n, inputs, rfl, hn, hi, .inr ⟨body, iteration, kinds, ofAppend _ instances⟩⟩
    | spawn path node item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, body, c, hn, kind, _, _, f, _, _, _, _, instances, _⟩ := effect_spawn s next path node item distinct executed
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨path, node, item, n, body, rfl, hn, kind, ofAppend _ instances⟩)))))))
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
            exact (ofUpdate i (instance?_mem found) _ rfl rfl).elim
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
            exact (ofUpdate i (instance?_mem found) _ rfl rfl).elim
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
            exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
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
          exact (ofUpdate i (instance?_mem found) _ rfl rfl).elim
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
          exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
    | emit auth port item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, _, instances, _⟩ := effect_emit s next auth port item executed
      exact (ofSame s instances rfl).elim
    | complete auth outputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, found, _, _, _, _, instances, _⟩ := effect_complete s next auth outputs executed
      exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
    | fireWaitAll path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, inputs, hn, kind, hi, _, instances, _⟩ := effect_fireWaitAll s next path node executed
      exact .inr (.inl ⟨path, node, n, inputs, rfl, hn, kind, hi, ofAppend _ instances⟩)
    | fireBranch path node arm =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, arms, inputs, item, hn, kind, _, hi, _, _, instances, _⟩ := effect_fireBranch s next path node arm executed
      exact .inr (.inr (.inl ⟨path, node, arm, n, arms, inputs, rfl, hn, kind, hi, ofAppend _ instances⟩))
    | fireCollect path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, c, hn, kind, hc, _, _, _, instances, _⟩ := effect_fireCollect s next path node executed
      exact .inr (.inr (.inr (.inl ⟨path, node, n, c, rfl, hn, kind, hc, ofAppend _ instances⟩)))
    | fireCoalesce path node edge item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, c, p0, hn, kind, hc, _, _, _, instances, _⟩ := effect_fireCoalesce s next path node edge item distinct executed
      exact .inr (.inr (.inr (.inr (.inl ⟨path, node, edge, item, n, c, rfl, hn, kind, hc, ofAppend _ instances⟩))))
    | fireFilter path node item keep =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, _, hn, kind, _, _, controller, _⟩ := effect_fireFilter s next path node item keep distinct executed
      rcases controller with ⟨_, _, instances⟩ | ⟨_, instances⟩
      · exact (ofSame s instances rfl).elim
      · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨path, node, n, .inl ⟨item, keep, rfl, kind⟩, hn, ofAppend _ instances⟩)))))
    | fireMerge path node edge item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, _, _, hn, kind, _, _, _, _, controller, _⟩ := effect_fireMerge s next path node edge item distinct executed
      rcases controller with ⟨_, _, instances⟩ | ⟨_, instances⟩
      · exact (ofSame s instances rfl).elim
      · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨path, node, n, .inr ⟨edge, item, rfl, kind⟩, hn, ofAppend _ instances⟩)))))
    | propagateEos path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, hn, kind, _, _, ⟨_, instances⟩ | ⟨old, foundOld, _, instances⟩, _⟩ := effect_propagateEos s next path node executed
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨path, node, n, rfl, hn, kind, ofAppend _ instances⟩))))))
      · exact (ofUpdate old (nodeInstance?_mem foundOld).1 _ instances rfl).elim
    | finishSubworkflow inst =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, _, _, found, _, _, _, _, _, _, _, instances, _⟩ := effect_finishSubworkflow s next inst executed
      exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
    | loopIterate inst done =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, _, _, _, _, _, found, _, _, _, _, _, _, _,
        ⟨_, _, _, _, instances, _⟩ | ⟨_, _, _, instances, _, _⟩ | ⟨_, _, _, _, _, _, _, instances, _⟩⟩ :=
        effect_loopIterate s next inst done executed
      · exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
      · exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
      · exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
    | skip path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, hn, _, _, _, instances, _⟩ := effect_skip s next path node executed
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨path, node, n, rfl, hn, ofAppend _ instances⟩)))))))
    | cancel =>
      simp only [transitionOrIdle] at executed
      simp only [transition, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      simp only [List.mem_map] at memberJ
      obtain ⟨i, memberI, eq⟩ := memberJ
      refine absurd ?_ (absent i memberI)
      rw [← eq]
      split <;> rfl
    | manualRetry inst =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, found, _, _, ⟨_, _, _, _, instances⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, instances, _, _⟩⟩ :=
        effect_manualRetry s next inst executed
      · exact (ofUpdate i (instance?_mem found) _ instances rfl).elim
      · exact (ofUpdate i (instance?_mem found) _ instances rfl).elim

/-- Every instance present at the end and absent at the start was created by some step,
    with its binding (node, path, trigger, inputs) preserved to the end. -/
theorem instance_created {allows : State → Op → Prop} {s0 last : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops last) (safe0 : Invariants s0)
    (i : Instance) (memberL : i ∈ last.instances) (absent0 : ∀ j ∈ s0.instances, j.id ≠ i.id) :
    ∃ pre op post s s' j, ops = pre ++ op :: post ∧
      ConformingSteps allows s0 pre s ∧ allows s op ∧ step s op = .ok s' ∧
      ConformingSteps allows s' post last ∧ Invariants s ∧ (∀ k ∈ s.instances, k.id ≠ j.id) ∧
      j ∈ s'.instances ∧ j.id = i.id ∧ j.binding = i.binding ∧ CreatedBy s op j := by
  obtain ⟨pre, op, post, s, s', j, split, head, allowed, accepted, rest, safeS, absentS, memberJ, idJ, bindJ⟩ :=
    instance_origin run safe0 i memberL absent0
  have absentJ : ∀ k ∈ s.instances, k.id ≠ j.id := fun k hk eq => absentS k hk (eq.trans idJ)
  exact ⟨pre, op, post, s, s', j, split, head, allowed, accepted, rest, safeS, absentJ, memberJ, idJ, bindJ,
    step_instance_created s s' op safeS accepted j memberJ absentJ⟩

/-- Status and iteration changes of a retained instance across one step. -/
def Evolution (s : State) (op : Op) (k j : Instance) : Prop :=
    (j.iteration = k.iteration ∨
      (j.iteration = k.iteration + 1 ∧ (k.status = .waitingInputs ∧ op = .loopIterate k.id false ∨ k.status = .failed ∧ op = .manualRetry k.id) ∧
        ∃ n body limit, getNode s k.path k.node = .ok n ∧ n.kind = .loop body limit)) ∧
    (j.status = k.status ∨
      (op = .cancel ∧ j.status = .cancelled) ∨
      (j.status = .succeeded ∧
        ((∃ auth outputs, op = .complete auth outputs ∧ ∃ n r c, getNode s k.path k.node = .ok n ∧ n.kind = .leaf r c) ∨
         op = .finishSubworkflow k.id ∨ op = .loopIterate k.id true ∨
         (op = .propagateEos k.path k.node ∧ k.trigger = none))) ∨
      (j.status = .failed ∧
        ((∃ n r c, getNode s k.path k.node = .ok n ∧ n.kind = .leaf r c) ∨ op = .loopIterate k.id false)) ∨
      j.status = .running ∨ j.status = .retryWait ∨ j.status = .ready ∨
      (j.status = .waitingInputs ∧ op = .manualRetry k.id))

theorem step_instance_evolves (s next : State) (op : Op) (safe : Invariants s) (h : step s op = .ok next)
    (k j : Instance) (memberK : k ∈ s.instances) (memberJ : j ∈ next.instances) (sameId : j.id = k.id) :
    Evolution s op k j := by
  have distinct := safe.channelIds
  have safeNext := preserves_invariants s next op safe h
  have idsS := safe.instanceIds
  have idsNext := safeNext.instanceIds
  -- the retained instance is `k` whenever it is an old element
  have old : ∀ a ∈ s.instances, a.id = j.id → a = k := fun a ha eq =>
    eq_of_mapped_nodup (·.id) s.instances idsS a k ha memberK (eq.trans sameId)
  have same : ∀ (a : State), next.instances = a.instances → a = s → j = k := by
    intro a eq' eq
    subst eq
    rw [eq'] at memberJ
    exact old j memberJ rfl
  have appended : ∀ (i : Instance), next.instances = s.instances ++ [i] → j = k := by
    intro i eq
    have memberK' : k ∈ next.instances := by rw [eq]; exact List.mem_append_left _ memberK
    exact eq_of_mapped_nodup (·.id) next.instances idsNext j k memberJ memberK' sameId
  have updated : ∀ (i i' : Instance), i ∈ s.instances → next.instances = (setInstance s i').instances → i'.id = i.id →
      (j = k ∨ (j = i' ∧ i = k)) := by
    intro i i' memberI eq idI
    rw [eq] at memberJ
    rcases setInstance_mem s i' j memberJ with eq' | oldJ
    · subst eq'
      exact .inr ⟨rfl, old i memberI idI.symm⟩
    · exact .inl (old j oldJ rfl)
  have trivial : j = k → Evolution s op k j := fun eq => by subst eq; exact ⟨.inl rfl, .inl rfl⟩
  unfold Evolution
  rcases step_ok_cases s op next h with ⟨_, eq⟩ | ⟨_, _, prepared, _, _⟩
  · subst eq; exact trivial (old j memberJ rfl)
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      rw [idleState_instances] at memberJ
      exact trivial (old j memberJ rfl)
    | start inputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, instances, _⟩ := effect_start s next inputs executed
      exact trivial (same s instances rfl)
    | activate path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, inputs, hn, hi, ⟨r, c, kind, _, instances, _⟩ | ⟨body, iteration, kinds, f, _, _, _, _, instances, _⟩⟩ :=
        effect_activate s next path node executed
      · exact trivial (appended _ instances)
      · exact trivial (appended _ instances)
    | spawn path node item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, body, c, hn, kind, _, _, f, _, _, _, _, instances, _⟩ := effect_spawn s next path node item distinct executed
      exact trivial (appended _ instances)
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
            rcases updated i _ (instance?_mem found) rfl rfl with eq | ⟨eq, ik⟩
            · exact trivial eq
            · subst eq; subst k
              exact ⟨.inl rfl, .inr (.inr (.inr (.inr (.inl rfl))))⟩
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
            rcases updated i _ (instance?_mem found) rfl rfl with eq | ⟨eq, ik⟩
            · exact trivial eq
            · subst eq; subst k
              exact ⟨.inl rfl, .inl rfl⟩
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
          · have leaf : ∃ r c, n.kind = .leaf r c := by
              unfold expireOrFail at executed
              simp only [bind, Except.bind] at executed
              cases hl : leafPolicy n with
              | error e => simp [hl] at executed
              | ok policy => exact leafPolicy_kind n policy hl
            obtain ⟨_, _, _, retry, retryAt, instances⟩ := expireOrFail_effect s next i n now _ _ _ executed
            rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
            · exact trivial eq
            · subst eq; subst k
              refine ⟨.inl rfl, ?_⟩
              cases retry
              · exact .inr (.inr (.inr (.inl ⟨rfl, .inl ⟨n, leaf.choose, leaf.choose_spec.choose, hn, leaf.choose_spec.choose_spec⟩⟩)))
              · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
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
          rcases updated i _ (instance?_mem found) rfl rfl with eq | ⟨eq, ik⟩
          · exact trivial eq
          · subst eq; subst k
            exact ⟨.inl rfl, .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))⟩
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
          have leaf : ∃ r c, n.kind = .leaf r c := by
            unfold expireOrFail at executed
            simp only [bind, Except.bind] at executed
            cases hl : leafPolicy n with
            | error e => simp [hl] at executed
            | ok policy => exact leafPolicy_kind n policy hl
          obtain ⟨_, _, _, retry, retryAt, instances⟩ := expireOrFail_effect s next i n _ _ _ _ executed
          rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
          · exact trivial eq
          · subst eq; subst k
            refine ⟨.inl rfl, ?_⟩
            cases retry
            · exact .inr (.inr (.inr (.inl ⟨rfl, .inl ⟨n, leaf.choose, leaf.choose_spec.choose, hn, leaf.choose_spec.choose_spec⟩⟩)))
            · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
    | emit auth port item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, _, _, _, _, _, _, instances, _⟩ := effect_emit s next auth port item executed
      exact trivial (same s instances rfl)
    | complete auth outputs =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, n, found, hn, leaf, _, _, instances, _⟩ := effect_complete s next auth outputs executed
      rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
      · exact trivial eq
      · subst eq; subst k
        exact ⟨.inl rfl, .inr (.inr (.inl ⟨rfl, .inl ⟨auth, outputs, rfl, n, leaf.choose, leaf.choose_spec.choose, hn, leaf.choose_spec.choose_spec⟩⟩))⟩
    | fireWaitAll path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, inputs, hn, kind, hi, _, instances, _⟩ := effect_fireWaitAll s next path node executed
      exact trivial (appended _ instances)
    | fireBranch path node arm =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, arms, inputs, item, hn, kind, _, hi, _, _, instances, _⟩ := effect_fireBranch s next path node arm executed
      exact trivial (appended _ instances)
    | fireCollect path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, c, hn, kind, hc, _, _, _, instances, _⟩ := effect_fireCollect s next path node executed
      exact trivial (appended _ instances)
    | fireCoalesce path node edge item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, c, p0, hn, kind, hc, _, _, _, instances, _⟩ := effect_fireCoalesce s next path node edge item distinct executed
      exact trivial (appended _ instances)
    | fireFilter path node item keep =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, _, hn, _, _, _, controller, _⟩ := effect_fireFilter s next path node item keep distinct executed
      rcases controller with ⟨_, _, instances⟩ | ⟨_, instances⟩
      · exact trivial (same s instances rfl)
      · exact trivial (appended _ instances)
    | fireMerge path node edge item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, _, _, hn, _, _, _, _, _, controller, _⟩ := effect_fireMerge s next path node edge item distinct executed
      rcases controller with ⟨_, _, instances⟩ | ⟨_, instances⟩
      · exact trivial (same s instances rfl)
      · exact trivial (appended _ instances)
    | propagateEos path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, hn, _, _, _, ⟨_, instances⟩ | ⟨old', foundOld, _, instances⟩, _⟩ := effect_propagateEos s next path node executed
      · exact trivial (appended _ instances)
      · obtain ⟨memberOld, pathOld, nodeOld, triggerOld⟩ := nodeInstance?_mem foundOld
        rcases updated old' _ memberOld instances rfl with eq | ⟨eq, ik⟩
        · exact trivial eq
        · subst eq; subst k
          exact ⟨.inl rfl, .inr (.inr (.inl ⟨rfl, .inr (.inr (.inr ⟨by rw [pathOld, nodeOld], triggerOld⟩))⟩))⟩
    | finishSubworkflow inst =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, _, _, found, _, _, _, _, _, _, _, instances, _⟩ := effect_finishSubworkflow s next inst executed
      rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
      · exact trivial eq
      · subst eq; subst k
        have idI : inst = i.id := (instance?_id found).symm
        subst idI
        exact ⟨.inl rfl, .inr (.inr (.inl ⟨rfl, .inr (.inl rfl)⟩))⟩
    | loopIterate inst done =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, n, body, limit, f, items, item, found, waiting, hn, kind, _, _, _, _,
        ⟨hd, _, _, _, instances, _⟩ | ⟨hd, _, _, instances, _, _⟩ | ⟨hd, _, f', _, _, _, _, instances, _⟩⟩ :=
        effect_loopIterate s next inst done executed
      · rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
        · exact trivial eq
        · subst eq; subst k
          have idI : inst = i.id := (instance?_id found).symm
          subst idI; subst hd
          exact ⟨.inl rfl, .inr (.inr (.inl ⟨rfl, .inr (.inr (.inl rfl))⟩))⟩
      · rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
        · exact trivial eq
        · subst eq; subst k
          have idI : inst = i.id := (instance?_id found).symm
          subst idI; subst hd
          exact ⟨.inl rfl, .inr (.inr (.inr (.inl ⟨rfl, .inr rfl⟩)))⟩
      · rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
        · exact trivial eq
        · subst eq; subst k
          have idI : inst = i.id := (instance?_id found).symm
          subst idI; subst hd
          exact ⟨.inr ⟨rfl, .inl ⟨waiting, rfl⟩, n, body, limit, hn, kind⟩, .inl rfl⟩
    | skip path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨n, hn, _, _, _, instances, _⟩ := effect_skip s next path node executed
      exact trivial (appended _ instances)
    | cancel =>
      simp only [transitionOrIdle] at executed
      simp only [transition, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      simp only [List.mem_map] at memberJ
      obtain ⟨i, memberI, eq⟩ := memberJ
      have ik : i = k := by
        apply old i memberI
        rw [← eq]
        split <;> rfl
      subst ik
      rw [← eq]
      split
      · exact ⟨.inl rfl, .inl rfl⟩
      · exact ⟨.inl rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
    | manualRetry inst =>
      simp only [transitionOrIdle] at executed
      obtain ⟨i, _, found, failed, hn, ⟨r, c, leaf, _, instances⟩ | ⟨body, limit, f, items, kind, _, _, _, f', _, _, _, _, instances, _, _⟩⟩ :=
        effect_manualRetry s next inst executed
      · rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
        · exact trivial eq
        · subst eq; subst k
          exact ⟨.inl rfl, .inr (.inr (.inr (.inr (.inr (.inl rfl)))))⟩
      · rcases updated i _ (instance?_mem found) instances rfl with eq | ⟨eq, ik⟩
        · exact trivial eq
        · subst eq; subst k
          have idI : inst = i.id := (instance?_id found).symm
          subst idI
          exact ⟨.inr ⟨rfl, .inr ⟨failed, rfl⟩, _, body, limit, hn, kind⟩, .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))))⟩

/-- Every instance's node resolves (from `loopBoundsOK`). -/
theorem Invariants.instance_node {s : State} (safe : Invariants s) (i : Instance) (member : i ∈ s.instances) :
    ∃ n, s.node? i.path i.node = some n := by
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  have bounds := List.all_eq_true.mp safe.2 i member
  cases found : s.node? i.path i.node with
  | none => rw [found] at bounds; simp at bounds
  | some n => exact ⟨n, rfl⟩

/-- Iterations never decrease along a run, and stay fixed for non-loop nodes. -/
theorem ConformingSteps.iteration_evolves {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (k : Instance) (memberK : k ∈ s.instances)
    (j : Instance) (memberJ : j ∈ last.instances) (sameId : j.id = k.id) :
    k.iteration ≤ j.iteration ∧
    ((∀ n body limit, s.node? k.path k.node = some n → n.kind ≠ .loop body limit) → j.iteration = k.iteration) := by
  induction run generalizing k with
  | nil =>
    have same : j = k := eq_of_mapped_nodup (·.id) _ safe.instanceIds j k memberJ memberK sameId
    subst same
    exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid := preserves_invariants s middle op safe accepted
    obtain ⟨m, memberM, bindM⟩ := (ConformingSteps.cons allowed accepted (.nil middle)).retains_binding safe k memberK
    have idM : m.id = k.id := congrArg Prod.fst bindM
    have evolved := (step_instance_evolves s middle op safe accepted k m memberK memberM idM).1
    obtain ⟨le, fixed⟩ := ih safeMid m memberM memberJ (sameId.trans idM.symm)
    have pathM : m.path = k.path := Instance.binding_path bindM
    have nodeM : m.node = k.node := Instance.binding_node bindM
    refine ⟨?_, ?_⟩
    · rcases evolved with eq | ⟨eq, _, _⟩ <;> omega
    · intro notLoop
      have notLoopMid : ∀ n body limit, middle.node? m.path m.node = some n → n.kind ≠ .loop body limit := by
        intro n body limit found
        rw [pathM, nodeM] at found
        obtain ⟨n0, found0⟩ := safe.instance_node k memberK
        have kept := retained_node s middle _ _ n0 (step_frameDefinitions s middle op accepted) found0
        rw [kept] at found
        have same : n0 = n := Option.some.inj found
        subst same
        exact notLoop n0 body limit found0
      rcases evolved with eq | ⟨_, _, n, body, limit, hn, kind⟩
      · rw [fixed notLoopMid, eq]
      · exact absurd kind (notLoop n body limit (getNode_node? s _ _ n hn))

/-- The first step at which a retained instance starts satisfying `P`. -/
theorem ConformingSteps.reached {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (P : Instance → Prop)
    (k : Instance) (memberK : k ∈ s.instances) (before : ¬ P k)
    (j : Instance) (memberJ : j ∈ last.instances) (sameId : j.id = k.id) (after : P j) :
    ∃ pre op post t t' a b, ops = pre ++ op :: post ∧
      ConformingSteps allows s pre t ∧ allows t op ∧ step t op = .ok t' ∧ ConformingSteps allows t' post last ∧
      Invariants t ∧ a ∈ t.instances ∧ b ∈ t'.instances ∧ a.id = k.id ∧ b.id = k.id ∧ a.binding = k.binding ∧
      ¬ P a ∧ P b ∧ Evolution t op a b := by
  induction run generalizing k with
  | nil =>
    have same : j = k := eq_of_mapped_nodup (·.id) _ safe.instanceIds j k memberJ memberK sameId
    subst same
    exact absurd after before
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid := preserves_invariants s middle op safe accepted
    obtain ⟨m, memberM, bindM⟩ := (ConformingSteps.cons allowed accepted (.nil middle)).retains_binding safe k memberK
    have idM : m.id = k.id := congrArg Prod.fst bindM
    by_cases now : P m
    · exact ⟨[], op, ops, s, middle, k, m, rfl, .nil s, allowed, accepted, tail, safe, memberK, memberM, rfl, idM, rfl,
        before, now, step_instance_evolves s middle op safe accepted k m memberK memberM idM⟩
    · obtain ⟨pre, op', post, t, t', a, b, split, head, allowed', accepted', rest, safeT, memberA, memberB, idA, idB,
        bindA, notA, yesB, evolved⟩ := ih safeMid m memberM now memberJ (sameId.trans idM.symm)
      exact ⟨op :: pre, op', post, t, t', a, b, by simp [split], .cons allowed accepted head, allowed', accepted', rest,
        safeT, memberA, memberB, idA.trans idM, idB.trans idM, bindA.trans bindM, notA, yesB, evolved⟩

/-- A succeeded instance keeps its iteration. -/
theorem ConformingSteps.iteration_of_succeeded {allows : State → Op → Prop} {s last : State} {ops : List Op}
    (run : ConformingSteps allows s ops last) (safe : Invariants s) (k : Instance) (memberK : k ∈ s.instances)
    (done : k.status = .succeeded) (j : Instance) (memberJ : j ∈ last.instances) (sameId : j.id = k.id) :
    j.iteration = k.iteration := by
  induction run generalizing k with
  | nil =>
    have same : j = k := eq_of_mapped_nodup (·.id) _ safe.instanceIds j k memberJ memberK sameId
    subst same
    rfl
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid := preserves_invariants s middle op safe accepted
    obtain ⟨m, memberM, bindM⟩ := (ConformingSteps.cons allowed accepted (.nil middle)).retains_binding safe k memberK
    have idM : m.id = k.id := congrArg Prod.fst bindM
    have evolved := (step_instance_evolves s middle op safe accepted k m memberK memberM idM).1
    obtain ⟨m', memberM', idM', statusM'⟩ := (ConformingSteps.cons allowed accepted (.nil middle)).retains_status safe k memberK (.inl done)
    have same : m' = m := eq_of_mapped_nodup (·.id) _ safeMid.instanceIds m' m memberM' memberM (idM'.trans idM.symm)
    subst same
    have doneM : m'.status = .succeeded := statusM'.trans done
    rcases evolved with eq | ⟨_, ⟨w, _⟩ | ⟨f, _⟩, _⟩
    · rw [ih safeMid m' memberM' doneM memberJ (sameId.trans idM.symm), eq]
    · rw [done] at w; cases w
    · rw [done] at f; cases f

end Suimon
