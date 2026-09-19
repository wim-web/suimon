import Suimon.Theorems.Helpers

/-! Exact effects of each operation (part 1: start, containers, leaf ops, plain controls). -/

namespace Suimon
open Effects

/-- Consumption records appended by an operation, attributed to `who` on `chans`. -/
def RecordsBy (s next : State) (who : InstanceId) (chans : List String) : Prop :=
  ∃ rs, next.consumed = s.consumed ++ rs ∧ ∀ r ∈ rs, r.byInstance = who ∧ r.channel ∈ chans

theorem ConsumeEffect.records {who : InstanceId} {chans : List String} {a b : State}
    (h : ConsumeEffect who chans a b) : RecordsBy a b who chans := h.2.2.2.2

/-- Fields of the frame opened for `owner` with body `body`, without exposing `definition`. -/
def OpenedFrame (owner : Instance) (body : Graph) (f : Frame) : Prop :=
  f.path = owner.path ++ [identity [owner.id, toString owner.iteration]] ∧ f.graph = body ∧
  f.owner = some owner.id ∧ f.closed = false

theorem childFrame_opened (s : State) (owner : Instance) (body : Graph) :
    OpenedFrame owner body (childFrame s owner body) := ⟨rfl, rfl, rfl, rfl⟩

theorem effect_start (s next : State) (inputs : List Input)
    (h : transition s (.start inputs) = .ok next) :
    s.started = false ∧ s.instances = [] ∧
    (∃ f, s.frame? [] = some f ∧ (unique (inputs.map (·.entry)) && inputs.length == f.graph.entries.length &&
      inputs.all (fun i => f.graph.entries.contains i.entry)) = true) ∧
    next.placedView = (applyWrites (rootWrites inputs) s).placedView ∧
    next.instances = s.instances ∧ next.frames = s.frames ∧ next.consumed = s.consumed ∧
    next.started = true := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i u ready
    have cond := require_ok _ _ _ u ready
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at cond
    cases hf : s.frame? [] with
    | none => simp [hf] at h
    | some f =>
      simp only [hf] at h
      split at h
      · contradiction
      · rename_i u2 entries
        have cond2 := require_ok _ _ _ u2 entries
        split at h
        · contradiction
        · rename_i s1 started
          have value := startInputs_writes s s1 inputs started
          simp only [Except.ok.injEq] at h
          subst h
          subst value
          refine ⟨cond.1, cond.2, ⟨f, rfl, cond2⟩, ?_, ?_, ?_, ?_, rfl⟩
          · rfl
          · exact applyWrites_instances _ _
          · exact applyWrites_frames _ _
          · exact applyWrites_consumed _ _

theorem effect_activate (s next : State) (path : Path) (node : NodeId)
    (h : transition s (.activate path node) = .ok next) :
    s.started = true ∧ ∃ n inputs, getNode s path node = .ok n ∧ plainInputs s path n = .ok inputs ∧
    ((∃ r c, n.kind = .leaf r c ∧
        let i := makeInstance path n .ready inputs
        next.placedView = s.placedView ∧ next.instances = s.instances ++ [i] ∧ next.frames = s.frames ∧
        RecordsBy s next i.id ((s.incoming path node).map (·.id))) ∨
      (∃ body iteration, ((n.kind = .subworkflow body ∧ iteration = 0) ∨ (∃ m, n.kind = .loop body m ∧ iteration = 1)) ∧
        let i := { makeInstance path n .waitingInputs inputs with iteration }
        ∃ f, OpenedFrame i body f ∧ s.frame? f.path = none ∧ (inputs.map (·.2)).length = body.entries.length ∧
          next.placedView = (applyWrites (seedWrites f.path body.entries (inputs.map (·.2)))
            { s with channels := s.channels ++ f.channels }).placedView ∧
          next.instances = s.instances ++ [i] ∧ next.frames = s.frames ++ [f] ∧
          RecordsBy s next i.id ((s.incoming path node).map (·.id)))) := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i u started
    have startedTrue := require_ok _ _ _ u started
    refine ⟨startedTrue, ?_⟩
    cases hn : getNode s path node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      split at h
      · contradiction
      · rename_i inputs plain
        refine ⟨n, inputs, rfl, plain, ?_⟩
        split at h
        · -- leaf
          rename_i r c kind
          split at h
          · contradiction
          · rename_i s1 created
            have value := freshInstance_value s s1 _ created
            subst value
            have effect := consumeInputs_effect _ next path node _ h
            obtain ⟨v, inst, fr, _, rs, log, all⟩ := effect
            refine .inl ⟨r, c, kind, ?_, ?_, ?_, rs, log, ?_⟩
            · simpa [State.placedView] using v
            · simpa using inst
            · simpa using fr
            · intro x hx; simpa [State.incoming] using all x hx
        · -- subworkflow
          rename_i body kind
          simp only [kind] at h
          split at h
          · contradiction
          · rename_i s1 created
            have value := freshInstance_value s s1 _ created
            subst value
            split at h
            · contradiction
            · rename_i s2 consumed
              have effect := consumeInputs_effect _ s2 path node _ consumed
              obtain ⟨v, inst, fr, _, rs, log, all⟩ := effect
              have added := addFrame_effect s2 next _ body _ h
              obtain ⟨none, arity, view, frames, instances, consumedEq, _⟩ := added
              refine .inr ⟨body, 0, .inl ⟨kind, rfl⟩, childFrame s2 _ body, childFrame_opened s2 _ body, ?_, arity, ?_, ?_, ?_, rs, ?_, ?_⟩
              · simpa [State.frame?, fr] using none
              · rw [view]
                apply applyWrites_placedView
                simpa [State.placedView] using v
              · rw [instances, inst]
              · rw [frames, fr]
              · rw [consumedEq, log]
              · intro x hx; simpa [State.incoming] using all x hx
        · -- loop
          rename_i body m kind
          simp only [kind] at h
          split at h
          · contradiction
          · rename_i s1 created
            have value := freshInstance_value s s1 _ created
            subst value
            split at h
            · contradiction
            · rename_i s2 consumed
              have effect := consumeInputs_effect _ s2 path node _ consumed
              obtain ⟨v, inst, fr, _, rs, log, all⟩ := effect
              have added := addFrame_effect s2 next _ body _ h
              obtain ⟨none, arity, view, frames, instances, consumedEq, _⟩ := added
              refine .inr ⟨body, 1, .inr ⟨m, kind, rfl⟩, childFrame s2 _ body, childFrame_opened s2 _ body, ?_, arity, ?_, ?_, ?_, rs, ?_, ?_⟩
              · simpa [State.frame?, fr] using none
              · rw [view]
                apply applyWrites_placedView
                simpa [State.placedView] using v
              · rw [instances, inst]
              · rw [frames, fr]
              · rw [consumedEq, log]
              · intro x hx; simpa [State.incoming] using all x hx
        · contradiction


theorem effect_spawn (s next : State) (path : Path) (node : NodeId) (item : ItemId)
    (distinct : (s.channels.map (·.id)).Nodup)
    (h : transition s (.spawn path node item) = .ok next) :
    s.started = true ∧ ∃ n body c, getNode s path node = .ok n ∧ n.kind = .forEach body ∧
      (s.incoming path node).head? = some c ∧ c.pending.head? = some (.item item) ∧
      let i := makeInstance path n .waitingInputs [("item", item)] (some item)
      ∃ f, OpenedFrame i body f ∧ s.frame? f.path = none ∧ 1 = body.entries.length ∧
        next.placedView = (applyWrites (seedWrites f.path body.entries [item])
          { s with channels := s.channels ++ f.channels }).placedView ∧
        next.instances = s.instances ++ [i] ∧ next.frames = s.frames ++ [f] ∧
        next.consumed = s.consumed ++ [{ channel := c.id, index := c.consumed, item, byInstance := i.id }] := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i u started
    have startedTrue := require_ok _ _ _ u started
    refine ⟨startedTrue, ?_⟩
    cases hn : getNode s path node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      split at h
      · rename_i body kind
        cases hc : (s.incoming path node).head? with
        | none => simp [hc] at h
        | some c =>
          simp only [hc] at h
          split at h
          · contradiction
          · rename_i s1 created
            have value := freshInstance_value s s1 _ created
            subst value
            split at h
            · contradiction
            · rename_i s2 consumed
              have effect := consume_effect _ s2 c.id _ (some item) consumed
              obtain ⟨v, inst, fr, _, _⟩ := effect
              obtain ⟨c', memberC', idC', headC', log⟩ := consume_item_receipt _ s2 c.id _ item consumed
              have sameC : c' = c := by
                have memberC : c ∈ s.channels := (List.mem_filter.mp (List.mem_of_mem_head? hc)).1
                have memberC'' : c' ∈ s.channels := by simpa using memberC'
                exact eq_of_mapped_nodup (·.id) s.channels distinct c' c memberC'' memberC idC'
              have added := addFrame_effect s2 next _ body [item] h
              obtain ⟨none, arity, view, frames, instances, consumedEq, _⟩ := added
              refine ⟨n, body, c, rfl, kind, rfl, ?_, childFrame s2 _ body, childFrame_opened s2 _ body, ?_, arity, ?_, ?_, ?_, ?_⟩
              · rw [← sameC]; exact headC'
              · simpa [State.frame?, fr] using none
              · rw [view]
                apply applyWrites_placedView
                simpa [State.placedView] using v
              · rw [instances, inst]
              · rw [frames, fr]
              · rw [consumedEq, log, sameC]
      · contradiction


/-! ### Instance bookkeeping -/

/-- No instance becomes succeeded that was not already succeeded. -/
def NoNewSuccess (before after : List Instance) : Prop :=
  ∀ j ∈ after, j.status = .succeeded → ∃ i ∈ before, i.id = j.id ∧ i.status = .succeeded

theorem setInstance_mem (s : State) (j k : Instance) (member : k ∈ (setInstance s j).instances) :
    k = j ∨ k ∈ s.instances := by
  simp only [setInstance, List.mem_map] at member
  obtain ⟨i, hi, eq⟩ := member
  split at eq
  · exact .inl eq.symm
  · exact .inr (eq ▸ hi)

theorem noNewSuccess_setInstance (s : State) (i j : Instance) (member : i ∈ s.instances)
    (idEq : j.id = i.id) (statusLe : j.status = .succeeded → i.status = .succeeded) :
    NoNewSuccess s.instances (setInstance s j).instances := by
  intro k inNext done
  rcases setInstance_mem s j k inNext with rfl | old
  · exact ⟨i, member, idEq.symm, statusLe done⟩
  · exact ⟨k, old, rfl, done⟩

theorem NoNewSuccess.refl (xs : List Instance) : NoNewSuccess xs xs :=
  fun j member done => ⟨j, member, rfl, done⟩

theorem instance?_mem {s : State} {id : InstanceId} {i : Instance} (found : s.instance? id = some i) :
    i ∈ s.instances := List.mem_of_find?_eq_some found

theorem instance?_id {s : State} {id : InstanceId} {i : Instance} (found : s.instance? id = some i) :
    i.id = id := by simpa using List.find?_some found

/-! ### Lease and retry bookkeeping -/

/-- Data-plane fields are untouched and no instance newly succeeds. -/
def AdminEffect (s next : State) : Prop :=
  next.channels = s.channels ∧ next.frames = s.frames ∧ next.consumed = s.consumed ∧
  NoNewSuccess s.instances next.instances

theorem effect_claim (s next : State) (auth : Credentials) (worker : String)
    (h : transition s (.claim auth worker) = .ok next) : AdminEffect s next := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? auth.instance with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    cases hn : getNode s i.path i.node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      cases hl : leafPolicy n with
      | error e => simp [hl] at h
      | ok policy =>
        rcases policy with ⟨r, concurrency⟩
        simp only [hl] at h
        repeat (first | split at h | contradiction)
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨rfl, rfl, rfl, ?_⟩
        exact noNewSuccess_setInstance s i _ (instance?_mem found) rfl (fun done => by simp at done)

theorem effect_renew (s next : State) (auth : Credentials)
    (h : transition s (.renew auth) = .ok next) : AdminEffect s next := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? auth.instance with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    cases hn : getNode s i.path i.node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      cases hl : leafPolicy n with
      | error e => simp [hl] at h
      | ok policy =>
        rcases policy with ⟨r, concurrency⟩
        simp only [hl, Except.ok.injEq] at h
        subst h
        refine ⟨rfl, rfl, rfl, ?_⟩
        exact noNewSuccess_setInstance s i _ (instance?_mem found) rfl (fun done => done)

theorem effect_expireLease (s next : State) (inst : InstanceId) (now : Time)
    (h : transition s (.expireLease inst now) = .ok next) : AdminEffect s next := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? inst with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    cases hn : getNode s i.path i.node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      split at h
      · contradiction
      · obtain ⟨channels, frames, consumed, retry, retryAt, instances⟩ := expireOrFail_effect s next i n now _ _ _ h
        refine ⟨channels, frames, consumed, ?_⟩
        rw [instances]
        exact noNewSuccess_setInstance s i _ (instance?_mem found) rfl (fun done => by
          cases retry <;> simp at done)

theorem effect_promoteRetry (s next : State) (inst : InstanceId) (now : Time)
    (h : transition s (.promoteRetry inst now) = .ok next) : AdminEffect s next := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? inst with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    split at h
    · contradiction
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨rfl, rfl, rfl, ?_⟩
      exact noNewSuccess_setInstance s i _ (instance?_mem found) rfl (fun done => by simp at done)

theorem effect_fail (s next : State) (auth : Credentials) (code : String) (retryable : Bool)
    (h : transition s (.fail auth code retryable) = .ok next) : AdminEffect s next := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? auth.instance with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    cases hn : getNode s i.path i.node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      obtain ⟨channels, frames, consumed, retry, retryAt, instances⟩ := expireOrFail_effect s next i n _ _ _ _ h
      refine ⟨channels, frames, consumed, ?_⟩
      rw [instances]
      exact noNewSuccess_setInstance s i _ (instance?_mem found) rfl (fun done => by
        cases retry <;> simp at done)

/-! ### Leaf data operations -/

theorem leafPolicy_kind (n : Node) (policy : RetryPolicy × Nat) (h : leafPolicy n = .ok policy) :
    ∃ r c, n.kind = .leaf r c := by
  unfold leafPolicy at h
  split at h
  · rename_i r c kind; exact ⟨r, c, kind⟩
  · contradiction

theorem effect_emit (s next : State) (auth : Credentials) (port : PortName) (item : ItemId)
    (h : transition s (.emit auth port item) = .ok next) :
    ∃ i n, s.instance? auth.instance = some i ∧ getNode s i.path i.node = .ok n ∧
      (∃ r c, n.kind = .leaf r c) ∧
      n.outputs.any (fun p => p.name == port && p.kind == .stream) = true ∧
      next.placedView = (applyWrites [.out i.path i.node port (.item item)] s).placedView ∧
      next.instances = s.instances ∧ next.frames = s.frames ∧ next.consumed = s.consumed := by
  simp only [transition, getInstance, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases found : s.instance? auth.instance with
  | none => simp [found] at h
  | some i =>
    simp only [found] at h
    cases hn : getNode s i.path i.node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      cases hl : leafPolicy n with
      | error e => simp [hl] at h
      | ok policy =>
      simp only [hl] at h
      have leafKind := leafPolicy_kind n policy hl
      split at h
      · contradiction
      · rename_i u hr
        have cond := require_ok _ _ _ u hr
        split at h
        · contradiction
        · rename_i s1 placed
          have value := putOutput_value s s1 _ _ _ _ placed
          simp only [Except.ok.injEq] at h
          subst h
          subst value
          exact ⟨i, n, rfl, hn, leafKind, cond, rfl, rfl, rfl, rfl⟩

theorem effect_complete (s next : State) (auth : Credentials) (outputs : List Output)
    (h : transition s (.complete auth outputs) = .ok next) :
    ∃ i n, s.instance? auth.instance = some i ∧ getNode s i.path i.node = .ok n ∧
      (∃ r c, n.kind = .leaf r c) ∧
      (unique (outputs.map (·.port)) && outputs.length == (n.outputs.filter (·.kind == .plain)).length &&
        outputs.all (fun o => o.items.length == 1 &&
          (n.outputs.filter (·.kind == .plain)).any (·.name == o.port))) = true ∧
      next.placedView = (applyWrites (outputWrites i.path i.node outputs ++ eosWrites i.path n) s).placedView ∧
      next.instances = (setInstance s { i with status := .succeeded, lease := none }).instances ∧
      next.frames = s.frames ∧ next.consumed = s.consumed := by
  cases found : s.instance? auth.instance with
  | none => simp [transition, getInstance, found, Option.toExcept, bind, Except.bind] at h
  | some i =>
    cases hn : getNode s i.path i.node with
    | error e => simp [transition, getInstance, found, hn, Option.toExcept, bind, Except.bind] at h
    | ok n =>
      obtain ⟨checked, s1, s2, s3, hd, hp, hc, channels⟩ := complete_transition_shape s next auth outputs i n found hn h
      have leafKind : ∃ r c, n.kind = .leaf r c := by
        simp only [transition, getInstance, found, hn, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
        cases hl : leafPolicy n with
        | error e => simp [hl] at h
        | ok policy =>
          unfold leafPolicy at hl
          split at hl
          · rename_i r c kind; exact ⟨r, c, kind⟩
          · contradiction
      obtain ⟨dch, dinst, dfr, dcons, _⟩ := decision_value s s1 _ _ hd
      have p2 := placeOutputs_writes s1 s2 _ _ _ hp
      have p3 := closeOutputs_writes s2 s3 _ _ hc
      subst p2 p3
      -- instances / frames / consumed of `next` from the tail of the body
      have tail : next.instances = (setInstance s { i with status := .succeeded, lease := none }).instances ∧
          next.frames = s.frames ∧ next.consumed = s.consumed := by
        simp only [transition, getInstance, found, hn, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
        cases hl : leafPolicy n with
        | error e => simp [hl] at h
        | ok policy =>
          simp only [hl] at h
          split at h
          · contradiction
          · rw [hd] at h
            simp only [] at h
            rw [hp] at h
            simp only [] at h
            rw [hc] at h
            simp only [Except.ok.injEq] at h
            subst h
            refine ⟨?_, ?_, ?_⟩
            · simp only [setAttempt, setInstance, applyWrites_instances, dinst]
            · simp only [setAttempt, setInstance, applyWrites_frames, dfr]
            · simp only [setAttempt, setInstance, applyWrites_consumed, dcons]
      refine ⟨i, n, rfl, hn, leafKind, checked, ?_, tail.1, tail.2.1, tail.2.2⟩
      rw [applyWrites_append]
      have view : next.placedView = (applyWrites (eosWrites i.path n) (applyWrites (outputWrites i.path i.node outputs) s1)).placedView := by
        simp only [State.placedView, channels]
      rw [view]
      apply applyWrites_placedView
      apply applyWrites_placedView
      simp only [State.placedView, dch]


/-! ### Plain control nodes -/

theorem effect_fireWaitAll (s next : State) (path : Path) (node : NodeId)
    (h : transition s (.fireWaitAll path node) = .ok next) :
    ∃ n inputs, getNode s path node = .ok n ∧ n.kind = .waitAll ∧ plainInputs s path n = .ok inputs ∧
      let item := derivedItem "record" path node (inputs.map (fun (p, i) => identity [p, i]))
      let i := makeInstance path n .succeeded inputs
      next.placedView = (applyWrites (routeWrites path n (some item) none ++ eosWrites path n) s).placedView ∧
      next.instances = s.instances ++ [i] ∧ next.frames = s.frames ∧
      RecordsBy s next i.id ((s.incoming path node).map (·.id)) := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · rename_i kind
      split at h
      · contradiction
      · rename_i inputs plain
        obtain ⟨view, inst, fr, _, rs, log, all⟩ := finishControl_effect s next path n inputs _ none h
        rw [getNode_id s path node n hn] at all
        exact ⟨n, inputs, rfl, kind, plain, view, inst, fr, rs, log, all⟩
    · contradiction

theorem effect_fireBranch (s next : State) (path : Path) (node : NodeId) (arm : PortName)
    (h : transition s (.fireBranch path node arm) = .ok next) :
    ∃ n arms inputs item, getNode s path node = .ok n ∧ n.kind = .branch arms ∧ arms.contains arm = true ∧
      plainInputs s path n = .ok inputs ∧ inputs.head?.map (·.2) = some item ∧
      let i := makeInstance path n .succeeded inputs
      next.placedView = (applyWrites (routeWrites path n (some item) (some arm) ++ eosWrites path n) s).placedView ∧
      next.instances = s.instances ++ [i] ∧ next.frames = s.frames ∧
      RecordsBy s next i.id ((s.incoming path node).map (·.id)) := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · rename_i arms kind
      split at h
      · contradiction
      · rename_i u hr
        have armOK := require_ok _ _ _ u hr
        split at h
        · contradiction
        · rename_i inputs plain
          cases hi : inputs.head?.map (·.2) with
          | none => simp [hi] at h
          | some item =>
            simp only [hi] at h
            split at h
            · contradiction
            · rename_i s1 hd
              obtain ⟨dch, dinst, dfr, dcons, _⟩ := decision_value s s1 _ _ hd
              obtain ⟨view, inst, fr, _, rs, log, all⟩ := finishControl_effect s1 next path n inputs _ (some arm) h
              refine ⟨n, arms, inputs, item, rfl, kind, armOK, plain, hi, ?_, ?_, ?_, rs, ?_, ?_⟩
              · rw [view]
                apply applyWrites_placedView
                simp only [State.placedView, dch]
              · rw [inst, dinst]
              · rw [fr, dfr]
              · rw [log, dcons]
              · intro r hr
                have := all r hr
                rw [getNode_id s path node n hn] at this
                simpa [State.incoming, dch] using this
    · contradiction

theorem effect_fireCollect (s next : State) (path : Path) (node : NodeId)
    (h : transition s (.fireCollect path node) = .ok next) :
    ∃ n c, getNode s path node = .ok n ∧ n.kind = .collect ∧ (s.incoming path node).head? = some c ∧
      c.closed = true ∧ c.consumed = 0 ∧
      let items := sortedItems c.items
      let i := makeInstance path n .succeeded (items.map ("item", ·))
      next.placedView = (applyWrites (routeWrites path n (some (derivedItem "list" path node items)) none ++
        eosWrites path n) s).placedView ∧
      next.instances = s.instances ++ [i] ∧ next.frames = s.frames ∧
      RecordsBy s next i.id ((s.incoming path node).map (·.id)) := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · rename_i kind
      cases hc : (s.incoming path node).head? with
      | none => simp [hc] at h
      | some c =>
        simp only [hc] at h
        split at h
        · contradiction
        · rename_i u hr
          have cond := require_ok _ _ _ u hr
          simp only [Bool.and_eq_true, beq_iff_eq] at cond
          obtain ⟨view, inst, fr, _, rs, log, all⟩ := finishControl_effect s next path n _ _ none h
          rw [getNode_id s path node n hn] at all
          exact ⟨n, c, rfl, kind, rfl, cond.1, cond.2, view, inst, fr, rs, log, all⟩
    · contradiction

theorem effect_fireCoalesce (s next : State) (path : Path) (node : NodeId) (edge : String) (item : ItemId)
    (distinct : (s.channels.map (·.id)).Nodup)
    (h : transition s (.fireCoalesce path node edge item) = .ok next) :
    ∃ n c p0, getNode s path node = .ok n ∧ n.kind = .coalesce ∧
      (s.incoming path node).find? (·.id == edge) = some c ∧ c.pending.head? = some (.item item) ∧
      n.outputs.head? = some p0 ∧
      let i := makeInstance path n .succeeded [(c.edge.dst.port, item)]
      next.placedView = (applyWrites (.out path node p0.name (.item item) :: eosWrites path n) s).placedView ∧
      next.instances = s.instances ++ [i] ∧ next.frames = s.frames ∧
      next.consumed = s.consumed ++ [{ channel := c.id, index := c.consumed, item, byInstance := i.id }] := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · rename_i kind
      cases hc : (s.incoming path node).find? (·.id == edge) with
      | none => simp [hc] at h
      | some c =>
        simp only [hc] at h
        split at h
        · contradiction
        · rename_i s1 created
          have value := freshInstance_value s s1 _ created
          subst value
          split at h
          · contradiction
          · rename_i s2 consumed
            obtain ⟨v, inst, fr, _, _⟩ := consume_effect _ s2 c.id _ (some item) consumed
            obtain ⟨c', memberC', idC', headC', log⟩ := consume_item_receipt _ s2 c.id _ item consumed
            have memberC : c ∈ s.channels := (List.mem_filter.mp (List.mem_of_find?_eq_some hc)).1
            have sameC : c' = c := by
              have memberC'' : c' ∈ s.channels := by simpa using memberC'
              exact eq_of_mapped_nodup (·.id) s.channels distinct c' c memberC'' memberC idC'
            rw [sameC] at headC' log
            cases hp : n.outputs.head? with
            | none => simp [hp] at h
            | some p0 =>
              simp only [hp] at h
              split at h
              · contradiction
              · rename_i s3 placed
                have p3 := putOutput_value s2 s3 _ _ _ _ placed
                have p4 := closeOutputs_writes s3 next path n h
                subst p3 p4
                refine ⟨n, c, p0, rfl, kind, rfl, headC', hp, ?_, ?_, ?_, ?_⟩
                · simp only [applyWrites_cons, applyWrite_out]
                  apply applyWrites_placedView
                  exact applyWrite_placedView s2 s (.out path node p0.name (.item item)) (by simpa [State.placedView] using v)
                · simp only [applyWrites_instances, Effects.output, write, inst]
                · simp only [applyWrites_frames, Effects.output, write, fr]
                · simp only [applyWrites_consumed, Effects.output, write, log]
    · contradiction

end Suimon
