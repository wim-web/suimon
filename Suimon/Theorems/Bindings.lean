import Suimon.Theorems.Effects
import Suimon.Theorems.Graph

namespace Suimon

/-- The logical invocation and its input snapshot survive every retry. --/
def Instance.binding (i : Instance) : String × NodeId × Path × Option ItemId × List (PortName × ItemId) :=
  (i.id, i.node, i.path, i.trigger, i.inputs)

def State.bindings (s : State) := s.instances.map Instance.binding

theorem place_instances (s next : State) (ids : List String) (token : Token)
    (accepted : place s ids token = .ok next) : next.instances = s.instances := by
  rw [Effects.place_value s next ids token accepted]
  rfl

theorem consume_instances (s next : State) (channel who : String) (expected : Option ItemId)
    (accepted : consume s channel who expected = .ok next) : next.instances = s.instances := by
  simp only [consume, Option.toExcept, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | split at accepted
    | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
    | contradiction
    | (cases accepted; rfl))

theorem consumeRest_instances (s next : State) (c : Channel) (who : String)
    (accepted : consumeRest s c who = .ok next) : next.instances = s.instances :=
  foldlM_preserves State.instances _ c.pending s next
    (fun current _ _ after valid => consume_instances current after c.id who none valid) accepted

theorem consumeChannels_instances (s next : State) (channels : List Channel) (who : String)
    (accepted : consumeChannels s channels who = .ok next) : next.instances = s.instances :=
  foldlM_preserves State.instances _ channels s next
    (fun current c _ after valid => consumeRest_instances current after c who valid) accepted

theorem consumeInputs_instances (s next : State) (path : Path) (node who : String)
    (accepted : consumeInputs s path node who = .ok next) : next.instances = s.instances :=
  consumeChannels_instances s next _ who accepted

theorem closeOutputs_instances (s next : State) (path : Path) (n : Node)
    (accepted : closeOutputs s path n = .ok next) : next.instances = s.instances :=
  foldlM_preserves State.instances _ n.outputs s next
    (fun current p _ after valid => place_instances current after _ .eos valid) accepted

theorem placeOutputs_instances (s next : State) (path : Path) (node : NodeId) (outputs : List Output)
    (accepted : placeOutputs s path node outputs = .ok next) : next.instances = s.instances := by
  apply foldlM_preserves State.instances _ outputs s next _ accepted
  intro current out _ after valid
  exact foldlM_preserves State.instances _ out.items current after
    (fun current item _ after valid => place_instances current after _ (.item item) valid) valid

theorem placeBodyOutputs_instances (s next : State) (path : Path) (n : Node) (items : List ItemId)
    (accepted : placeBodyOutputs s path n items = .ok next) : next.instances = s.instances :=
  foldlM_preserves State.instances _ (n.outputs.zip items) s next
    (fun current pair _ after valid => place_instances current after _ (.item pair.2) valid) accepted

theorem routeOutputs_instances (s next : State) (path : Path) (n : Node)
    (output : Option ItemId) (arm : Option PortName)
    (accepted : routeOutputs s path n output arm = .ok next) : next.instances = s.instances := by
  apply foldlM_preserves State.instances _ n.outputs s next _ accepted
  intro current p _ after valid
  dsimp at valid
  split at valid
  · exact place_instances current after _ _ valid
  · cases valid; rfl

theorem seedEntries_instances (s next : State) (path : Path) (entries : List PortRef) (items : List ItemId)
    (accepted : seedEntries s path entries items = .ok next) : next.instances = s.instances := by
  apply foldlM_preserves State.instances _ (entries.zip items) s next _ accepted
  intro current pair _ after valid
  rcases pair with ⟨p, item⟩
  dsimp at valid
  cases first : place current
      (((current.incoming path p.node).filter (fun c => c.entry && c.edge.dst == p)).map (·.id)) (.item item) with
  | error e => simp [first, bind, Except.bind] at valid
  | ok middle =>
    simp only [first, bind, Except.bind] at valid
    exact (place_instances middle after _ .eos valid).trans (place_instances current middle _ (.item item) first)

theorem addFrame_instances (s next : State) (owner : Instance) (body : Graph) (items : List ItemId)
    (accepted : addFrame s owner body items = .ok next) : next.instances = s.instances := by
  unfold addFrame at accepted
  simp only [require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | (have effect := seedEntries_instances _ _ _ _ _ accepted; exact effect)
    | split at accepted
    | contradiction)

theorem closeFrame_instances (s next : State) (f : Frame) (who : InstanceId)
    (accepted : closeFrame s f who = .ok next) : next.instances = s.instances := by
  unfold closeFrame at accepted
  cases result : consumeChannels s (s.channels.filter (fun c => c.path == f.path && c.exit)) who with
  | error e => simp [result, bind, Except.bind] at accepted
  | ok middle =>
    have effect := consumeChannels_instances s middle _ who result
    simp only [result, bind, Except.bind, pure, Except.pure] at accepted
    cases accepted
    exact effect

theorem decision_instances (s next : State) (key value : String)
    (accepted : decision s key value = .ok next) : next.instances = s.instances := by
  simp only [decision, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first | split at accepted | contradiction | (cases accepted; rfl))

theorem freshInstance_instances (s next : State) (i : Instance)
    (accepted : freshInstance s i = .ok next) : next.instances = s.instances ++ [i] := by
  simp only [freshInstance, require, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first | split at accepted | contradiction | (cases accepted; rfl))

theorem finishControl_instances (s next : State) (path : Path) (n : Node)
    (inputs : List (PortName × ItemId)) (output : Option ItemId) (arm : Option PortName)
    (accepted : finishControl s path n inputs output arm = .ok next) :
    next.instances = s.instances ++ [makeInstance path n .succeeded inputs] := by
  unfold finishControl at accepted
  cases created : freshInstance s (makeInstance path n .succeeded inputs) with
  | error e => simp [created, bind, Except.bind] at accepted
  | ok a =>
    have first := freshInstance_instances s a _ created
    simp only [created, bind, Except.bind] at accepted
    cases consumed : consumeInputs a path n.id (instanceId path n.id) with
    | error e => simp [consumed, bind, Except.bind, makeInstance] at accepted
    | ok b =>
      have second := consumeInputs_instances a b path n.id _ consumed
      simp only [makeInstance, consumed, bind, Except.bind] at accepted
      cases emitted : routeOutputs b path n output arm with
      | error e => simp [emitted, bind, Except.bind] at accepted
      | ok c =>
        have third := routeOutputs_instances b c path n output arm emitted
        simp only [emitted, bind, Except.bind] at accepted
        exact (closeOutputs_instances c next path n accepted).trans (third.trans (second.trans first))

theorem streamController_instances (s next : State) (path : Path) (n : Node)
    (accepted : streamController s path n = .ok next) :
    next.instances = s.instances ∨ next.instances = s.instances ++ [makeInstance path n .waitingInputs] := by
  unfold streamController at accepted
  cases found : s.nodeInstance? path n.id with
  | none => exact .inr (freshInstance_instances s next _ (by simpa [found] using accepted))
  | some i =>
    simp only [found, require, bind, Except.bind, pure, Except.pure] at accepted
    repeat (first | split at accepted | contradiction | (cases accepted; exact .inl rfl))

theorem eq_of_mapped_nodup {α β : Type} (key : α → β) (xs : List α)
    (distinct : (xs.map key).Nodup) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (same : key a = key b) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp ha with aHead | aTail
    · rcases List.mem_cons.mp hb with bHead | bTail
      · exact aHead.trans bHead.symm
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨b, bTail, same.symm.trans (congrArg key aHead)⟩))
    · rcases List.mem_cons.mp hb with bHead | bTail
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨a, aTail, same.trans (congrArg key bHead)⟩))
      · exact ih distinct.2 aTail bTail

theorem setInstance_bindings (s : State) (old replacement : Instance)
    (distinct : (s.instances.map (·.id)).Nodup) (member : old ∈ s.instances)
    (same : replacement.binding = old.binding) :
    (setInstance s replacement).bindings = s.bindings := by
  have idEq : replacement.id = old.id := congrArg Prod.fst same
  simp only [State.bindings, setInstance, List.map_map]
  apply List.map_congr_left
  intro i memberI
  dsimp
  split
  · rename_i idI
    have oldEq : i = old := eq_of_mapped_nodup (·.id) s.instances distinct i old memberI member
      (by simpa [idEq] using idI)
    simpa [oldEq] using same
  · rfl

theorem startInputs_instances (s next : State) (inputs : List Input)
    (accepted : startInputs s inputs = .ok next) : next.instances = s.instances := by
  apply foldlM_preserves State.instances _ inputs s next _ accepted
  intro state input member result valid
  let channels : List Channel := state.channels.filter (fun c => c.path.isEmpty && c.entry && c.edge.dst == input.entry)
  have placed : ∀ middle, input.items.foldlM (fun current item => place current (channels.map (·.id)) (.item item)) state = .ok middle →
      middle.instances = state.instances := by
    intro middle correct
    exact foldlM_preserves State.instances _ input.items state middle
      (fun current item _ after yes => place_instances current after _ (.item item) yes) correct
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
      exact (place_instances middle result _ .eos valid).trans (placed middle body)

theorem getInstance_member (s : State) (id : InstanceId) (i : Instance)
    (found : getInstance s id = .ok i) : i ∈ s.instances := by
  cases lookup : s.instance? id with
  | none => simp [getInstance, lookup, Option.toExcept] at found
  | some value =>
    simp only [getInstance, lookup, Option.toExcept, Except.ok.injEq] at found
    subst i
    exact List.mem_of_find?_eq_some lookup

theorem expireOrFail_bindings (s next : State) (i : Instance) (n : Node) (now : Time)
    (outcome : AttemptStatus) (retryable : Bool) (code : String)
    (distinct : (s.instances.map (·.id)).Nodup) (member : i ∈ s.instances)
    (accepted : expireOrFail s i n now outcome retryable code = .ok next) : next.bindings = s.bindings := by
  cases policyResult : leafPolicy n with
  | error e => simp [expireOrFail, policyResult, bind, Except.bind] at accepted
  | ok pair =>
    rcases pair with ⟨r, concurrency⟩
    cases leaseResult : i.lease with
    | none => simp [expireOrFail, policyResult, leaseResult, Option.toExcept, bind, Except.bind] at accepted
    | some lease =>
      simp only [expireOrFail, policyResult, leaseResult, Option.toExcept, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      let retry := retryable && i.attemptCount < r.maxAttempts + i.extraAttempts
      exact setInstance_bindings s i
        { i with
          status := if retry then .retryWait else .failed
          lease := none
          retryAt := if retry then some (now + r.retrySeconds) else none } distinct member rfl

theorem Invariants.instanceIds {s : State} (safe : Invariants s) :
    (s.instances.map (·.id)).Nodup := by
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  exact unique_nodup _ safe.1.1.1.1.1.2

private theorem binding_update_of_member (s : State) (old : Instance)
    (distinct : (s.instances.map (·.id)).Nodup) (member : old ∈ s.instances) :
    ∀ state replacement, state.instances = s.instances → replacement.binding = old.binding →
      (setInstance state replacement).instances.map Instance.binding = s.instances.map Instance.binding := by
  intro state replacement same binding
  have result := setInstance_bindings state old replacement (by simpa [same] using distinct)
    (by simpa [same] using member) binding
  simpa only [State.bindings, same] using result

open Lean Elab Tactic Meta in
/-- Specialize the checked update lemma at invocation lookups already in the
    goal. This only constructs applications of the lemmas above. --/
elab "specialize_binding_updates " distinct:term : tactic => withMainContext do
  let distinctProof ← elabTerm distinct none
  let context ← getLCtx
  for decl in context do
    let ty := decl.type
    if !ty.isAppOfArity ``Eq 3 then continue
    let lhs := ty.getAppArgs[1]!
    let rhs := ty.getAppArgs[2]!
    let recognized := lhs.isAppOfArity ``getInstance 2 && rhs.isAppOfArity ``Except.ok 3
    let nodeLookup := lhs.isAppOfArity ``State.nodeInstance? 3 && rhs.isAppOfArity ``Option.some 2
    if !recognized && !nodeLookup then continue
    let state := lhs.getAppArgs[0]!
    let old := rhs.getAppArgs.back!
    let member ← if recognized then
      mkAppM ``getInstance_member #[state, lhs.getAppArgs[1]!, old, decl.toExpr]
      else mkAppM ``List.mem_of_find?_eq_some #[decl.toExpr]
    let update ← mkAppM ``binding_update_of_member #[state, old, distinctProof, member]
    let (_, goal) ← (← getMainGoal).note (← mkFreshUserName `bindingUpdate) update
    replaceMainGoal [goal]

set_option maxHeartbeats 2400000 in
theorem transition_bindings (s next : State) (op : Op) (safe : Invariants s)
    (accepted : transition s op = .ok next) : s.bindings.IsPrefix next.bindings := by
  have distinct := safe.instanceIds
  have hPlace := place_instances
  have hConsume := consume_instances
  have hInputs := consumeInputs_instances
  have hClose := closeOutputs_instances
  have hFresh := freshInstance_instances
  have hDecision := decision_instances
  have hFrame := closeFrame_instances
  have hControl := finishControl_instances
  have hStream := streamController_instances
  have hOutputs := placeOutputs_instances
  have hBody := placeBodyOutputs_instances
  have hChannels := consumeChannels_instances
  have hStart := startInputs_instances
  have hAdd := addFrame_instances
  have hFailure : ∀ next i n now outcome retryable code, i ∈ s.instances →
      expireOrFail s i n now outcome retryable code = .ok next → next.bindings = s.bindings :=
    fun next i n now outcome retryable code member accepted =>
      expireOrFail_bindings s next i n now outcome retryable code distinct member accepted
  have hGet := getInstance_member s
  have hNode : ∀ path node i, s.nodeInstance? path node = some i → i ∈ s.instances :=
    fun _ _ _ found => List.mem_of_find?_eq_some found
  have hSet : ∀ state old replacement, state.instances = s.instances → old ∈ s.instances →
      replacement.binding = old.binding → (setInstance state replacement).bindings = s.bindings := by
    intro state old replacement same member binding
    have result := setInstance_bindings state old replacement (by simpa [same] using distinct)
      (by simpa [same] using member) binding
    simpa only [State.bindings, same] using result
  have hCancel : (s.instances.map (fun i => if i.status.finished then i else
      { i with status := .cancelled, lease := none, retryAt := none })).map Instance.binding = s.bindings := by
    simp only [State.bindings, List.map_map]
    apply List.map_congr_left
    intro i member
    dsimp
    split <;> rfl
  simp only [State.bindings] at hFailure hSet hCancel ⊢
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
    specialize_binding_updates distinct
    try simp only [putOutput, setAttempt] at *
    grind only [List.prefix_refl, List.prefix_append, List.map_append, Instance.binding]

theorem step_bindings (s next : State) (op : Op) (safe : Invariants s)
    (accepted : step s op = .ok next) : s.bindings.IsPrefix next.bindings := by
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
      exact transition_bindings s next _ safe executed

theorem ConformingSteps.bindings {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (safe : Invariants s) : s.bindings.IsPrefix next.bindings := by
  induction run with
  | nil => exact List.prefix_refl _
  | cons allowed accepted tail ih =>
    exact (step_bindings _ _ _ safe accepted).trans (ih (preserves_invariants _ _ _ safe accepted))

theorem ConformingSteps.invariants {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (safe : Invariants s) : Invariants next := by
  induction run with
  | nil => exact safe
  | cons allowed accepted tail ih => exact ih (preserves_invariants _ _ _ safe accepted)

theorem ConformingSteps.retains_binding {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (safe : Invariants s) (i : Instance) (member : i ∈ s.instances) :
    ∃ j ∈ next.instances, j.binding = i.binding := by
  have before : i.binding ∈ s.bindings := List.mem_map.mpr ⟨i, member, rfl⟩
  have after := (run.bindings safe).sublist.subset before
  exact List.mem_map.mp after

/-- Leases, failures, manual retries, and unrelated node work cannot replace a
    retained invocation's inputs or logical identity. --/
theorem ConformingSteps.input_snapshot {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (safe : Invariants s) (i j : Instance) (old : i ∈ s.instances) (current : j ∈ next.instances)
    (sameId : i.id = j.id) :
    j.node = i.node ∧ j.path = i.path ∧ j.trigger = i.trigger ∧ j.inputs = i.inputs := by
  obtain ⟨retained, member, same⟩ := run.retains_binding safe i old
  have idEq : retained.id = i.id := congrArg Prod.fst same
  have actual : retained = j := eq_of_mapped_nodup (·.id) next.instances
    (run.invariants safe).instanceIds retained j member current (idEq.trans sameId)
  subst retained
  simpa only [Instance.binding, Prod.mk.injEq, sameId, true_and] using same

end Suimon
