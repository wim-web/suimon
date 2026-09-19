import Suimon.Theorems.Writes

/-! Exact effects of the operational helpers, phrased over the placed view, the
    consumption log, instances and frames. `transition_effect` composes them. -/

namespace Suimon
open Effects

/-- Consumption by `who` on some of `chans`: the placed view, instances and frames
    are unchanged, and the log grows by records attributed to `who`. -/
def ConsumeEffect (who : InstanceId) (chans : List String) (s next : State) : Prop :=
  next.placedView = s.placedView ∧ next.instances = s.instances ∧ next.frames = s.frames ∧
  next.status = s.status ∧
  ∃ rs, next.consumed = s.consumed ++ rs ∧ ∀ r ∈ rs, r.byInstance = who ∧ r.channel ∈ chans

theorem ConsumeEffect.refl (who : InstanceId) (chans : List String) (s : State) : ConsumeEffect who chans s s :=
  ⟨rfl, rfl, rfl, rfl, [], by simp, by simp⟩

theorem ConsumeEffect.trans {who : InstanceId} {chans : List String} {a b c : State}
    (ab : ConsumeEffect who chans a b) (bc : ConsumeEffect who chans b c) : ConsumeEffect who chans a c := by
  obtain ⟨v1, i1, f1, st1, rs1, log1, all1⟩ := ab
  obtain ⟨v2, i2, f2, st2, rs2, log2, all2⟩ := bc
  refine ⟨v2.trans v1, i2.trans i1, f2.trans f1, st2.trans st1, rs1 ++ rs2, ?_, ?_⟩
  · rw [log2, log1, List.append_assoc]
  · intro r member
    rcases List.mem_append.mp member with h | h
    · exact all1 r h
    · exact all2 r h

theorem ConsumeEffect.mono {who : InstanceId} {chans more : List String} {a b : State}
    (h : ConsumeEffect who chans a b) (sub : ∀ x ∈ chans, x ∈ more) : ConsumeEffect who more a b := by
  obtain ⟨v, i, f, st, rs, log, all⟩ := h
  exact ⟨v, i, f, st, rs, log, fun r m => ⟨(all r m).1, sub _ (all r m).2⟩⟩

theorem foldlM_effect {α β ε : Type} (R : α → α → Prop) (refl : ∀ a, R a a)
    (trans : ∀ a b c, R a b → R b c → R a c) (f : α → β → Except ε α) (xs : List β)
    (start last : α) (step : ∀ a x, x ∈ xs → ∀ b, f a x = .ok b → R a b)
    (accepted : xs.foldlM f start = .ok last) : R start last := by
  induction xs generalizing start with
  | nil => cases accepted; exact refl _
  | cons x xs ih =>
    simp only [List.foldlM_cons] at accepted
    cases h : f start x with
    | error e => simp [h, bind, Except.bind] at accepted
    | ok mid =>
      simp only [h, bind, Except.bind] at accepted
      exact trans _ _ _ (step start x (by simp) mid h)
        (ih mid (fun a y hy => step a y (by simp [hy])) accepted)

theorem consume_effect (s next : State) (channel who : String) (expected : Option ItemId)
    (accepted : consume s channel who expected = .ok next) :
    ConsumeEffect who [channel] s next := by
  cases found : s.channels.find? (·.id == channel) with
  | none => simp [consume, found, Option.toExcept, bind, Except.bind] at accepted
  | some c =>
    cases pending : c.pending.head? with
    | none => simp [consume, found, pending, Option.toExcept, bind, Except.bind] at accepted
    | some t =>
      have finish : ∀ (audit : List Consumption) (next' : State),
          next'.channels = s.channels.map (fun d => if d.id == c.id then { d with consumed := d.consumed + 1 } else d) →
          next'.consumed = s.consumed ++ audit → next'.instances = s.instances → next'.frames = s.frames →
          next'.status = s.status →
          (∀ r ∈ audit, r.byInstance = who ∧ r.channel ∈ [channel]) → ConsumeEffect who [channel] s next' := by
        intro audit next' channels consumed instances frames status all
        refine ⟨?_, instances, frames, status, audit, consumed, all⟩
        simp only [State.placedView, channels, List.map_map]
        apply List.map_congr_left
        intro d _
        simp only [Function.comp_def]
        split <;> rfl
      simp only [consume, found, pending, Option.toExcept, require, bind, Except.bind, pure, Except.pure] at accepted
      repeat (first | split at accepted | contradiction)
      all_goals (first | (cases accepted; exact finish _ _ rfl rfl rfl rfl rfl (by first | (cases t <;> simp) | simp)) | cases accepted)

theorem consumeRest_effect (s next : State) (c : Channel) (who : String)
    (accepted : consumeRest s c who = .ok next) : ConsumeEffect who [c.id] s next :=
  foldlM_effect (ConsumeEffect who [c.id]) (ConsumeEffect.refl who _) (fun _ _ _ => ConsumeEffect.trans)
    _ c.pending s next (fun a _ _ b h => consume_effect a b c.id who none h) accepted

theorem consumeChannels_effect (s next : State) (channels : List Channel) (who : String)
    (accepted : consumeChannels s channels who = .ok next) :
    ConsumeEffect who (channels.map (·.id)) s next :=
  foldlM_effect (ConsumeEffect who (channels.map (·.id))) (ConsumeEffect.refl who _)
    (fun _ _ _ => ConsumeEffect.trans) _ channels s next
    (fun a c member b h => (consumeRest_effect a b c who h).mono
      (fun x hx => by simp at hx; subst hx; exact List.mem_map.mpr ⟨c, member, rfl⟩)) accepted

theorem consumeInputs_effect (s next : State) (path : Path) (node who : String)
    (accepted : consumeInputs s path node who = .ok next) :
    ConsumeEffect who ((s.incoming path node).map (·.id)) s next :=
  consumeChannels_effect s next _ who accepted

theorem freshInstance_value (s next : State) (i : Instance) (accepted : freshInstance s i = .ok next) :
    next = { s with instances := s.instances ++ [i] } := by
  simp only [freshInstance, require, bind, Except.bind, pure, Except.pure] at accepted
  split at accepted <;> first | (cases accepted; rfl) | contradiction | cases accepted

theorem decision_value (s next : State) (key value : String) (accepted : decision s key value = .ok next) :
    next.channels = s.channels ∧ next.instances = s.instances ∧ next.frames = s.frames ∧
    next.consumed = s.consumed ∧ next.status = s.status := by
  unfold decision at accepted
  split at accepted
  · simp only [require, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted <;> first | (cases accepted; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) | cases accepted
  · cases accepted; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem streamController_value (s next : State) (path : Path) (n : Node)
    (accepted : streamController s path n = .ok next) :
    next.channels = s.channels ∧ next.frames = s.frames ∧ next.consumed = s.consumed ∧ next.status = s.status ∧
    ((∃ old, s.nodeInstance? path n.id = some old ∧ next.instances = s.instances) ∨
      (s.nodeInstance? path n.id = none ∧ next.instances = s.instances ++ [makeInstance path n .waitingInputs])) := by
  unfold streamController at accepted
  cases found : s.nodeInstance? path n.id with
  | none =>
    simp only [found] at accepted
    rw [freshInstance_value s next _ accepted]
    exact ⟨rfl, rfl, rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  | some i =>
    simp only [found, require, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted <;> first | (cases accepted; exact ⟨rfl, rfl, rfl, rfl, .inl ⟨i, rfl, rfl⟩⟩) | contradiction | cases accepted

/-! ### Write lists of the placement helpers -/

def eosWrites (path : Path) (n : Node) : List Write := n.outputs.map fun p => .out path n.id p.name .eos
def outputWrites (path : Path) (node : NodeId) (outputs : List Output) : List Write :=
  outputs.flatMap fun o => o.items.map fun x => .out path node o.port (.item x)
def bodyWrites (path : Path) (n : Node) (items : List ItemId) : List Write :=
  (n.outputs.zip items).map fun pair => .out path n.id pair.1.name (.item pair.2)
def routeWrites (path : Path) (n : Node) (output : Option ItemId) (arm : Option PortName) : List Write :=
  n.outputs.filterMap fun p => (routeOutput arm p.name output).map fun id => .out path n.id p.name (.item id)
def seedWrites (path : Path) (entries : List PortRef) (items : List ItemId) : List Write :=
  (entries.zip items).flatMap fun pair => [.seed path pair.1 (.item pair.2), .seed path pair.1 .eos]
def rootWrites (inputs : List Input) : List Write :=
  inputs.flatMap fun input => input.items.map (fun x => .root input.entry (.item x)) ++ [.root input.entry .eos]

theorem applyWrites_flatMap {β : Type} (g : β → List Write) (xs : List β) (st : State) :
    applyWrites (xs.flatMap g) st = xs.foldl (fun st x => applyWrites (g x) st) st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, applyWrites_append, List.foldl_cons, ih]

theorem applyWrites_map {β : Type} (g : β → Write) (xs : List β) (st : State) :
    applyWrites (xs.map g) st = xs.foldl (fun st x => applyWrite st (g x)) st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, applyWrites_cons, List.foldl_cons, ih]

theorem closeOutputs_writes (s next : State) (path : Path) (n : Node)
    (accepted : closeOutputs s path n = .ok next) : next = applyWrites (eosWrites path n) s := by
  rw [closeOutputs_value s next path n accepted, eosWrites, applyWrites_map]
  rfl

theorem placeOutputs_writes (s next : State) (path : Path) (node : NodeId) (outputs : List Output)
    (accepted : placeOutputs s path node outputs = .ok next) :
    next = applyWrites (outputWrites path node outputs) s := by
  rw [placeOutputs_value s next path node outputs accepted, outputWrites, applyWrites_flatMap]
  apply congrArg (fun f => outputs.foldl f s)
  funext st o
  rw [applyWrites_map]
  rfl

theorem placeBodyOutputs_writes (s next : State) (path : Path) (n : Node) (items : List ItemId)
    (accepted : placeBodyOutputs s path n items = .ok next) :
    next = applyWrites (bodyWrites path n items) s := by
  rw [placeBodyOutputs_value s next path n items accepted, bodyWrites, applyWrites_map]
  rfl

theorem routeOutputs_writes (s next : State) (path : Path) (n : Node) (value : Option ItemId)
    (arm : Option PortName) (accepted : routeOutputs s path n value arm = .ok next) :
    next = applyWrites (routeWrites path n value arm) s := by
  unfold routeOutputs at accepted
  have folded := foldlM_eq_foldl _ (fun (st : State) (p : Port) =>
      match routeOutput arm p.name value with
      | some id => output st path n.id p.name (.item id)
      | none => st) n.outputs s next (by
    intro st p _ after valid
    cases h : routeOutput arm p.name value with
    | some id =>
      simp only [h] at valid ⊢
      exact putOutput_value st after path n.id p.name _ valid
    | none =>
      simp only [h, pure, Except.pure, Except.ok.injEq] at valid ⊢
      exact valid.symm) accepted
  rw [folded, routeWrites]
  clear folded accepted
  induction n.outputs generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons, List.filterMap_cons]
    cases routeOutput arm p.name value with
    | none => exact ih s
    | some id => simp only [Option.map_some, applyWrites_cons, applyWrite_out]; exact ih _

theorem insertToken_layout (c : Channel) (t : Token) : (insertToken c t).layout = c.layout := by
  unfold insertToken; split <;> rfl

theorem write_channelLayout (st : State) (ids : List String) (t : Token) :
    (write st ids t).channelLayout = st.channelLayout := by
  simp only [write, State.channelLayout, List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_def]
  split <;> simp [insertToken_layout]

theorem applyWrite_channelLayout (st : State) (w : Write) : (applyWrite st w).channelLayout = st.channelLayout :=
  write_channelLayout _ _ _

theorem applyWrites_channelLayout (ws : List Write) (st : State) :
    (applyWrites ws st).channelLayout = st.channelLayout := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => exact (ih _).trans (applyWrite_channelLayout st w)

/-- Selected identifiers depend only on the layout (never on placed tokens). -/
theorem Write.ids_layout (w : Write) (a b : State) (same : a.channelLayout = b.channelLayout) :
    w.ids a = w.ids b := by
  have channels : ∀ (pred : Channel → Bool), (∀ c : Channel, pred c.layout = pred c) →
      (a.channels.filter pred).map (·.id) = (b.channels.filter pred).map (·.id) := by
    intro pred stable
    have view : ∀ s : State, (s.channels.filter pred).map (·.id) = (s.channelLayout.filter pred).map (·.id) := by
      intro s
      simp only [State.channelLayout, List.filter_map, List.map_map]
      congr 1
      exact List.filter_congr (fun c _ => by simp [Function.comp_def, stable])
    rw [view a, view b, same]
  cases w with
  | out path node port t => exact channels _ (fun c => by simp [Channel.layout])
  | seed path p t =>
    simp only [Write.ids, State.incoming, List.filter_filter]
    exact channels _ (fun c => by simp [Channel.layout])
  | root p t => exact channels _ (fun c => by simp [Channel.layout])

theorem applyWrite_ids_after (st : State) (v w : Write) : w.ids (applyWrite st v) = w.ids st :=
  w.ids_layout _ _ (applyWrite_channelLayout st v)

theorem seedEntries_writes (s next : State) (path : Path) (entries : List PortRef) (items : List ItemId)
    (accepted : seedEntries s path entries items = .ok next) :
    next = applyWrites (seedWrites path entries items) s := by
  unfold seedEntries at accepted
  have value := foldlM_eq_foldl _ (fun (st : State) (pair : PortRef × ItemId) =>
      applyWrite (applyWrite st (.seed path pair.1 (.item pair.2))) (.seed path pair.1 .eos))
      (entries.zip items) s next (by
    intro st pair _ after valid
    rcases pair with ⟨p, id⟩
    simp only [bind, Except.bind] at valid
    cases first : place st (((st.incoming path p.node).filter (fun c => c.entry && c.edge.dst == p)).map (·.id)) (.item id) with
    | error e => simp [first] at valid
    | ok middle =>
      simp only [first] at valid
      rw [place_value middle after _ _ valid, place_value st middle _ _ first]
      show _ = write (applyWrite st (.seed path p (.item id))) ((Write.seed path p .eos).ids (applyWrite st (.seed path p (.item id)))) .eos
      rw [applyWrite_ids_after]
      rfl) accepted
  rw [value, seedWrites, applyWrites_flatMap]
  rfl

theorem foldl_root_items (st a : State) (entry : PortRef) (xs : List ItemId)
    (same : a.channelLayout = st.channelLayout) :
    xs.foldl (fun b x => write b ((Write.root entry .eos).ids st) (.item x)) a =
      xs.foldl (fun b x => applyWrite b (.root entry (.item x))) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have step : write a ((Write.root entry .eos).ids st) (.item x) = applyWrite a (.root entry (.item x)) := by
      show _ = write a ((Write.root entry (.item x)).ids a) (.item x)
      rw [show (Write.root entry (.item x)).ids a = (Write.root entry .eos).ids st from
        (Write.root entry .eos).ids_layout a st same]
    rw [step]
    exact ih _ ((applyWrite_channelLayout a _).trans same)

theorem startInputs_writes (s next : State) (inputs : List Input)
    (accepted : startInputs s inputs = .ok next) : next = applyWrites (rootWrites inputs) s := by
  unfold startInputs at accepted
  have value := foldlM_eq_foldl _ (fun (st : State) (input : Input) =>
      applyWrite (input.items.foldl (fun st x => applyWrite st (.root input.entry (.item x))) st) (.root input.entry .eos))
      inputs s next (by
    intro st input _ after valid
    let channels : List Channel := st.channels.filter (fun c => c.path.isEmpty && c.entry && c.edge.dst == input.entry)
    change ((do
      require (unique input.items && channels.all (fun (c : Channel) => c.kind != PortKind.plain || input.items.length == 1)) "INVALID_INPUT"
      let middle ← input.items.foldlM (fun (current : State) (item : ItemId) => place current (channels.map Channel.id) (.item item)) st
      place middle (channels.map Channel.id) .eos) : Result State) = .ok after at valid
    cases ready : require (unique input.items && channels.all (fun c => c.kind != .plain || input.items.length == 1)) "INVALID_INPUT" with
    | error e => rw [ready] at valid; contradiction
    | ok u =>
      rw [ready] at valid
      simp only [bind, Except.bind] at valid
      cases body : input.items.foldlM (fun current item => place current (channels.map (·.id)) (.item item)) st with
      | error e => rw [body] at valid; contradiction
      | ok middle =>
        rw [body] at valid
        simp only [bind, Except.bind] at valid
        have inner := foldlM_eq_foldl _ (fun (b : State) (x : ItemId) => write b (channels.map (·.id)) (.item x))
          input.items st middle (fun a x _ b h => place_value a b _ _ h) body
        have idsEq : channels.map (·.id) = (Write.root input.entry .eos).ids st := rfl
        rw [place_value middle after _ _ valid, inner, idsEq, foldl_root_items st st input.entry input.items rfl]
        show _ = write _ ((Write.root input.entry .eos).ids _) .eos
        have layout : (input.items.foldl (fun b x => applyWrite b (.root input.entry (.item x))) st).channelLayout = st.channelLayout := by
          rw [← applyWrites_map]
          exact applyWrites_channelLayout _ _
        rw [(Write.root input.entry .eos).ids_layout _ st layout]) accepted
  rw [value, rootWrites, applyWrites_flatMap]
  apply congrArg (fun f => inputs.foldl f s)
  funext st input
  rw [applyWrites_append, applyWrites_map]
  rfl

theorem applyWrite_instances (st : State) (w : Write) : (applyWrite st w).instances = st.instances := rfl
theorem applyWrite_frames (st : State) (w : Write) : (applyWrite st w).frames = st.frames := rfl
theorem applyWrite_consumed (st : State) (w : Write) : (applyWrite st w).consumed = st.consumed := rfl
theorem applyWrite_status (st : State) (w : Write) : (applyWrite st w).status = st.status := rfl

theorem applyWrites_instances (ws : List Write) (st : State) : (applyWrites ws st).instances = st.instances := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => exact ih _
theorem applyWrites_frames (ws : List Write) (st : State) : (applyWrites ws st).frames = st.frames := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => exact ih _
theorem applyWrites_consumed (ws : List Write) (st : State) : (applyWrites ws st).consumed = st.consumed := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => exact ih _
theorem applyWrites_status (ws : List Write) (st : State) : (applyWrites ws st).status = st.status := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => exact ih _

/-- The frame a container operation opens, exactly as `addFrame` builds it. -/
def childFrame (s : State) (owner : Instance) (body : Graph) : Frame :=
  { path := owner.path ++ [identity [owner.id, toString owner.iteration]], graph := body
    definition := ((s.frame? owner.path).map (·.definition)).getD [] ++ [owner.node]
    owner := some owner.id }

theorem addFrame_effect (s next : State) (owner : Instance) (body : Graph) (items : List ItemId)
    (accepted : addFrame s owner body items = .ok next) :
    let f := childFrame s owner body
    s.frame? f.path = none ∧ items.length = body.entries.length ∧
    next.placedView = (applyWrites (seedWrites f.path body.entries items)
      { s with channels := s.channels ++ f.channels }).placedView ∧
    next.frames = s.frames ++ [f] ∧ next.instances = s.instances ∧ next.consumed = s.consumed ∧
    next.status = s.status := by
  intro f
  unfold addFrame at accepted
  simp only [require, bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · rename_i _ _ frameEq _ _ arityEq
      have seeded := seedEntries_writes _ next _ body.entries items accepted
      have frameNone : s.frame? f.path = none := by
        split at frameEq
        · rename_i cond
          simpa [f, childFrame] using cond
        · contradiction
      have lengths : items.length = body.entries.length := by
        split at arityEq
        · rename_i cond
          simpa using cond
        · contradiction
      refine ⟨frameNone, lengths, ?_, ?_, ?_, ?_, ?_⟩
      · rw [seeded]
        exact applyWrites_placedView _ _ _ rfl
      · rw [seeded, applyWrites_frames]
        rfl
      · rw [seeded, applyWrites_instances]
      · rw [seeded, applyWrites_consumed]
      · rw [seeded, applyWrites_status]

theorem closeFrame_effect (s next : State) (f : Frame) (who : InstanceId)
    (accepted : closeFrame s f who = .ok next) :
    ConsumeEffect who ((s.channels.filter (fun c => c.path == f.path && c.exit)).map (·.id)) s
      { next with frames := s.frames } ∧
    next.frames = s.frames.map (fun g => if g.path == f.path then { g with closed := true } else g) := by
  unfold closeFrame at accepted
  cases consumed : consumeChannels s (s.channels.filter (fun c => c.path == f.path && c.exit)) who with
  | error e => simp [consumed, bind, Except.bind] at accepted
  | ok middle =>
    simp only [consumed, bind, Except.bind, pure, Except.pure] at accepted
    cases accepted
    have effect := consumeChannels_effect s middle _ who consumed
    obtain ⟨v, i, fr, st, rs, log, all⟩ := effect
    refine ⟨⟨v, i, rfl, st, rs, log, all⟩, ?_⟩
    rw [fr]

theorem finishControl_effect (s next : State) (path : Path) (n : Node)
    (inputs : List (PortName × ItemId)) (value : Option ItemId) (arm : Option PortName)
    (accepted : finishControl s path n inputs value arm = .ok next) :
    let i := makeInstance path n .succeeded inputs
    next.placedView = (applyWrites (routeWrites path n value arm ++ eosWrites path n) s).placedView ∧
    next.instances = s.instances ++ [i] ∧ next.frames = s.frames ∧ next.status = s.status ∧
    ∃ rs, next.consumed = s.consumed ++ rs ∧
      ∀ r ∈ rs, r.byInstance = i.id ∧ r.channel ∈ (s.incoming path n.id).map (·.id) := by
  intro i
  unfold finishControl at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · contradiction
  · rename_i a created
    have first := freshInstance_value s a _ created
    subst first
    split at accepted
    · contradiction
    · rename_i b consumed
      have second := consumeInputs_effect _ b path n.id _ consumed
      split at accepted
      · contradiction
      · rename_i c emitted
        have third := routeOutputs_writes b c path n value arm emitted
        have fourth := closeOutputs_writes c next path n accepted
        obtain ⟨v, inst, fr, st, rs, log, all⟩ := second
        subst third
        subst fourth
        refine ⟨?_, ?_, ?_, ?_, rs, ?_, ?_⟩
        · rw [applyWrites_append]
          apply applyWrites_placedView
          apply applyWrites_placedView
          simpa [State.placedView] using v
        · simp only [applyWrites_instances]; exact inst
        · simp only [applyWrites_frames]; exact fr
        · simp only [applyWrites_status]; exact st
        · simp only [applyWrites_consumed]; exact log
        · intro r member
          have := all r member
          simpa [State.incoming, i, makeInstance] using this

theorem expireOrFail_effect (s next : State) (i : Instance) (n : Node) (now : Time)
    (outcome : AttemptStatus) (retryable : Bool) (code : String)
    (accepted : expireOrFail s i n now outcome retryable code = .ok next) :
    next.channels = s.channels ∧ next.frames = s.frames ∧ next.consumed = s.consumed ∧
    ∃ (retry : Bool) (retryAt : Option Time), next.instances =
      (setInstance s { i with status := (if retry then InstanceStatus.retryWait else InstanceStatus.failed), lease := none, retryAt }).instances := by
  simp only [expireOrFail, require, Option.toExcept, bind, Except.bind, pure, Except.pure] at accepted
  repeat (first
    | split at accepted
    | contradiction
    | (cases accepted; first | exact ⟨rfl, rfl, rfl, true, _, rfl⟩ | exact ⟨rfl, rfl, rfl, false, _, rfl⟩))

end Suimon
