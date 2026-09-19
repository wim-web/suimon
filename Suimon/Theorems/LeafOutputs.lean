import Suimon.Theorems.Accounting

/-! First bridge stage for T9: after a conforming, non-absorbed `complete`, every
    stream output channel of the leaf carries exactly the oracle-prescribed
    multiset, and keeps it (closed) through the rest of the run. -/

namespace Suimon
open Effects

theorem require_ok (b : Bool) (code message : String) (u : Unit)
    (h : require b code message = .ok u) : b = true := by
  unfold require at h
  split at h
  · assumption
  · contradiction

theorem getNode_node? (s : State) (path : Path) (id : NodeId) (n : Node)
    (h : getNode s path id = .ok n) : s.node? path id = some n := by
  cases hf : s.frame? path with
  | none => simp [getNode, hf, Option.toExcept, bind, Except.bind] at h
  | some f =>
    simp only [getNode, hf, Option.toExcept, bind, Except.bind] at h
    split at h
    · contradiction
    · cases hn : f.graph.node? id with
      | none => simp [hn] at h
      | some m =>
        simp only [hn, Except.ok.injEq] at h
        subst m
        simp [State.node?, hf, hn]

theorem getNode_id (s : State) (path : Path) (id : NodeId) (n : Node)
    (h : getNode s path id = .ok n) : n.id = id := by
  cases hf : s.frame? path with
  | none => simp [getNode, hf, Option.toExcept, bind, Except.bind] at h
  | some f =>
    simp only [getNode, hf, Option.toExcept, bind, Except.bind] at h
    split at h
    · contradiction
    · cases hn : f.graph.node? id with
      | none => simp [hn] at h
      | some m =>
        simp only [hn, Except.ok.injEq] at h
        subst m
        simpa using List.find?_some hn

theorem decision_channels (s next : State) (key value : String)
    (h : decision s key value = .ok next) : next.channels = s.channels := by
  unfold decision at h
  split at h
  · simp only [require, bind, Except.bind, pure, Except.pure] at h
    split at h <;> first | (cases h; rfl) | cases h
  · cases h; rfl

/-! ### Field-level facts about token insertion -/

theorem insertToken_edge (c : Channel) (t : Token) : (insertToken c t).edge = c.edge := by
  unfold insertToken; split <;> rfl
theorem insertToken_path (c : Channel) (t : Token) : (insertToken c t).path = c.path := by
  unfold insertToken; split <;> rfl
theorem insertToken_entry (c : Channel) (t : Token) : (insertToken c t).entry = c.entry := by
  unfold insertToken; split <;> rfl

theorem insertToken_eos_items (c : Channel) : (insertToken c .eos).items = c.items := by
  unfold insertToken
  split
  · rfl
  · simp [Channel.items, List.filterMap_append]

theorem insertToken_eos_closed (c : Channel) : (insertToken c .eos).closed = true := by
  unfold insertToken
  split
  · rename_i present
    simpa [Channel.closed] using present
  · simp [Channel.closed]

theorem insertToken_closed_mono (c : Channel) (t : Token) (h : c.closed = true) :
    (insertToken c t).closed = true := by
  unfold insertToken
  split
  · exact h
  · simp only [Channel.closed] at h ⊢
    simp only [List.contains_iff_mem] at h ⊢
    exact List.mem_append_left _ h

theorem write_ids (s : State) (ids : List String) (t : Token) :
    (write s ids t).channels.map (·.id) = s.channels.map (·.id) := by
  simp only [write, List.map_map]
  apply List.map_congr_left
  intro c _
  dsimp
  split <;> simp [insertToken_id]

/-! ### Following one logical channel through placements -/

/-- The channel `c` is still present with the same items (placement may only have
    appended EOS or touched other channels). -/
def Follows (c : Channel) (st : State) : Prop :=
  ∃ d ∈ st.channels, d.id = c.id ∧ d.edge = c.edge ∧ d.path = c.path ∧ d.entry = c.entry ∧ d.items = c.items

def FollowsClosed (c : Channel) (st : State) : Prop :=
  ∃ d ∈ st.channels, d.id = c.id ∧ d.edge = c.edge ∧ d.path = c.path ∧ d.entry = c.entry ∧
    d.items = c.items ∧ d.closed = true

theorem Follows.refl (c : Channel) (st : State) (member : c ∈ st.channels) : Follows c st :=
  ⟨c, member, rfl, rfl, rfl, rfl, rfl⟩

theorem Follows.transport {c : Channel} {a b : State} (h : Follows c a) (same : b.channels = a.channels) :
    Follows c b := by
  obtain ⟨d, member, rest⟩ := h
  exact ⟨d, same ▸ member, rest⟩

theorem FollowsClosed.transport {c : Channel} {a b : State} (h : FollowsClosed c a)
    (same : b.channels = a.channels) : FollowsClosed c b := by
  obtain ⟨d, member, rest⟩ := h
  exact ⟨d, same ▸ member, rest⟩

theorem write_member (st : State) (ids : List String) (t : Token) (d : Channel)
    (member : d ∈ st.channels) :
    (if ids.contains d.id then insertToken d t else d) ∈ (write st ids t).channels := by
  simp only [write]
  exact List.mem_map.mpr ⟨d, member, rfl⟩

theorem write_follows (c : Channel) (st : State) (ids : List String) (t : Token)
    (follows : Follows c st) (safe : ids.contains c.id = true → t = .eos) :
    Follows c (write st ids t) := by
  obtain ⟨d, member, idD, edgeD, pathD, entryD, itemsD⟩ := follows
  refine ⟨_, write_member st ids t d member, ?_⟩
  by_cases selected : ids.contains d.id = true
  · have eos : t = .eos := safe (idD ▸ selected)
    subst eos
    simp only [selected, ↓reduceIte, insertToken_id, insertToken_edge, insertToken_path,
      insertToken_entry, insertToken_eos_items]
    exact ⟨idD, edgeD, pathD, entryD, itemsD⟩
  · simp only [Bool.not_eq_true] at selected
    simp only [selected, Bool.false_eq_true, ↓reduceIte]
    exact ⟨idD, edgeD, pathD, entryD, itemsD⟩

theorem write_followsClosed (c : Channel) (st : State) (ids : List String) (t : Token)
    (follows : FollowsClosed c st) (safe : ids.contains c.id = true → t = .eos) :
    FollowsClosed c (write st ids t) := by
  obtain ⟨d, member, idD, edgeD, pathD, entryD, itemsD, closedD⟩ := follows
  refine ⟨_, write_member st ids t d member, ?_⟩
  by_cases selected : ids.contains d.id = true
  · have eos : t = .eos := safe (idD ▸ selected)
    subst eos
    simp only [selected, ↓reduceIte, insertToken_id, insertToken_edge, insertToken_path,
      insertToken_entry, insertToken_eos_items]
    exact ⟨idD, edgeD, pathD, entryD, itemsD, insertToken_closed_mono d .eos closedD⟩
  · simp only [Bool.not_eq_true] at selected
    simp only [selected, Bool.false_eq_true, ↓reduceIte]
    exact ⟨idD, edgeD, pathD, entryD, itemsD, closedD⟩

theorem write_eos_closes (c : Channel) (st : State) (ids : List String)
    (follows : Follows c st) (selected : ids.contains c.id = true) :
    FollowsClosed c (write st ids .eos) := by
  obtain ⟨d, member, idD, edgeD, pathD, entryD, itemsD⟩ := follows
  refine ⟨_, write_member st ids .eos d member, ?_⟩
  have selectedD : ids.contains d.id = true := idD ▸ selected
  simp only [selectedD, ↓reduceIte, insertToken_id, insertToken_edge, insertToken_path,
    insertToken_entry, insertToken_eos_items]
  exact ⟨idD, edgeD, pathD, entryD, itemsD, insertToken_eos_closed d⟩

/-- A channel followed from `c` is selected by `output` exactly when `c` sits on
    that node/port (given distinct channel IDs in the state). -/
theorem outgoing_ids_of_follows (c : Channel) (st : State) (path : Path) (node port : String)
    (distinct : (st.channels.map (·.id)).Nodup) (follows : Follows c st) :
    ((st.outgoing path node port).map (·.id)).contains c.id = true ↔
      (c.path = path ∧ c.entry = false ∧ c.edge.src = ⟨node, port⟩) := by
  obtain ⟨d, member, idD, edgeD, pathD, entryD, _⟩ := follows
  rw [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨e, memberE, idE⟩
    have inChannels : e ∈ st.channels := (List.mem_filter.mp memberE).1
    have predicate := (List.mem_filter.mp memberE).2
    have same : e = d := eq_of_mapped_nodup (·.id) st.channels distinct e d inChannels member (idE.trans idD.symm)
    subst same
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at predicate
    exact ⟨pathD ▸ predicate.1.1, entryD ▸ predicate.1.2, edgeD ▸ predicate.2⟩
  · rintro ⟨pathC, entryC, srcC⟩
    refine ⟨d, List.mem_filter.mpr ⟨member, ?_⟩, idD⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    exact ⟨⟨pathD.trans pathC, entryD.trans entryC⟩, edgeD ▸ srcC⟩

/-- Bookkeeping carried through a fold of placements. -/
def Good (c : Channel) (st : State) : Prop := Follows c st ∧ (st.channels.map (·.id)).Nodup
def GoodClosed (c : Channel) (st : State) : Prop := FollowsClosed c st ∧ (st.channels.map (·.id)).Nodup

theorem output_item_good (c : Channel) (st : State) (path : Path) (node port : String) (item : ItemId)
    (good : Good c st) (other : c.edge.src ≠ ⟨node, port⟩) :
    Good c (output st path node port (.item item)) := by
  obtain ⟨follows, distinct⟩ := good
  refine ⟨write_follows c st _ _ follows ?_, by simpa [output, write_ids] using distinct⟩
  intro selected
  have := ((outgoing_ids_of_follows c st path node port distinct follows).mp selected).2.2
  exact absurd this other

theorem output_eos_good (c : Channel) (st : State) (path : Path) (node port : String)
    (good : Good c st) : Good c (output st path node port .eos) := by
  obtain ⟨follows, distinct⟩ := good
  exact ⟨write_follows c st _ _ follows (fun _ => rfl), by simpa [output, write_ids] using distinct⟩

theorem output_eos_goodClosed (c : Channel) (st : State) (path : Path) (node port : String)
    (good : GoodClosed c st) : GoodClosed c (output st path node port .eos) := by
  obtain ⟨follows, distinct⟩ := good
  exact ⟨write_followsClosed c st _ _ follows (fun _ => rfl), by simpa [output, write_ids] using distinct⟩

theorem output_eos_closes (c : Channel) (st : State) (path : Path) (node port : String)
    (good : Good c st) (pathC : c.path = path) (entryC : c.entry = false)
    (srcC : c.edge.src = ⟨node, port⟩) : GoodClosed c (output st path node port .eos) := by
  obtain ⟨follows, distinct⟩ := good
  refine ⟨write_eos_closes c st _ follows ?_, by simpa [output, write_ids] using distinct⟩
  exact (outgoing_ids_of_follows c st path node port distinct follows).mpr ⟨pathC, entryC, srcC⟩

theorem foldl_preserves {α β : Type} (P : α → Prop) (f : α → β → α) (xs : List β) (init : α)
    (step : ∀ a x, x ∈ xs → P a → P (f a x)) (start : P init) : P (xs.foldl f init) := by
  induction xs generalizing init with
  | nil => exact start
  | cons x xs ih =>
    exact ih (f init x) (fun a y hy => step a y (List.mem_cons_of_mem x hy)) (step init x (List.mem_cons_self ..) start)

/-- Placing plain outputs on other ports leaves the followed channel untouched. -/
theorem placeOutputs_good (c : Channel) (st : State) (path : Path) (node : NodeId)
    (outputs : List Output) (good : Good c st)
    (other : ∀ out ∈ outputs, c.edge.src ≠ ⟨node, out.port⟩) :
    Good c (outputs.foldl (fun state out => out.items.foldl
      (fun state item => output state path node out.port (.item item)) state) st) := by
  apply foldl_preserves (Good c) _ outputs st _ good
  intro a out member goodA
  apply foldl_preserves (Good c) _ out.items a _ goodA
  intro b item _ goodB
  exact output_item_good c b path node out.port item goodB (other out member)

/-- Closing every output of the node closes the followed channel and keeps its items. -/
theorem closeOutputs_goodClosed (c : Channel) (st : State) (path : Path) (n : Node) (p : Port)
    (port : p ∈ n.outputs) (good : Good c st) (pathC : c.path = path) (entryC : c.entry = false)
    (srcC : c.edge.src = ⟨n.id, p.name⟩) :
    GoodClosed c (n.outputs.foldl (fun state q => output state path n.id q.name .eos) st) := by
  obtain ⟨before, after, split⟩ := List.append_of_mem port
  rw [split, List.foldl_append, List.foldl_cons]
  apply foldl_preserves (GoodClosed c) _ after _ (fun a q _ => output_eos_goodClosed c a path n.id q.name)
  apply output_eos_closes c _ path n.id p.name _ pathC entryC srcC
  exact foldl_preserves (Good c) _ before st (fun a q _ => output_eos_good c a path n.id q.name) good

/-! ### The shape of an accepted `complete` -/

theorem complete_transition_shape (s next : State) (auth : Credentials) (outputs : List Output)
    (i : Instance) (n : Node) (found : s.instance? auth.instance = some i)
    (node : getNode s i.path i.node = .ok n)
    (h : transition s (.complete auth outputs) = .ok next) :
    (unique (outputs.map (·.port)) && outputs.length == (n.outputs.filter (·.kind == .plain)).length &&
      outputs.all (fun o => o.items.length == 1 &&
        (n.outputs.filter (·.kind == .plain)).any (·.name == o.port))) = true ∧
    ∃ s1 s2 s3 : State,
      decision s (identity ["leaf", i.id]) (Lean.toJson outputs).compress = .ok s1 ∧
      placeOutputs s1 i.path i.node outputs = .ok s2 ∧
      closeOutputs s2 i.path n = .ok s3 ∧
      next.channels = s3.channels := by
  simp only [transition, getInstance, found, Option.toExcept, node, bind, Except.bind, pure, Except.pure] at h
  cases hl : leafPolicy n with
  | error e => simp [hl] at h
  | ok policy =>
    simp only [hl] at h
    split at h
    · contradiction
    · rename_i u hr
      have checked := require_ok _ _ _ u hr
      refine ⟨checked, ?_⟩
      split at h
      · contradiction
      · rename_i s1 hd
        split at h
        · contradiction
        · rename_i s2 hp
          split at h
          · contradiction
          · rename_i s3 hc
            simp only [Except.ok.injEq] at h
            subst h
            exact ⟨s1, s2, s3, hd, hp, hc, rfl⟩

/-- Ports named by an accepted `complete` are plain; with distinct port names they
    differ from every stream port of the node. -/
theorem complete_ports_plain (n : Node) (outputs : List Output)
    (names : (n.outputs.map (·.name)).Nodup)
    (checked : (unique (outputs.map (·.port)) && outputs.length == (n.outputs.filter (·.kind == .plain)).length &&
      outputs.all (fun o => o.items.length == 1 &&
        (n.outputs.filter (·.kind == .plain)).any (·.name == o.port))) = true)
    (p : Port) (port : p ∈ n.outputs) (stream : p.kind = .stream) :
    ∀ out ∈ outputs, out.port ≠ p.name := by
  intro out member equal
  simp only [Bool.and_eq_true] at checked
  have each := List.all_eq_true.mp checked.2 out member
  simp only [Bool.and_eq_true] at each
  obtain ⟨q, memberQ, nameQ⟩ := List.any_eq_true.mp each.2
  have inOutputs : q ∈ n.outputs := (List.mem_filter.mp memberQ).1
  have plainQ : (q.kind == PortKind.plain) = true := (List.mem_filter.mp memberQ).2
  have sameName : q.name = p.name := by
    have := (beq_iff_eq.mp nameQ)
    exact this.trans equal
  have same : q = p := eq_of_mapped_nodup (·.name) n.outputs names q p inOutputs port sameName
  subst same
  simp [stream] at plainQ

/-! ### Main statement of this stage -/

theorem complete_stream_output_final (oracle : ScopedOracle) {s last : State}
    {auth : Credentials} {outputs : List Output} {rest : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s
      (.complete auth outputs :: rest) last)
    (safe : Invariants s) (notAbsorbed : absorbed s (.complete auth outputs) = false)
    (i : Instance) (found : s.instance? auth.instance = some i)
    (n : Node) (node : getNode s i.path i.node = .ok n)
    (names : (n.outputs.map (·.name)).Nodup)
    (p : Port) (port : p ∈ n.outputs) (stream : p.kind = .stream)
    (c : Channel) (outgoing : c ∈ s.outgoing i.path i.node p.name) :
    ∃ d ∈ last.channels, d.id = c.id ∧ d.closed = true ∧
      d.items.Perm (outputItems ((oracle i.path).leaf i.node i.inputs) p.name) := by
  cases run with
  | cons allowed accepted tail =>
    rename_i middle
    -- The channel's items conform at the moment of completion.
    have memberC : c ∈ s.channels := (List.mem_filter.mp outgoing).1
    have predicate := (List.mem_filter.mp outgoing).2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at predicate
    obtain ⟨⟨pathC, entryC⟩, srcC⟩ := predicate
    have conforms : c.items.Perm (outputItems ((oracle i.path).leaf i.node i.inputs) p.name) := by
      have h := allowed
      simp only [oracleConforms, notAbsorbed, Bool.false_eq_true, ↓reduceIte, found,
        getNode_node? s i.path i.node n node, Option.any_some, Bool.and_eq_true] at h
      have streams := List.all_eq_true.mp h.2 p (List.mem_filter.mpr ⟨port, by simp [stream]⟩)
      have channel := List.all_eq_true.mp streams c outgoing
      simpa using channel
    -- The accepted step executes the operational body.
    rcases step_ok_cases s _ middle accepted with ⟨absorbedTrue, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [notAbsorbed] at absorbedTrue
      contradiction
    · have executed := prepareWith_body transitionOrIdle s middle _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨checked, s1, s2, s3, hd, hp, hc, channels⟩ :=
        complete_transition_shape s middle auth outputs i n found node executed
      -- Follow `c` through the completion.
      have distinct : (s.channels.map (·.id)).Nodup := by
        simp only [Invariants, invariants, Bool.and_eq_true] at safe
        exact unique_nodup _ safe.1.1.1.1.1.1.2
      have good1 : Good c s1 := by
        refine ⟨Follows.refl c s memberC |>.transport (decision_channels s s1 _ _ hd), ?_⟩
        rw [decision_channels s s1 _ _ hd]
        exact distinct
      have good2 : Good c s2 := by
        rw [placeOutputs_value s1 s2 _ _ _ hp]
        apply placeOutputs_good c s1 i.path i.node outputs good1
        intro out member equal
        have := complete_ports_plain n outputs names checked p port stream out member
        apply this
        rw [srcC] at equal
        exact (PortRef.mk.inj equal).2.symm
      have good3 : GoodClosed c s3 := by
        rw [closeOutputs_value s2 s3 _ _ hc]
        have srcN : c.edge.src = ⟨n.id, p.name⟩ := by rw [getNode_id s i.path i.node n node]; exact srcC
        exact closeOutputs_goodClosed c s2 i.path n p port good2 pathC entryC srcN
      obtain ⟨d, memberD, idD, _, _, _, itemsD, closedD⟩ := good3.1.transport channels
      -- Closed channels keep their history to the end of the run.
      have safeMiddle : Invariants middle := preserves_invariants s middle _ safe accepted
      obtain ⟨e, memberE, idE, placedE⟩ := tail.retains_closed_channel safeMiddle d memberD closedD
      refine ⟨e, memberE, idE.trans idD, ?_, ?_⟩
      · simpa [Channel.closed, placedE] using closedD
      · have itemsE : e.items = d.items := by simp [Channel.items, placedE]
        rw [itemsE, itemsD]
        exact conforms


end Suimon
