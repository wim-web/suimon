import Suimon.Theorems.Origins

namespace Suimon
open Effects

/-! ### Plain outputs after a conforming complete -/

theorem find?_filter_of_imp {α : Type} (p f : α → Bool) (l : List α) (h : ∀ x, p x = true → f x = true) :
    (l.filter f).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases px : p x = true
    · have fx := h x px
      simp [List.filter_cons, fx, List.find?_cons, px]
    · simp only [Bool.not_eq_true] at px
      cases fx : f x <;> simp [List.filter_cons, fx, List.find?_cons, px, ih]

theorem find?_eq_of_perm_nodup (l₁ l₂ : List Output) (perm : l₁.Perm l₂)
    (nodup : (l₁.map (·.port)).Nodup) (q : PortName) :
    l₁.find? (·.port == q) = l₂.find? (·.port == q) := by
  have nodup₂ : (l₂.map (·.port)).Nodup := (perm.map (·.port)).nodup_iff.mp nodup
  cases h₁ : l₁.find? (·.port == q) with
  | none =>
    symm
    rw [List.find?_eq_none]
    intro o mem
    exact List.find?_eq_none.mp h₁ o (perm.symm.subset mem)
  | some o =>
    have memberO : o ∈ l₂ := perm.subset (List.mem_of_find?_eq_some h₁)
    have portO : (o.port == q) = true := by simpa using List.find?_some h₁
    cases h₂ : l₂.find? (·.port == q) with
    | none => exact absurd portO (by simpa using List.find?_eq_none.mp h₂ o memberO)
    | some o' =>
      have memberO' : o' ∈ l₂ := List.mem_of_find?_eq_some h₂
      have portO' : (o'.port == q) = true := by simpa using List.find?_some h₂
      have same : o = o' := eq_of_mapped_nodup (·.port) l₂ nodup₂ o o' memberO memberO'
        ((beq_iff_eq.mp portO).trans (beq_iff_eq.mp portO').symm)
      rw [same]

/-- The single item a conforming complete places on plain port `q`. -/
theorem complete_plain_item (n : Node) (outputs : List Output) (expected : List Output)
    (names : (n.outputs.map (·.name)).Nodup)
    (checked : (unique (outputs.map (·.port)) && outputs.length == (n.outputs.filter (·.kind == .plain)).length &&
      outputs.all (fun o => o.items.length == 1 &&
        (n.outputs.filter (·.kind == .plain)).any (·.name == o.port))) = true)
    (perm : outputs.Perm (expected.filter fun out => n.outputs.any (fun p => p.name == out.port && p.kind == .plain)))
    (q : Port) (port : q ∈ n.outputs) (plain : q.kind = .plain) :
    ∃ x, outputs.find? (·.port == q.name) = some { port := q.name, items := [x] } ∧
      outputItems expected q.name = [x] := by
  simp only [Bool.and_eq_true] at checked
  obtain ⟨⟨uniq, len⟩, all⟩ := checked
  have nodupPorts : (outputs.map (·.port)).Nodup := unique_nodup _ uniq
  -- the plain port names of n, as a nodup list
  let ps := n.outputs.filter (·.kind == .plain)
  have nodupPs : (ps.map (·.name)).Nodup := by
    have : (ps.map (·.name)).Sublist (n.outputs.map (·.name)) := List.filter_sublist.map _
    exact names.sublist this
  have subset : (outputs.map (·.port)) ⊆ ps.map (·.name) := by
    intro name mem
    obtain ⟨o, memberO, rfl⟩ := List.mem_map.mp mem
    have each := List.all_eq_true.mp all o memberO
    simp only [Bool.and_eq_true] at each
    obtain ⟨p, memberP, nameP⟩ := List.any_eq_true.mp each.2
    exact List.mem_map.mpr ⟨p, memberP, beq_iff_eq.mp nameP⟩
  have qInPs : q.name ∈ ps.map (·.name) := List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨port, by simp [plain]⟩, rfl⟩
  have qInOutputs : q.name ∈ outputs.map (·.port) := by
    apply Classical.byContradiction
    intro absent
    have subset' : (outputs.map (·.port)) ⊆ (ps.map (·.name)).erase q.name := by
      intro name mem
      have ne : name ≠ q.name := fun eq => absent (eq ▸ mem)
      exact (List.mem_erase_of_ne ne).mpr (subset mem)
    have bound := nodupPorts.length_le_of_subset subset'
    rw [List.length_erase_of_mem qInPs] at bound
    have lenEq : (outputs.map (·.port)).length = (ps.map (·.name)).length := by
      simp only [List.length_map]
      exact beq_iff_eq.mp len
    have pos : 0 < (ps.map (·.name)).length := List.length_pos_of_mem qInPs
    omega
  obtain ⟨o, memberO, portO⟩ := List.mem_map.mp qInOutputs
  have each := List.all_eq_true.mp all o memberO
  simp only [Bool.and_eq_true] at each
  obtain ⟨x, itemsO⟩ : ∃ x, o.items = [x] := by
    have := beq_iff_eq.mp each.1
    match hi : o.items, this with
    | [x], _ => exact ⟨x, rfl⟩
  have oShape : o = { port := q.name, items := [x] } := by
    cases o with
    | mk p items =>
      simp only at portO itemsO
      rw [portO, itemsO]
  have findOutputs : outputs.find? (·.port == q.name) = some o := by
    cases h : outputs.find? (·.port == q.name) with
    | none => exact absurd (by simp [portO] : (o.port == q.name) = true) (by simpa using List.find?_eq_none.mp h o memberO)
    | some o' =>
      have memberO' : o' ∈ outputs := List.mem_of_find?_eq_some h
      have portO' : (o'.port == q.name) = true := by simpa using List.find?_some h
      have := eq_of_mapped_nodup (·.port) outputs nodupPorts o' o memberO' memberO ((beq_iff_eq.mp portO').trans portO.symm)
      rw [this]
  refine ⟨x, by rw [findOutputs, oShape], ?_⟩
  have findFiltered := find?_eq_of_perm_nodup outputs _ perm nodupPorts q.name
  have findExpected : expected.find? (·.port == q.name) = some o := by
    rw [← find?_filter_of_imp (·.port == q.name) (fun out => n.outputs.any (fun p => p.name == out.port && p.kind == .plain)) expected]
    · rw [← findFiltered, findOutputs]
    · intro out portOut
      apply List.any_eq_true.mpr
      exact ⟨q, port, by simp [beq_iff_eq.mp portOut, plain]⟩
  simp [outputItems, findExpected, oShape]

theorem plain_items_singleton (c : Channel) (safe : channelOK c = true) (plain : c.kind = .plain) (x : ItemId)
    (present : x ∈ c.items) : c.items = [x] := by
  simp only [channelOK, Bool.and_eq_true] at safe
  have bound := safe.2
  simp only [plain, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at bound
  cases hi : c.items with
  | nil => rw [hi] at present; simp at present
  | cons y ys =>
    cases ys with
    | nil =>
      rw [hi] at present
      have : x = y := by simpa using present
      rw [this]
    | cons z zs => rw [hi] at bound; simp at bound

/-- After a conforming, non-absorbed complete, each plain output channel of the leaf ends
    closed with exactly the oracle's item for that port. -/
theorem complete_plain_output_final (oracle : ScopedOracle) {s last : State}
    {auth : Credentials} {outputs : List Output} {rest : List Op}
    (run : ConformingSteps (fun s op => oracleConforms oracle s op = true) s
      (.complete auth outputs :: rest) last)
    (safe : Invariants s) (notAbsorbed : absorbed s (.complete auth outputs) = false)
    (i : Instance) (found : s.instance? auth.instance = some i)
    (n : Node) (node : getNode s i.path i.node = .ok n)
    (names : (n.outputs.map (·.name)).Nodup)
    (q : Port) (port : q ∈ n.outputs) (plain : q.kind = .plain)
    (c : Channel) (outgoing : c ∈ s.outgoing i.path i.node q.name) (kindC : c.kind = .plain) :
    ∃ d ∈ last.channels, d.id = c.id ∧ d.closed = true ∧
      d.items = outputItems ((oracle i.path).leaf i.node i.inputs) q.name := by
  cases run with
  | cons allowed accepted tail =>
    rename_i middle
    have memberC : c ∈ s.channels := (List.mem_filter.mp outgoing).1
    have predicate := (List.mem_filter.mp outgoing).2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at predicate
    obtain ⟨⟨pathC, entryC⟩, srcC⟩ := predicate
    -- conformance: plain outputs are a permutation of the oracle's plain outputs
    have perm : outputs.Perm (((oracle i.path).leaf i.node i.inputs).filter
        fun out => n.outputs.any (fun p => p.name == out.port && p.kind == .plain)) := by
      have h := allowed
      simp only [oracleConforms, notAbsorbed, Bool.false_eq_true, ↓reduceIte, found,
        getNode_node? s i.path i.node n node, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    rcases step_ok_cases s _ middle accepted with ⟨absorbedTrue, _⟩ | ⟨_, _, prepared, _, _⟩
    · rw [notAbsorbed] at absorbedTrue; contradiction
    · have executed := prepareWith_body transitionOrIdle s middle _ prepared
      simp only [transitionOrIdle] at executed
      obtain ⟨i', n', found', node', _, checked, view, _⟩ := effect_complete s middle auth outputs executed
      rw [found] at found'; cases found'
      rw [node] at node'; cases node'
      obtain ⟨x, findO, expectedX⟩ := complete_plain_item n outputs _ names checked perm q port plain
      have memberO := List.mem_of_find?_eq_some findO
      have nodeC : c.edge.src.node = i.node := by rw [srcC]
      have portC : c.edge.src.port = q.name := by rw [srcC]
      have nid := getNode_id s i.path i.node n node
      let ws := outputWrites i.path i.node outputs ++ eosWrites i.path n
      have itemWrite : Write.out c.path c.edge.src.node c.edge.src.port (.item x) ∈ ws := by
        apply List.mem_append_left
        rw [pathC, nodeC, portC]
        exact List.mem_flatMap.mpr ⟨_, memberO, List.mem_map.mpr ⟨x, by simp, rfl⟩⟩
      have eosWrite : Write.out c.path c.edge.src.node c.edge.src.port .eos ∈ ws := by
        apply List.mem_append_right
        rw [pathC, nodeC, portC, ← nid]
        exact List.mem_map.mpr ⟨q, port, rfl⟩
      have distinct := safe.channelIds
      obtain ⟨d1, member1, id1, layout1, item1⟩ := applyWrites_token ws s c memberC entryC distinct (.item x) itemWrite
      obtain ⟨d2, member2, id2, layout2, eos2⟩ := applyWrites_token ws s c memberC entryC distinct .eos eosWrite
      have distinctW : ((applyWrites ws s).channels.map (·.id)).Nodup := by rw [applyWrites_ids]; exact distinct
      have same : d1 = d2 := eq_of_mapped_nodup (·.id) _ distinctW d1 d2 member1 member2 (id1.trans id2.symm)
      subst same
      have inView : d1.core ∈ middle.placedView := by
        rw [view]; exact placedView_member member1
      obtain ⟨e, memberE, coreE⟩ := List.mem_map.mp inView
      have idE : e.id = c.id := by simpa using (congrArg Channel.id coreE).trans id1
      have layoutE : e.layout = c.layout := by
        have := congrArg Channel.layout coreE
        simpa [Channel.core_layout] using this.trans layout1
      have placedE : e.placed = d1.placed := by simpa using congrArg Channel.placed coreE
      have closedE : e.closed = true := by
        simp only [Channel.closed, placedE]
        exact List.contains_iff_mem.mpr eos2
      have safeMiddle : Invariants middle := preserves_invariants s middle _ safe accepted
      have safeLast : Invariants last := tail.invariants safeMiddle
      obtain ⟨f, memberF, idF, placedF⟩ := tail.retains_closed_channel safeMiddle e memberE closedE
      obtain ⟨f', memberF', idF', layoutF', _⟩ := run_image tail safeMiddle e memberE
      have sameF : f' = f := unique_channel safeLast memberF' memberF (idF'.trans idF.symm)
      subst sameF
      have kindF : f'.kind = .plain := by
        have := congrArg Channel.kind (layoutF'.trans layoutE)
        simpa using this.trans kindC
      have presentF : x ∈ f'.items := by
        rw [Effects.item_mem, placedF, placedE]
        exact item1
      have okF : channelOK f' = true := by
        simp only [Invariants, invariants, Bool.and_eq_true] at safeLast
        exact List.all_eq_true.mp safeLast.1.1.1.1.1.1.1 f' memberF
      refine ⟨f', memberF, idF.trans idE, ?_, ?_⟩
      · simpa [Channel.closed, placedF] using closedE
      · rw [plain_items_singleton f' okF kindF x presentF, expectedX]

end Suimon
