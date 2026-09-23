import Suimon.Theorems.Basic

/-! Helper facts for the delivery theorems: membership in the filtered views of a state, the input
    shape and kind of a placement, how a Single connection resolves, and what a settlement records. -/

namespace Suimon.Delivery
open State

/-! ### Lists -/

theorem mem_map_replace' {α : Type} {l : List α} {q : α → Bool} {y z : α}
    (h : z ∈ l.map fun x => if q x then y else x) : z = y ∨ (z ∈ l ∧ q z = false) := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  by_cases hq : q x = true
  · simp [hq]
  · simp only [hq, Bool.false_eq_true, ↓reduceIte]
    exact Or.inr ⟨hx, trivial⟩

theorem mapM_cons_eq_some {α β : Type} {f : α → Option β} {x : α} {l : List α} {ys : List β} :
    (x :: l).mapM f = some ys ↔ ∃ y, f x = some y ∧ ∃ ys', l.mapM f = some ys' ∧ y :: ys' = ys := by
  simp [List.mapM_cons, Option.bind_eq_some_iff]

theorem mapM_some_mono {α β : Type} {f g : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → (∀ x ∈ l, ∀ y, f x = some y → g x = some y) →
      l.mapM g = some ys
  | [], ys, h, _ => by simpa using h
  | x :: l, ys, h, hfg => by
    obtain ⟨y, hy, ys', hl, rfl⟩ := mapM_cons_eq_some.mp h
    exact mapM_cons_eq_some.mpr ⟨y, hfg x List.mem_cons_self y hy, ys',
      mapM_some_mono hl fun z hz => hfg z (List.mem_cons_of_mem x hz), rfl⟩

theorem mapM_eq_some_nil {α β : Type} {f : α → Option β} {l : List α} (h : l.mapM f = some []) : l = [] := by
  cases l with
  | nil => rfl
  | cons x l =>
    obtain ⟨y, -, ys', -, h⟩ := mapM_cons_eq_some.mp h
    cases h

/-! ### Views of a state -/

@[simp] theorem mem_invocationsOf {s : State} {path : Path} {name : String} {i : Invocation} :
    i ∈ s.invocationsOf path name ↔ i ∈ s.invocations ∧ i.run = path ∧ i.placement = name := by
  simp [invocationsOf]

@[simp] theorem mem_resultsOf {s : State} {path : Path} {name : String} {r : Result} :
    r ∈ s.resultsOf path name ↔ r ∈ s.results ∧ r.run = path ∧ r.placement = name := by
  simp [resultsOf]

@[simp] theorem mem_deliveriesOn {s : State} {path : Path} {index : Nat} {d : Delivery} :
    d ∈ s.deliveriesOn path index ↔ d ∈ s.deliveries ∧ d.run = path ∧ d.connection = index := by
  simp [deliveriesOn]

@[simp] theorem mem_eligible {s : State} {path : Path} {c : Connection} {r : Result} :
    r ∈ s.eligible path c ↔ r ∈ s.results ∧ r.run = path ∧ r.placement = c.source ∧ (c.arm = none ∨ r.arm = c.arm) := by
  simp only [eligible, List.mem_filter, mem_resultsOf, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq,
    and_assoc]

theorem invocationEnded_iff {s : State} {i : Invocation} :
    s.invocationEnded i = true ↔ i.status ≠ .active ∧
      (∀ c ∈ s.calls, c.owner = i.id → c.task = none → c.status.ended = true) ∧
      (∀ r ∈ s.runs, r.owner = some i.id → r.task = none → r.complete = true) ∧
      (∀ e ∈ s.executions, e.id = i.id → e.complete = true) := by
  simp only [invocationEnded, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_filter,
    beq_iff_eq, Option.isNone_iff_eq_none, and_imp, and_assoc]

theorem holdsSlot_eq_false {s : State} {e : Execution} {t : TaskState} :
    s.holdsSlot e t = false ↔ t.status ≠ .active ∧
      ∀ c ∈ s.calls, c.owner = e.id → c.task = some t.name → c.status ≠ .cancelling := by
  simp only [holdsSlot, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, List.any_eq_false,
    Bool.and_eq_true, beq_iff_eq, not_and, and_imp]

theorem taskEnded_iff {s : State} {e : Execution} {t : TaskState} :
    s.taskEnded e t = true ↔ t.status.ended = true ∧ t.status ≠ .active ∧
      (∀ c ∈ s.calls, c.owner = e.id → c.task = some t.name → c.status ≠ .cancelling) ∧
      (∀ r ∈ s.runs, r.owner = some e.id → r.task = some t.name → r.complete = true) := by
  simp only [taskEnded, Bool.and_eq_true, Bool.not_eq_true', holdsSlot_eq_false, List.all_eq_true, List.mem_filter,
    beq_iff_eq, and_imp, and_assoc]

/-! ### Input connections -/

theorem mem_inputs {w : Workflow} {name : String} {j : Nat} {c : Connection} :
    (j, c) ∈ w.inputs name ↔ w.connections[j]? = some c ∧ c.target = name := by
  unfold Workflow.inputs
  constructor
  · intro h
    obtain ⟨⟨c', j'⟩, hmem, heq⟩ := List.mem_filterMap.mp h
    by_cases ht : c'.target = name
    · simp only [ht, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨List.mem_zipIdx_iff_getElem?.mp hmem, ht⟩
    · simp [ht] at heq
  · rintro ⟨hc, ht⟩
    exact List.mem_filterMap.mpr ⟨(c, j), List.mem_zipIdx_iff_getElem?.mpr hc, by simp [ht]⟩

theorem inputs_map_snd_aux (name : String) :
    ∀ (l : List Connection) (n : Nat),
      ((l.zipIdx n).filterMap fun (x : Connection × Nat) =>
        if x.1.target == name then some (x.2, x.1) else none).map (·.2) = l.filter (·.target == name)
  | [], _ => rfl
  | c :: l, n => by
    have ih := inputs_map_snd_aux name l (n + 1)
    rw [List.zipIdx_cons, List.filterMap_cons, List.filter_cons]
    by_cases h : (c.target == name) = true
    · simp only [h, ↓reduceIte, List.map_cons, ih]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ih]

theorem inputs_map_snd (w : Workflow) (name : String) : (w.inputs name).map (·.2) = w.incoming name :=
  inputs_map_snd_aux name w.connections 0

/-! ### Kinds -/

/-- More fuel never changes a derived kind. --/
theorem kind?_mono {p : Program} {w : Workflow} :
    ∀ {n m : Nat} {x : String} {k : Kind}, w.kind? p n x = some k → n ≤ m → w.kind? p m x = some k
  | 0, _, _, _, h, _ => by simp [Workflow.kind?] at h
  | n + 1, m, x, k, h, hle => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Workflow.kind?, option_bind_eq_some] at h ⊢
    obtain ⟨pl, hpl, sources, hsrc, h⟩ := h
    refine ⟨pl, hpl, sources, ?_, h⟩
    exact mapM_some_mono hsrc fun c _ k' hk => kind?_mono hk (by omega)

/-- The kind of input a shape supplies, for placements other than Merge. --/
def shapeInput : Workflow.Shape → Option (Option Kind)
  | .none => some none
  | .entry => some (some .single)
  | .single .. => some (some .single)
  | .stream .. => some (some .stream)
  | .merge _ => none

/-- The derived kind of a placement other than Merge is the §5.2 rule applied to the input its shape
    supplies; an entry has no input connection. --/
theorem outputKind?_shape {p : Program} {w : Workflow} {name : String} {sh : Workflow.Shape} {k : Kind}
    {pl : Placement} (hsh : w.shape? p name = some sh) (hk : w.outputKind? p name = some k)
    (hpl : w.placement? name = some pl) (hm : ∀ e, pl.control ≠ .merge e) :
    ∃ inp, shapeInput sh = some inp ∧ p.outputKind pl.control inp = some k ∧
      (sh = .entry → w.incoming name = []) := by
  unfold Workflow.outputKind? Workflow.depth at hk
  simp only [Workflow.kind?, option_bind_eq_some, hpl, Option.some.injEq, exists_eq_left'] at hk
  obtain ⟨sources, hsrc, inp, hcomb, hk⟩ := hk
  unfold Workflow.shape? at hsh
  simp only [option_bind_eq_some, hpl, Option.some.injEq, exists_eq_left', Bool.false_eq_true,
    ↓reduceIte] at hsh
  have hinc := inputs_map_snd w name
  unfold Workflow.combineInput at hcomb
  by_cases he : w.isEntry name = true
  · simp only [he, ↓reduceIte, pure, Option.some.injEq] at hsh
    subst hsh
    simp only [he, ↓reduceIte] at hcomb
    by_cases hs : sources.isEmpty = true
    · simp only [hs, ↓reduceIte, Option.some.injEq] at hcomb
      subst hcomb
      refine ⟨_, rfl, hk, fun _ => ?_⟩
      have hs' : sources = [] := List.isEmpty_iff.mp hs
      subst hs'
      exact mapM_eq_some_nil hsrc
    · simp [hs] at hcomb
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at hsh hcomb
    split at hsh
    · rename_i hnil
      simp only [pure, Option.some.injEq] at hsh
      subst hsh
      rw [hnil, List.map_nil] at hinc
      rw [← hinc] at hsrc
      simp only [List.mapM_nil, pure, Option.some.injEq] at hsrc
      subst hsrc
      simp only [Option.some.injEq] at hcomb
      subst hcomb
      exact ⟨_, rfl, hk, fun h => by cases h⟩
    · rename_i j c hone
      rw [hone] at hinc
      simp only [List.map_cons, List.map_nil] at hinc
      rw [← hinc, List.mapM_cons] at hsrc
      simp only [List.mapM_nil, option_bind_eq_some, pure, Option.some.injEq] at hsrc
      obtain ⟨k', hk', _, rfl, rfl⟩ := hsrc
      have hk'' := kind?_mono hk' (Nat.le_succ _)
      simp only [List.all_nil, ↓reduceIte, Option.some.injEq] at hcomb
      subst hcomb
      unfold Workflow.outputKind? Workflow.depth at hsh
      rw [hk''] at hsh
      cases k' <;> simp only [pure, Option.some.injEq] at hsh <;> subst hsh <;>
        exact ⟨_, rfl, hk, fun h => by cases h⟩
    · simp at hsh

theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → ∀ x ∈ l, ∃ y ∈ ys, f x = some y
  | [], _, _, x, hx => by cases hx
  | a :: l, ys, h, x, hx => by
    obtain ⟨y, hy, ys', hl, rfl⟩ := mapM_cons_eq_some.mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨y', hy', hfy⟩ := mapM_mem hl x hx
      exact ⟨y', List.mem_cons_of_mem _ hy', hfy⟩

/-- A Merge with a derived kind takes only Single inputs (§9.2). --/
theorem merge_input_single {p : Program} {w : Workflow} {name : String} {pl : Placement} {e : ValueType} {k : Kind}
    (hpl : w.placement? name = some pl) (hm : pl.control = .merge e) (hk : w.outputKind? p name = some k)
    {c : Connection} (hc : c ∈ w.incoming name) : w.outputKind? p c.source = some .single := by
  unfold Workflow.outputKind? Workflow.depth at hk ⊢
  simp only [Workflow.kind?, option_bind_eq_some, hpl, Option.some.injEq, exists_eq_left'] at hk
  obtain ⟨sources, hsrc, inp, hcomb, hk⟩ := hk
  rw [hm] at hk
  have hinp : inp = some .single := by
    rcases inp with _ | (_ | _) <;> simp [Program.outputKind] at hk ⊢
  subst hinp
  obtain ⟨kc, hkc, hfc⟩ := mapM_mem hsrc c hc
  have hall : ∀ k' ∈ sources, k' = .single := by
    unfold Workflow.combineInput at hcomb
    split at hcomb
    · split at hcomb
      · rename_i hempty
        rw [List.isEmpty_iff.mp hempty] at hkc
        cases hkc
      · cases hcomb
    · split at hcomb
      · cases hcomb
      · rename_i kind rest
        split at hcomb
        · rename_i hrest
          simp only [Option.some.injEq] at hcomb
          intro k' hk'
          rcases List.mem_cons.mp hk' with rfl | hk'
          · exact hcomb
          · have := List.all_eq_true.mp hrest k' hk'
            simp only [beq_iff_eq] at this
            rw [this, hcomb]
        · cases hcomb
  rw [hall kc hkc] at hfc
  exact kind?_mono hfc (Nat.le_succ _)

/-! ### Resolving a Single connection -/

theorem resolveSingle_of_cons {s : State} {path : Path} {j : Nat} {c : Connection} {d : Delivery}
    {rest : List Delivery} (h : s.deliveriesOn path j = d :: rest) :
    s.resolveSingle path j c = match d.outcome with
      | .value v => .value d.source (some v)
      | .trigger => .value d.source none
      | .failed => .transformFailed := by
  unfold resolveSingle
  rw [h]
  rfl

theorem resolveSingle_of_nil {s : State} {path : Path} {j : Nat} {c : Connection}
    (h : s.deliveriesOn path j = []) :
    s.resolveSingle path j c = match s.settled? path c.source with
      | none => .pending
      | some x => match armOutcome x c.arm with
        | .normal => .pending
        | .skipped => .skipped
        | .failed | .upstreamFailed => .failure := by
  unfold resolveSingle
  rw [h]
  rfl

/-- A resolution other than a delivered value or a failed transform means nothing was delivered and
    the source settled without a value on the connection's arm. --/
theorem resolveSingle_no_delivery {s : State} {path : Path} {j : Nat} {c : Connection}
    (h : s.resolveSingle path j c = .skipped ∨ s.resolveSingle path j c = .failure) :
    s.deliveriesOn path j = [] ∧ ∃ x, s.settled? path c.source = some x ∧ armOutcome x c.arm ≠ .normal := by
  rcases hd : s.deliveriesOn path j with _ | ⟨d, rest⟩
  · rw [resolveSingle_of_nil hd] at h
    refine ⟨rfl, ?_⟩
    rcases hx : s.settled? path c.source with _ | x
    · simp [hx] at h
    · refine ⟨x, rfl, ?_⟩
      intro hn
      simp [hx, hn] at h
  · rw [resolveSingle_of_cons hd] at h
    split at h <;> simp at h

theorem resolveSingle_value_iff {s : State} {path : Path} {j : Nat} {c : Connection} {src : ResultId}
    {inp : Option Value} :
    s.resolveSingle path j c = .value src inp ↔ ∃ d rest, s.deliveriesOn path j = d :: rest ∧ d.source = src ∧
      ((∃ v, d.outcome = .value v ∧ inp = some v) ∨ (d.outcome = .trigger ∧ inp = none)) := by
  constructor
  · intro h
    rcases hd : s.deliveriesOn path j with _ | ⟨d, rest⟩
    · rw [resolveSingle_of_nil hd] at h
      split at h
      · simp at h
      · split at h <;> simp at h
    · rw [resolveSingle_of_cons hd] at h
      refine ⟨d, rest, rfl, ?_⟩
      split at h <;> rename_i hout <;> simp only [Resolution.value.injEq, reduceCtorEq] at h
      · exact ⟨h.1.symm ▸ rfl, Or.inl ⟨_, hout, h.2.symm⟩⟩
      · exact ⟨h.1.symm ▸ rfl, Or.inr ⟨hout, h.2.symm⟩⟩
  · rintro ⟨d, rest, hd, rfl, ⟨v, hv, rfl⟩ | ⟨hv, rfl⟩⟩ <;> rw [resolveSingle_of_cons hd, hv]

/-- The deliveries on a connection only grow at the end. --/
theorem deliveriesOn_prefix {s t : State} (g : s.Grows t) (path : Path) (j : Nat) :
    s.deliveriesOn path j <+: t.deliveriesOn path j := by
  obtain ⟨rest, hrest⟩ := g.deliveries
  refine ⟨rest.filter fun d => d.run == path && d.connection == j, ?_⟩
  simp only [deliveriesOn, ← hrest, List.filter_append]

/-- Once a connection is resolved, the resolution stays, unless a delivery arrives where nothing was
    delivered. --/
theorem resolveSingle_stable {s t : State} (g : s.Grows t) {path : Path} {j : Nat} {c : Connection}
    (hne : s.resolveSingle path j c ≠ .pending)
    (hnil : s.deliveriesOn path j = [] → t.deliveriesOn path j = []) :
    t.resolveSingle path j c = s.resolveSingle path j c := by
  rcases hd : s.deliveriesOn path j with _ | ⟨d, rest⟩
  · rw [resolveSingle_of_nil (hnil hd), resolveSingle_of_nil hd]
    rw [resolveSingle_of_nil hd] at hne
    rcases hx : s.settled? path c.source with _ | x
    · simp [hx] at hne
    · rw [g.settled?_eq_some hx]
  · obtain ⟨rest', hrest'⟩ := deliveriesOn_prefix g path j
    rw [hd] at hrest'
    rw [resolveSingle_of_cons hd, resolveSingle_of_cons (rest := rest ++ rest') (by rw [← hrest']; rfl)]

/-! ### Streams and arms -/

theorem streamEnd?_eq_some {s : State} {path : Path} {j : Nat} {c : Connection} {o : Outcome} :
    s.streamEnd? path j c = some o ↔ ∃ x, s.settled? path c.source = some x ∧
      (∀ r ∈ s.eligible path c, (s.delivery? path j r.id).isSome) ∧ o = armOutcome x c.arm := by
  unfold streamEnd?
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff, List.all_eq_true, pure,
    Option.some.injEq]
  constructor
  · rintro ⟨x, hx, hall, rfl⟩
    exact ⟨x, hx, hall, rfl⟩
  · rintro ⟨x, hx, hall, rfl⟩
    exact ⟨x, hx, hall, rfl⟩

theorem armOutcome_none (x : Settled) : armOutcome x none = x.outcome := rfl

theorem armOutcome_nil {x : Settled} (h : x.arms = []) (a : Option String) : armOutcome x a = x.outcome := by
  cases a <;> simp [armOutcome, h]

theorem find?_map_pair {arms : List String} {f : String → Outcome} {b : String} :
    (arms.map fun a => (a, f a)).find? (·.1 == b) = if b ∈ arms then some (b, f b) else none := by
  induction arms with
  | nil => simp
  | cons a rest ih =>
    by_cases hab : a = b
    · subst hab; simp
    · have hne : (a == b) = false := by simpa using hab
      simp only [List.map_cons, List.find?_cons, hne, ih, List.mem_cons]
      by_cases hb : b ∈ rest
      · simp [hb]
      · simp [hb, Ne.symm hab]

/-- A branch settlement records one outcome per arm; an unknown arm reads the overall outcome. --/
theorem armOutcome_arms {x : Settled} {arms : List String} {f : String → Outcome}
    (h : x.arms = arms.map fun a => (a, f a)) (b : String) :
    armOutcome x (some b) = if b ∈ arms then f b else x.outcome := by
  simp only [armOutcome, h, find?_map_pair]
  by_cases hb : b ∈ arms <;> simp [hb]

end Suimon.Delivery
