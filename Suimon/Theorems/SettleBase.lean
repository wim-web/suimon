import Suimon.Theorems.Basic

/-! Helpers for the settlement theorems (§10.3, §9.1, §4.5): lists updated by key, the ending check
    of an invocation, the stability of connection resolutions, and what a settlement records. -/

namespace Suimon.Settle

open State

section Lists
variable {α β : Type}

/-- A member of a list updated by key is the new element, or an old member with another key. --/
theorem mem_replace [BEq β] [LawfulBEq β] {l : List α} {f : α → β} {y z : α}
    (h : z ∈ l.map fun x => if f x == f y then y else x) : z = y ∨ (z ∈ l ∧ f z ≠ f y) := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  by_cases hxy : f x = f y
  · simp [hxy]
  · simp [hxy, hx]

theorem mem_replace_of_mem [BEq β] [LawfulBEq β] {l : List α} {f : α → β} {y x : α} (hx : x ∈ l)
    (hne : f x ≠ f y) : x ∈ l.map fun x => if f x == f y then y else x :=
  List.mem_map.mpr ⟨x, hx, by simp [hne]⟩

theorem mem_replace_self [BEq β] [LawfulBEq β] {l : List α} {f : α → β} {y x : α} (hx : x ∈ l)
    (heq : f x = f y) : y ∈ l.map fun x => if f x == f y then y else x :=
  List.mem_map.mpr ⟨x, hx, by simp [heq]⟩

theorem filter_prefix {l l' : List α} (h : l <+: l') (q : α → Bool) : l.filter q <+: l'.filter q := by
  obtain ⟨rest, rfl⟩ := h
  exact ⟨rest.filter q, by rw [List.filter_append]⟩

end Lists

/-! ### Ending checks -/

theorem invocationEnded_iff {s : State} {i : Invocation} :
    s.invocationEnded i = true ↔ i.status ≠ .active ∧
      (∀ c ∈ s.calls, c.owner = i.id → c.task = none → c.status.ended = true) ∧
      (∀ r ∈ s.runs, r.owner = some i.id → r.task = none → r.complete = true) ∧
      (∀ e ∈ s.executions, e.id = i.id → e.complete = true) := by
  simp only [State.invocationEnded, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_filter, beq_iff_eq, Option.isNone_iff_eq_none, and_imp, and_assoc]

/-! ### Deliveries and resolutions -/

theorem deliveriesOn_prefix {s t : State} (h : s.deliveries <+: t.deliveries) (path : Path) (index : Nat) :
    s.deliveriesOn path index <+: t.deliveriesOn path index :=
  filter_prefix h _

theorem mem_deliveriesOn {s : State} {path : Path} {index : Nat} {d : Delivery} :
    d ∈ s.deliveriesOn path index ↔ d ∈ s.deliveries ∧ d.run = path ∧ d.connection = index := by
  simp [State.deliveriesOn]

/-- Once a Single connection has a delivery, its resolution no longer changes. --/
theorem resolveSingle_of_prefix {s t : State} (h : s.deliveries <+: t.deliveries) {path : Path} {index : Nat}
    {c : Connection} (hne : s.deliveriesOn path index ≠ []) :
    t.resolveSingle path index c = s.resolveSingle path index c := by
  obtain ⟨rest, hrest⟩ := deliveriesOn_prefix h path index
  unfold State.resolveSingle
  rw [← hrest]
  cases hd : s.deliveriesOn path index with
  | nil => exact absurd hd hne
  | cons d ds => rfl

theorem deliveriesOn_ne_nil_of_value {s : State} {path : Path} {index : Nat} {c : Connection}
    {source : ResultId} {input : Option Value} (h : s.resolveSingle path index c = .value source input) :
    s.deliveriesOn path index ≠ [] := by
  intro hnil
  unfold State.resolveSingle at h
  rw [hnil] at h
  simp only at h
  split at h
  · simp at h
  · split at h <;> simp at h

/-- A resolution without deliveries that is not pending comes from a source settled without a value
    on the connection's arm. --/
theorem resolveSingle_nil {s : State} {path : Path} {index : Nat} {c : Connection}
    (h : s.resolveSingle path index c ≠ .pending) (hnil : s.deliveriesOn path index = []) :
    ∃ y, s.settled? path c.source = some y ∧ State.armOutcome y c.arm ≠ .normal := by
  unfold State.resolveSingle at h
  rw [hnil] at h
  simp only at h
  split at h
  · simp at h
  · rename_i y hy
    refine ⟨y, hy, fun hn => ?_⟩
    simp [hn] at h

theorem streamEnd?_eq_some {s : State} {path : Path} {index : Nat} {c : Connection} {o : Outcome}
    (h : s.streamEnd? path index c = some o) :
    ∃ y, s.settled? path c.source = some y ∧ o = State.armOutcome y c.arm ∧
      ∀ r ∈ s.eligible path c, (s.delivery? path index r.id).isSome := by
  unfold State.streamEnd? at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨y, hy, hall, h⟩ := h
  simp only [pure, Option.some.injEq] at h
  refine ⟨y, hy, h.symm, fun r hr => ?_⟩
  have := List.all_eq_true.mp hall r hr
  simpa using this

theorem mem_eligible {s : State} {path : Path} {c : Connection} {r : Result} :
    r ∈ s.eligible path c ↔ r ∈ s.results ∧ r.run = path ∧ r.placement = c.source ∧
      (c.arm.isNone || r.arm == c.arm) = true := by
  simp only [State.eligible, State.resultsOf, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3⟩, h4⟩

theorem mem_invocationsOf {s : State} {path : Path} {name : String} {i : Invocation} :
    i ∈ s.invocationsOf path name ↔ i ∈ s.invocations ∧ i.run = path ∧ i.placement = name := by
  simp [State.invocationsOf]

theorem mem_resultsOf {s : State} {path : Path} {name : String} {r : Result} :
    r ∈ s.resultsOf path name ↔ r ∈ s.results ∧ r.run = path ∧ r.placement = name := by
  simp [State.resultsOf]

/-! ### Shapes -/

theorem mem_inputs {w : Workflow} {name : String} {i : Nat} {c : Connection} (h : (i, c) ∈ w.inputs name) :
    w.connections[i]? = some c ∧ c.target = name := by
  unfold Workflow.inputs at h
  simp only [List.mem_filterMap] at h
  obtain ⟨⟨c', i'⟩, hmem, hif⟩ := h
  by_cases ht : c'.target = name
  · simp only [ht, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hif
    obtain ⟨rfl, rfl⟩ := hif
    exact ⟨List.mem_zipIdx_iff_getElem?.mp hmem, ht⟩
  · simp [ht] at hif

/-- How a placement's input shape arises (§3.2, §5.3). --/
theorem shape?_cases {p : Definition} {w : Workflow} {name : String} {sh : Workflow.Shape}
    (h : w.shape? p name = some sh) : ∃ pl, w.placement? name = some pl ∧
      ((∃ e, pl.control = .merge e) ∧ sh = .merge (w.inputs name) ∨
       (∀ e, pl.control ≠ .merge e) ∧
        (w.isEntry name = true ∧ sh = .entry ∨
         w.isEntry name = false ∧
          (w.inputs name = [] ∧ sh = .none ∨
           ∃ i c, w.inputs name = [(i, c)] ∧
            (w.outputKind? p c.source = some .single ∧ sh = .single i c ∨
             w.outputKind? p c.source = some .stream ∧ sh = .stream i c)))) := by
  unfold Workflow.shape? at h
  cases hpl : w.placement? name with
  | none => simp [hpl] at h
  | some pl =>
    refine ⟨pl, rfl, ?_⟩
    simp only [hpl, Option.bind_eq_bind, Option.bind_some] at h
    cases hc : pl.control <;> simp [hc] at h
    case merge e => exact Or.inl ⟨⟨e, rfl⟩, h.symm⟩
    all_goals
      refine Or.inr ⟨by simp, ?_⟩
      split at h
      · rename_i hentry; exact Or.inl ⟨hentry, (Option.some.inj h).symm⟩
      · rename_i hentry
        refine Or.inr ⟨by simpa using hentry, ?_⟩
        split at h
        · rename_i hin; exact Or.inl ⟨hin, (Option.some.inj h).symm⟩
        · rename_i i c hin
          refine Or.inr ⟨i, c, hin, ?_⟩
          split at h
          · rename_i hk; exact Or.inl ⟨hk, (Option.some.inj h).symm⟩
          · rename_i hk; exact Or.inr ⟨hk, (Option.some.inj h).symm⟩
          · simp at h
        · simp at h

/-- A Single or Stream input names one input connection of the placement. --/
theorem shape?_connection {p : Definition} {w : Workflow} {name : String} {i : Nat} {c : Connection}
    (h : w.shape? p name = some (.single i c) ∨ w.shape? p name = some (.stream i c)) :
    w.connections[i]? = some c ∧ c.target = name := by
  have key : ∀ sh, w.shape? p name = some sh → (sh = .single i c ∨ sh = .stream i c) →
      (i, c) ∈ w.inputs name := by
    intro sh hsh hc
    obtain ⟨pl, -, h⟩ := shape?_cases hsh
    rcases h with ⟨-, rfl⟩ | ⟨-, ⟨-, rfl⟩ | ⟨-, ⟨-, rfl⟩ | ⟨i', c', hin, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩⟩⟩ <;>
      rcases hc with h | h <;> cases h <;> rw [hin] <;> exact List.mem_singleton_self _
  rcases h with h | h
  · exact mem_inputs (key _ h (Or.inl rfl))
  · exact mem_inputs (key _ h (Or.inr rfl))

theorem shape?_of_merge {p : Definition} {w : Workflow} {name : String} {pl : Placement} {e : ValueType}
    (hpl : w.placement? name = some pl) (he : pl.control = .merge e) :
    w.shape? p name = some (.merge (w.inputs name)) := by
  unfold Workflow.shape?
  simp [hpl, he]

/-! ### What a settlement records -/

/-- The values a list of deliveries carries. --/
def deliveredValues (ds : List Delivery) : List Value := ds.filterMap fun d => match d.outcome with
  | .value v => some v
  | _ => none

theorem armOutcome_map {x : Settled} {arms : List String} {f : String → Outcome}
    (hx : x.arms = arms.map fun a => (a, f a)) (a : String) :
    State.armOutcome x (some a) = if a ∈ arms then f a else x.outcome := by
  simp only [State.armOutcome]
  rw [hx, List.find?_map]
  cases hf : List.find? ((fun y : String × Outcome => y.1 == a) ∘ fun a => (a, f a)) arms with
  | none =>
    have : a ∉ arms := by
      intro ha
      have := List.find?_eq_none.mp hf a ha
      simp at this
    simp [this]
  | some b =>
    have hb := List.find?_some hf
    have hmem := List.mem_of_find?_eq_some hf
    simp only [Function.comp, beq_iff_eq] at hb
    subst hb
    simp [hmem]

/-- Arms settled from one invocation: only a selected arm of a succeeded invocation keeps a value. --/
def ArmsBy (x : Settled) (inv : Invocation) : Prop :=
  ∀ arm, State.armOutcome x arm ≠ .normal → inv.status ≠ .succeeded ∨ ∃ a, arm = some a ∧ inv.arm ≠ some a

theorem armsBy_succeeded {path : Path} {name : String} {arms : List String} {inv : Invocation} :
    ArmsBy
      { run := path, placement := name, outcome := .normal,
        arms := arms.map fun a => (a, if (inv.arm == some a) = true then Outcome.normal else .skipped) } inv := by
  intro arm harm
  cases arm with
  | none => exact absurd rfl harm
  | some a =>
    right
    refine ⟨a, rfl, fun ha => harm ?_⟩
    rw [armOutcome_map (f := fun a => if (inv.arm == some a) = true then Outcome.normal else .skipped) rfl]
    simp [ha]

theorem armsBy_of_ne {x : Settled} {inv : Invocation} (h : inv.status ≠ .succeeded) : ArmsBy x inv :=
  fun _ _ => Or.inl h

/-- Every delivery on a Stream input that carries a value or a trigger started an invocation. --/
def Triggered (s : State) (path : Path) (name : String) (index : Nat) : Prop :=
  ∀ d ∈ s.deliveriesOn path index, d.outcome ≠ .failed → ∃ inv ∈ s.invocationsOf path name, inv.trigger = some d.source

theorem triggered_of {s : State} {path : Path} {name : String} {index : Nat}
    (h : ((s.deliveriesOn path index).all fun d => d.outcome == .failed ||
      (s.invocationsOf path name).any (·.trigger == some d.source)) = true) : Triggered s path name index := by
  intro d hd hf
  have := List.all_eq_true.mp h d hd
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
  rcases this with h | ⟨inv, hinv, ht⟩
  · exact absurd h hf
  · exact ⟨inv, hinv, by simpa using ht⟩

theorem settleOutcome_branch {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Option Result} {j : String} {arms : List String}
    (h : s.settleOutcome path pl shape kind = some (x, res)) (he : pl.control = .branch j arms) :
    res = none ∧ x.run = path ∧ x.placement = pl.name ∧
    ((shape = .entry ∧ ∃ inv ∈ s.invocationsOf path pl.name, inv.trigger = none ∧ ArmsBy x inv) ∨
     (∃ i c, shape = .single i c ∧ s.resolveSingle path i c ≠ .pending ∧
       ((∃ source input, s.resolveSingle path i c = .value source input ∧
          ∃ inv ∈ s.invocationsOf path pl.name, inv.trigger = some source ∧ ArmsBy x inv) ∨
        (∀ source input, s.resolveSingle path i c ≠ .value source input))) ∨
     (∃ i c ended, shape = .stream i c ∧ s.streamEnd? path i c = some ended ∧ Triggered s path pl.name i ∧
       (ended = .skipped ∨ ∀ arm, State.armOutcome x arm ≠ .normal →
          ∃ a, arm = some a ∧ ∀ r ∈ s.resultsOf path pl.name, r.arm ≠ some a))) := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff, he] at h
  obtain ⟨-, h⟩ := h
  cases shape <;> simp only at h
  case entry =>
    simp only [option_bind_eq_some] at h
    obtain ⟨inv, hinv, h⟩ := h
    have hmem := List.mem_of_find?_eq_some hinv
    have ht : inv.trigger = none := by simpa using List.find?_some hinv
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      refine ⟨rfl, rfl, rfl, Or.inl ⟨rfl, inv, hmem, ht, ?_⟩⟩
    · exact armsBy_succeeded
    all_goals exact armsBy_of_ne (by simp_all)
  case single i c =>
    split at h
    · simp at h
    · rename_i source input hres
      simp only [option_bind_eq_some] at h
      obtain ⟨inv, hinv, h⟩ := h
      have hmem := List.mem_of_find?_eq_some hinv
      have ht : inv.trigger = some source := by simpa using List.find?_some hinv
      split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
        refine ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨i, c, rfl, by simp [hres], Or.inl ⟨source, input, hres, inv, hmem, ht, ?_⟩⟩)⟩
      · exact armsBy_succeeded
      all_goals exact armsBy_of_ne (by simp_all)
    all_goals
      rename_i hres
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨i, c, rfl, by simp [hres], Or.inr fun _ _ => by simp [hres]⟩)⟩
  case stream i c =>
    simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
    obtain ⟨ended, hend, htrig, h⟩ := h
    have htrig' := triggered_of htrig
    split at h
    · rename_i hsk
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, Or.inr (Or.inr ⟨i, c, ended, rfl, hend, htrig', Or.inl (by simpa using hsk)⟩)⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, rfl, rfl, Or.inr (Or.inr ⟨i, c, ended, rfl, hend, htrig', Or.inr ?_⟩)⟩
      intro arm harm
      cases arm with
      | none => exact absurd rfl harm
      | some a =>
        refine ⟨a, rfl, fun r hr hra => harm ?_⟩
        rw [armOutcome_map rfl]
        have hchosen : ((s.resultsOf path pl.name).filterMap (·.arm)).contains a = true := by
          rw [List.contains_iff_mem, List.mem_filterMap]
          exact ⟨r, hr, hra⟩
        simp only [hchosen, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          ite_self]
  all_goals simp at h
/-- How a waitStream settles: after its input ended, with the delivered values unless skipped (§9.1). --/
theorem settleOutcome_waitStream {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Option Result} {e : ValueType}
    (h : s.settleOutcome path pl shape kind = some (x, res)) (he : pl.control = .waitStream e) :
    ∃ i c o, shape = .stream i c ∧ s.streamEnd? path i c = some o ∧
      ((o = .skipped ∧ x = { run := path, placement := pl.name, outcome := .skipped } ∧ res = none) ∨
       (x = { run := path, placement := pl.name, outcome := .normal } ∧
        res = some
          { id := Key.aggregate path pl.name, run := path, placement := pl.name,
            producer := Key.aggregate path pl.name, value := listValue (deliveredValues (s.deliveriesOn path i)) })) := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff, he] at h
  obtain ⟨hall, h⟩ := h
  cases shape <;> simp only at h
  case stream i c =>
    simp only [option_bind_eq_some] at h
    obtain ⟨o, ho, h⟩ := h
    refine ⟨i, c, o, rfl, ho, ?_⟩
    split at h
    · rename_i hsk
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨by simpa using hsk, h.1.symm, h.2.symm⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨h.1.symm, h.2.symm⟩
  all_goals simp at h

/-- How a Merge settles: skipped, or with a list result. --/
theorem settleOutcome_merge {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Option Result} {e : ValueType}
    (h : s.settleOutcome path pl shape kind = some (x, res)) (he : pl.control = .merge e) :
    (x = { run := path, placement := pl.name, outcome := .skipped } ∧ res = none) ∨
    (x = { run := path, placement := pl.name, outcome := .normal } ∧ ∃ values, res = some
      { id := Key.aggregate path pl.name, run := path, placement := pl.name,
        producer := Key.aggregate path pl.name, value := listValue values }) := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff, he] at h
  obtain ⟨-, h⟩ := h
  cases shape <;> simp only at h
  case merge cs =>
    simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
    obtain ⟨-, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨h.1.symm, _, h.2.symm⟩
  all_goals simp at h

/-- How a call or concurrency settles: from its unique invocation, from its input, or after its Stream
    input ended. --/
theorem settleOutcome_call {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Option Result} (h : s.settleOutcome path pl shape kind = some (x, res))
    (he : (∃ b, pl.control = .call b) ∨ (∃ cc, pl.control = .concurrency cc)) :
    res = none ∧ x.run = path ∧ x.placement = pl.name ∧ x.arms = [] ∧
    (((shape = .none ∨ shape = .entry) ∧ ∃ inv ∈ s.invocationsOf path pl.name, inv.trigger = none ∧
        x.outcome = State.invocationOutcome kind inv.status) ∨
     (∃ i c, shape = .single i c ∧ s.resolveSingle path i c ≠ .pending ∧
       ((∃ source input, s.resolveSingle path i c = .value source input ∧
          ∃ inv ∈ s.invocationsOf path pl.name, inv.trigger = some source ∧
            x.outcome = State.invocationOutcome kind inv.status) ∨
        (∀ source input, s.resolveSingle path i c ≠ .value source input))) ∨
     (∃ i c ended, shape = .stream i c ∧ s.streamEnd? path i c = some ended ∧ Triggered s path pl.name i ∧
       (ended = .skipped ∨ (∀ inv ∈ s.invocationsOf path pl.name, inv.status = .skipped) ∨ x.outcome = .normal))) := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨-, h⟩ := h
  rcases he with ⟨b, he⟩ | ⟨cc, he⟩ <;> rw [he] at h <;> cases shape <;> simp only at h
  all_goals first
    | (simp at h; done)
    | (simp only [option_bind_eq_some] at h
       obtain ⟨inv, hinv, h⟩ := h
       simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨by simp, inv, List.mem_of_find?_eq_some hinv,
         by simpa using List.find?_some hinv, rfl⟩⟩)
    | (simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
       obtain ⟨ended, hend, htrig, h⟩ := h
       split at h
       · rename_i hsk
         simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨_, _, ended, rfl, hend, triggered_of htrig,
           Or.inl (by simpa using hsk)⟩)⟩
       · simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         refine ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨_, _, ended, rfl, hend, triggered_of htrig, ?_⟩)⟩
         by_cases hall : ((s.invocationsOf path pl.name).all fun i => i.status == .skipped) = true
         · refine Or.inr (Or.inl fun inv hinv => ?_)
           simpa using List.all_eq_true.mp hall inv hinv
         · refine Or.inr (Or.inr ?_)
           simp only [Bool.not_eq_true] at hall
           simp [hall])
    | (split at h
       · simp at h
       · rename_i source input hres
         simp only [option_bind_eq_some] at h
         obtain ⟨inv, hinv, h⟩ := h
         simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨_, _, rfl, by simp [hres], Or.inl ⟨source, input, hres, inv,
           List.mem_of_find?_eq_some hinv, by simpa using List.find?_some hinv, rfl⟩⟩)⟩
       all_goals
         rename_i hres
         simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ⟨rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨_, _, rfl, by simp [hres], Or.inr fun _ _ => by simp [hres]⟩)⟩)
/-- A function call placement of Single kind calls a function with a Single contract. --/
theorem outputKind?_function {p : Definition} {w : Workflow} {name : String} {pl : Placement} {f : String}
    (hk : w.outputKind? p name = some .single) (hpl : w.placement? name = some pl)
    (hc : pl.control = .call (.function f)) :
    ∃ decl, p.function? f = some decl ∧ decl.output.kind = .single := by
  unfold Workflow.outputKind? Workflow.depth at hk
  rw [Workflow.kind?.eq_2] at hk
  simp only [option_bind_eq_some] at hk
  obtain ⟨pl', hpl', sources, -, input, -, hk⟩ := hk
  rw [hpl] at hpl'
  cases hpl'
  rw [hc] at hk
  cases input with
  | none =>
    simp only [Definition.outputKind, Definition.bodyKind, Option.map_eq_some_iff] at hk
    obtain ⟨decl, hdecl, hkind⟩ := hk
    exact ⟨decl, hdecl, hkind⟩
  | some k =>
    cases k with
    | single =>
      simp only [Definition.outputKind, Definition.bodyKind, Option.map_eq_some_iff] at hk
      obtain ⟨decl, hdecl, hkind⟩ := hk
      exact ⟨decl, hdecl, hkind⟩
    | stream => simp [Definition.outputKind] at hk

/-- An invocation outcome without a value comes from a skipped invocation, or from a Single placement
    whose invocation did not succeed. --/
theorem invocationOutcome_ne_normal {kind : Kind} {status : InvocationStatus}
    (h : State.invocationOutcome kind status ≠ .normal) :
    status = .skipped ∨ (kind = .single ∧ status ≠ .succeeded) := by
  cases kind <;> cases status <;> simp_all [State.invocationOutcome]
/-- A settlement with a result is the normal settlement of a waitStream or a Merge, without arms. --/
theorem settleOutcome_aggregate {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Result} (h : s.settleOutcome path pl shape kind = some (x, some res)) :
    x = { run := path, placement := pl.name, outcome := .normal } ∧ res.run = path ∧ res.placement = pl.name ∧
      (∃ e, pl.control = .waitStream e ∨ pl.control = .merge e) := by
  cases hc : pl.control with
  | call b => have := (settleOutcome_call h (Or.inl ⟨b, hc⟩)).1; cases this
  | concurrency cc => have := (settleOutcome_call h (Or.inr ⟨cc, hc⟩)).1; cases this
  | branch j arms => have := (settleOutcome_branch h hc).1; cases this
  | waitStream e =>
    obtain ⟨i, c, o, -, -, ⟨-, -, h'⟩ | ⟨hx, h'⟩⟩ := settleOutcome_waitStream h hc
    · cases h'
    · cases h'
      exact ⟨hx, rfl, rfl, e, Or.inl rfl⟩
  | merge e =>
    rcases settleOutcome_merge h hc with ⟨-, h'⟩ | ⟨hx, values, h'⟩
    · cases h'
    · cases h'
      exact ⟨hx, rfl, rfl, e, Or.inr rfl⟩

end Suimon.Settle
