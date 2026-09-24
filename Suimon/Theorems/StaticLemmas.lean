import Suimon.Step

/-! Reusable lemmas about the static checks in `Suimon/Validate.lean`: inversion of the validator's
    `Except` computations, `unique` as `Nodup`, ranks from Kahn elimination, and the fuel stability
    of `Workflow.kind?` in an acyclic workflow. -/

namespace Suimon

namespace Static

section Except
variable {ε α β : Type _}

theorem except_bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem except_pure_eq_ok {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem except_throw_eq_ok {e : ε} {b : α} : (throw e : Except ε α) = .ok b ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- A for-in loop over `PUnit` in `Except` whose body never stops early succeeds only if every
    iteration yields. --/
theorem forIn_ok {xs : List α} {f : α → PUnit → Except ε (ForInStep PUnit)} {b : PUnit}
    (h : forIn xs PUnit.unit f = .ok b) (hdone : ∀ a s, f a PUnit.unit ≠ .ok (.done s)) :
    ∀ a ∈ xs, f a PUnit.unit = .ok (.yield PUnit.unit) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    intro a ha
    rcases hx : f x PUnit.unit with e | s
    · rw [hx] at h
      simp [bind, Except.bind] at h
    · rcases s with s | s
      · exact absurd hx (hdone x s)
      · rw [hx] at h
        simp only [bind, Except.bind] at h
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hx
        · exact ih h a ha

/-- `for a in xs do g a` succeeds only if `g a` succeeds for every element. --/
theorem forIn_yield_ok {xs : List α} {g : α → Except ε PUnit} {b : PUnit}
    (h : forIn xs PUnit.unit (fun a _ => g a >>= fun _ => pure (ForInStep.yield PUnit.unit)) = .ok b) :
    ∀ a ∈ xs, g a = .ok PUnit.unit := by
  intro a ha
  have := forIn_ok h (by
    intro a s h
    simp only [except_bind_eq_ok, except_pure_eq_ok, reduceCtorEq, and_false, exists_false] at h) a ha
  simp only [except_bind_eq_ok, except_pure_eq_ok, and_true] at this
  obtain ⟨⟨⟩, h⟩ := this
  exact h

end Except

theorem mapM_congr {m : Type u → Type v} [Monad m] [LawfulMonad m] {α β} {f g : α → m β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, List.mapM_cons, h x List.mem_cons_self,
      mapM_congr fun y hy => h y (List.mem_cons_of_mem x hy)]

theorem length_eraseDups_le {α} [BEq α] : ∀ xs : List α, xs.eraseDups.length ≤ xs.length
  | [] => by simp
  | a :: as => by
    have := length_eraseDups_le (as.filter fun b => !b == a)
    have := List.length_filter_le (fun b => !b == a) as
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    omega
termination_by xs => xs.length
decreasing_by have := List.length_filter_le (fun b => !b == a) as; simp; omega

/-- With distinct keys, looking up the key of a member finds that member. --/
theorem find?_key_of_nodup {α β} [BEq β] [LawfulBEq β] {f : α → β} :
    ∀ {xs : List α}, (xs.map f).Nodup → ∀ {x : α}, x ∈ xs → xs.find? (fun y => f y == f x) = some x
  | [], _, _, hx => by simp at hx
  | y :: ys, hu, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hu
    rw [List.find?_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have hne : (f y == f x) = false :=
        beq_eq_false_iff_ne.2 fun he => hu.1 (List.mem_map.2 ⟨x, hx, he.symm⟩)
      simp only [hne]
      exact find?_key_of_nodup hu.2 hx

theorem eraseDups_of_nodup {α} [BEq α] [LawfulBEq α] : ∀ {xs : List α}, xs.Nodup → xs.eraseDups = xs
  | [], _ => rfl
  | a :: as, h => by
    rw [List.nodup_cons] at h
    have hfilter : as.filter (fun b => !b == a) = as := List.filter_eq_self.2 fun b hb => by
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      exact fun he => h.1 (he ▸ hb)
    rw [List.eraseDups_cons, hfilter, eraseDups_of_nodup h.2]

/-- A list with an element that `p` rejects is longer than its filter. --/
theorem length_filter_lt {α} {p : α → Bool} {l : List α} {x : α} (hx : x ∈ l) (hp : p x = false) :
    (l.filter p).length < l.length := by
  refine Nat.lt_of_le_of_ne (List.length_filter_le p l) fun heq => ?_
  have := List.filter_eq_self.1 (List.filter_sublist.eq_of_length heq) x hx
  simp [hp] at this

/-- A non-empty list has an element of least rank. --/
theorem exists_min_rank {α} (rank : α → Nat) : ∀ {l : List α}, l ≠ [] → ∃ v ∈ l, ∀ u ∈ l, rank v ≤ rank u
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨v, hv, hmin⟩ := exists_min_rank rank (l := b :: l) (by simp)
    by_cases hav : rank a ≤ rank v
    · refine ⟨a, by simp, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact Nat.le_refl _
      · exact Nat.le_trans hav (hmin u hu)
    · refine ⟨v, List.mem_cons_of_mem a hv, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · omega
      · exact hmin u hu

end Static

namespace Validate

theorem check_eq_ok {ok : Bool} {message : String} {u : Unit} : check ok message = .ok u ↔ ok = true := by
  cases ok <;> simp [check, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem need_eq_ok {α} {value : Option α} {message : String} {a : α} :
    need value message = .ok a ↔ value = some a := by
  cases value <;> simp [need, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

end Validate

theorem Definition.validateTypes_eq_ok {at_ : String} {types : List ValueType} {u : Unit} :
    Definition.validateTypes at_ types = .ok u ↔ ∀ t ∈ types, t.name ≠ "" := by
  simp [Definition.validateTypes, Validate.check_eq_ok]

theorem nodup_of_unique {α} [BEq α] [LawfulBEq α] : ∀ {xs : List α}, unique xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | a :: as, h => by
    simp only [unique, beq_iff_eq, List.eraseDups_cons, List.length_cons, Nat.add_right_cancel_iff] at h
    have h1 := Static.length_eraseDups_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    -- Full length after deduplication forces the filter to keep everything, so `a ∉ as`.
    have hf : as.filter (fun b => !b == a) = as := List.filter_sublist.eq_of_length (by omega)
    rw [hf] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodup_of_unique (by simp [unique, h])⟩
    have := List.filter_eq_self.1 hf a ha
    simp at this
termination_by xs => xs.length

theorem unique_of_nodup {α} [BEq α] [LawfulBEq α] {xs : List α} (h : xs.Nodup) : unique xs = true := by
  simp [unique, Static.eraseDups_of_nodup h]

theorem Workflow.placement?_of_mem {w : Workflow} (hu : (w.placements.map (·.name)).Nodup) {pl : Placement}
    (h : pl ∈ w.placements) : w.placement? pl.name = some pl :=
  Static.find?_key_of_nodup hu h

theorem Workflow.placement?_eq_none {w : Workflow} {name : String} (h : name ∉ w.placements.map (·.name)) :
    w.placement? name = none := by
  simp only [Workflow.placement?, List.find?_eq_none, beq_iff_eq]
  intro x hx he
  exact h (List.mem_map.2 ⟨x, hx, he⟩)

/-- Successful Kahn elimination yields a rank below the fuel for every vertex that strictly
    increases along every edge between vertices. --/
theorem acyclic_rank {edges : List (String × String)} :
    ∀ {fuel : Nat} {vertices : List String}, acyclic edges fuel vertices = true →
    ∃ rank : String → Nat, (∀ v ∈ vertices, rank v < fuel) ∧
      ∀ e ∈ edges, e.1 ∈ vertices → e.2 ∈ vertices → rank e.1 < rank e.2
  | 0, vertices, h => by
    simp only [acyclic, List.isEmpty_iff] at h
    subst h
    exact ⟨fun _ => 0, by simp, by simp⟩
  | fuel + 1, vertices, h => by
    simp only [acyclic] at h
    split at h
    · rename_i hv
      simp only [List.isEmpty_iff] at hv
      subst hv
      exact ⟨fun _ => 0, by simp, by simp⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨-, hrec⟩ := h
      obtain ⟨rank, hlt, hedge⟩ := acyclic_rank hrec
      -- The roots of this round get rank 0; the remaining vertices move one rank up.
      let isRoot := fun v => !edges.any fun x => x.snd == v && vertices.contains x.fst
      have hrest : ∀ v ∈ vertices, isRoot v = false →
          v ∈ vertices.filter (fun x => !(vertices.filter isRoot).contains x) := by
        intro v hv hr
        simp only [List.mem_filter, hv, true_and, Bool.not_eq_true']
        simp [hr]
      refine ⟨fun v => if isRoot v then 0 else rank v + 1, ?_, ?_⟩
      · intro v hv
        by_cases hr : isRoot v = true
        · simp [hr]
        · simp only [hr, Bool.false_eq_true, ↓reduceIte]
          have := hlt v (hrest v hv (by simpa using hr))
          omega
      · intro e he h1 h2
        have hr2 : isRoot e.2 = false := by
          simp only [isRoot, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
            List.contains_iff_mem]
          exact ⟨e, he, rfl, h1⟩
        have hin2 := hrest _ h2 hr2
        simp only [hr2, Bool.false_eq_true, ↓reduceIte]
        by_cases hr1 : isRoot e.1 = true
        · simp [hr1]
        · simp only [hr1, Bool.false_eq_true, ↓reduceIte]
          have := hedge e he (hrest _ h1 (by simpa using hr1)) hin2
          omega

/-- Conversely, Kahn elimination with enough fuel succeeds on a graph with a rank that increases along
    every edge: a vertex of least rank is a root in each round. --/
theorem acyclic_of_rank {edges : List (String × String)} {rank : String → Nat}
    (hrank : ∀ e ∈ edges, rank e.1 < rank e.2) :
    ∀ {fuel : Nat} {vertices : List String}, vertices.length ≤ fuel → acyclic edges fuel vertices = true
  | 0, vertices, h => by simp_all [acyclic]
  | fuel + 1, vertices, h => by
    unfold acyclic
    split
    · rfl
    · rename_i hne
      simp only [List.isEmpty_iff] at hne
      obtain ⟨v, hv, hmin⟩ := Static.exists_min_rank rank hne
      generalize hroots : vertices.filter _ = roots
      have hvroots : v ∈ roots := by
        rw [← hroots]
        refine List.mem_filter.2 ⟨hv, ?_⟩
        simp only [Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
          not_and]
        rintro ⟨src, dst⟩ he hdst hsrc
        have h1 := hrank _ he
        have h2 := hmin src hsrc
        simp only at h1 hdst
        subst hdst
        omega
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨by simpa using List.ne_nil_of_mem hvroots, acyclic_of_rank hrank ?_⟩
      have := Static.length_filter_lt (p := fun x => !roots.contains x) hv (by simpa using hvroots)
      omega

theorem Workflow.kind?_of_not_mem {p : Definition} {w : Workflow} {v : String}
    (h : v ∉ w.placements.map (·.name)) : ∀ fuel, w.kind? p fuel v = none
  | 0 => rfl
  | _ + 1 => by simp [Workflow.kind?, Workflow.placement?_eq_none h]

/-- `kind?` stops depending on the fuel once the fuel exceeds the rank of the placement, for any
    rank that increases along connections. --/
theorem Workflow.kind?_fuel_stable {p : Definition} {w : Workflow} {rank : String → Nat}
    (hrank : ∀ c ∈ w.connections, c.source ∈ w.placements.map (·.name) →
      c.target ∈ w.placements.map (·.name) → rank c.source < rank c.target) :
    ∀ m v f g, (v ∈ w.placements.map (·.name) → rank v < m) → m ≤ f → m ≤ g →
      w.kind? p f v = w.kind? p g v := by
  intro m
  induction m with
  | zero =>
    intro v f g hv _ _
    have hn : v ∉ w.placements.map (·.name) := fun h => by have := hv h; omega
    rw [kind?_of_not_mem hn, kind?_of_not_mem hn]
  | succ m ih =>
    intro v f g hv hf hg
    by_cases hn : v ∈ w.placements.map (·.name)
    · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hsources : (w.incoming v).mapM (fun c => w.kind? p f c.source) =
          (w.incoming v).mapM (fun c => w.kind? p g c.source) := by
        apply Static.mapM_congr
        intro c hc
        simp only [Workflow.incoming, List.mem_filter, beq_iff_eq] at hc
        apply ih c.source f g _ (by omega) (by omega)
        intro hs
        have := hrank c hc.1 hs (hc.2 ▸ hn)
        have := hv hn
        rw [hc.2] at *
        omega
      simp only [Workflow.kind?, hsources]
    · rw [kind?_of_not_mem hn, kind?_of_not_mem hn]

/-- In an acyclic workflow, `kind?` with at least as much fuel as there are placements gives the
    same answer as with exactly that much. --/
theorem Workflow.kind?_stable_of_acyclic {p : Definition} {w : Workflow} (h : w.acyclic = true) {v : String}
    {fuel : Nat} (hf : w.placements.length ≤ fuel) :
    w.kind? p fuel v = w.kind? p w.placements.length v := by
  obtain ⟨rank, hlt, hedge⟩ := acyclic_rank h
  refine kind?_fuel_stable (rank := rank) ?_ w.placements.length v fuel w.placements.length
    (fun hv => by simpa using hlt v hv) hf (Nat.le_refl _)
  intro c hc hs ht
  exact hedge (c.source, c.target) (List.mem_map.2 ⟨c, hc, rfl⟩) hs ht

/-- In an acyclic workflow with distinct placement names, the output kind of a placement is the
    §5.2 rule applied to its input kind. --/
theorem Workflow.outputKind?_eq_bind {p : Definition} {w : Workflow} (hu : (w.placements.map (·.name)).Nodup)
    (ha : w.acyclic = true) {pl : Placement} (hpl : pl ∈ w.placements) :
    w.outputKind? p pl.name = (w.inputKind? p pl.name).bind (p.outputKind pl.control) := by
  have hsources : (w.incoming pl.name).mapM (fun c => w.kind? p w.placements.length c.source) =
      (w.incoming pl.name).mapM (fun c => w.kind? p (w.placements.length + 1) c.source) :=
    Static.mapM_congr fun c _ => (kind?_stable_of_acyclic ha (Nat.le_succ _)).symm
  unfold Workflow.outputKind? Workflow.inputKind? Workflow.depth
  rw [Workflow.kind?.eq_2, Workflow.placement?_of_mem hu hpl, hsources]
  cases (w.incoming pl.name).mapM (fun c => w.kind? p (w.placements.length + 1) c.source) <;> rfl

/-- Reduces a successful validator computation to its conditions. --/
local macro "validate_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, Definition.validateTypes_eq_ok, exists_const, and_true,
    true_and, Bool.false_eq_true, ↓reduceIte, false_and, and_false, exists_false] at $h:ident)

/-- What `validatePlacement` guarantees about one placement. --/
structure PlacementChecked (p : Definition) (w : Workflow) (pl : Placement) : Prop where
  kind : (w.outputKind? p pl.name).isSome = true
  inputs : (∀ e, pl.control ≠ .merge e) →
    (w.incoming pl.name).length + (if w.isEntry pl.name then 1 else 0) ≤ 1
  merge : ∀ e, pl.control = .merge e → ∀ c ∈ w.incoming pl.name, w.outputKind? p c.source = some .single
  waitStream : ∀ e, pl.control = .waitStream e → w.inputKind? p pl.name = some (some .stream)
  concurrency : ∀ c, pl.control = .concurrency c → 0 < c.limit ∧ (c.tasks.map (·.name)).Nodup ∧
    c.tasks.any (·.output.isSome) = true ∧ ∀ task ∈ c.tasks, ∃ at_, p.validateTask at_ c task = .ok ()

theorem Definition.validatePlacement_ok {p : Definition} {w : Workflow} {pl : Placement}
    (h : p.validatePlacement w pl = .ok ()) : PlacementChecked p w pl := by
  rcases pl with ⟨name, control, policy, timeout⟩
  unfold Definition.validatePlacement at h
  cases control with
  | call body =>
    validate_simp at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> validate_simp at h
    · obtain ⟨hcount, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simp only [beq_iff_eq] at hcount; dsimp only; omega, by simp, by simp, by simp⟩
    · obtain ⟨hcount, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simpa using hcount, by simp, by simp, by simp⟩
  | branch judge arms =>
    validate_simp at h
    obtain ⟨_, -, -, -, a, -, h⟩ := h
    split at h <;> validate_simp at h
    · obtain ⟨hcount, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simp only [beq_iff_eq] at hcount; dsimp only; omega, by simp, by simp, by simp⟩
    · obtain ⟨hcount, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simpa using hcount, by simp, by simp, by simp⟩
  | waitStream element =>
    validate_simp at h
    obtain ⟨-, a, -, h⟩ := h
    split at h <;> validate_simp at h
    · obtain ⟨hcount, hwait, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simp only [beq_iff_eq] at hcount; dsimp only; omega, by simp,
        fun _ _ => by simpa using hwait, by simp⟩
    · obtain ⟨hcount, hwait, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simpa using hcount, by simp, fun _ _ => by simpa using hwait, by simp⟩
  | merge element =>
    validate_simp at h
    obtain ⟨-, -, a, -, u, hloop, hkind, -⟩ := h
    refine ⟨hkind, fun hne => absurd rfl (hne element), fun _ _ c hc => ?_, by simp, by simp⟩
    have := Static.forIn_yield_ok hloop c hc
    validate_simp at this
    simpa using this
  | concurrency c =>
    validate_simp at h
    obtain ⟨-, hlimit, -, -, hunique, hany, u, hloop, a, -, h⟩ := h
    have hconc : 0 < c.limit ∧ (c.tasks.map (·.name)).Nodup ∧ c.tasks.any (·.output.isSome) = true ∧
        ∀ task ∈ c.tasks, ∃ at_, p.validateTask at_ c task = .ok () :=
      ⟨by simpa using hlimit, nodup_of_unique hunique, hany,
        fun task ht => ⟨_, Static.forIn_yield_ok hloop task ht⟩⟩
    split at h <;> validate_simp at h
    · obtain ⟨hcount, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simp only [beq_iff_eq] at hcount; dsimp only; omega, by simp, by simp,
        fun _ hc => by cases hc; exact hconc⟩
    · obtain ⟨hcount, hkind, -⟩ := h
      exact ⟨hkind, fun _ => by simpa using hcount, by simp, by simp, fun _ hc => by cases hc; exact hconc⟩

theorem Definition.validateConnection_ok {p : Definition} {w : Workflow} {c : Connection}
    (h : p.validateConnection w c = .ok ()) :
    ∃ src dst, w.placement? c.source = some src ∧ w.placement? c.target = some dst ∧
      match c.transform with
      | .declared id => ∃ t, p.transform? id = some t ∧ p.resultType src.control = some t.input ∧
          p.inputType dst.control = some (some t.output)
      | .discard => (p.resultType src.control).isSome ∧ p.inputType dst.control = some none := by
  unfold Definition.validateConnection at h
  validate_simp at h
  obtain ⟨src, hsrc, dst, hdst, h⟩ := h
  refine ⟨src, dst, hsrc, hdst, ?_⟩
  -- Only a branch with a known arm, or a non-branch without an arm, gets past the arm check.
  split at h <;> validate_simp at h
  case' h_1 => obtain ⟨-, h⟩ := h
  all_goals
    obtain ⟨produced, hprod, expected, hexp, h⟩ := h
    cases htr : c.transform with
    | declared id =>
      rw [htr] at h
      cases expected <;> validate_simp at h
      obtain ⟨t, ht, hin, hout⟩ := h
      exact ⟨t, ht, by rw [hprod, beq_iff_eq.1 hin], by rw [hexp, beq_iff_eq.1 hout]⟩
    | discard =>
      rw [htr] at h
      cases expected <;> validate_simp at h
      exact ⟨by simp [hprod], hexp⟩

theorem Definition.validateTask_output {p : Definition} {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) {id : String} (hout : task.output = some id) :
    ∃ t, p.transform? id = some t ∧ t.output = c.element ∧ p.bodyElement p.depth task.body = some t.input := by
  unfold Definition.validateTask at h
  validate_simp at h
  obtain ⟨-, input, -, h⟩ := h
  simp only [hout] at h
  -- Every accepted input transform continues with the same output check.
  split at h <;> validate_simp at h
  case' h_1 => obtain ⟨-, h⟩ := h
  case' h_2 => obtain ⟨-, h⟩ := h
  case' h_6 => obtain ⟨-, -, -, -, -, -, h⟩ := h
  all_goals
    obtain ⟨t, ht, element, helement, hin, hout, -⟩ := h
    exact ⟨t, ht, beq_iff_eq.1 hout, by rw [helement, beq_iff_eq.1 hin]⟩

/-- What `validateWorkflow` guarantees about one workflow. --/
structure WorkflowChecked (p : Definition) (w : Workflow) : Prop where
  nonempty : w.placements ≠ []
  names : (w.placements.map (·.name)).Nodup
  connections : ∀ c ∈ w.connections, p.validateConnection w c = .ok ()
  acyclic : w.acyclic = true
  entry : ∀ e, w.input = some e → p.validateEntry w e = .ok ()
  placements : ∀ pl ∈ w.placements, PlacementChecked p w pl
  endpoints : ∀ pl ∈ w.placements, w.isEndpoint pl.name = true → w.outputKind? p pl.name = some .single

theorem Definition.validateWorkflow_ok {p : Definition} {w : Workflow} (h : p.validateWorkflow w = .ok ()) :
    WorkflowChecked p w := by
  unfold Definition.validateWorkflow at h
  validate_simp at h
  obtain ⟨-, hne, -, hu, u, hc, ha, h⟩ := h
  have hnonempty : w.placements ≠ [] := by simpa using hne
  split at h <;> validate_simp at h
  case' h_1 =>
    rename_i e he
    obtain ⟨_, hentry, h⟩ := h
    have hentry : ∀ e', w.input = some e' → p.validateEntry w e' = .ok () := by
      intro e' he'
      rw [he, Option.some.injEq] at he'
      subst he'
      exact hentry
  case' h_2 =>
    rename_i hnone
    have hentry : ∀ e', w.input = some e' → p.validateEntry w e' = .ok () :=
      fun e' he' => absurd he' (hnone e')
  all_goals
    obtain ⟨u₁, h1, u₂, h2⟩ := h
    refine ⟨hnonempty, nodup_of_unique hu, Static.forIn_yield_ok hc, ha, hentry,
      fun pl hpl => validatePlacement_ok (Static.forIn_yield_ok h1 pl hpl), ?_⟩
    intro pl hpl hend
    have := Static.forIn_ok h2 (by
      intro a s h
      split at h
      · simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, reduceCtorEq, and_false,
          exists_false] at h
      · simp only [Static.except_pure_eq_ok, reduceCtorEq] at h) pl hpl
    simp only [hend, ↓reduceIte, Static.except_bind_eq_ok, Validate.check_eq_ok, Static.except_pure_eq_ok,
      and_true, exists_const] at this
    simpa using this

/-- What `validate` guarantees about a definition. --/
structure DefinitionChecked (p : Definition) : Prop where
  functions : (p.functions.map (·.id)).Nodup
  judges : (p.judges.map (·.id)).Nodup
  transforms : (p.transforms.map (·.id)).Nodup
  discard : ∀ t ∈ p.transforms, t.id ≠ TransformRef.discardName
  workflowIds : (p.workflows.map (·.id)).Nodup
  main : (p.workflow? p.main).isSome = true
  callsAcyclic : p.callsAcyclic = true
  workflows : ∀ w ∈ p.workflows, WorkflowChecked p w

/-- Validation checks every declared workflow. --/
theorem Definition.validateWorkflow_of_validate {p : Definition} (h : p.validate = .ok ()) {w : Workflow}
    (hw : w ∈ p.workflows) : p.validateWorkflow w = .ok () := by
  unfold Definition.validate at h
  validate_simp at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, u, hloop⟩ := h
  exact Static.forIn_yield_ok hloop w hw

theorem Definition.validate_ok {p : Definition} (h : p.validate = .ok ()) : DefinitionChecked p := by
  have hworkflows := fun w hw => validateWorkflow_ok (validateWorkflow_of_validate h (w := w) hw)
  unfold Definition.validate at h
  validate_simp at h
  obtain ⟨hf, hj, ht, hd, hw, hm, hcalls, -⟩ := h
  exact ⟨nodup_of_unique hf, nodup_of_unique hj, nodup_of_unique ht, by simpa using hd,
    nodup_of_unique hw, hm, hcalls, hworkflows⟩

end Suimon
