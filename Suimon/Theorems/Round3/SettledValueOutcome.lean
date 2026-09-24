import Suimon.Theorems.Round3.Conformance

/-! Facts for `settled_value` (task B2) about one settlement: what validation says about the arm of a
    connection and the kind of a placement, and why a Single output settles with a value on an arm
    (`settleOutcome_normal`): its aggregate, or an invocation that succeeded, on that arm for a branch. -/

namespace Suimon.Round3.SettledAux
open State

/-! ### Static facts -/

/-- A connection out of a branch names one of its arms; any other connection has no arm. -/
theorem connection_arm {p : Definition} {w : Workflow} {c : Connection} (h : p.validateConnection w c = .ok ())
    {src : Placement} (hsrc : w.placement? c.source = some src) :
    (∀ j arms, src.control = .branch j arms → ∃ a, c.arm = some a ∧ a ∈ arms) ∧
    ((∀ j arms, src.control ≠ .branch j arms) → c.arm = none) := by
  unfold Definition.validateConnection at h
  simp only [Static.except_bind_eq_ok, Validate.need_eq_ok, hsrc, Option.some.injEq, exists_eq_left'] at h
  obtain ⟨dst, -, h⟩ := h
  split at h
  · rename_i j arms arm hc harm
    simp only [Static.except_bind_eq_ok, Validate.check_eq_ok, List.contains_iff_mem] at h
    obtain ⟨-, h, -⟩ := h
    refine ⟨fun j' arms' hc' => ?_, fun hne => absurd hc (hne j arms)⟩
    rw [hc] at hc'
    cases hc'
    exact ⟨arm, harm, h⟩
  · simp at h
  · simp at h
  · rename_i harm hne
    exact ⟨fun j arms hc => absurd hc (hne j arms), fun _ => harm⟩

/-- A placement with a Single output and a Stream input is a waitStream (§5.2). -/
theorem waitStream_of_stream {p : Definition} {w : Workflow} {name : String} {pl : Placement} {j : Nat}
    {c : Connection} (hpl : w.placement? name = some pl) (hsh : w.shape? p name = some (.stream j c))
    (hk : w.outputKind? p name = some .single) : ∃ e, pl.control = .waitStream e := by
  have hm : ∀ e, pl.control ≠ .merge e := fun e he => by
    rw [Settle.shape?_of_merge hpl he] at hsh; cases hsh
  obtain ⟨inp, hinp, hout, -⟩ := Delivery.outputKind?_shape hsh hk hpl hm
  simp only [Delivery.shapeInput, Option.some.injEq] at hinp
  subst hinp
  cases hc : pl.control with
  | waitStream e => exact ⟨e, rfl⟩
  | merge e => exact absurd hc (hm e)
  | call b => rw [hc] at hout; simp [Definition.outputKind] at hout
  | branch j arms => rw [hc] at hout; simp [Definition.outputKind] at hout
  | concurrency cc => rw [hc] at hout; simp [Definition.outputKind] at hout

/-- Controls whose succeeded invocation produced a result: a function call with a Single contract, a
    sub-workflow call, a branch, and a concurrency with a List output. -/
def SingleBody (p : Definition) : Control → Prop
  | .call (.function f) => ∃ decl, p.function? f = some decl ∧ decl.output.kind = .single
  | .call (.workflow _ _) => True
  | .branch _ _ => True
  | .concurrency cc => cc.output = .list
  | _ => False

/-- An invoked placement with a Single output has a Single body. -/
theorem singleBody_of_kind {p : Definition} {w : Workflow} {name : String} {pl : Placement} {sh : Workflow.Shape}
    (hpl : w.placement? name = some pl) (hsh : w.shape? p name = some sh) (hk : w.outputKind? p name = some .single)
    (hinv : (∃ b, pl.control = .call b) ∨ (∃ j arms, pl.control = .branch j arms) ∨
      (∃ cc, pl.control = .concurrency cc)) :
    SingleBody p pl.control := by
  rcases hinv with ⟨b, hc⟩ | ⟨j, arms, hc⟩ | ⟨cc, hc⟩
  · cases b with
    | function f => rw [hc]; exact Settle.outputKind?_function hk hpl hc
    | workflow wf out => rw [hc]; trivial
  · rw [hc]; trivial
  · rw [hc]
    have hm : ∀ e, pl.control ≠ .merge e := fun e he => by rw [hc] at he; cases he
    obtain ⟨inp, -, hout, -⟩ := Delivery.outputKind?_shape hsh hk hpl hm
    rw [hc] at hout
    show cc.output = .list
    rcases inp with _ | (_ | _) <;> cases ho : cc.output <;> simp [Definition.outputKind, ho] at hout ⊢

/-! ### Settlements with a value -/

/-- A settlement that records one outcome for every arm reads it on every arm. -/
theorem armOutcome_const {path : Path} {name : String} {o : Outcome} {arms : List String} (a : Option String) :
    armOutcome { run := path, placement := name, outcome := o, arms := arms.map fun b => (b, o) } a = o := by
  cases a with
  | none => rfl
  | some b => rw [Delivery.armOutcome_arms (f := fun _ => o) rfl]; split <;> rfl

/-- After a judge chose `chosen`, a declared arm reads a value only if it is the chosen one. -/
theorem chosen_arm {x : Settled} {arms : List String} {chosen a : Option String}
    (hx : x.arms = arms.map fun b => (b, if (chosen == some b) = true then Outcome.normal else .skipped))
    (ha : armOutcome x a = .normal) (hb : ∀ b, a = some b → b ∈ arms) : a = none ∨ chosen = a := by
  cases a with
  | none => exact Or.inl rfl
  | some b =>
    rw [Delivery.armOutcome_arms hx] at ha
    simp only [hb b rfl, ↓reduceIte] at ha
    refine Or.inr ?_
    cases hcb : (chosen == some b)
    · simp [hcb] at ha
    · exact beq_iff_eq.mp hcb

/-- A Single output that settled with a value on an arm: the aggregate recorded with the settlement,
    or a succeeded invocation, on that arm for a branch. The arm is `none` or, for a branch, a declared
    arm, as validation guarantees for the arm of a connection; a Stream input is excluded, since only a
    waitStream has a Single output with it. -/
theorem settleOutcome_normal {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape}
    {x : Settled} {res : Option Result} (h : s.settleOutcome path pl shape .single = some (x, res))
    (hstream : ∀ j c, shape = .stream j c → ∃ e, pl.control = .waitStream e)
    {a : Option String} (harm : a = none ∨ ∃ j arms b, pl.control = .branch j arms ∧ a = some b ∧ b ∈ arms)
    (ha : armOutcome x a = .normal) :
    (∃ r, res = some r ∧ r.run = path ∧ r.placement = pl.name ∧ r.arm = none ∧ a = none) ∨
    (((∃ b, pl.control = .call b) ∨ (∃ j arms, pl.control = .branch j arms) ∨
        (∃ cc, pl.control = .concurrency cc)) ∧
      ∃ inv ∈ s.invocationsOf path pl.name, inv.status = .succeeded ∧ (a = none ∨ inv.arm = a)) := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨-, h⟩ := h
  -- Only a branch has arms on its connections.
  have noArm : (∀ j arms, pl.control ≠ .branch j arms) → a = none := fun hne =>
    harm.elim id fun ⟨j, arms, _, hc, _⟩ => absurd hc (hne j arms)
  -- A settlement without a value on any arm contradicts `ha`.
  have noValue : ∀ {o : Outcome} {arms : List String}, o ≠ .normal →
      some ({ run := path, placement := pl.name, outcome := o, arms := arms.map fun b => (b, o) }, none) =
        some (x, res) → False := by
    intro o arms ho hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact ho ((armOutcome_const a).symm.trans ha)
  have noValue' : ∀ {o : Outcome}, o ≠ .normal →
      some ({ run := path, placement := pl.name, outcome := o }, none) = some (x, res) → False := by
    intro o ho hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact ho ((Delivery.armOutcome_nil rfl a).symm.trans ha)
  split at h
  · -- A waitStream: skipped, or its aggregate.
    rename_i e j c hc
    simp only [option_bind_eq_some] at h
    obtain ⟨o, -, h⟩ := h
    split at h
    · exact (noValue' (by decide) h).elim
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨_, rfl, rfl, rfl, rfl, noArm fun j arms h' => by rw [hc] at h'; cases h'⟩
  · -- A Merge: skipped, or its aggregate.
    rename_i e cs hc
    simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
    obtain ⟨-, h⟩ := h
    split at h
    · exact (noValue' (by decide) h).elim
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨_, rfl, rfl, rfl, rfl, noArm fun j arms h' => by rw [hc] at h'; cases h'⟩
  · -- A branch settles by its invocation, or by why no input came.
    rename_i j arms hc
    have ctrl : (∃ b, pl.control = .call b) ∨ (∃ j arms, pl.control = .branch j arms) ∨
        (∃ cc, pl.control = .concurrency cc) := Or.inr (Or.inl ⟨j, arms, hc⟩)
    have hb : ∀ b, a = some b → b ∈ arms := by
      intro b hab
      rcases harm with h' | ⟨j', arms', b', hc', rfl, hb'⟩
      · rw [h'] at hab; cases hab
      · rw [hc] at hc'
        cases hc'
        cases hab
        exact hb'
    split at h
    · simp only [option_bind_eq_some] at h
      obtain ⟨inv, hinv, h⟩ := h
      obtain ⟨hmem, -⟩ := Delivery.find?_trigger_none hinv
      split at h
      · rename_i hsucc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨ctrl, inv, hmem, hsucc, chosen_arm rfl ha hb⟩
      · exact (noValue (by decide) h).elim
      · exact (noValue (by decide) h).elim
      · exact (noValue (by decide) h).elim
    · rename_i i c
      split at h
      · cases h
      · simp only [option_bind_eq_some] at h
        obtain ⟨inv, hinv, h⟩ := h
        obtain ⟨hmem, -⟩ := Delivery.find?_trigger_some hinv
        split at h
        · rename_i hsucc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr ⟨ctrl, inv, hmem, hsucc, chosen_arm rfl ha hb⟩
        · exact (noValue (by decide) h).elim
        · exact (noValue (by decide) h).elim
        · exact (noValue (by decide) h).elim
      · exact (noValue (by decide) h).elim
      · exact (noValue (by decide) h).elim
      · exact (noValue (by decide) h).elim
    · rename_i i c
      obtain ⟨e, he⟩ := hstream i c rfl
      rw [hc] at he
      cases he
    · cases h
  -- A call or concurrency settles by its invocation, whose outcome is normal only if it succeeded.
  all_goals first
    | (cases h; done)
    | skip
  all_goals
    rename_i hc
    have ctrl : (∃ b, pl.control = .call b) ∨ (∃ j arms, pl.control = .branch j arms) ∨
        (∃ cc, pl.control = .concurrency cc) := by
      first | exact Or.inl ⟨_, hc⟩ | exact Or.inr (Or.inr ⟨_, hc⟩)
    have ha0 : a = none := noArm fun j arms h' => by rw [hc] at h'; cases h'
    have succ : ∀ {o : InvocationStatus},
        some ({ run := path, placement := pl.name, outcome := invocationOutcome .single o }, none) =
          some (x, res) → o = .succeeded := by
      intro o hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      have := (Delivery.armOutcome_nil rfl a).symm.trans ha
      cases o <;> simp [invocationOutcome] at this ⊢
    split at h
    · simp only [option_bind_eq_some] at h
      obtain ⟨inv, hinv, h⟩ := h
      exact Or.inr ⟨ctrl, inv, (Delivery.find?_trigger_none hinv).1, succ h, Or.inl ha0⟩
    · simp only [option_bind_eq_some] at h
      obtain ⟨inv, hinv, h⟩ := h
      exact Or.inr ⟨ctrl, inv, (Delivery.find?_trigger_none hinv).1, succ h, Or.inl ha0⟩
    · split at h
      · cases h
      · simp only [option_bind_eq_some] at h
        obtain ⟨inv, hinv, h⟩ := h
        exact Or.inr ⟨ctrl, inv, (Delivery.find?_trigger_some hinv).1, succ h, Or.inl ha0⟩
      · exact (noValue' (by decide) h).elim
      · exact (noValue' (by decide) h).elim
      · exact (noValue' (by decide) h).elim
    · obtain ⟨e, he⟩ := hstream _ _ rfl
      rw [hc] at he
      cases he
    · cases h

end Suimon.Round3.SettledAux
