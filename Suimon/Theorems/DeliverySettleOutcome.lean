import Suimon.Theorems.DeliveryBase

/-! What `State.settleOutcome` guarantees: the input of the placement is used up, an aggregate is
    recorded only with a normal outcome, and a Single output settles without a value only when its
    invocation did not succeed, or on another arm of a branch. -/

namespace Suimon.Delivery
open State

/-- Controls that are applied by invocations. --/
def Invocable : Control → Prop
  | .call _ | .branch .. | .concurrency _ => True
  | _ => False

/-- The trigger of an invocation fits the input shape of its placement (§3.1, §5.3). --/
def TriggerOk (s : State) (path : Path) (i : Invocation) : Workflow.Shape → Prop
  | .none | .entry => i.trigger = none
  | .single j c => ∃ src inp, s.resolveSingle path j c = .value src inp ∧ i.trigger = some src
  | .stream j _ => ∃ src d, i.trigger = some src ∧ s.delivery? path j src = some d ∧ d.outcome ≠ .failed
  | .merge _ => False

/-- What a settlement found about the input of its placement: no input remains that could start
    another invocation, and a Stream input ended. --/
def InputDone (s : State) (path : Path) (pl : Placement) : Workflow.Shape → Prop
  | .none | .entry => ∃ i ∈ s.invocationsOf path pl.name, i.trigger = none
  | .single j c => s.resolveSingle path j c ≠ .pending ∧
      ∀ src inp, s.resolveSingle path j c = .value src inp → ∃ i ∈ s.invocationsOf path pl.name, i.trigger = some src
  | .stream j c => (s.settled? path c.source).isSome ∧ (∀ r ∈ s.eligible path c, (s.delivery? path j r.id).isSome) ∧
      ((∀ e, pl.control ≠ .waitStream e) → ∀ d ∈ s.deliveriesOn path j, d.outcome ≠ .failed →
        ∃ i ∈ s.invocationsOf path pl.name, i.trigger = some d.source)
  | .merge cs => ∀ jc ∈ cs, s.resolveSingle path jc.1 jc.2 ≠ .pending

section
variable {s : State} {path : Path} {pl : Placement}

theorem find?_trigger_none {inv : Invocation}
    (h : List.find? (fun x => x.trigger.isNone) (s.invocationsOf path pl.name) = some inv) :
    inv ∈ s.invocationsOf path pl.name ∧ inv.trigger = none :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem find?_trigger_some {src : ResultId} {inv : Invocation}
    (h : List.find? (fun x => x.trigger == some src) (s.invocationsOf path pl.name) = some inv) :
    inv ∈ s.invocationsOf path pl.name ∧ inv.trigger = some src :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem triggered_of_all {j : Nat}
    (h : ((s.deliveriesOn path j).all fun d =>
      d.outcome == Delivered.failed || (s.invocationsOf path pl.name).any fun x => x.trigger == some d.source) = true) :
    ∀ d ∈ s.deliveriesOn path j, d.outcome ≠ .failed → ∃ i ∈ s.invocationsOf path pl.name, i.trigger = some d.source := by
  intro d hd hne
  have := List.all_eq_true.mp h d hd
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
  rcases this with h | ⟨i, hi, hi'⟩
  · exact absurd h hne
  · exact ⟨i, hi, by simpa using hi'⟩

end

/-- A settlement used up the input of its placement. --/
theorem settleOutcome_input {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Option Result} (h : s.settleOutcome path pl shape kind = some (x, res)) :
    InputDone s path pl shape := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i e j c hc
    simp only [option_bind_eq_some] at h
    obtain ⟨o, ho, -⟩ := h
    obtain ⟨x', hx', hall, -⟩ := streamEnd?_eq_some.mp ho
    exact ⟨by rw [hx']; rfl, hall, fun hne => absurd hc (hne _)⟩
  · rename_i e cs hc
    simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
    obtain ⟨hall, -⟩ := h
    intro jc hjc
    have := List.all_eq_true.mp hall _ (List.mem_map_of_mem (f := fun x => s.resolveSingle path x.fst x.snd) hjc)
    simpa using this
  · rename_i j arms hc
    split at h
    · simp only [option_bind_eq_some] at h
      obtain ⟨inv, hinv, -⟩ := h
      obtain ⟨hmem, htr⟩ := find?_trigger_none hinv
      exact ⟨inv, hmem, htr⟩
    · rename_i j' c
      split at h
      · cases h
      · rename_i src inp hres
        simp only [option_bind_eq_some] at h
        obtain ⟨inv, hinv, -⟩ := h
        refine ⟨by rw [hres]; simp, fun src' inp' h' => ?_⟩
        rw [hres] at h'
        cases h'
        exact ⟨inv, find?_trigger_some hinv⟩
      all_goals
        rename_i hres
        exact ⟨by rw [hres]; simp, fun _ _ h' => by rw [hres] at h'; cases h'⟩
    · rename_i j' c
      simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
      obtain ⟨o, ho, htrig, -⟩ := h
      obtain ⟨x', hx', hall, -⟩ := streamEnd?_eq_some.mp ho
      exact ⟨by rw [hx']; rfl, hall, fun _ => triggered_of_all htrig⟩
    · cases h
  all_goals first
    | cases h
    | split at h
      · simp only [option_bind_eq_some] at h
        obtain ⟨inv, hinv, -⟩ := h
        obtain ⟨hmem, htr⟩ := find?_trigger_none hinv
        exact ⟨inv, hmem, htr⟩
      · simp only [option_bind_eq_some] at h
        obtain ⟨inv, hinv, -⟩ := h
        obtain ⟨hmem, htr⟩ := find?_trigger_none hinv
        exact ⟨inv, hmem, htr⟩
      · rename_i j' c
        split at h
        · cases h
        · rename_i src inp hres
          simp only [option_bind_eq_some] at h
          obtain ⟨inv, hinv, -⟩ := h
          refine ⟨by rw [hres]; simp, fun src' inp' h' => ?_⟩
          rw [hres] at h'
          cases h'
          exact ⟨inv, find?_trigger_some hinv⟩
        all_goals
          rename_i hres
          exact ⟨by rw [hres]; simp, fun _ _ h' => by rw [hres] at h'; cases h'⟩
      · rename_i j' c
        simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
        obtain ⟨o, ho, htrig, -⟩ := h
        obtain ⟨x', hx', hall, -⟩ := streamEnd?_eq_some.mp ho
        exact ⟨by rw [hx']; rfl, hall, fun _ => triggered_of_all htrig⟩
      · cases h

/-- A settlement records a result only as the aggregate of a waitStream or Merge, with a normal
    outcome (§9). --/
theorem settleOutcome_res {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {r : Result} (h : s.settleOutcome path pl shape kind = some (x, some r)) :
    x.outcome = .normal ∧ x.arms = [] ∧
      ((∃ e j c, pl.control = .waitStream e ∧ shape = .stream j c) ∨ (∃ e cs, pl.control = .merge e ∧ shape = .merge cs)) ∧
      r.id = Key.aggregate path pl.name ∧ r.run = path ∧ r.placement = pl.name ∧
      r.producer = Key.aggregate path pl.name ∧ r.arm = none := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i e j c hc
    simp only [option_bind_eq_some] at h
    obtain ⟨o, -, h⟩ := h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, Or.inl ⟨e, j, c, hc, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i e cs hc
    simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
    obtain ⟨-, h⟩ := h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, Or.inr ⟨e, cs, hc, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    repeat' (first
      | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h; done)
      | (simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h)
      | obtain ⟨_, _, h⟩ := h
      | obtain ⟨_, h⟩ := h
      | split at h)

/-- The arms a branch settles after its judge chose `arm`. --/
def chosenArms (arm : Option String) (arms : List String) : List (String × Outcome) :=
  arms.map fun a => (a, if (arm == some a) = true then Outcome.normal else Outcome.skipped)

/-- A Single output that settled without a value on some arm had no succeeded invocation, except
    that a branch whose judge chose another arm settles that arm as not selected (§7.2, §10.1). --/
theorem settleOutcome_nonnormal {s : State} {path : Path} {pl : Placement} {shape : Workflow.Shape}
    {x : Settled} {res : Option Result} (h : s.settleOutcome path pl shape .single = some (x, res))
    (huniq : ∀ i₁ ∈ s.invocationsOf path pl.name, ∀ i₂ ∈ s.invocationsOf path pl.name,
      i₁.trigger = i₂.trigger → i₁ = i₂)
    (hstream : ∀ j c, shape ≠ .stream j c) {a : Option String} (ha : armOutcome x a ≠ .normal)
    {inv : Invocation} (hinv : inv ∈ s.invocationsOf path pl.name) (htrig : TriggerOk s path inv shape)
    (hsucc : inv.status = .succeeded) :
    (∃ j arms, pl.control = .branch j arms) ∧ ∃ b, a = some b ∧ inv.arm ≠ some b := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨-, h⟩ := h
  -- A branch judged `inv`; only the arms it did not choose settle without a value.
  have byInv : ∀ {j arms}, pl.control = .branch j arms →
      armOutcome { run := path, placement := pl.name, outcome := .normal, arms := chosenArms inv.arm arms } a ≠
        .normal →
      (∃ j arms, pl.control = .branch j arms) ∧ ∃ b, a = some b ∧ inv.arm ≠ some b := by
    intro j arms hc ha
    refine ⟨⟨j, arms, hc⟩, ?_⟩
    cases a with
    | none => exact absurd rfl ha
    | some b =>
      refine ⟨b, rfl, fun hb => ha ?_⟩
      rw [armOutcome_arms (f := fun a => if (inv.arm == some a) = true then Outcome.normal else Outcome.skipped) rfl]
      simp [hb]
  -- Calls and concurrency settle normally after a succeeded invocation.
  have byCall : ∀ {x' : Settled}, x'.outcome = invocationOutcome .single inv.status → x'.arms = [] →
      x' = x → False := by
    rintro x' hout harms rfl
    apply ha
    rw [armOutcome_nil harms, hout, hsucc]
    rfl
  split at h
  · exact absurd rfl (hstream _ _)
  · exact htrig.elim
  · rename_i j arms hc
    split at h
    · simp only [option_bind_eq_some] at h
      obtain ⟨inv', hinv', h⟩ := h
      obtain ⟨hmem', htr'⟩ := find?_trigger_none hinv'
      obtain rfl : inv' = inv := huniq _ hmem' _ hinv (htr'.trans htrig.symm)
      rw [hsucc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact byInv hc ha
    · rename_i j' c
      obtain ⟨src', inp', hres', htr⟩ := htrig
      rw [hres'] at h
      simp only [option_bind_eq_some] at h
      obtain ⟨inv', hinv', h⟩ := h
      obtain ⟨hmem', htr'⟩ := find?_trigger_some hinv'
      obtain rfl : inv' = inv := huniq _ hmem' _ hinv (htr'.trans htr.symm)
      rw [hsucc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact byInv hc ha
    · exact absurd rfl (hstream _ _)
    · cases h
  all_goals first
    | cases h
    | split at h
      · simp only [option_bind_eq_some] at h
        obtain ⟨inv', hinv', h⟩ := h
        obtain ⟨hmem', htr'⟩ := find?_trigger_none hinv'
        obtain rfl : inv' = inv := huniq _ hmem' _ hinv (htr'.trans htrig.symm)
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact (byCall rfl rfl h.1).elim
      · simp only [option_bind_eq_some] at h
        obtain ⟨inv', hinv', h⟩ := h
        obtain ⟨hmem', htr'⟩ := find?_trigger_none hinv'
        obtain rfl : inv' = inv := huniq _ hmem' _ hinv (htr'.trans htrig.symm)
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact (byCall rfl rfl h.1).elim
      · rename_i j' c
        obtain ⟨src', inp', hres', htr⟩ := htrig
        rw [hres'] at h
        simp only [option_bind_eq_some] at h
        obtain ⟨inv', hinv', h⟩ := h
        obtain ⟨hmem', htr'⟩ := find?_trigger_some hinv'
        obtain rfl : inv' = inv := huniq _ hmem' _ hinv (htr'.trans htr.symm)
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact (byCall rfl rfl h.1).elim
      · exact absurd rfl (hstream _ _)
      · cases h

end Suimon.Delivery
