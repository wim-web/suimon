import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## [16] Round3/SettleView.lean — task F2 -/

section SettleView
variable {s t : State}

/-- Two states agree on everything `settleOutcome path pl shape` reads. The reads depend on the input
    shape: a Stream input is read through `streamEnd?` and its deliveries; a Single input, and each input
    of a Merge, only through `resolveSingle`, which reads the one delivery or, without one, the source's
    settlement. Only the arms of the placement's results are read, never whole results: the complete run
    already holds the aggregate of a waitStream or Merge when the other run settles it. (A view that
    compared `resolveSingle` on a Stream input, or `streamEnd?` on a Single input, would be false:
    reviewers' counterexamples `cex.lean`, CEX 2 and CEX 3.) -/
structure SettleViewAgree (s t : State) (path : Path) (pl : Placement) (shape : Workflow.Shape) : Prop where
  invocations : (s.invocationsOf path pl.name).Perm (t.invocationsOf path pl.name)
  triggers : ((s.invocationsOf path pl.name).map (·.trigger)).Nodup
  ended : ∀ i ∈ s.invocationsOf path pl.name, s.invocationEnded i = t.invocationEnded i
  chosen : ((s.resultsOf path pl.name).filterMap (·.arm)).Perm ((t.resultsOf path pl.name).filterMap (·.arm))
  input : match shape with
    | .none | .entry => True
    | .single j c => s.resolveSingle path j c = t.resolveSingle path j c
    | .stream j c => s.streamEnd? path j c = t.streamEnd? path j c ∧
        (s.deliveriesOn path j).Perm (t.deliveriesOn path j)
    | .merge cs => ∀ jc ∈ cs, s.resolveSingle path jc.1 jc.2 = t.resolveSingle path jc.1 jc.2

namespace SettleView

/-- A list whose image under `f` has no duplicates meets each fibre of `f` at most once. -/
theorem eq_of_map_nodup {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, ha, b, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hx, hl⟩ := h
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'
      exact absurd (hab ▸ List.mem_map_of_mem hb') hx
    · subst hb'
      exact absurd (hab.symm ▸ List.mem_map_of_mem ha') hx
    · exact eq_of_map_nodup hl a ha' b hb' hab

/-- `find?` does not see the order of a list in which at most one element passes the test. -/
theorem find?_eq_of_perm {α : Type _} {p : α → Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂)
    (uniq : ∀ a ∈ l₁, ∀ b ∈ l₁, p a = true → p b = true → a = b) : l₁.find? p = l₂.find? p := by
  cases h₁ : l₁.find? p with
  | none =>
    symm
    rw [List.find?_eq_none] at h₁ ⊢
    exact fun x hx => h₁ x (h.mem_iff.mpr hx)
  | some a =>
    have ha := List.mem_of_find?_eq_some h₁
    have hpa := List.find?_some h₁
    cases h₂ : l₂.find? p with
    | none =>
      rw [List.find?_eq_none] at h₂
      exact absurd hpa (h₂ a (h.mem_iff.mp ha))
    | some b =>
      have hb := h.mem_iff.mpr (List.mem_of_find?_eq_some h₂)
      exact congrArg some (uniq a ha b hb hpa (List.find?_some h₂))

theorem all_eq_of_perm {α : Type _} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Bool) :
    l₁.all f = l₂.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H x hx => H x (h.mem_iff.mpr hx), fun H x hx => H x (h.mem_iff.mp hx)⟩

theorem any_eq_of_perm {α : Type _} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Bool) :
    l₁.any f = l₂.any f := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hf⟩ => ⟨x, h.mem_iff.mp hx, hf⟩, fun ⟨x, hx, hf⟩ => ⟨x, h.mem_iff.mpr hx, hf⟩⟩

end SettleView

/-- `settleOutcome` reads lists only through order-insensitive tests (`all`, `any`, `isEmpty`, lengths
    of filters, `find?` by a unique trigger, `listValue`), so it agrees on agreeing views. Suggested
    proof: define the tuple of reads `settleView` and `settleOutcome'` over it, prove
    `settleOutcome = settleOutcome' ∘ settleView` by unfolding, and compare views. -/
theorem settleOutcome_congr {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    (h : SettleViewAgree s t path pl shape) :
    s.settleOutcome path pl shape kind = t.settleOutcome path pl shape kind := by
  -- Instead of a separate view function, each read of `s` in the unfolded rule is rewritten into the
  -- same read of `t`; the reads that are equal (not only permutations) are proven first.
  obtain ⟨hinv, htrig, hended, hchosen, hinput⟩ := h
  have uniq := SettleView.eq_of_map_nodup htrig
  have hall : (s.invocationsOf path pl.name).all s.invocationEnded =
      (t.invocationsOf path pl.name).all t.invocationEnded := by
    rw [← SettleView.all_eq_of_perm hinv t.invocationEnded, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun H x hx => by rw [← hended x hx]; exact H x hx, fun H x hx => by rw [hended x hx]; exact H x hx⟩
  -- Triggers are unique, so at most one invocation has a given trigger.
  have hnone : (s.invocationsOf path pl.name).find? (fun x => x.trigger.isNone) =
      (t.invocationsOf path pl.name).find? (fun x => x.trigger.isNone) :=
    SettleView.find?_eq_of_perm hinv fun a ha b hb hpa hpb => uniq a ha b hb (by
      simp only [Option.isNone_iff_eq_none] at hpa hpb; rw [hpa, hpb])
  have hsrc : ∀ src, (s.invocationsOf path pl.name).find? (fun x => x.trigger == some src) =
      (t.invocationsOf path pl.name).find? (fun x => x.trigger == some src) := fun src =>
    SettleView.find?_eq_of_perm hinv fun a ha b hb hpa hpb => uniq a ha b hb (by
      simp only [beq_iff_eq] at hpa hpb; rw [hpa, hpb])
  have hany : ∀ src, (s.invocationsOf path pl.name).any (fun x => x.trigger == some src) =
      (t.invocationsOf path pl.name).any (fun x => x.trigger == some src) := fun src =>
    SettleView.any_eq_of_perm hinv _
  have hfail : ∀ f : Invocation → Bool, ((s.invocationsOf path pl.name).filter f).length =
      ((t.invocationsOf path pl.name).filter f).length := fun f => (hinv.filter f).length_eq
  have hempty : (s.invocationsOf path pl.name).isEmpty = (t.invocationsOf path pl.name).isEmpty :=
    hinv.isEmpty_eq
  have hskip : ∀ f : Invocation → Bool, (s.invocationsOf path pl.name).all f =
      (t.invocationsOf path pl.name).all f := fun f => SettleView.all_eq_of_perm hinv f
  have hcempty : ((s.resultsOf path pl.name).filterMap (·.arm)).isEmpty =
      ((t.resultsOf path pl.name).filterMap (·.arm)).isEmpty := hchosen.isEmpty_eq
  have hccont : ∀ a, ((s.resultsOf path pl.name).filterMap (·.arm)).contains a =
      ((t.resultsOf path pl.name).filterMap (·.arm)).contains a := fun a => hchosen.contains_eq
  obtain ⟨name, control, policy, timeout⟩ := pl
  unfold State.settleOutcome
  cases shape with
  | none => cases control <;> simp only [hall, hnone]
  | entry => cases control <;> simp only [hall, hnone]
  | single i c =>
    have hres : s.resolveSingle path i c = t.resolveSingle path i c := hinput
    cases control <;> simp only [hall, hsrc, hres]
  | stream i c =>
    obtain ⟨hend, hdel⟩ := hinput
    have hdall := SettleView.all_eq_of_perm hdel
    have hdfilt : ∀ f : Delivery → Bool, ((s.deliveriesOn path i).filter f).length =
        ((t.deliveriesOn path i).filter f).length := fun f => (hdel.filter f).length_eq
    have hdlv : ∀ f : Delivery → Option Value, listValue ((s.deliveriesOn path i).filterMap f) =
        listValue ((t.deliveriesOn path i).filterMap f) := fun f => listValue_perm (hdel.filterMap f)
    cases control <;>
      simp only [hall, hany, hfail, hempty, hskip, hcempty, hccont, hend, hdall, hdfilt, hdlv]
  | merge cs =>
    -- `simp` turns `fun (i, c) => …` into `fun x => … x.1 x.2`, the form of `hmap`.
    have hmap : cs.map (fun x => s.resolveSingle path x.1 x.2) = cs.map (fun x => t.resolveSingle path x.1 x.2) :=
      List.map_congr_left hinput
    cases control <;> simp only [hall, hmap]

namespace SettleView

/-- Agreement is an equivalence on the states whose triggers of the placement are unique. -/
theorem agree_refl {path : Path} {pl : Placement} {shape : Workflow.Shape}
    (h : ((s.invocationsOf path pl.name).map (·.trigger)).Nodup) : SettleViewAgree s s path pl shape where
  invocations := .refl _
  triggers := h
  ended := fun _ _ => rfl
  chosen := .refl _
  input := by cases shape <;> simp

theorem agree_symm {path : Path} {pl : Placement} {shape : Workflow.Shape}
    (h : SettleViewAgree s t path pl shape) : SettleViewAgree t s path pl shape where
  invocations := h.invocations.symm
  triggers := (h.invocations.map (·.trigger)).nodup_iff.mp h.triggers
  ended := fun i hi => (h.ended i (h.invocations.mem_iff.mpr hi)).symm
  chosen := h.chosen.symm
  input := by
    have hin := h.input
    cases shape with
    | none => trivial
    | entry => trivial
    | single j c => exact hin.symm
    | stream j c => exact ⟨hin.1.symm, hin.2.symm⟩
    | merge cs => exact fun jc hjc => (hin jc hjc).symm

theorem agree_trans {u : State} {path : Path} {pl : Placement} {shape : Workflow.Shape}
    (h₁ : SettleViewAgree s t path pl shape) (h₂ : SettleViewAgree t u path pl shape) :
    SettleViewAgree s u path pl shape where
  invocations := h₁.invocations.trans h₂.invocations
  triggers := h₁.triggers
  ended := fun i hi => (h₁.ended i hi).trans (h₂.ended i (h₁.invocations.mem_iff.mp hi))
  chosen := h₁.chosen.trans h₂.chosen
  input := by
    have hin₁ := h₁.input
    have hin₂ := h₂.input
    cases shape with
    | none => trivial
    | entry => trivial
    | single j c => exact hin₁.trans hin₂
    | stream j c => exact ⟨hin₁.1.trans hin₂.1, hin₁.2.trans hin₂.2⟩
    | merge cs => exact fun jc hjc => (hin₁ jc hjc).trans (hin₂ jc hjc)

end SettleView

end SettleView

end Suimon.Round3
