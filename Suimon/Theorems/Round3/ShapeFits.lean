import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## [6] Round3/ShapeFits.lean — task B4 (static) -/

section ShapeFitsSection
variable {p : Program}

/-- How a placement takes its input, by its control (§3.2, §9). -/
def ShapeFits : Control → Workflow.Shape → Prop
  | .merge _, .merge _ => True
  | .waitStream _, .stream .. => True
  | .branch .., .entry | .branch .., .single .. | .branch .., .stream .. => True
  | .call _, .none | .call _, .entry | .call _, .single .. | .call _, .stream .. => True
  | .concurrency _, .none | .concurrency _, .entry | .concurrency _, .single .. | .concurrency _, .stream .. => True
  | _, _ => False

/-- The input kind of an entry is Single. -/
theorem ShapeFits.inputKind?_entry {w : Workflow} {name : String} {inp : Option Kind}
    (he : w.isEntry name = true) (h : w.inputKind? p name = some inp) : inp = some .single := by
  unfold Workflow.inputKind? at h
  simp only [option_bind_eq_some] at h
  obtain ⟨sources, -, hcomb⟩ := h
  unfold Workflow.combineInput at hcomb
  simp only [he, ↓reduceIte] at hcomb
  split at hcomb
  · exact (Option.some.inj hcomb).symm
  · cases hcomb

/-- A placement that is not the entry and has no input connection takes no input. -/
theorem ShapeFits.inputKind?_none {w : Workflow} {name : String} {inp : Option Kind}
    (he : w.isEntry name = false) (hinc : w.incoming name = []) (h : w.inputKind? p name = some inp) :
    inp = none := by
  unfold Workflow.inputKind? at h
  rw [hinc] at h
  simp only [List.mapM_nil, option_bind_eq_some, pure, Option.some.injEq, exists_eq_left'] at h
  unfold Workflow.combineInput at h
  simp only [he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
  exact h.symm

/-- A placement that is not the entry and has one input connection takes the kind of its source. -/
theorem ShapeFits.inputKind?_one {w : Workflow} {name : String} {c : Connection} {inp : Option Kind}
    (he : w.isEntry name = false) (hinc : w.incoming name = [c]) (h : w.inputKind? p name = some inp) :
    ∃ k', w.outputKind? p c.source = some k' ∧ inp = some k' := by
  unfold Workflow.inputKind? at h
  rw [hinc] at h
  simp only [List.mapM_cons, List.mapM_nil, option_bind_eq_some, pure, Option.some.injEq] at h
  obtain ⟨sources, ⟨k', hk', -, rfl, rfl⟩, hcomb⟩ := h
  unfold Workflow.combineInput at hcomb
  simp only [he, Bool.false_eq_true, ↓reduceIte, List.all_nil, Option.some.injEq] at hcomb
  exact ⟨k', hk', hcomb.symm⟩

/-- A placement of a valid workflow has an input shape, and it fits its control. -/
private theorem shape_exists {w : Workflow} {pl : Placement} (hwc : WorkflowChecked p w)
    (hpl : pl ∈ w.placements) {k : Kind} (hk : w.outputKind? p pl.name = some k) :
    ∃ sh, w.shape? p pl.name = some sh ∧ ShapeFits pl.control sh := by
  have hplc := hwc.placements pl hpl
  have hfind : w.placement? pl.name = some pl := Workflow.placement?_of_mem hwc.names hpl
  -- The output kind is the rule applied to the input kind.
  obtain ⟨inp, hin, hrule⟩ : ∃ inp, w.inputKind? p pl.name = some inp ∧
      p.outputKind pl.control inp = some k := by
    have hbind := Workflow.outputKind?_eq_bind (p := p) hwc.names hwc.acyclic hpl
    rw [hk] at hbind
    cases h : w.inputKind? p pl.name with
    | none => rw [h] at hbind; cases hbind
    | some inp => rw [h] at hbind; exact ⟨inp, rfl, hbind.symm⟩
  by_cases hm : ∃ e, pl.control = .merge e
  · obtain ⟨e, he⟩ := hm
    refine ⟨_, Settle.shape?_of_merge hfind he, ?_⟩
    rw [he]
    trivial
  have hm' : ∀ e, pl.control ≠ .merge e := fun e he => hm ⟨e, he⟩
  have hcount := hplc.inputs hm'
  have hinc := Delivery.inputs_map_snd w pl.name
  -- `shape?` past the Merge test.
  have hshape : w.shape? p pl.name =
      if w.isEntry pl.name then some .entry else
      match w.inputs pl.name with
      | [] => some .none
      | [(i, c)] => match w.outputKind? p c.source with
        | some .single => some (.single i c)
        | some .stream => some (.stream i c)
        | none => none
      | _ => none := by
    unfold Workflow.shape?
    cases hc : pl.control <;> simp only [hfind, hc, Option.bind_eq_bind, Option.bind_some] <;>
      first | exact absurd hc (hm' _) | rfl
  cases hentry : w.isEntry pl.name
  · simp only [hentry, Bool.false_eq_true, ↓reduceIte] at hshape
    match hinputs : w.inputs pl.name, hshape with
    | [], hshape =>
      rw [hinputs, List.map_nil] at hinc
      have hnone := ShapeFits.inputKind?_none hentry hinc.symm hin
      subst hnone
      refine ⟨_, hshape, ?_⟩
      cases hc : pl.control <;> rw [hc] at hrule <;> simp [Program.outputKind] at hrule <;>
        first | exact absurd hc (hm' _) | trivial
    | [(i, c)], hshape =>
      rw [hinputs, List.map_cons, List.map_nil] at hinc
      obtain ⟨k', hk', rfl⟩ := ShapeFits.inputKind?_one hentry hinc.symm hin
      dsimp only at hshape hk'
      rw [hk'] at hshape
      cases k'
      · refine ⟨_, hshape, ?_⟩
        cases hc : pl.control <;> rw [hc] at hrule <;> simp [Program.outputKind] at hrule <;>
          first | exact absurd hc (hm' _) | trivial
      · refine ⟨_, hshape, ?_⟩
        cases hc : pl.control <;> first | exact absurd hc (hm' _) | trivial
    | _ :: _ :: _, _ =>
      rw [hinputs] at hinc
      have := congrArg List.length hinc
      simp only [List.length_map, List.length_cons, hentry, Bool.false_eq_true, ↓reduceIte] at this hcount
      omega
  · simp only [hentry, ↓reduceIte] at hshape
    have hsingle := ShapeFits.inputKind?_entry hentry hin
    subst hsingle
    refine ⟨_, hshape, ?_⟩
    cases hc : pl.control <;> rw [hc] at hrule <;> simp [Program.outputKind] at hrule <;>
      first | exact absurd hc (hm' _) | trivial

/-- (N6) Every placement of a valid program has an input shape that fits its control and an output
    kind; a Single input comes from a Single source, a Stream input from a Stream source, and a Merge
    reads all its inputs, which are Single. -/
theorem shape_fits (valid : p.validate = .ok ()) :
    ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∃ sh k, w.shape? p pl.name = some sh ∧
      w.outputKind? p pl.name = some k ∧ ShapeFits pl.control sh ∧
      (∀ j c, sh = .single j c → w.outputKind? p c.source = some .single ∧ (j, c) ∈ w.inputs pl.name) ∧
      (∀ j c, sh = .stream j c → w.outputKind? p c.source = some .stream ∧ (j, c) ∈ w.inputs pl.name) ∧
      (∀ cs, sh = .merge cs → cs = w.inputs pl.name ∧ ∀ jc ∈ cs, w.outputKind? p jc.2.source = some .single) := by
  intro w hw pl hpl
  have hwc := (Program.validate_ok valid).workflows w hw
  have hplc := hwc.placements pl hpl
  have hfind : w.placement? pl.name = some pl := Workflow.placement?_of_mem hwc.names hpl
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hplc.kind
  obtain ⟨sh, hsh, hfit⟩ := shape_exists hwc hpl hk
  refine ⟨sh, k, hsh, hk, hfit, ?_, ?_, ?_⟩
  · rintro j c rfl
    obtain ⟨hone, -, -, hkc⟩ := Delivery.shape?_single hsh
    exact ⟨hkc, hone ▸ List.mem_singleton_self _⟩
  · rintro j c rfl
    obtain ⟨hone, -, -, hkc⟩ := Delivery.shape?_stream hsh
    exact ⟨hkc, hone ▸ List.mem_singleton_self _⟩
  · rintro cs rfl
    obtain ⟨pl', hpl', hcase⟩ := Delivery.shape?_eq hsh
    rw [hfind, Option.some.injEq] at hpl'
    subst hpl'
    rcases hcase with ⟨⟨e, he⟩, hcs⟩ | ⟨-, hrest⟩
    · cases hcs
      refine ⟨rfl, fun jc hjc => hplc.merge e he jc.2 ?_⟩
      rw [← Delivery.inputs_map_snd]
      exact List.mem_map_of_mem hjc
    · rcases hrest with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, j, c, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;> cases h

end ShapeFitsSection

end Suimon.Round3
