import Suimon.Theorems.DeliveryDyn

/-! Every step keeps the settlement invariant `Sett`: a settled placement gets no new result and no
    new invocation, so what its settlement found stays true. -/

namespace Suimon.Delivery
open State

/-! ### Shapes -/

theorem shape?_eq {p : Definition} {w : Workflow} {name : String} {sh : Workflow.Shape} (h : w.shape? p name = some sh) :
    ∃ pl, w.placement? name = some pl ∧
      (((∃ e, pl.control = .merge e) ∧ sh = .merge (w.inputs name)) ∨
       ((∀ e, pl.control ≠ .merge e) ∧
        ((w.isEntry name = true ∧ sh = .entry) ∨
         (w.isEntry name = false ∧ w.inputs name = [] ∧ sh = .none) ∨
         (w.isEntry name = false ∧ ∃ j c, w.inputs name = [(j, c)] ∧
            ((w.outputKind? p c.source = some .single ∧ sh = .single j c) ∨
             (w.outputKind? p c.source = some .stream ∧ sh = .stream j c)))))) := by
  unfold Workflow.shape? at h
  simp only [option_bind_eq_some] at h
  obtain ⟨pl, hpl, h⟩ := h
  refine ⟨pl, hpl, ?_⟩
  by_cases hm : ∃ e, pl.control = .merge e
  · obtain ⟨e, he⟩ := hm
    simp only [he, pure, ite_true] at h
    exact Or.inl ⟨⟨e, he⟩, (Option.some.inj h).symm⟩
  · have hm'' : ∀ e, pl.control ≠ .merge e := fun e he => hm ⟨e, he⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    refine Or.inr ⟨hm'', ?_⟩
    by_cases he : w.isEntry name = true
    · simp only [he, ↓reduceIte, pure, Option.some.injEq] at h
      exact Or.inl ⟨he, h.symm⟩
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at h
      have he' : w.isEntry name = false := by simpa using he
      split at h
      · rename_i hnil
        simp only [pure, Option.some.injEq] at h
        exact Or.inr (Or.inl ⟨he', hnil, h.symm⟩)
      · rename_i j c hone
        split at h
        · rename_i hk
          simp only [pure, Option.some.injEq] at h
          exact Or.inr (Or.inr ⟨he', j, c, hone, Or.inl ⟨hk, h.symm⟩⟩)
        · rename_i hk
          simp only [pure, Option.some.injEq] at h
          exact Or.inr (Or.inr ⟨he', j, c, hone, Or.inr ⟨hk, h.symm⟩⟩)
        · cases h
      · cases h

theorem shape?_single {p : Definition} {w : Workflow} {name : String} {j : Nat} {c : Connection}
    (h : w.shape? p name = some (.single j c)) :
    w.inputs name = [(j, c)] ∧ w.connections[j]? = some c ∧ c.target = name ∧ w.outputKind? p c.source = some .single := by
  obtain ⟨pl, -, (⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, j', c', hone, ⟨hk, h⟩ | ⟨-, h⟩⟩⟩)⟩ := shape?_eq h <;> cases h
  exact ⟨hone, mem_inputs.mp (hone ▸ List.mem_singleton_self _) |>.1, mem_inputs.mp (hone ▸ List.mem_singleton_self _) |>.2,
    hk⟩

theorem shape?_stream {p : Definition} {w : Workflow} {name : String} {j : Nat} {c : Connection}
    (h : w.shape? p name = some (.stream j c)) :
    w.inputs name = [(j, c)] ∧ w.connections[j]? = some c ∧ c.target = name ∧ w.outputKind? p c.source = some .stream := by
  obtain ⟨pl, -, (⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, j', c', hone, ⟨-, h⟩ | ⟨hk, h⟩⟩⟩)⟩ := shape?_eq h <;> cases h
  exact ⟨hone, mem_inputs.mp (hone ▸ List.mem_singleton_self _) |>.1, mem_inputs.mp (hone ▸ List.mem_singleton_self _) |>.2,
    hk⟩

/-- A Single output that the control computes from its input kind: Stream functions, Stream
    concurrency outputs and Stream inputs all give Stream outputs (§5.2). --/
theorem single_kind {p : Definition} {w : Workflow} {name : String} {sh : Workflow.Shape} {pl : Placement}
    (hsh : w.shape? p name = some sh) (hk : w.outputKind? p name = some .single) (hpl : w.placement? name = some pl)
    (hinv : Invocable pl.control) :
    (∀ j c, sh ≠ .stream j c) ∧
    (∀ f d, pl.control = .call (.function f) → p.function? f = some d → d.output.kind ≠ .stream) ∧
    (∀ c, pl.control = .concurrency c → c.output ≠ .stream) := by
  have hm : ∀ e, pl.control ≠ .merge e := fun e h => by rw [h] at hinv; exact hinv
  obtain ⟨inp, hinp, hout, -⟩ := outputKind?_shape hsh hk hpl hm
  refine ⟨?_, ?_, ?_⟩
  · rintro j c rfl
    simp only [shapeInput, Option.some.injEq] at hinp
    subst hinp
    cases hc : pl.control <;> rw [hc] at hout hinv <;> simp [Definition.outputKind, Invocable] at hout hinv
  · intro f d hf hd hkd
    rw [hf] at hout
    cases sh <;> simp only [shapeInput, Option.some.injEq, reduceCtorEq] at hinp <;> subst hinp <;>
      simp [Definition.outputKind, Definition.bodyKind, hd, hkd] at hout
  · intro c hc hco
    rw [hc] at hout
    cases sh <;> simp only [shapeInput, Option.some.injEq, reduceCtorEq] at hinp <;> subst hinp <;>
      simp [Definition.outputKind, hco] at hout

section
variable {p : Definition} {s t : State} {op : Op}

theorem mem_invocationsOf_of {s : State} {i : Invocation} {path : Path} {name : String} (hi : i ∈ s.invocations)
    (hr : i.run = path) (hp : i.placement = name) : i ∈ s.invocationsOf path name :=
  mem_invocationsOf.mpr ⟨hi, hr, hp⟩

/-- A settled placement accepts no new result (§10.3). --/
theorem frozen_results (inv : Inv p s) (hs : step p s op = .ok t) {x : Settled} (hx : x ∈ s.settled) :
    ∀ r ∈ t.results, r.run = x.run → r.placement = x.placement → r ∈ s.results := by
  intro r hr hrun hpl
  rcases step_results_back hs r hr with h | ⟨-, -, -, hcase⟩
  · exact h
  · exfalso
    have ended : ∀ {i : Invocation}, i ∈ s.invocations → i.run = x.run → i.placement = x.placement →
        s.invocationEnded i = true := fun hi hir hip => inv.sett.ended x hx _ hi hir hip
    rcases hcase with ⟨c, hc, i, hi, hct, hst, -, -, hio, hrr, hrp, -⟩ |
        ⟨c, hc, i, hi, -, -, -, -, -, hct, hst, hio, -, -, -, hrr, hrp, -⟩ |
        ⟨c, hc, i, hi, hct, hst, -, hio, hrr, hrp, -⟩ |
        ⟨e, he, cc, tr, hcc, -, htr, htre, htrp, hinc, hrr, hrp, -⟩ |
        ⟨e, he, i, hi, cc, hec, hio, -, -, hrr, hrp, -⟩ |
        ⟨R, hR, i, hi, hRc, hRt, hRo, hrr, hrp, -⟩ |
        ⟨run, w, pl, shape, kind, x', -, -, hpl', hnone, -⟩
    · have := (invocationEnded_iff.mp (ended hi (hrr ▸ hrun) (hrp ▸ hpl))).2.1 c hc hio.symm hct
      simp [hst, CallStatus.ended] at this
    · have := (invocationEnded_iff.mp (ended hi (hrr ▸ hrun) (hrp ▸ hpl))).2.1 c hc hio.symm hct
      simp [hst, CallStatus.ended] at this
    · have := (invocationEnded_iff.mp (ended hi (hrr ▸ hrun) (hrp ▸ hpl))).2.1 c hc hio.symm hct
      simp [hst, CallStatus.ended] at this
    · -- A task output needs a pending transform, but the execution completed its output.
      obtain ⟨i, hi, hiid, hir, hip, -⟩ := inv.own.executions e he
      have hcomp := (invocationEnded_iff.mp (ended hi (by rw [hir, ← hrr, hrun]) (by rw [hip, ← hrp, hpl]))).2.2.2
        e he hiid.symm
      exact (inv.dyn.execDone e he hcomp).2.2 cc hcc tr htr htre hinc htrp
    · have hir := (execution_placement inv.own inv.wk he hi hio).1
      have hip := (execution_placement inv.own inv.wk he hi hio).2.1
      have := (invocationEnded_iff.mp (ended hi (by rw [hir, ← hrr, hrun]) (by rw [hip, ← hrp, hpl]))).2.2.2 e he
        hio.symm
      rw [hec] at this; cases this
    · have := (invocationEnded_iff.mp (ended hi (hrr ▸ hrun) (hrp ▸ hpl))).2.2.1 R hR hRo hRt
      rw [hRc] at this; cases this
    · have := inv.wk.settled?_of_mem hx
      rw [← hrun, ← hpl, hnone] at this
      cases this

/-- A settled placement is invoked no more. --/
theorem frozen_invocations (inv : Inv p s) (hs : step p s op = .ok t) {x : Settled} (hx : x ∈ s.settled) :
    ∀ i ∈ t.invocations, i.run = x.run → i.placement = x.placement → InvOld s i := by
  intro i hi hrun hpl
  rcases step_invocations_back hs i hi with h | ⟨-, -, r, w', pl', hr, -, hw', hpl'', hinvc, hinput, -, -, -, hdup, -⟩
  · exact h
  · exfalso
    obtain ⟨w, pl, sh, hw, hplx, hsh, hdone⟩ := inv.sett.input x hx
    have hww : w' = w := by
      rw [← hrun, workflow?_iff] at hw
      obtain ⟨r', hr', hw''⟩ := hw
      rw [hr] at hr'; cases hr'
      rw [hw'] at hw''; cases hw''
      rfl
    subst hww
    rw [← hpl] at hplx hsh
    rw [hpl''] at hplx
    cases hplx
    have hname : pl'.name = x.placement := (Workflow.placement?_eq_some hpl'').2.trans hpl
    have hpath := (run?_eq_some hr).2
    rcases Step.invocationInput_inv hinput with ⟨hsh', htr, -⟩ | ⟨hsh', htr, -⟩ | ⟨j, c, src, hsh', htr, hres⟩ |
        ⟨j, c, src, d, hsh', htr, hd, hout⟩ <;> rw [hsh] at hsh' <;> cases hsh'
    · obtain ⟨i', hi', htr'⟩ := hdone
      exact hdup i' (by rw [hrun, hpl, ← hname]; exact hi') (htr'.trans htr.symm)
    · obtain ⟨i', hi', htr'⟩ := hdone
      exact hdup i' (by rw [hrun, hpl, ← hname]; exact hi') (htr'.trans htr.symm)
    · obtain ⟨i', hi', htr'⟩ := hdone.2 src i.input (by rw [← hrun, ← hpath]; exact hres)
      exact hdup i' (by rw [hrun, hpl, ← hname]; exact hi') (htr'.trans htr.symm)
    · have hnw : ∀ e, pl'.control ≠ .waitStream e := fun e h => by rw [h] at hinvc; exact hinvc
      obtain ⟨hdm, hdrun, hdconn, hdsrc⟩ := delivery?_eq_some hd
      have hne : d.outcome ≠ .failed := by rcases hout with ⟨v, hv, -⟩ | ⟨hv, -⟩ <;> rw [hv] <;> simp
      obtain ⟨i', hi', htr'⟩ := hdone.2.2 hnw d (mem_deliveriesOn.mpr ⟨hdm, by rw [hdrun, hpath, hrun], hdconn⟩) hne
      exact hdup i' (by rw [hrun, hpl, ← hname]; exact hi') (by rw [htr', hdsrc, htr])

theorem step_ended (inv : Inv p s) (hs : step p s op = .ok t) :
    ∀ x ∈ t.settled, ∀ i ∈ t.invocations, i.run = x.run → i.placement = x.placement → t.invocationEnded i = true := by
  intro x hx i hi hrun hpl
  rcases step_settled_back hs x hx with hx₀ | ⟨-, -, run, w, pl, shape, kind, res, -, -, -, hpl', -, -, -, hout, -, -, -,
      hti, -⟩
  · obtain ⟨i₀, hi₀, hid, hir, hip, -, -⟩ := frozen_invocations inv hs hx₀ i hi hrun hpl
    exact ended_kept inv hs hi₀ (inv.sett.ended x hx₀ i₀ hi₀ (hir.trans hrun) (hip.trans hpl)) hi hid.symm
  · obtain ⟨hall, -, -, -⟩ := State.settleOutcome_some hout
    have hi₀ : i ∈ s.invocations := hti ▸ hi
    have hend := List.all_eq_true.mp hall i
      (mem_invocationsOf.mpr ⟨hi₀, hrun, by rw [hpl, (Workflow.placement?_eq_some hpl').2]⟩)
    exact ended_kept inv hs hi₀ hend hi rfl

theorem resolveSingle_ne_pending_kept {s t : State} (g : s.Grows t) {path : Path} {j : Nat} {c : Connection}
    (h : s.resolveSingle path j c ≠ .pending) : t.resolveSingle path j c ≠ .pending := by
  rcases hd : t.deliveriesOn path j with _ | ⟨d, rest⟩
  · have hnil : s.deliveriesOn path j = [] := by
      obtain ⟨rest', hrest⟩ := deliveriesOn_prefix g path j
      rw [hd] at hrest
      exact (List.append_eq_nil_iff.mp hrest).1
    rw [resolveSingle_stable g h (fun _ => hd)]
    exact h
  · rw [resolveSingle_of_cons hd]
    split <;> simp

/-- What a settlement found about its input stays true (§10.3). --/
theorem inputDone_kept (inv : Inv p s) (hs : step p s op = .ok t) {path : Path} {w : Workflow} {pl : Placement}
    {sh : Workflow.Shape} (hw : s.workflow? p path = some w) (hsh : w.shape? p pl.name = some sh)
    (h : InputDone s path pl sh) : InputDone t path pl sh := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  have kept_inv : ∀ {i : Invocation}, i ∈ s.invocationsOf path pl.name →
      ∃ i' ∈ t.invocationsOf path pl.name, i'.trigger = i.trigger := by
    intro i hi
    obtain ⟨hi, hir, hip⟩ := mem_invocationsOf.mp hi
    obtain ⟨i', hi', -, a2, a3, a4, -⟩ := K.invocation i hi
    exact ⟨i', mem_invocationsOf.mpr ⟨hi', a2.trans hir, a3.trans hip⟩, a4⟩
  cases sh with
  | none =>
    obtain ⟨i, hi, htr⟩ := h
    obtain ⟨i', hi', htr'⟩ := kept_inv hi
    exact ⟨i', hi', htr'.trans htr⟩
  | entry =>
    obtain ⟨i, hi, htr⟩ := h
    obtain ⟨i', hi', htr'⟩ := kept_inv hi
    exact ⟨i', hi', htr'.trans htr⟩
  | single j c =>
    obtain ⟨hne, hval⟩ := h
    obtain ⟨-, hcj, -, hkind⟩ := shape?_single hsh
    have hstable : t.resolveSingle path j c = s.resolveSingle path j c := by
      refine resolveSingle_stable K.grows hne fun hnil => ?_
      -- Nothing arrives where the source settled without a value on the connection's arm.
      rcases hd : t.deliveriesOn path j with _ | ⟨d, rest⟩
      · rfl
      · exfalso
        have hdm : d ∈ t.deliveriesOn path j := by rw [hd]; exact List.mem_cons_self
        obtain ⟨hdm, hdr, hdc⟩ := mem_deliveriesOn.mp hdm
        rcases step_deliveries_back hs d hdm with hd' | ⟨-, -, -, w', c', r, hw', hc', hr, hrr, hrp, harm⟩
        · have : d ∈ s.deliveriesOn path j := mem_deliveriesOn.mpr ⟨hd', hdr, hdc⟩
          rw [hnil] at this; cases this
        · rw [hdr, hw] at hw'; cases hw'
          rw [hdc, hcj] at hc'; cases hc'
          have hres : s.resolveSingle path j c = .skipped ∨ s.resolveSingle path j c = .failure := by
            cases hr' : s.resolveSingle path j c with
            | pending => exact absurd hr' hne
            | value src inp =>
              obtain ⟨d, rest, hd', -⟩ := resolveSingle_value_iff.mp hr'
              rw [hnil] at hd'; cases hd'
            | transformFailed =>
              rw [resolveSingle_of_nil hnil] at hr'
              split at hr'
              · cases hr'
              · split at hr' <;> cases hr'
            | skipped => exact Or.inl rfl
            | failure => exact Or.inr rfl
          obtain ⟨-, y, hy, hyo⟩ := resolveSingle_no_delivery hres
          obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
          obtain ⟨hrm, -⟩ := result?_eq_some hr
          have := inv.sett.none y hym w (by rw [hyr]; exact hw) (by rw [hyp]; exact hkind) c.arm hyo r hrm
            (by rw [hyr, hrr, hdr]) (by rw [hyp, hrp])
          rcases harm with h' | h'
          · exact this.1 h'
          · exact this.2 h'
    refine ⟨by rw [hstable]; exact hne, fun src inp hres => ?_⟩
    rw [hstable] at hres
    obtain ⟨i, hi, htr⟩ := hval src inp hres
    obtain ⟨i', hi', htr'⟩ := kept_inv hi
    exact ⟨i', hi', htr'.trans htr⟩
  | stream j c =>
    obtain ⟨hsettled, hall, htrig⟩ := h
    obtain ⟨-, hcj, -, -⟩ := shape?_stream hsh
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsettled
    obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
    refine ⟨by rw [K.settled? hy]; rfl, fun r hr => ?_, fun hnw d hd hne => ?_⟩
    · -- The source settled, so every eligible result is from before, and was delivered.
      obtain ⟨hrm, hrr, hrp, harm⟩ := mem_eligible.mp hr
      have hr₀ := frozen_results inv hs hym r hrm (by rw [hyr, hrr]) (by rw [hyp, hrp])
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hall r (mem_eligible.mpr ⟨hr₀, hrr, hrp, harm⟩))
      rw [K.delivery? hd]
      rfl
    · obtain ⟨hdm, hdr, hdc⟩ := mem_deliveriesOn.mp hd
      rcases step_deliveries_back hs d hdm with hd' | ⟨-, -, hfresh, w', c', r, hw', hc', hr, hrr, hrp, harm⟩
      · obtain ⟨i, hi, htr⟩ := htrig hnw d (mem_deliveriesOn.mpr ⟨hd', hdr, hdc⟩) hne
        obtain ⟨i', hi', htr'⟩ := kept_inv hi
        exact ⟨i', hi', htr'.trans htr⟩
      · -- Every eligible result was delivered already.
        exfalso
        rw [hdr, hw] at hw'; cases hw'
        rw [hdc, hcj] at hc'; cases hc'
        obtain ⟨hrm, hrid⟩ := result?_eq_some hr
        obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp
          (hall r (mem_eligible.mpr ⟨hrm, by rw [hrr, hdr], hrp, harm⟩))
        rw [hdr, hdc, ← hrid, hd'] at hfresh
        cases hfresh
  | merge cs =>
    intro jc hjc
    exact resolveSingle_ne_pending_kept K.grows (h jc hjc)

theorem step_input (inv : Inv p s) (hs : step p s op = .ok t) :
    ∀ x ∈ t.settled, ∃ w pl sh, t.workflow? p x.run = some w ∧ w.placement? x.placement = some pl ∧
      w.shape? p x.placement = some sh ∧ InputDone t x.run pl sh := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  intro x hx
  rcases step_settled_back hs x hx with hx₀ | ⟨-, -, run, w, pl, shape, kind, res, hr, -, hw, hpl, -, hsh, -, hout, -⟩
  · obtain ⟨w, pl, sh, hw, hpl, hsh, hdone⟩ := inv.sett.input x hx₀
    have hname := (Workflow.placement?_eq_some hpl).2
    exact ⟨w, pl, sh, K.workflow? wk' hw, hpl, hsh, inputDone_kept inv hs hw (by rw [hname]; exact hsh) hdone⟩
  · have hw' : s.workflow? p x.run = some w := workflow?_iff.mpr ⟨run, hr, hw⟩
    have hname := (Workflow.placement?_eq_some hpl).2
    exact ⟨w, pl, shape, K.workflow? wk' hw', hpl, hsh,
      inputDone_kept inv hs hw' (by rw [hname]; exact hsh) (settleOutcome_input hout)⟩

theorem uniq_trigger (own : Own p s) (wk : s.WellKeyed) {path : Path} {name : String} :
    ∀ i₁ ∈ s.invocationsOf path name, ∀ i₂ ∈ s.invocationsOf path name, i₁.trigger = i₂.trigger → i₁ = i₂ := by
  intro i₁ h₁ i₂ h₂ ht
  obtain ⟨h₁, r₁, p₁⟩ := mem_invocationsOf.mp h₁
  obtain ⟨h₂, r₂, p₂⟩ := mem_invocationsOf.mp h₂
  exact wk.invocation_eq_of_id h₁ h₂ (by rw [(own.invocations i₁ h₁).1, (own.invocations i₂ h₂).1, r₁, r₂, p₁, p₂, ht])

theorem step_none (inv : Inv p s) (hs : step p s op = .ok t) :
    ∀ x ∈ t.settled, ∀ w, t.workflow? p x.run = some w → w.outputKind? p x.placement = some .single →
      ∀ a, armOutcome x a ≠ .normal → ∀ r ∈ t.results, r.run = x.run → r.placement = x.placement →
        a ≠ none ∧ r.arm ≠ a := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  intro x hx w hw hk a ha r hr hrun hpl
  rcases step_settled_back hs x hx with hx₀ | ⟨-, -, run, w', pl, shape, kind, res, hr', -, hw', hpl', hfresh, hsh,
      hkind, hout, -, htr, -⟩
  · obtain ⟨w₀, -, -, hw₀, -⟩ := inv.sett.input x hx₀
    rw [K.workflow? wk' hw₀] at hw; cases hw
    exact inv.sett.none x hx₀ w hw₀ hk a ha r (frozen_results inv hs hx₀ r hr hrun hpl) hrun hpl
  · have hws : s.workflow? p x.run = some w' := workflow?_iff.mpr ⟨run, hr', hw'⟩
    rw [K.workflow? wk' hws] at hw; cases hw
    rw [hk] at hkind; cases hkind
    have hname := (Workflow.placement?_eq_some hpl').2
    rw [htr] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases inv.dyn.results r hr with ⟨i, hi, -, hir, hipl, hia, hst⟩ | ⟨-, -, y, hy, hyr, hyp, -⟩
      · -- The owner invocation applies this placement, which is invocable and Single.
        obtain ⟨-, w₂, pl₂, sh₂, hw₂, hpl₂, hinvc, hsh₂, htrig, -⟩ := inv.own.invocations i hi
        rw [hir, hrun, hws] at hw₂
        cases hw₂
        rw [hipl, hpl, hpl'] at hpl₂
        cases hpl₂
        rw [hipl, hpl, hsh] at hsh₂
        cases hsh₂
        obtain ⟨hnostream, hnofun, hnoconc⟩ := single_kind hsh hk hpl' hinvc
        have hsucc : i.status = .succeeded := by
          rcases hst with h | ⟨w₁, pl₁, hw₁, hpl₁, hk₁⟩
          · exact h
          · rw [hir, hrun, hws] at hw₁; cases hw₁
            rw [hipl, hpl, hpl'] at hpl₁; cases hpl₁
            rcases hk₁ with ⟨f, d, hf, hd, hkd⟩ | ⟨c, hc, hco⟩
            · exact absurd hkd (hnofun f d hf hd)
            · exact absurd hco (hnoconc c hc)
        have hmem : i ∈ s.invocationsOf x.run pl.name := mem_invocationsOf.mpr ⟨hi, hir.trans hrun, by
          rw [hipl, hpl, hname]⟩
        have htrig' : TriggerOk s x.run i shape := by rw [← hrun, ← hir]; exact htrig
        obtain ⟨-, b, hb, hib⟩ := settleOutcome_nonnormal hout (uniq_trigger inv.own inv.wk) hnostream ha hmem htrig' hsucc
        subst hb
        exact ⟨by simp, by rw [← hia]; exact hib⟩
      · -- An aggregate would have been recorded with a settlement.
        have := inv.wk.settled?_of_mem hy
        rw [hyr, hyp, hrun, hpl, hfresh] at this
        cases this
    · cases res with
      | none => cases hr
      | some r' =>
        rw [Option.toList_some, List.mem_singleton] at hr
        subst hr
        obtain ⟨hxo, hxa, -⟩ := settleOutcome_res hout
        exact absurd (by rw [armOutcome_nil hxa, hxo]) ha

theorem step_runs (inv : Inv p s) (hs : step p s op = .ok t) :
    ∀ r ∈ t.runs, r.complete = true → (∀ i ∈ t.invocations, i.run = r.path → t.invocationEnded i = true) ∧
      ∀ w, p.workflow? r.workflow = some w → ∀ pl ∈ w.placements, (t.settled? r.path pl.name).isSome := by
  have K := inv.kept hs
  intro r hr hcomp
  rcases step_runs_back (runs_nil_or_started inv) hs r hr with ⟨r₀, hr₀, hp, hwf, -, -, -, -⟩ | ⟨-, hc, -⟩
  · have hr₀lookup : s.run? r₀.path = some r₀ := inv.wk.run?_of_mem hr₀
    rcases step_run_completed inv.wk (runs_nil_or_started inv) hs hr₀ hr hp.symm with hsame | ⟨⟨w, hw, hall⟩, hold⟩
    · have hc₀ : r₀.complete = true := hsame ▸ hcomp
      obtain ⟨hends, hsett⟩ := inv.sett.runs r₀ hr₀ hc₀
      refine ⟨fun i hi hir => ?_, fun w hw pl hpl => ?_⟩
      · rcases step_invocations_back hs i hi with ⟨i₀, hi₀, hid, hrun, -, -, -⟩ | ⟨-, -, r', -, -, hr', hc', -⟩
        · exact ended_kept inv hs hi₀ (hends i₀ hi₀ (by rw [hrun, hir, hp])) hi hid.symm
        · -- A complete run is invoked no more.
          rw [hir, ← hp, hr₀lookup] at hr'
          cases hr'
          rw [hc₀] at hc'; cases hc'
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hsett w (hwf ▸ hw) pl hpl)
        rw [← hp, K.settled? hy]; rfl
    · refine ⟨fun i hi hir => ?_, fun w₃ hw₃ pl hpl => ?_⟩
      · obtain ⟨i₀, hi₀, hid, hrun, hipl, -, -⟩ := hold i hi
        obtain ⟨-, w₂, pl₂, -, hw₂, hpl₂, -⟩ := inv.own.invocations i₀ hi₀
        have hrp : i₀.run = r₀.path := by rw [hrun, hir, hp]
        rw [hrp, workflow?_iff] at hw₂
        obtain ⟨r₂, hr₂, hwx⟩ := hw₂
        rw [hr₀lookup] at hr₂; cases hr₂
        rw [hw] at hwx; cases hwx
        obtain ⟨hplm, hpln⟩ := Workflow.placement?_eq_some hpl₂
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall pl₂ hplm)
        obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
        exact ended_kept inv hs hi₀ (inv.sett.ended y hym i₀ hi₀ (hrp.trans hyr.symm) (hpln.symm.trans hyp.symm)) hi
          hid.symm
      · rw [hwf] at hw
        rw [hw] at hw₃; cases hw₃
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall pl hpl)
        rw [← hp, K.settled? hy]; rfl
  · rw [hc] at hcomp; cases hcomp

theorem step_sett (inv : Inv p s) (hs : step p s op = .ok t) : Sett p t :=
  ⟨step_ended inv hs, step_input inv hs, step_none inv hs, step_runs inv hs⟩

/-- Every step keeps the invariant. --/
theorem step_inv (inv : Inv p s) (hs : step p s op = .ok t) : Inv p t :=
  ⟨step_wellKeyed inv.wk hs, fun h => absurd (step_started hs) (by simp [h]), step_own inv hs, step_dyn inv hs,
    step_sett inv hs⟩

end

end Suimon.Delivery
