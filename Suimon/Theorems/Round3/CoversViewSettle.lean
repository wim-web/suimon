import Suimon.Theorems.Round3.CoversViewInv

namespace Suimon.Round3
open State

/-! ## Helpers for [21] Round3/CoversView.lean — task F3: reading the complete run

`Covers p T s` puts the runs, settlements and deliveries of run 1 into the final state `T` of a
complete run. What `settle` reads about the input of a placement then agrees: a resolved Single
connection resolves alike in both states (it carries at most one delivery, or none at all when its
source settled without a value on its arm), and a Stream connection whose source settled has no
delivery in `T` beyond those of `s` (the source's results are frozen, `Covers.footprint`). -/

namespace CoversViewAux

variable {p : Definition} {s T : State}

/-! ### Lookups carried by `Covers` -/

/-- A run of `s` runs the same workflow in `T`. -/
theorem covers_workflow? (cov : Covers p T s) (wkT : T.WellKeyed) {path : Path} {w : Workflow}
    (h : s.workflow? p path = some w) : T.workflow? p path = some w := by
  obtain ⟨r, hr, hw⟩ := Delivery.workflow?_iff.mp h
  obtain ⟨hrm, hrp⟩ := State.run?_eq_some hr
  obtain ⟨r', hr', h1, h2, -⟩ := cov.runs r hrm
  exact Delivery.workflow?_iff.mpr ⟨r', by rw [← hrp, ← h1]; exact wkT.run?_of_mem hr', by rw [h2]; exact hw⟩

/-- A settlement of `s` is found in `T` under its key. -/
theorem covers_settled? (cov : Covers p T s) (wkT : T.WellKeyed) {path : Path} {name : String} {y : Settled}
    (hy : s.settled? path name = some y) : T.settled? path name = some y := by
  obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
  rw [← hyr, ← hyp]
  exact wkT.settled?_of_mem (cov.settled y hym)

/-! ### Single connections -/

/-- A connection whose source has a Single output carries at most one delivery (Round 2 `Deliv.one`,
    `DeliveryEligible` and unique delivery keys). -/
theorem single_delivery (h : Reachable p s) {path : Path} {w : Workflow} {j : Nat} {c : Connection}
    (hw : s.workflow? p path = some w) (hc : w.connections[j]? = some c) (hk : w.outputKind? p c.source = some .single)
    {d d' : Delivery} (hd : d ∈ s.deliveriesOn path j) (hd' : d' ∈ s.deliveriesOn path j) : d = d' := by
  have inv := Delivery.Reachable.inv h
  obtain ⟨hdm, hdr, hdj⟩ := Delivery.mem_deliveriesOn.mp hd
  obtain ⟨hdm', hdr', hdj'⟩ := Delivery.mem_deliveriesOn.mp hd'
  obtain ⟨w₁, c₁, r, hw₁, hc₁, hr, hrid, hrr, hrp, -⟩ := inv.own.deliveries d hdm
  obtain ⟨w₂, c₂, r', hw₂, hc₂, hr', hrid', hrr', hrp', -⟩ := inv.own.deliveries d' hdm'
  rw [hdr, hw] at hw₁
  cases hw₁
  rw [hdr', hw] at hw₂
  cases hw₂
  rw [hdj, hc] at hc₁
  cases hc₁
  rw [hdj', hc] at hc₂
  cases hc₂
  have hid := (Delivery.Reachable.deliv h).one w path c.source hw hk r hr r' hr' (hrr.trans hdr) hrp
    (hrr'.trans hdr') hrp'
  have hkey : (d.run, d.connection, d.source) = (d'.run, d'.connection, d'.source) := by
    rw [hdr, hdj, hdr', hdj', ← hrid, ← hrid', hid]
  exact Limit.eq_of_key inv.wk.deliveries hdm hdm' hkey

/-- A resolved Single connection resolves in `T` as in `s`. With a delivery in `s`, `T` has the same
    one and no other (`single_delivery`); without one, the source settled in `s` without a value on the
    connection's arm, `T` has that settlement, and no result of the source is eligible in `T`
    (`SettledInv.noEligible`), so `T` has no delivery either. -/
theorem resolveSingle_covers (hT : Reachable p T) (cov : Covers p T s) {path : Path} {w : Workflow} {j : Nat}
    {c : Connection} (hwT : T.workflow? p path = some w) (hc : w.connections[j]? = some c)
    (hk : w.outputKind? p c.source = some .single) (hne : s.resolveSingle path j c ≠ .pending) :
    s.resolveSingle path j c = T.resolveSingle path j c := by
  have wkT := hT.wellKeyed
  have inv := Delivery.Reachable.inv hT
  rcases hs : s.deliveriesOn path j with _ | ⟨d, rest⟩
  · have hres : s.resolveSingle path j c = .skipped ∨ s.resolveSingle path j c = .failure := by
      rw [Delivery.resolveSingle_of_nil hs] at hne ⊢
      cases hx : s.settled? path c.source with
      | none => simp [hx] at hne
      | some y => cases ho : armOutcome y c.arm <;> simp [hx, ho] at hne ⊢
    obtain ⟨-, y, hy, hyo⟩ := Delivery.resolveSingle_no_delivery hres
    obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
    have hTnil : T.deliveriesOn path j = [] := by
      rcases hTd : T.deliveriesOn path j with _ | ⟨d', rest'⟩
      · rfl
      · exfalso
        have hdm : d' ∈ T.deliveriesOn path j := by rw [hTd]; exact List.mem_cons_self
        obtain ⟨hdm, hdr, hdc⟩ := Delivery.mem_deliveriesOn.mp hdm
        obtain ⟨w₁, c₁, r, hw₁, hc₁, hr, -, hrr, hrp, harm⟩ := inv.own.deliveries d' hdm
        rw [hdr, hwT] at hw₁
        cases hw₁
        rw [hdc, hc] at hc₁
        cases hc₁
        have := (Settle.reachable hT).2.2.2.noEligible y (cov.settled y hym) c.arm hyo r
          (Delivery.mem_resultsOf.mpr ⟨hr, by rw [hyr, hrr, hdr], by rw [hyp, hrp]⟩)
        rcases harm with h' | h' <;> simp [h'] at this
    rw [Delivery.resolveSingle_of_nil hs, Delivery.resolveSingle_of_nil hTnil, hy, covers_settled? cov wkT hy]
  · have hds : d ∈ s.deliveriesOn path j := by rw [hs]; exact List.mem_cons_self
    obtain ⟨hdm, hdr, hdj⟩ := Delivery.mem_deliveriesOn.mp hds
    have hdT : d ∈ T.deliveriesOn path j := Delivery.mem_deliveriesOn.mpr ⟨cov.deliveries d hdm, hdr, hdj⟩
    rcases hTd : T.deliveriesOn path j with _ | ⟨d', rest'⟩
    · rw [hTd] at hdT
      cases hdT
    · have e : d' = d := single_delivery hT hwT hc hk (by rw [hTd]; exact List.mem_cons_self) hdT
      subst e
      rw [Delivery.resolveSingle_of_cons hs, Delivery.resolveSingle_of_cons hTd]

/-! ### Stream connections -/

/-- A Stream connection whose source settled in `s`, with every eligible result delivered in `s`: the
    source's results in `T` are those of `s` (`Covers.footprint`), so each eligible result of `T` has
    its delivery in `s`, and `T` has no delivery on the connection beyond those of `s`. -/
theorem stream_back (hT : Reachable p T) (cov : Covers p T s) {path : Path} {w : Workflow} {j : Nat}
    {c : Connection} (hwT : T.workflow? p path = some w) (hc : w.connections[j]? = some c)
    {y : Settled} (hy : s.settled? path c.source = some y)
    (hall : ∀ r ∈ s.eligible path c, (s.delivery? path j r.id).isSome) :
    (∀ r ∈ T.eligible path c, ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = j ∧ d.source = r.id) ∧
    ∀ d ∈ T.deliveriesOn path j, d ∈ s.deliveries := by
  have wkT := hT.wellKeyed
  have inv := Delivery.Reachable.inv hT
  obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
  have fp := (cov.footprint y hym).2.1
  have elig : ∀ r ∈ T.eligible path c, ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = j ∧ d.source = r.id := by
    intro r hr
    obtain ⟨hrm, hrr, hrp, harm⟩ := Delivery.mem_eligible.mp hr
    have hrs := fp r (Delivery.mem_resultsOf.mpr ⟨hrm, by rw [hyr, hrr], by rw [hyp, hrp]⟩)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hall r (Delivery.mem_eligible.mpr ⟨hrs, hrr, hrp, harm⟩))
    obtain ⟨hdm, hdr, hdj, hds⟩ := delivery?_eq_some hd
    exact ⟨d, hdm, hdr, hdj, hds⟩
  refine ⟨elig, fun d hd => ?_⟩
  obtain ⟨hdm, hdr, hdj⟩ := Delivery.mem_deliveriesOn.mp hd
  obtain ⟨w₁, c₁, r, hw₁, hc₁, hr, hrid, hrr, hrp, harm⟩ := inv.own.deliveries d hdm
  rw [hdr, hwT] at hw₁
  cases hw₁
  rw [hdj, hc] at hc₁
  cases hc₁
  obtain ⟨d₀, hd₀, h1, h2, h3⟩ := elig r (Delivery.mem_eligible.mpr ⟨hr, hrr.trans hdr, hrp, harm⟩)
  have hkey : (d₀.run, d₀.connection, d₀.source) = (d.run, d.connection, d.source) := by
    rw [h1, h2, h3, hrid, hdr, hdj]
  have e : d₀ = d := Limit.eq_of_key wkT.deliveries (cov.deliveries d₀ hd₀) hdm hkey
  exact e ▸ hd₀

/-! ### Small facts -/

/-- Only results with an arm contribute arms. -/
theorem filterMap_arm (l : List Result) : l.filterMap (·.arm) = (l.filter (·.arm.isSome)).filterMap (·.arm) := by
  induction l with
  | nil => rfl
  | cons x l ih => cases hx : x.arm <;> simp [hx, ih]

/-- A waitStream is not invoked. -/
theorem not_waitStream_of_invocable {ctl : Control} (h : Delivery.Invocable ctl) : ∀ e, ctl ≠ .waitStream e := by
  intro e he
  rw [he] at h
  exact h

/-- Task results with the same fields are equal. -/
theorem taskResult_ext {a b : TaskResult} (h1 : a.execution = b.execution) (h2 : a.task = b.task)
    (h3 : a.index = b.index) (h4 : a.value = b.value) (h5 : a.output = b.output) : a = b := by
  cases a
  cases b
  simp_all

end CoversViewAux

end Suimon.Round3
