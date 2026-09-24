import Suimon.Theorems.SettleProv

/-! Layer 4 of the settlement invariant: a settled placement keeps its ended invocations, its closed
    input, its missing results, and its waitStream value. `Facts` lists what a step keeps for the
    placements already settled; every step other than a settlement establishes it. -/

namespace Suimon.Settle

open State

variable {p : Definition} {s t u : State}

/-- A delivery that does not reopen the input of a settled placement: it is not on a Stream input
    that ended, and it is on a Single input only after its first delivery. --/
def DeliveryFits (p : Definition) (s : State) (d : Delivery) : Prop :=
  ∀ x ∈ s.settled, d.run = x.run → ∀ w, s.workflow? p x.run = some w → ∀ idx c,
    (w.shape? p x.placement = some (.stream idx c) → d.connection ≠ idx) ∧
    (w.shape? p x.placement = some (.single idx c) → d.connection = idx → s.deliveriesOn x.run idx ≠ [])

/-- What a step keeps for the placements settled before it. --/
structure Facts (p : Definition) (s t : State) : Prop where
  workflows : KeepsWorkflows p s t
  settled : s.settled <+: t.settled
  results : ∃ new, t.results = s.results ++ new ∧ ∀ r ∈ new, s.settled? r.run r.placement = none
  deliveries : ∃ new, t.deliveries = s.deliveries ++ new ∧ ∀ d ∈ new, DeliveryFits p s d
  invocations : ∀ j ∈ s.invocations, ∃ j' ∈ t.invocations, invKey j' = invKey j
  invNew : ∀ i' ∈ t.invocations, (∃ i ∈ s.invocations, invKey i' = invKey i ∧ (i.status ≠ .active → i' = i)) ∨
    s.settled? i'.run i'.placement = none
  callsNew : ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement, ∀ c' ∈ t.calls, c'.owner = i.id →
    c'.task = none → ∃ c ∈ s.calls, c.owner = i.id ∧ c.task = none ∧ (c.status.ended = true → c'.status.ended = true)
  runsNew : ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement, ∀ r' ∈ t.runs, r'.owner = some i.id →
    r'.task = none → ∃ r ∈ s.runs, r.owner = some i.id ∧ r.task = none ∧ (r.complete = true → r'.complete = true)
  execsNew : ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement, ∀ e' ∈ t.executions, e'.id = i.id →
    ∃ e ∈ s.executions, e.id = i.id ∧ (e.complete = true → e'.complete = true)

theorem deliveriesOn_append {s t : State} {new : List Delivery} (h : t.deliveries = s.deliveries ++ new)
    {path : Path} {idx : Nat} : t.deliveriesOn path idx = s.deliveriesOn path idx ++
      new.filter (fun d => d.run == path && d.connection == idx) := by
  simp only [State.deliveriesOn, h, List.filter_append]

theorem deliveriesOn_eq_of_fits {s t : State} {new : List Delivery} (h : t.deliveries = s.deliveries ++ new)
    {path : Path} {idx : Nat} (hnew : ∀ d ∈ new, d.run = path → d.connection ≠ idx) :
    t.deliveriesOn path idx = s.deliveriesOn path idx := by
  rw [deliveriesOn_append h]
  have : new.filter (fun d => d.run == path && d.connection == idx) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hnew d hd hcond.1 hcond.2
  rw [this, List.append_nil]

theorem delivery?_isSome_of_prefix {s t : State} (h : s.deliveries <+: t.deliveries) {path : Path} {index : Nat}
    {source : ResultId} (hd : (s.delivery? path index source).isSome) : (t.delivery? path index source).isSome := by
  cases hs : s.delivery? path index source with
  | none => rw [hs] at hd; cases hd
  | some d => rw [delivery?_of_prefix h hs]; rfl

/-- A settled placement stays closed. --/
theorem Closed.mono {x : Settled} {w : Workflow} {pl : Placement} (h : Closed p s x w pl)
    (hinv : ∀ j ∈ s.invocations, ∃ j' ∈ t.invocations, invKey j' = invKey j)
    (hset : s.settled <+: t.settled)
    (hres : ∃ new, t.results = s.results ++ new ∧ ∀ r ∈ new, s.settled? r.run r.placement = none)
    (hdel : ∃ new, t.deliveries = s.deliveries ++ new ∧ ∀ d ∈ new, d.run = x.run → ∀ idx c,
      (w.shape? p x.placement = some (.stream idx c) → d.connection ≠ idx) ∧
      (w.shape? p x.placement = some (.single idx c) → d.connection = idx → s.deliveriesOn x.run idx ≠ [])) :
    Closed p t x w pl := by
  obtain ⟨newr, hres, hnewr⟩ := hres
  obtain ⟨newd, hdel, hnewd⟩ := hdel
  have hpre : s.deliveries <+: t.deliveries := ⟨newd, hdel.symm⟩
  have hinvOf : ∀ j ∈ s.invocationsOf x.run x.placement, ∃ j' ∈ t.invocationsOf x.run x.placement,
      j'.trigger = j.trigger := by
    intro j hj
    rw [mem_invocationsOf] at hj
    obtain ⟨j', hj', hk⟩ := hinv j hj.1
    simp only [invKey_eq] at hk
    exact ⟨j', mem_invocationsOf.mpr ⟨hj', hk.2.1.trans hj.2.1, hk.2.2.1.trans hj.2.2⟩, hk.2.2.2⟩
  unfold Closed at h ⊢
  cases hsh : w.shape? p x.placement with
  | none => trivial
  | some sh =>
    rw [hsh] at h
    cases sh with
    | none =>
      intro hc
      obtain ⟨j, hj, ht⟩ := h hc
      obtain ⟨j', hj', ht'⟩ := hinvOf j hj
      exact ⟨j', hj', ht'.trans ht⟩
    | entry =>
      intro hc
      obtain ⟨j, hj, ht⟩ := h hc
      obtain ⟨j', hj', ht'⟩ := hinvOf j hj
      exact ⟨j', hj', ht'.trans ht⟩
    | single idx c =>
      obtain ⟨hval, hnil⟩ := h
      have fromS : ∀ src v, s.resolveSingle x.run idx c = .value src v →
          ∃ j ∈ t.invocationsOf x.run x.placement, j.trigger = some src := by
        intro src v hv
        obtain ⟨j, hj, ht⟩ := hval src v hv
        obtain ⟨j', hj', ht'⟩ := hinvOf j hj
        exact ⟨j', hj', ht'.trans ht⟩
      by_cases hne : s.deliveriesOn x.run idx = []
      · have heq : t.deliveriesOn x.run idx = s.deliveriesOn x.run idx :=
          deliveriesOn_eq_of_fits hdel fun d hd hdr hdc => (hnewd d hd hdr idx c).2 hsh hdc hne
        obtain ⟨y, hy, hyo⟩ := hnil hne
        have hy' : t.settled? x.run c.source = some y := settled?_of_prefix hset hy
        have hres_eq : t.resolveSingle x.run idx c = s.resolveSingle x.run idx c := by
          unfold State.resolveSingle
          rw [heq, hne, hy', hy]
        exact ⟨fun src v hv => fromS src v (hres_eq ▸ hv), fun _ => ⟨y, hy', hyo⟩⟩
      · have hres_eq := resolveSingle_of_prefix hpre (c := c) hne
        refine ⟨fun src v hv => fromS src v (hres_eq ▸ hv), fun hnil' => absurd ?_ hne⟩
        obtain ⟨rest, hrest⟩ := deliveriesOn_prefix hpre x.run idx
        rw [hnil'] at hrest
        exact (List.append_eq_nil_iff.mp hrest).1
    | stream idx c =>
      obtain ⟨hsrc, hall, htrig⟩ := h
      have heq : t.deliveriesOn x.run idx = s.deliveriesOn x.run idx :=
        deliveriesOn_eq_of_fits hdel fun d hd hdr => (hnewd d hd hdr idx c).1 hsh
      refine ⟨settled?_isSome_of_prefix hset hsrc, fun r hr => ?_, fun hc d hd hf => ?_⟩
      · rw [mem_eligible, hres] at hr
        obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
        rcases List.mem_append.mp hr1 with hr1 | hr1
        · exact delivery?_isSome_of_prefix hpre (hall r (mem_eligible.mpr ⟨hr1, hr2, hr3, hr4⟩))
        · exfalso
          have := hnewr r hr1
          rw [hr2, hr3] at this
          rw [this] at hsrc
          cases hsrc
      · rw [heq] at hd
        obtain ⟨j, hj, ht⟩ := htrig hc d hd hf
        obtain ⟨j', hj', ht'⟩ := hinvOf j hj
        exact ⟨j', hj', ht'.trans ht⟩
    | merge cs => trivial

namespace SettledInv

theorem ended_mono (h : SettledInv p s) (wk : s.WellKeyed) (f : Facts p s t) :
    ∀ x ∈ s.settled, ∀ i' ∈ t.invocationsOf x.run x.placement, t.invocationEnded i' = true := by
  intro x hx i' hi'
  rw [mem_invocationsOf] at hi'
  obtain ⟨hi'm, hi'r, hi'p⟩ := hi'
  rcases f.invNew i' hi'm with ⟨i, hi, hk, hfix⟩ | hnone
  · simp only [invKey_eq] at hk
    have hiOf : i ∈ s.invocationsOf x.run x.placement :=
      mem_invocationsOf.mpr ⟨hi, hk.2.1.symm.trans hi'r, hk.2.2.1.symm.trans hi'p⟩
    have hend := h.ended x hx i hiOf
    rw [invocationEnded_iff] at hend
    obtain ⟨hst, hcalls, hruns, hexecs⟩ := hend
    have : i' = i := hfix hst
    subst this
    rw [invocationEnded_iff]
    refine ⟨hst, fun c' hc' hco hct => ?_, fun r' hr' hro hrt => ?_, fun e' he' hid => ?_⟩
    · obtain ⟨c, hc, hco', hct', himp⟩ := f.callsNew x hx i' hiOf c' hc' hco hct
      exact himp (hcalls c hc hco' hct')
    · obtain ⟨r, hr, hro', hrt', himp⟩ := f.runsNew x hx i' hiOf r' hr' hro hrt
      exact himp (hruns r hr hro' hrt')
    · obtain ⟨e, he, hid', himp⟩ := f.execsNew x hx i' hiOf e' he' hid
      exact himp (hexecs e he hid')
  · rw [hi'r, hi'p, wk.settled?_of_mem hx] at hnone
    cases hnone

theorem closed_mono (h : SettledInv p s) (f : Facts p s t) :
    ∀ x ∈ s.settled, ∃ w pl, t.workflow? p x.run = some w ∧ w.placement? x.placement = some pl ∧
      Closed p t x w pl := by
  intro x hx
  obtain ⟨w, pl, hw, hpl, hcl⟩ := h.closed x hx
  obtain ⟨new, hdel, hnew⟩ := f.deliveries
  exact ⟨w, pl, f.workflows _ _ hw, hpl,
    hcl.mono f.invocations f.settled f.results ⟨new, hdel, fun d hd hdr => hnew d hd x hx hdr w hw⟩⟩

theorem noEligible_mono (h : SettledInv p s) (wk : s.WellKeyed) (f : Facts p s t) :
    ∀ x ∈ s.settled, ∀ arm, State.armOutcome x arm ≠ .normal →
      ∀ r ∈ t.resultsOf x.run x.placement, (arm.isNone || r.arm == arm) = false := by
  intro x hx arm harm r hr
  obtain ⟨new, hres, hnew⟩ := f.results
  rw [mem_resultsOf, hres] at hr
  obtain ⟨hr1, hr2, hr3⟩ := hr
  rcases List.mem_append.mp hr1 with hr1 | hr1
  · exact h.noEligible x hx arm harm r (mem_resultsOf.mpr ⟨hr1, hr2, hr3⟩)
  · have := hnew r hr1
    rw [hr2, hr3, wk.settled?_of_mem hx] at this
    cases this

/-- A placement with an invocation is invoked, never a waitStream. --/
theorem not_wait_of_inv (own : Own p s) (hw : KeepsWorkflows p s t) {i : Invocation} (hi : i ∈ s.invocations)
    {w : Workflow} {pl : Placement} (hwt : t.workflow? p i.run = some w) (hpl : w.placement? i.placement = some pl)
    (e : ValueType) : pl.control ≠ .waitStream e := by
  obtain ⟨w0, pl0, hw0, hpl0, hinv⟩ := own.invPlaced i hi
  rw [hw _ _ hw0] at hwt
  cases hwt
  rw [hpl0] at hpl
  cases hpl
  intro he
  rw [he] at hinv
  cases hinv

theorem waitValue_mono (h : SettledInv p s) (own : Own p s) (prov : Prov p s) (hnt : s.status.terminal = false)
    (f : Facts p s t)
    (hnew : ∀ r ∈ t.results, r ∉ s.results → ∀ w pl, t.workflow? p r.run = some w →
      w.placement? r.placement = some pl → ∀ e, pl.control ≠ .waitStream e) :
    ∀ r ∈ t.results, ∀ w pl i c, t.workflow? p r.run = some w → w.placement? r.placement = some pl →
      (∃ e, pl.control = .waitStream e) → w.shape? p r.placement = some (.stream i c) →
        r.value = listValue (deliveredValues (t.deliveriesOn r.run i)) := by
  intro r hr w pl i c hw hpl ⟨e, he⟩ hsh
  by_cases hrs : r ∈ s.results
  · rcases prov.results hnt r hrs with ⟨x, hx, hxr, hxp, -, -⟩ | ⟨-, -, -, j, hj, -, hjr, hjp, -⟩ |
      ⟨-, -, j, hj, -, hjr, hjp, -⟩ | ⟨j, hj, hjr, hjp, -⟩
    · obtain ⟨w0, pl0, hw0, -, -⟩ := h.closed x hx
      have hw0t := f.workflows _ _ hw0
      rw [hxr, hw] at hw0t
      have hww : w0 = w := (Option.some.inj hw0t).symm
      subst hww
      have hws : s.workflow? p r.run = some w0 := hxr ▸ hw0
      have hval := h.waitValue r hrs w0 pl i c hws hpl ⟨e, he⟩ hsh
      obtain ⟨newd, hdel, hnewd⟩ := f.deliveries
      rw [hval, deliveriesOn_eq_of_fits hdel fun d hd hdr =>
        (hnewd d hd x hx (hdr.trans hxr.symm) w0 hw0 i c).1 (by rw [hxp]; exact hsh)]
    all_goals
      exact absurd he (not_wait_of_inv own f.workflows hj (hjr ▸ hw) (hjp ▸ hpl) e)
  · exact absurd he (hnew r hr hrs w pl hw hpl e)

theorem of_facts (h : SettledInv p s) (own : Own p s) (prov : Prov p s) (hnt : s.status.terminal = false)
    (wk : s.WellKeyed) (f : Facts p s t)
    (hsettled : t.settled = s.settled)
    (hnew : ∀ r ∈ t.results, r ∉ s.results → ∀ w pl, t.workflow? p r.run = some w →
      w.placement? r.placement = some pl → ∀ e, pl.control ≠ .waitStream e) :
    SettledInv p t where
  ended := by rw [hsettled]; exact h.ended_mono wk f
  closed := by rw [hsettled]; exact h.closed_mono f
  noEligible := by rw [hsettled]; exact h.noEligible_mono wk f
  waitValue := h.waitValue_mono own prov hnt f hnew

end SettledInv

namespace Facts

theorem refl : Facts p s s where
  workflows := KeepsWorkflows.refl
  settled := List.prefix_refl _
  results := ⟨[], by simp, by simp⟩
  deliveries := ⟨[], by simp, by simp⟩
  invocations := fun j hj => ⟨j, hj, rfl⟩
  invNew := fun i hi => Or.inl ⟨i, hi, rfl, fun _ => rfl⟩
  callsNew := fun _ _ _ _ c hc hco hct => ⟨c, hc, hco, hct, id⟩
  runsNew := fun _ _ _ _ r hr hro hrt => ⟨r, hr, hro, hrt, id⟩
  execsNew := fun _ _ _ _ e he hid => ⟨e, he, hid, id⟩

/-- A step's facts are the facts of its parts. --/
theorem trans (f1 : Facts p s u) (f2 : Facts p u t) : Facts p s t := by
  -- An invocation of a settled placement keeps its key.
  have keepInv : ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement,
      x ∈ u.settled ∧ ∃ i' ∈ u.invocationsOf x.run x.placement, i'.id = i.id := by
    intro x hx i hi
    rw [mem_invocationsOf] at hi
    obtain ⟨i', hi', hk⟩ := f1.invocations i hi.1
    simp only [invKey_eq] at hk
    exact ⟨f1.settled.subset hx, i', mem_invocationsOf.mpr ⟨hi', hk.2.1.trans hi.2.1, hk.2.2.1.trans hi.2.2⟩, hk.1⟩
  have noneBack : ∀ path name, u.settled? path name = none → s.settled? path name = none := by
    intro path name h
    cases hs : s.settled? path name with
    | none => rfl
    | some x => rw [settled?_of_prefix f1.settled hs] at h; cases h
  exact {
    workflows := f1.workflows.trans f2.workflows
    settled := f1.settled.trans f2.settled
    results := by
      obtain ⟨new1, h1, hn1⟩ := f1.results
      obtain ⟨new2, h2, hn2⟩ := f2.results
      refine ⟨new1 ++ new2, by rw [h2, h1, List.append_assoc], fun r hr => ?_⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact hn1 r hr
      · exact noneBack _ _ (hn2 r hr)
    deliveries := by
      obtain ⟨new1, h1, hn1⟩ := f1.deliveries
      obtain ⟨new2, h2, hn2⟩ := f2.deliveries
      refine ⟨new1 ++ new2, by rw [h2, h1, List.append_assoc], fun d hd => ?_⟩
      rcases List.mem_append.mp hd with hd | hd
      · exact hn1 d hd
      · intro x hx hdr w hw idx c
        obtain ⟨hs, hsg⟩ := hn2 d hd x (f1.settled.subset hx) hdr w (f1.workflows _ _ hw) idx c
        refine ⟨hs, fun hsh hdc hnil => ?_⟩
        -- A first delivery on this input in the first part would need an earlier one.
        apply hsg hsh hdc
        rw [deliveriesOn_append h1, hnil, List.nil_append, List.filter_eq_nil_iff]
        intro d1 hd1 hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        exact (hn1 d1 hd1 x hx hcond.1 w hw idx c).2 hsh hcond.2 hnil
    invocations := fun j hj => by
      obtain ⟨j', hj', hk⟩ := f1.invocations j hj
      obtain ⟨j'', hj'', hk'⟩ := f2.invocations j' hj'
      exact ⟨j'', hj'', hk'.trans hk⟩
    invNew := fun i' hi' => by
      rcases f2.invNew i' hi' with ⟨i, hi, hk, hfix⟩ | hnone
      · rcases f1.invNew i hi with ⟨i0, hi0, hk0, hfix0⟩ | hnone0
        · refine Or.inl ⟨i0, hi0, hk.trans hk0, fun hst => ?_⟩
          have := hfix0 hst
          subst this
          exact hfix hst
        · simp only [invKey_eq] at hk
          exact Or.inr (by rw [hk.2.1, hk.2.2.1]; exact hnone0)
      · exact Or.inr (noneBack _ _ hnone)
    callsNew := fun x hx i hi c' hc' hco hct => by
      obtain ⟨hxu, i', hi', hid⟩ := keepInv x hx i hi
      obtain ⟨c, hc, hco', hct', himp⟩ := f2.callsNew x hxu i' hi' c' hc' (hco.trans hid.symm) hct
      obtain ⟨c0, hc0, hco0, hct0, himp0⟩ := f1.callsNew x hx i hi c hc (hco'.trans hid) hct'
      exact ⟨c0, hc0, hco0, hct0, himp ∘ himp0⟩
    runsNew := fun x hx i hi r' hr' hro hrt => by
      obtain ⟨hxu, i', hi', hid⟩ := keepInv x hx i hi
      obtain ⟨r, hr, hro', hrt', himp⟩ := f2.runsNew x hxu i' hi' r' hr' (hro.trans (by rw [hid])) hrt
      obtain ⟨r0, hr0, hro0, hrt0, himp0⟩ := f1.runsNew x hx i hi r hr (hro'.trans (by rw [hid])) hrt'
      exact ⟨r0, hr0, hro0, hrt0, himp ∘ himp0⟩
    execsNew := fun x hx i hi e' he' hid' => by
      obtain ⟨hxu, i', hi', hid⟩ := keepInv x hx i hi
      obtain ⟨e, he, heid, himp⟩ := f2.execsNew x hxu i' hi' e' he' (hid'.trans hid.symm)
      obtain ⟨e0, he0, heid0, himp0⟩ := f1.execsNew x hx i hi e he (heid.trans hid)
      exact ⟨e0, he0, heid0, himp ∘ himp0⟩ }

theorem of_records (hr : t.runs = s.runs) (hi : t.invocations = s.invocations) (hc : t.calls = s.calls)
    (he : t.executions = s.executions) (hres : t.results = s.results) (hd : t.deliveries = s.deliveries)
    (hs : t.settled = s.settled) : Facts p s t where
  workflows := KeepsWorkflows.of_runs hr
  settled := by rw [hs]; exact List.prefix_refl _
  results := ⟨[], by rw [hres, List.append_nil], by simp⟩
  deliveries := ⟨[], by rw [hd, List.append_nil], by simp⟩
  invocations := fun j hj => ⟨j, by rw [hi]; exact hj, rfl⟩
  invNew := fun i hi' => Or.inl ⟨i, by rw [← hi]; exact hi', rfl, fun _ => rfl⟩
  callsNew := fun _ _ _ _ c hc' hco hct => ⟨c, by rw [← hc]; exact hc', hco, hct, id⟩
  runsNew := fun _ _ _ _ r hr' hro hrt => ⟨r, by rw [← hr]; exact hr', hro, hrt, id⟩
  execsNew := fun _ _ _ _ e he' hid => ⟨e, by rw [← he]; exact he', hid, id⟩

/-- A call that has not ended changes status. --/
theorem setCall {c c' : Call} (hc : c ∈ s.calls) (howner : c'.owner = c.owner) (htask : c'.task = c.task)
    (hne : c.status.ended = false) : Facts p s (s.setCall c') := by
  refine { refl (p := p) (s := s) with callsNew := fun x hx i hi c'' hc'' hco hct => ?_ }
  rcases mem_replace hc'' with rfl | ⟨hc'', -⟩
  · exact ⟨c, hc, howner ▸ hco, htask ▸ hct, fun h => by rw [hne] at h; cases h⟩
  · exact ⟨c'', hc'', hco, hct, id⟩

/-- An active invocation changes status. --/
theorem setInvocation (hn : (s.invocations.map (·.id)).Nodup) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hk : invKey i' = invKey i) (hact : i.status = .active) : Facts p s (s.setInvocation i') := by
  simp only [invKey_eq] at hk
  refine { refl (p := p) (s := s) with
    invocations := fun j hj => ?_
    invNew := fun j' hj' => ?_ }
  · by_cases hji : j.id = i.id
    · have := eq_of_nodup_map hn hj hi hji
      subst this
      exact ⟨i', mem_replace_self hj hk.1.symm, invKey_eq.mpr hk⟩
    · exact ⟨j, mem_replace_of_mem hj (by rw [hk.1]; exact hji), rfl⟩
  · rcases mem_replace hj' with rfl | ⟨hj', -⟩
    · exact Or.inl ⟨i, hi, invKey_eq.mpr hk, fun h => absurd hact h⟩
    · exact Or.inl ⟨j', hj', rfl, fun _ => rfl⟩

theorem setTask {e : Execution} {ts : TaskState} (he : e ∈ s.executions) : Facts p s (s.setTask e ts) := by
  refine { refl (p := p) (s := s) with execsNew := fun x hx i hi e' he' hid => ?_ }
  rcases mem_replace he' with rfl | ⟨he', -⟩
  · exact ⟨e, he, hid, id⟩
  · exact ⟨e', he', hid, id⟩

theorem setExecution {e e' : Execution} (he : e ∈ s.executions) (hid : e'.id = e.id)
    (hc : e.complete = true → e'.complete = true) : Facts p s (s.setExecution e') := by
  refine { refl (p := p) (s := s) with execsNew := fun x hx i hi e'' he'' hid' => ?_ }
  rcases mem_replace he'' with rfl | ⟨he'', -⟩
  · exact ⟨e, he, hid.symm.trans hid', hc⟩
  · exact ⟨e'', he'', hid', id⟩

theorem setRun {r r' : Run} (hr : s.run? r'.path = some r) (hk : runKey r' = runKey r)
    (hc : r.complete = true → r'.complete = true) : Facts p s (s.setRun r') := by
  simp only [runKey_eq] at hk
  refine { refl (p := p) (s := s) with
    workflows := KeepsWorkflows.setRun hr hk.2.1
    runsNew := fun x hx i hi r'' hr'' hro hrt => ?_ }
  rcases mem_replace hr'' with rfl | ⟨hr'', -⟩
  · exact ⟨r, (run?_eq_some hr).1, hk.2.2.1 ▸ hro, hk.2.2.2 ▸ hrt, hc⟩
  · exact ⟨r'', hr'', hro, hrt, id⟩

theorem stop : Facts p s s.stop := by
  refine { refl (p := p) (s := s) with
    callsNew := fun x hx i hi c' hc' hco hct => ?_
    execsNew := fun x hx i hi e' he' hid => ?_ }
  · obtain ⟨c, hc, rfl⟩ := mem_stop_calls.mp hc'
    refine ⟨c, hc, by simpa using hco, by simpa using hct, fun hend => ?_⟩
    rw [stopCall_status]
    split
    · rename_i hrun
      rcases hrun with hrun | hrun <;> rw [hrun] at hend <;> cases hend
    · exact hend
  · obtain ⟨e, he, rfl⟩ := mem_stop_executions.mp he'
    exact ⟨e, he, hid, id⟩

/-- The conclusion after a stop changes only invocations and tasks that have not ended. --/
theorem endUnfinished : Facts p s s.endUnfinished := by
  refine { refl (p := p) (s := s) with
    invocations := fun j hj => ⟨endInvocation j, mem_endUnfinished_invocations.mpr ⟨j, hj, rfl⟩, by simp [invKey]⟩
    invNew := fun j' hj' => ?_
    execsNew := fun x hx i hi e' he' hid => ?_ }
  · obtain ⟨j, hj, rfl⟩ := mem_endUnfinished_invocations.mp hj'
    exact Or.inl ⟨j, hj, by simp [invKey], fun h => endInvocation_of_ne h⟩
  · obtain ⟨e, he, rfl⟩ := mem_endUnfinished_executions.mp he'
    exact ⟨e, he, hid, id⟩

theorem fail {f : Failure} {policy : Policy} : Facts p s (s.fail f policy) := by
  have h' : Facts p s { s with failures := s.failures ++ [f] } := of_records rfl rfl rfl rfl rfl rfl rfl
  cases policy
  · exact h'.trans stop
  · exact h'

theorem appendResult {r : Result} (hr : s.settled? r.run r.placement = none) :
    Facts p s { s with results := s.results ++ [r] } := by
  refine { refl (p := p) (s := s) with results := ⟨[r], rfl, fun r' hr' => ?_⟩ }
  rw [List.mem_singleton.mp hr']
  exact hr

theorem appendDelivery {d : Delivery} (hd : DeliveryFits p s d) :
    Facts p s { s with deliveries := s.deliveries ++ [d] } := by
  refine { refl (p := p) (s := s) with deliveries := ⟨[d], rfl, fun d' hd' => ?_⟩ }
  rw [List.mem_singleton.mp hd']
  exact hd

theorem appendInvocation {i : Invocation} (hnew : s.settled? i.run i.placement = none) :
    Facts p s { s with invocations := s.invocations ++ [i] } := by
  refine { refl (p := p) (s := s) with
    invocations := fun j hj => ⟨j, List.mem_append_left _ hj, rfl⟩
    invNew := fun j hj => ?_ }
  rcases List.mem_append.mp hj with hj | hj
  · exact Or.inl ⟨j, hj, rfl, fun _ => rfl⟩
  · rw [List.mem_singleton.mp hj]
    exact Or.inr hnew

theorem appendCall {c : Call}
    (hown : c.task = none → ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement, c.owner ≠ i.id) :
    Facts p s { s with calls := s.calls ++ [c] } := by
  refine { refl (p := p) (s := s) with callsNew := fun x hx i hi c' hc' hco hct => ?_ }
  rcases List.mem_append.mp hc' with hc' | hc'
  · exact ⟨c', hc', hco, hct, id⟩
  · rw [List.mem_singleton.mp hc'] at hco hct
    exact absurd hco (hown hct x hx i hi)

theorem appendRun {r : Run}
    (hown : r.task = none → ∀ o, r.owner = some o → ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement,
      o ≠ i.id) :
    Facts p s { s with runs := s.runs ++ [r] } := by
  refine { refl (p := p) (s := s) with
    workflows := KeepsWorkflows.of_append rfl
    runsNew := fun x hx i hi r' hr' hro hrt => ?_ }
  rcases List.mem_append.mp hr' with hr' | hr'
  · exact ⟨r', hr', hro, hrt, id⟩
  · rw [List.mem_singleton.mp hr'] at hro hrt
    exact absurd rfl (hown hrt i.id hro x hx i hi)

theorem appendExecution {e : Execution}
    (hown : ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement, e.id ≠ i.id) :
    Facts p s { s with executions := s.executions ++ [e] } := by
  refine { refl (p := p) (s := s) with execsNew := fun x hx i hi e' he' hid => ?_ }
  rcases List.mem_append.mp he' with he' | he'
  · exact ⟨e', he', hid, id⟩
  · rw [List.mem_singleton.mp he'] at hid
    exact absurd hid (hown x hx i hi)

end Facts

/-- A fresh delivery of an eligible result fits the settled placements: an ended Stream input has
    delivered all its results, and a Single input without deliveries has no eligible result. --/
theorem SettledInv.deliveryFits (h : SettledInv p s) {d : Delivery}
    (hfresh : s.delivery? d.run d.connection d.source = none)
    (helig : ∃ w, s.workflow? p d.run = some w ∧ ∃ c, w.connections[d.connection]? = some c ∧
      ∃ r ∈ s.results, r.id = d.source ∧ r.run = d.run ∧ r.placement = c.source ∧
        (c.arm.isNone || r.arm == c.arm) = true) :
    DeliveryFits p s d := by
  obtain ⟨w', hw', c', hc', r, hr, hrid, hrrun, hrpl, harm⟩ := helig
  intro x hx hdr w hw idx c
  rw [hdr, hw] at hw'
  cases hw'
  obtain ⟨w0, pl0, hw0, -, hcl⟩ := h.closed x hx
  rw [hw] at hw0
  cases hw0
  unfold Closed at hcl
  constructor
  · intro hsh hdc
    rw [hsh] at hcl
    obtain ⟨-, hall, -⟩ := hcl
    have hcc := (shape?_connection (Or.inr hsh)).1
    have hcc' : c = c' := by rw [hdc, hcc] at hc'; exact Option.some.inj hc'
    subst hcc'
    have := hall r (mem_eligible.mpr ⟨hr, hrrun.trans hdr, hrpl, harm⟩)
    rw [hrid, ← hdr, ← hdc, hfresh] at this
    cases this
  · intro hsh hdc hnil
    rw [hsh] at hcl
    obtain ⟨-, hnilc⟩ := hcl
    obtain ⟨y, hy, hyo⟩ := hnilc hnil
    have hcc := (shape?_connection (Or.inl hsh)).1
    have hcc' : c = c' := by rw [hdc, hcc] at hc'; exact Option.some.inj hc'
    subst hcc'
    have hyx := settled?_eq_some hy
    have := h.noEligible y hyx.1 c.arm hyo r
      (mem_resultsOf.mpr ⟨hr, hrrun.trans (hdr.trans hyx.2.1.symm), hrpl.trans hyx.2.2.symm⟩)
    rw [harm] at this
    cases this

theorem armOutcome_nil {x : Settled} (h : x.arms = []) (arm : Option String) : State.armOutcome x arm = x.outcome := by
  cases arm with
  | none => rfl
  | some a => simp [State.armOutcome, h]

/-- The origin of a result of a placement that has not settled: an invocation of the placement,
    through a call, an execution or a sub-workflow run. --/
theorem resultOrigin (prov : Prov p s) (hnt : s.status.terminal = false) (wk : s.WellKeyed) {r : Result}
    (hr : r ∈ s.results)
    (hnone : s.settled? r.run r.placement = none) :
    ∃ j ∈ s.invocations, j.run = r.run ∧ j.placement = r.placement ∧
      ((∃ c ∈ s.calls, c.task = none ∧ c.owner = j.id ∧
          ((c.stream = false ∧ j.status = .succeeded ∧ r.arm = j.arm) ∨ (c.stream = true ∧ j.status ≠ .skipped))) ∨
       ((∃ e ∈ s.executions, e.id = j.id) ∧ (j.status = .succeeded ∨ j.status = .active)) ∨
       (j.status = .succeeded ∧ ∃ pl wf out, placementAt p s j.run j.placement = some pl ∧
          pl.control = .call (.workflow wf out))) := by
  rcases prov.results hnt r hr with ⟨x, hx, hxr, hxp, -, -⟩ | ⟨c, hc, htc, j, hj, hjo, hjr, hjp, hst⟩ |
    ⟨e, he, j, hj, hje, hjr, hjp, hst⟩ | ⟨j, hj, hjr, hjp, hst, rest⟩
  · rw [← hxr, ← hxp, wk.settled?_of_mem hx] at hnone
    cases hnone
  · exact ⟨j, hj, hjr, hjp, Or.inl ⟨c, hc, htc, hjo.symm, hst⟩⟩
  · refine ⟨j, hj, hjr, hjp, Or.inr (Or.inl ⟨⟨e, he, hje.symm⟩, ?_⟩)⟩
    rcases hst with hst | ⟨hst, -⟩
    · exact Or.inl hst
    · exact Or.inr hst
  · exact ⟨j, hj, hjr, hjp, Or.inr (Or.inr ⟨hst, rest⟩)⟩

/-- Invocations of a placement differ in their triggers. --/
theorem inv_unique (own : Own p s) (wk : s.WellKeyed) {path : Path} {name : String} {j j' : Invocation}
    (hj : j ∈ s.invocationsOf path name) (hj' : j' ∈ s.invocationsOf path name) (ht : j.trigger = j'.trigger) :
    j = j' := by
  rw [mem_invocationsOf] at hj hj'
  apply wk.invocation_eq_of_id hj.1 hj'.1
  rw [own.invId j hj.1, own.invId j' hj'.1, hj.2.1, hj.2.2, hj'.2.1, hj'.2.2, ht]

/-- The trigger of an invocation, by the shape of its placement. --/
theorem inv_trigger (prov : Prov p s) {path : Path} {name : String} {w : Workflow} (hw : s.workflow? p path = some w)
    {j : Invocation} (hj : j ∈ s.invocationsOf path name) : TriggerOk p s w j := by
  rw [mem_invocationsOf] at hj
  obtain ⟨w', hw', ht⟩ := prov.invTrigger j hj.1
  rw [hj.2.1, hw] at hw'
  cases hw'
  exact ht

/-- A placement whose Stream input ended without a value on its arm has no invocation. --/
theorem no_inv_of_skipped_input (h : SettledInv p s) (prov : Prov p s) {path : Path} {name : String}
    {w : Workflow} (hw : s.workflow? p path = some w) {idx : Nat} {c : Connection}
    (hsh : w.shape? p name = some (.stream idx c)) {o : Outcome} (hend : s.streamEnd? path idx c = some o)
    (hsk : o ≠ .normal) : ∀ j ∈ s.invocationsOf path name, False := by
  intro j hj
  have ht := inv_trigger prov hw hj
  rw [mem_invocationsOf] at hj
  unfold TriggerOk at ht
  rw [hj.2.2, hsh] at ht
  obtain ⟨src, d, -, hd, -⟩ := ht
  obtain ⟨y, hy, rfl, -⟩ := streamEnd?_eq_some hend
  have hd' := delivery?_eq_some hd
  obtain ⟨w', hw', c', hc', r, hr, hrid, hrrun, hrpl, harm⟩ := prov.deliveries d hd'.1
  rw [hd'.2.1, hj.2.1, hw] at hw'
  cases hw'
  have hcc := (shape?_connection (Or.inr hsh)).1
  rw [hd'.2.2.1, hcc] at hc'
  cases hc'
  have hyx := settled?_eq_some hy
  have := h.noEligible y hyx.1 c.arm hsk r
    (mem_resultsOf.mpr ⟨hr, hrrun.trans (hd'.2.1.trans (hj.2.1.trans hyx.2.1.symm)), hrpl.trans hyx.2.2.symm⟩)
  rw [harm] at this
  cases this

/-- The placement of an execution's invocation is a concurrency. --/
theorem ctrl_of_exec (own : Own p s) (wk : s.WellKeyed) {e : Execution} (he : e ∈ s.executions) {j : Invocation}
    (hj : j ∈ s.invocations) (hid : e.id = j.id) :
    ∃ pl cc, placementAt p s j.run j.placement = some pl ∧ pl.control = .concurrency cc := by
  obtain ⟨i3, hi3, hi3e, hi3r, hi3p, pl3, cc3, hpl3, hcc3, -⟩ := own.execOwner e he
  have := wk.invocation_eq_of_id hi3 hj (hi3e.trans hid)
  subst this
  exact ⟨pl3, cc3, by rw [hi3r, hi3p]; exact hpl3, hcc3⟩

/-- The placement of a call's invocation is a function call, whose contract gives the Stream flag,
    or a branch, whose judge call has no Stream contract. --/
theorem ctrl_of_call (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) (htc : c.task = none)
    {j : Invocation} (hj : j ∈ s.invocations) (hco : c.owner = j.id) :
    ∃ pl, placementAt p s j.run j.placement = some pl ∧
      ((∃ f decl, pl.control = .call (.function f) ∧ p.function? f = some decl ∧
          c.stream = (decl.output.kind == .stream)) ∨
       (∃ jd arms, pl.control = .branch jd arms ∧ c.stream = false)) := by
  obtain ⟨-, i3, hi3, hi3o, pl3, hpl3, hctrl3⟩ := own.callNone c hc htc
  exact ⟨pl3, by rw [← Own.placementAt_of_id wk hi3 hj (hi3o.trans hco)]; exact hpl3, hctrl3⟩

/-- A new settlement has no result on an arm it settles without a value (§7.3, §9, §10.3). --/
theorem settle_noEligible (h : SettledInv p s) (prov : Prov p s) (hnt : s.status.terminal = false) (own : Own p s)
    (wk : s.WellKeyed)
    {path : Path} {name : String} {w : Workflow} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Option Result}
    (hwf : s.workflow? p path = some w) (hpl : w.placement? name = some pl)
    (hfresh : s.settled? path name = none) (hshape : w.shape? p name = some shape)
    (hkind : w.outputKind? p name = some kind) (hout : s.settleOutcome path pl shape kind = some (x, res)) :
    ∀ arm, State.armOutcome x arm ≠ .normal → ∀ r ∈ s.resultsOf path name, (arm.isNone || r.arm == arm) = false := by
  intro arm harm r hr'
  have hpln : pl.name = name := (Workflow.placement?_eq_some hpl).2
  obtain ⟨hall, -, -, -⟩ := settleOutcome_some hout
  rw [hpln] at hall
  have hended : ∀ j ∈ s.invocationsOf path name, j.status ≠ .active := fun j hj =>
    (invocationEnded_iff.mp (List.all_eq_true.mp hall j hj)).1
  rw [mem_resultsOf] at hr'
  obtain ⟨hrm, hrr, hrp⟩ := hr'
  obtain ⟨j, hj, hjr, hjp, horig⟩ := resultOrigin prov hnt wk hrm (by rw [hrr, hrp]; exact hfresh)
  have hjOf : j ∈ s.invocationsOf path name := mem_invocationsOf.mpr ⟨hj, hjr.trans hrr, hjp.trans hrp⟩
  have hjact := hended j hjOf
  have hpa : placementAt p s j.run j.placement = some pl := by rw [hjr, hjp, hrr, hrp, placementAt_eq hwf, hpl]
  have hjt := inv_trigger prov hwf hjOf
  unfold TriggerOk at hjt
  rw [hjp, hrp, hshape] at hjt
  -- A result of an invoked placement comes through its invocation, never a waitStream's or a Merge's.
  have invoked : invocable pl.control = true := by
    obtain ⟨w', pl', hw', hpl', hinv⟩ := own.invPlaced j hj
    rw [hjr, hrr, hwf] at hw'
    cases hw'
    rw [hjp, hrp, hpl] at hpl'
    cases hpl'
    exact hinv
  -- A call or a concurrency settles without a value only when its invocations cannot have `r`.
  have callCase : ((∃ b, pl.control = .call b) ∨ (∃ cc, pl.control = .concurrency cc)) →
      (arm.isNone || r.arm == arm) = false := by
    intro hcc
    exfalso
    obtain ⟨-, -, -, harms, hcases⟩ := settleOutcome_call hout hcc
    rw [armOutcome_nil harms] at harm
    rw [hpln] at hcases
    -- The invocation of `r` succeeded, or it is a Stream function that was not skipped.
    have hjok : j.status = .succeeded ∨ (j.status ≠ .skipped ∧ ∃ f decl, pl.control = .call (.function f) ∧
        p.function? f = some decl ∧ decl.output.kind = .stream) := by
      rcases horig with ⟨c, hcm, htc, hco, hst⟩ | ⟨-, hst⟩ | ⟨hst, -⟩
      · rcases hst with ⟨-, hs, -⟩ | ⟨hstr, hns⟩
        · exact Or.inl hs
        · obtain ⟨pl3, hpl3, hctrl3⟩ := ctrl_of_call own wk hcm htc hj hco
          rw [hpa] at hpl3
          cases hpl3
          rcases hctrl3 with ⟨f, decl, hf, hdecl, hs3⟩ | ⟨_, _, -, hs3⟩
          · refine Or.inr ⟨hns, f, decl, hf, hdecl, ?_⟩
            have : (decl.output.kind == .stream) = true := hs3.symm.trans hstr
            simpa using this
          · rw [hstr] at hs3; cases hs3
      · rcases hst with hs | hs
        · exact Or.inl hs
        · exact absurd hs hjact
      · exact Or.inl hst
    have fromInv : ∀ inv ∈ s.invocationsOf path name, inv.trigger = j.trigger →
        x.outcome = State.invocationOutcome kind inv.status → False := by
      intro inv hinv htr hxo
      have := inv_unique own wk hinv hjOf htr
      subst this
      rw [hxo] at harm
      rcases invocationOutcome_ne_normal harm with hsk | ⟨hk, hns⟩
      · rcases hjok with hs | ⟨hns', -⟩
        · rw [hs] at hsk; cases hsk
        · exact hns' hsk
      · rcases hjok with hs | ⟨-, f, decl, hf, hdecl, hstream⟩
        · exact hns hs
        · rw [hk] at hkind
          obtain ⟨decl', hdecl', hsingle⟩ := outputKind?_function hkind hpl hf
          rw [hdecl] at hdecl'
          cases hdecl'
          rw [hstream] at hsingle
          cases hsingle
    rcases hcases with ⟨hsh, inv, hinv, hit, hxo⟩ | ⟨i, c, rfl, -, ⟨src, v, hres, inv, hinv, hit, hxo⟩ | hnov⟩ |
      ⟨i, c, ended, rfl, hend, -, hsk | hallsk | hnorm⟩
    · have hjtn : j.trigger = none := by rcases hsh with rfl | rfl <;> exact hjt
      exact fromInv inv hinv (hit.trans hjtn.symm) hxo
    · obtain ⟨src', v', hjt', hres'⟩ := hjt
      rw [hjr, hrr, hres] at hres'
      cases hres'
      exact fromInv inv hinv (hit.trans hjt'.symm) hxo
    · obtain ⟨src', v', -, hres'⟩ := hjt
      rw [hjr, hrr] at hres'
      exact hnov src' v' hres'
    · exact no_inv_of_skipped_input h prov hwf hshape hend (by rw [hsk]; simp) j hjOf
    · have hjs := hallsk j hjOf
      rcases hjok with hs | ⟨hns, -⟩
      · rw [hs] at hjs; cases hjs
      · exact hns hjs
    · exact harm hnorm
  cases hc : pl.control with
  | waitStream e => rw [hc] at invoked; cases invoked
  | merge e => rw [hc] at invoked; cases invoked
  | branch jd arms =>
    -- A branch result comes through the judge call of a succeeded invocation, on its arm.
    have hsucc : j.status = .succeeded ∧ r.arm = j.arm := by
      rcases horig with ⟨c, hcm, htc, hco, hst⟩ | ⟨⟨e, he, hei⟩, -⟩ | ⟨-, pl', wf, out, hpl', hctrl⟩
      · obtain ⟨pl3, hpl3, hctrl3⟩ := ctrl_of_call own wk hcm htc hj hco
        rw [hpa] at hpl3
        cases hpl3
        rcases hctrl3 with ⟨_, _, h3, -⟩ | ⟨_, _, -, hs3⟩
        · rw [hc] at h3; cases h3
        · rcases hst with ⟨-, hs, ha⟩ | ⟨hs', -⟩
          · exact ⟨hs, ha⟩
          · rw [hs3] at hs'; cases hs'
      · obtain ⟨pl3, cc3, hpl3, hcc3⟩ := ctrl_of_exec own wk he hj hei
        rw [hpa] at hpl3
        cases hpl3
        rw [hc] at hcc3
        cases hcc3
      · rw [hpa] at hpl'
        cases hpl'
        rw [hc] at hctrl
        cases hctrl
    obtain ⟨-, -, -, hcases⟩ := settleOutcome_branch hout hc
    rw [hpln] at hcases
    -- The settled invocation is `j` whenever there is one.
    have byInv : ∀ inv ∈ s.invocationsOf path name, inv.trigger = j.trigger → ArmsBy x inv →
        (arm.isNone || r.arm == arm) = false := by
      intro inv hinv htr harms
      have := inv_unique own wk hinv hjOf htr
      subst this
      rcases harms arm harm with hns | ⟨a, rfl, hna⟩
      · exact absurd hsucc.1 hns
      · simp only [Option.isNone_some, Bool.false_or, beq_eq_false_iff_ne, ne_eq]
        rw [hsucc.2]
        exact hna
    rcases hcases with ⟨rfl, inv, hinv, hit, harms⟩ | ⟨i, c, rfl, -, ⟨src, v, hres, inv, hinv, hit, harms⟩ | hnov⟩ |
      ⟨i, c, ended, rfl, hend, -, hsk | hchosen⟩
    · exact byInv inv hinv (hit.trans hjt.symm) harms
    · obtain ⟨src', v', hjt', hres'⟩ := hjt
      rw [hjr, hrr, hres] at hres'
      cases hres'
      exact byInv inv hinv (hit.trans hjt'.symm) harms
    · obtain ⟨src', v', -, hres'⟩ := hjt
      rw [hjr, hrr] at hres'
      exact absurd hres' (hnov src' v')
    · exact (no_inv_of_skipped_input h prov hwf hshape hend (by rw [hsk]; simp) j hjOf).elim
    · obtain ⟨a, rfl, hno⟩ := hchosen arm harm
      simp only [Option.isNone_some, Bool.false_or, beq_eq_false_iff_ne, ne_eq]
      exact hno r (mem_resultsOf.mpr ⟨hrm, hrr, hrp⟩)
  | call b => exact callCase (Or.inl ⟨b, hc⟩)
  | concurrency cc => exact callCase (Or.inr ⟨cc, hc⟩)

/-- A new settlement closes its placement's input (§10.3). --/
theorem settle_closed {path : Path} {name : String} {w : Workflow} {pl : Placement}
    {shape : Workflow.Shape} {kind : Kind} {x : Settled} {res : Option Result}
    (hpl : w.placement? name = some pl) (hshape : w.shape? p name = some shape)
    (hout : s.settleOutcome path pl shape kind = some (x, res)) : Closed p s x w pl := by
  have hpln : pl.name = name := (Workflow.placement?_eq_some hpl).2
  obtain ⟨-, hxrun, hxpl, -⟩ := settleOutcome_some hout
  rw [hpln] at hxpl
  unfold Closed
  rw [hxpl, hxrun, hshape]
  by_cases hcall : (∃ b, pl.control = .call b) ∨ (∃ cc, pl.control = .concurrency cc)
  · obtain ⟨-, -, -, -, hcases⟩ := settleOutcome_call hout hcall
    rw [hpln] at hcases
    rcases hcases with ⟨hsh, inv, hinv, hit, -⟩ | ⟨i, c, rfl, hpend, hval⟩ | ⟨i, c, ended, rfl, hend, htrig, -⟩
    · rcases hsh with rfl | rfl
      · exact fun _ => ⟨inv, hinv, hit⟩
      · exact fun _ => ⟨inv, hinv, hit⟩
    · refine ⟨fun src v hv => ?_, fun hnil => resolveSingle_nil hpend hnil⟩
      rcases hval with ⟨src', v', hres, inv, hinv, hit, -⟩ | hnov
      · rw [hres] at hv
        cases hv
        exact ⟨inv, hinv, hit⟩
      · exact absurd hv (hnov src v)
    · obtain ⟨y, hy, -, hall⟩ := streamEnd?_eq_some hend
      exact ⟨by rw [hy]; rfl, hall, fun _ => htrig⟩
  · cases hc : pl.control with
    | call b => exact absurd (Or.inl ⟨b, hc⟩) hcall
    | concurrency cc => exact absurd (Or.inr ⟨cc, hc⟩) hcall
    | waitStream e =>
      obtain ⟨i, c, o, rfl, hend, -⟩ := settleOutcome_waitStream hout hc
      obtain ⟨y, hy, -, hall⟩ := streamEnd?_eq_some hend
      exact ⟨by rw [hy]; rfl, hall, fun hinv => by simp [invocable] at hinv⟩
    | merge e =>
      have := shape?_of_merge (p := p) hpl hc
      rw [hshape] at this
      cases this
      trivial
    | branch jd arms =>
      obtain ⟨-, -, -, hcases⟩ := settleOutcome_branch hout hc
      rw [hpln] at hcases
      rcases hcases with ⟨rfl, inv, hinv, hit, -⟩ | ⟨i, c, rfl, hpend, hval⟩ | ⟨i, c, ended, rfl, hend, htrig, -⟩
      · exact fun _ => ⟨inv, hinv, hit⟩
      · refine ⟨fun src v hv => ?_, fun hnil => resolveSingle_nil hpend hnil⟩
        rcases hval with ⟨src', v', hres, inv, hinv, hit, -⟩ | hnov
        · rw [hres] at hv
          cases hv
          exact ⟨inv, hinv, hit⟩
        · exact absurd hv (hnov src v)
      · obtain ⟨y, hy, -, hall⟩ := streamEnd?_eq_some hend
        exact ⟨by rw [hy]; rfl, hall, fun _ => htrig⟩

end Suimon.Settle
