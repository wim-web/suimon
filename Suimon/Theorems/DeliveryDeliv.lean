import Suimon.Theorems.DeliveryResults

/-! Delivery completeness: a settled placement received every result its input connections carry. -/

namespace Suimon.Delivery
open State

/-- A Single placement has at most one result in a run, and a settled placement received every
    eligible result on each input connection; unless its source settled, that connection has a
    delivery and a Single source. --/
structure Deliv (p : Definition) (s : State) : Prop where
  one : ∀ w path name, s.workflow? p path = some w → w.outputKind? p name = some .single →
    ∀ r ∈ s.results, ∀ r' ∈ s.results, r.run = path → r.placement = name → r'.run = path → r'.placement = name →
      r.id = r'.id
  delivered : ∀ x ∈ s.settled, ∀ w, s.workflow? p x.run = some w → ∀ j c, w.connections[j]? = some c →
    c.target = x.placement →
      (∀ r ∈ s.eligible x.run c, (s.delivery? x.run j r.id).isSome) ∧
      ((s.settled? x.run c.source).isSome ∨ (s.deliveriesOn x.run j ≠ [] ∧ w.outputKind? p c.source = some .single))

theorem Deliv.empty (p : Definition) : Deliv p {} :=
  ⟨(fun _ _ _ _ _ _ h => nomatch h), (fun _ h => nomatch h)⟩

section
variable {p : Definition} {s t : State} {op : Op}

/-- The run of a result exists. --/
theorem result_run (inv : Inv p s) {r : Result} (hr : r ∈ s.results) : ∃ w, s.workflow? p r.run = some w := by
  rcases inv.dyn.results r hr with ⟨i, hi, -, hir, -⟩ | ⟨-, -, x, hx, hxr, -⟩
  · obtain ⟨-, w, -, -, hw, -⟩ := inv.own.invocations i hi
    exact ⟨w, hir ▸ hw⟩
  · obtain ⟨w, -, -, hw, -⟩ := inv.sett.input x hx
    exact ⟨w, hxr ▸ hw⟩

theorem step_one (inv : Inv p s) (d : Deliv p s) (hs : step p s op = .ok t) :
    ∀ w path name, t.workflow? p path = some w → w.outputKind? p name = some .single →
      ∀ r ∈ t.results, ∀ r' ∈ t.results, r.run = path → r.placement = name → r'.run = path → r'.placement = name →
        r.id = r'.id := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  intro w path name hw hk r hr r' hr' hrr hrp hr'r hr'p
  by_cases h1 : r ∈ s.results
  · obtain ⟨w₀, hw₀⟩ := result_run inv h1
    rw [hrr] at hw₀
    rw [K.workflow? wk' hw₀] at hw; cases hw
    by_cases h2 : r' ∈ s.results
    · exact d.one w path name hw₀ hk r h1 r' h2 hrr hrp hr'r hr'p
    · exact (no_second_result inv hs hw₀ hk hr' h2 h1 hr'r hr'p hrr hrp).elim
  · by_cases h2 : r' ∈ s.results
    · obtain ⟨w₀, hw₀⟩ := result_run inv h2
      rw [hr'r] at hw₀
      rw [K.workflow? wk' hw₀] at hw; cases hw
      exact (no_second_result inv hs hw₀ hk hr h1 h2 hrr hrp hr'r hr'p).elim
    · rw [step_new_result_unique hs hr h1 hr' h2]

/-- A resolved Single connection delivered every result it carries: its source has at most one, the
    one on the connection; or the source settled without a value on the arm and has none (§6, §7.2). --/
theorem resolved_delivered (inv : Inv p s) (d : Deliv p s) {path : Path} {w : Workflow} {j : Nat} {c : Connection}
    (hw : s.workflow? p path = some w) (hc : w.connections[j]? = some c) (hk : w.outputKind? p c.source = some .single)
    (hne : s.resolveSingle path j c ≠ .pending) :
    (∀ r ∈ s.eligible path c, (s.delivery? path j r.id).isSome) ∧
      ((s.settled? path c.source).isSome ∨ (s.deliveriesOn path j ≠ [] ∧ w.outputKind? p c.source = some .single)) := by
  rcases hd : s.deliveriesOn path j with _ | ⟨dd, rest⟩
  · have hres : s.resolveSingle path j c = .skipped ∨ s.resolveSingle path j c = .failure := by
      cases hr' : s.resolveSingle path j c with
      | pending => exact absurd hr' hne
      | value src inp =>
        obtain ⟨d, rest, hd', -⟩ := resolveSingle_value_iff.mp hr'
        rw [hd] at hd'; cases hd'
      | transformFailed =>
        rw [resolveSingle_of_nil hd] at hr'
        split at hr'
        · cases hr'
        · split at hr' <;> cases hr'
      | skipped => exact Or.inl rfl
      | failure => exact Or.inr rfl
    obtain ⟨-, y, hy, hyo⟩ := resolveSingle_no_delivery hres
    refine ⟨fun r hr => ?_, Or.inl (by rw [hy]; rfl)⟩
    exfalso
    obtain ⟨hrm, hrr, hrp, harm⟩ := mem_eligible.mp hr
    obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
    have := inv.sett.none y hym w (hyr ▸ hw) (hyp ▸ hk) c.arm hyo r hrm (hyr ▸ hrr) (hyp ▸ hrp)
    rcases harm with h | h
    · exact this.1 h
    · exact this.2 h
  · have hdd : dd ∈ s.deliveriesOn path j := by rw [hd]; exact List.mem_cons_self
    obtain ⟨hddm, hddr, hddc⟩ := mem_deliveriesOn.mp hdd
    obtain ⟨w', c', r₀, hw', hc', hr₀, hr₀id, hr₀r, hr₀p, -⟩ := inv.own.deliveries dd hddm
    rw [hddr, hw] at hw'; cases hw'
    rw [hddc, hc] at hc'; cases hc'
    refine ⟨fun r hr => ?_, Or.inr ⟨by simp, hk⟩⟩
    obtain ⟨hrm, hrr, hrp, -⟩ := mem_eligible.mp hr
    have hid := d.one w path c.source hw hk r hrm r₀ hr₀ hrr hrp (hr₀r.trans hddr) hr₀p
    have hlook := inv.wk.delivery?_of_mem hddm
    rw [hddr, hddc, hr₀id.symm, ← hid] at hlook
    rw [hlook]; rfl

theorem deliveriesOn_ne_nil_kept {s t : State} (g : s.Grows t) {path : Path} {j : Nat}
    (h : s.deliveriesOn path j ≠ []) : t.deliveriesOn path j ≠ [] := by
  intro h'
  obtain ⟨rest, hrest⟩ := deliveriesOn_prefix g path j
  rw [h'] at hrest
  exact h (List.append_eq_nil_iff.mp hrest).1

theorem step_delivered (inv : Inv p s) (d : Deliv p s) (hs : step p s op = .ok t)
    (hone : ∀ w path name, t.workflow? p path = some w → w.outputKind? p name = some .single →
      ∀ r ∈ t.results, ∀ r' ∈ t.results, r.run = path → r.placement = name → r'.run = path → r'.placement = name →
        r.id = r'.id) :
    ∀ x ∈ t.settled, ∀ w, t.workflow? p x.run = some w → ∀ j c, w.connections[j]? = some c →
      c.target = x.placement →
        (∀ r ∈ t.eligible x.run c, (t.delivery? x.run j r.id).isSome) ∧
        ((t.settled? x.run c.source).isSome ∨ (t.deliveriesOn x.run j ≠ [] ∧ w.outputKind? p c.source = some .single)) := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  intro x hx w hw j c hc htgt
  rcases step_settled_back hs x hx with hx₀ | ⟨-, -, run, w', pl, shape, kind, res, hr', -, hw', hpl, hfresh, hsh,
      hkind, hout, -, htr, -, -, -, -, hdels, -, -⟩
  · -- A settlement from before: new results of its sources cannot arrive.
    obtain ⟨w₀, -, -, hw₀, -⟩ := inv.sett.input x hx₀
    rw [K.workflow? wk' hw₀] at hw; cases hw
    obtain ⟨hdel, hsrc⟩ := d.delivered x hx₀ w hw₀ j c hc htgt
    refine ⟨fun r hr => ?_, ?_⟩
    · obtain ⟨hrm, hrr, hrp, harm⟩ := mem_eligible.mp hr
      by_cases hold : r ∈ s.results
      · obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp (hdel r (mem_eligible.mpr ⟨hold, hrr, hrp, harm⟩))
        rw [K.delivery? hdv]; rfl
      · exfalso
        rcases hsrc with hset | ⟨hne, hk⟩
        · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hset
          obtain ⟨hym, hyr, hyp⟩ := settled?_eq_some hy
          exact hold (frozen_results inv hs hym r hrm (hyr ▸ hrr) (hyp ▸ hrp))
        · obtain ⟨dd, hdd⟩ := List.exists_mem_of_ne_nil _ hne
          obtain ⟨hddm, hddr, hddc⟩ := mem_deliveriesOn.mp hdd
          obtain ⟨w', c', r₀, hw', hc', hr₀, hr₀id, hr₀r, hr₀p, -⟩ := inv.own.deliveries dd hddm
          rw [hddr, hw₀] at hw'; cases hw'
          rw [hddc, hc] at hc'; cases hc'
          have hid := hone w x.run c.source (K.workflow? wk' hw₀) hk r hrm r₀ (K.mem_results hr₀) hrr hrp
            (hr₀r.trans hddr) hr₀p
          obtain rfl := wk'.result_eq_of_id hrm (K.mem_results hr₀) hid
          exact hold hr₀
    · rcases hsrc with hset | ⟨hne, hk⟩
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hset
        exact Or.inl (by rw [K.settled? hy]; rfl)
      · exact Or.inr ⟨deliveriesOn_ne_nil_kept K.grows hne, hk⟩
  · -- The settlement this step records.
    have hws : s.workflow? p x.run = some w' := workflow?_iff.mpr ⟨run, hr', hw'⟩
    rw [K.workflow? wk' hws] at hw; cases hw
    have hname := (Workflow.placement?_eq_some hpl).2
    have hdone := settleOutcome_input hout
    have hon : t.deliveriesOn x.run j = s.deliveriesOn x.run j := by simp only [deliveriesOn, hdels]
    have hlook : ∀ {src : ResultId}, (s.delivery? x.run j src).isSome → (t.delivery? x.run j src).isSome := by
      intro src h
      obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp h
      rw [K.delivery? hdv]; rfl
    have hin : (j, c) ∈ w.inputs x.placement := mem_inputs.mpr ⟨hc, htgt⟩
    -- An eligible result of a source other than this placement is from before.
    have old : c.source ≠ x.placement → ∀ r ∈ t.eligible x.run c, r ∈ s.eligible x.run c := by
      intro hne r hr
      obtain ⟨hrm, hrr, hrp, harm⟩ := mem_eligible.mp hr
      rw [htr, List.mem_append] at hrm
      rcases hrm with hrm | hrm
      · exact mem_eligible.mpr ⟨hrm, hrr, hrp, harm⟩
      · cases res with
        | none => cases hrm
        | some r' =>
          rw [Option.toList_some, List.mem_singleton] at hrm
          subst hrm
          obtain ⟨-, -, -, -, -, hrpl, -⟩ := settleOutcome_res hout
          exact absurd (hrp.symm.trans (hrpl.trans hname)) hne
    -- Transfer the facts found before the step.
    have transfer : c.source ≠ x.placement →
        ((∀ r ∈ s.eligible x.run c, (s.delivery? x.run j r.id).isSome) ∧
          ((s.settled? x.run c.source).isSome ∨ (s.deliveriesOn x.run j ≠ [] ∧ w.outputKind? p c.source = some .single))) →
        ((∀ r ∈ t.eligible x.run c, (t.delivery? x.run j r.id).isSome) ∧
          ((t.settled? x.run c.source).isSome ∨ (t.deliveriesOn x.run j ≠ [] ∧ w.outputKind? p c.source = some .single))) := by
      rintro hne ⟨hdel, hsrc⟩
      refine ⟨fun r hr => hlook (hdel r (old hne r hr)), ?_⟩
      rcases hsrc with hset | ⟨hne', hk⟩
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hset
        exact Or.inl (by rw [K.settled? hy]; rfl)
      · exact Or.inr ⟨by rw [hon]; exact hne', hk⟩
    -- A resolved source is not this placement when this placement has no result yet.
    have notSelf : ∀ (_ : ∀ e, pl.control = .merge e → True),
        ((s.settled? x.run c.source).isSome ∨ (s.deliveriesOn x.run j ≠ [] ∧ w.outputKind? p c.source = some .single)) →
        (¬ Invocable pl.control) → c.source ≠ x.placement := by
      intro _ hsrc hni heq
      rcases hsrc with hset | ⟨hne, -⟩
      · rw [heq, hfresh] at hset; cases hset
      · obtain ⟨dd, hdd⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨hddm, hddr, hddc⟩ := mem_deliveriesOn.mp hdd
        obtain ⟨w₂, c₂, r₀, hw₂, hc₂, hr₀, -, hr₀r, hr₀p, -⟩ := inv.own.deliveries dd hddm
        rw [hddr, hws] at hw₂; cases hw₂
        rw [hddc, hc] at hc₂; cases hc₂
        rcases inv.dyn.results r₀ hr₀ with ⟨i, hi, -, hir, hip, -⟩ | ⟨-, -, y, hy, hyr, hyp, -⟩
        · obtain ⟨-, w₃, pl₃, -, hw₃, hpl₃, hinvc, -⟩ := inv.own.invocations i hi
          rw [hir, hr₀r, hddr, hws] at hw₃; cases hw₃
          rw [hip, hr₀p, heq, hpl] at hpl₃; cases hpl₃
          exact hni hinvc
        · have := inv.wk.settled?_of_mem hy
          rw [hyr, hyp, hr₀r, hr₀p, hddr, heq, hfresh] at this
          cases this
    rcases shape?_eq hsh with ⟨pl', hpl', hcase⟩
    rw [hpl] at hpl'; cases hpl'
    rcases hcase with ⟨⟨e, hme⟩, rfl⟩ | ⟨hnm, hcase⟩
    · -- Merge: its inputs are Single, since it has a derived kind (§9.2).
      have hk : w.outputKind? p c.source = some .single :=
        merge_input_single hpl hme hkind (List.mem_filter.mpr ⟨List.mem_of_getElem? hc, by simp [htgt]⟩)
      have hres := resolved_delivered inv d hws hc hk (hdone (j, c) hin)
      exact transfer (notSelf (fun _ _ => trivial) hres.2 (by rw [hme]; exact id)) hres
    · rcases hcase with ⟨-, rfl⟩ | ⟨-, hnil, rfl⟩ | ⟨-, j', c', hone', ⟨hks, rfl⟩ | ⟨hks, rfl⟩⟩
      · -- An entry has no input connection.
        obtain ⟨-, -, -, hinc⟩ := outputKind?_shape hsh hkind hpl hnm
        have hmem : c ∈ w.incoming x.placement := List.mem_filter.mpr ⟨List.mem_of_getElem? hc, by simp [htgt]⟩
        rw [hinc rfl] at hmem
        cases hmem
      · rw [hnil] at hin; cases hin
      · rw [hone', List.mem_singleton, Prod.mk.injEq] at hin
        obtain ⟨rfl, rfl⟩ := hin
        have hres := resolved_delivered inv d hws hc hks hdone.1
        -- A Single input settles no aggregate, so no result is new.
        have hnone : res = none := by
          cases res with
          | none => rfl
          | some r =>
            obtain ⟨-, -, hctl, -⟩ := settleOutcome_res hout
            rcases hctl with ⟨_, _, _, -, h⟩ | ⟨_, _, -, h⟩ <;> cases h
        subst hnone
        obtain ⟨hdel, hsrc⟩ := hres
        refine ⟨fun r hr => ?_, ?_⟩
        · obtain ⟨hrm, hrr, hrp, harm⟩ := mem_eligible.mp hr
          rw [htr] at hrm
          simp only [Option.toList_none, List.append_nil] at hrm
          exact hlook (hdel r (mem_eligible.mpr ⟨hrm, hrr, hrp, harm⟩))
        · rcases hsrc with hset | ⟨hne', hk⟩
          · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hset
            exact Or.inl (by rw [K.settled? hy]; rfl)
          · exact Or.inr ⟨by rw [hon]; exact hne', hk⟩
      · rw [hone', List.mem_singleton, Prod.mk.injEq] at hin
        obtain ⟨rfl, rfl⟩ := hin
        obtain ⟨hset, hdel, -⟩ := hdone
        have hne : c.source ≠ x.placement := by
          intro heq
          rw [heq, hfresh] at hset
          cases hset
        exact transfer hne ⟨hdel, Or.inl hset⟩

theorem step_deliv (inv : Inv p s) (d : Deliv p s) (hs : step p s op = .ok t) : Deliv p t :=
  ⟨step_one inv d hs, step_delivered inv d hs (step_one inv d hs)⟩

end

theorem Reachable.deliv {p : Definition} {s : State} (h : Reachable p s) : Deliv p s := by
  induction h with
  | empty => exact Deliv.empty p
  | step op hr hs ih => exact step_deliv (Reachable.inv hr) ih hs

end Suimon.Delivery
