import Suimon.Theorems.Round3.Conformance
import Suimon.Theorems.Round3.SettledValueSucc

namespace Suimon.Round3
open State

/-! ## [4] Round3/SettledValue.lean — task B2

The proof is an induction over the reachable states. A settlement keeps its result once it has one,
since results are never withdrawn and runs keep their workflows. At the `settle` step, a Single output
settles with a value on an arm only through its aggregate or through an invocation that succeeded on
that arm (`SettledAux.settleOutcome_normal`), and such an invocation already has its result
(`SettledAux.reachable_succResult`). Validation makes the arm of a connection a declared arm of its
branch, or no arm for any other source. -/

namespace SettledAux

/-- (N4) in the form the induction keeps: for the outcome (arm `none`) and for the arm of each
    connection out of the placement, a value read on that arm names a result of the state. -/
def ValueInv (p : Definition) (s : State) : Prop :=
  ∀ x ∈ s.settled, ∀ w, s.workflow? p x.run = some w → w.outputKind? p x.placement = some .single →
    ∀ a : Option String, (a = none ∨ ∃ (j : Nat) (c : Connection), w.connections[j]? = some c ∧
        c.source = x.placement ∧ c.arm = a) →
      armOutcome x a = .normal →
        ∃ r ∈ s.results, r.run = x.run ∧ r.placement = x.placement ∧ (a = none ∨ r.arm = a)

theorem ValueInv.step {p : Definition} {s t : State} (valid : p.validate = .ok ()) (h : ValueInv p s)
    (hr : Reachable p s) {op : Op} (hs : Suimon.step p s op = .ok t) : ValueInv p t := by
  have wk' := step_wellKeyed hr.wellKeyed hs
  have hk := Delivery.Inv.kept (Delivery.Reachable.inv hr) hs
  obtain ⟨-, -, -, sinv⟩ := Settle.reachable hr
  intro x hx w hw hkind a ha harm
  rcases Delivery.step_settled_back hs x hx with hx' | hnew
  · -- A settlement from before keeps its workflow and its result.
    obtain ⟨w₀, -, hw₀, -⟩ := sinv.closed x hx'
    have hw₀' := hk.workflow? wk' hw₀
    rw [hw] at hw₀'
    cases hw₀'
    obtain ⟨r, hr', h1, h2, h3⟩ := h x hx' w hw₀ hkind a ha harm
    exact ⟨r, hk.mem_results hr', h1, h2, h3⟩
  · -- The settlement this step recorded, computed on the state before it.
    obtain ⟨-, -, run, w', pl, shape, kind, res, hrun, -, hw', hpl, -, hshape, hkind', hout, -, hres, -⟩ := hnew
    have hws : s.workflow? p x.run = some w' := Settle.workflow?_of_run hrun hw'
    have hwt := hk.workflow? wk' hws
    rw [hw] at hwt
    cases hwt
    rw [hkind] at hkind'
    cases hkind'
    have hwm : w ∈ p.workflows := (Definition.workflow?_eq_some hw').1
    have hname : pl.name = x.placement := (Workflow.placement?_eq_some hpl).2
    -- By validation, the arm is `none` or a declared arm of the branch.
    have harm' : a = none ∨ ∃ j arms b, pl.control = .branch j arms ∧ a = some b ∧ b ∈ arms := by
      rcases ha with rfl | ⟨j, c, hc, hsrc, rfl⟩
      · exact Or.inl rfl
      · have hcv := ((Definition.validate_ok valid).workflows w hwm).connections c (List.mem_of_getElem? hc)
        rw [← hsrc] at hpl
        obtain ⟨hbr, hnb⟩ := connection_arm hcv hpl
        by_cases hb : ∃ j arms, pl.control = .branch j arms
        · obtain ⟨j', arms, hc'⟩ := hb
          obtain ⟨b, hb', hbm⟩ := hbr j' arms hc'
          exact Or.inr ⟨j', arms, b, hc', hb', hbm⟩
        · exact Or.inl (hnb fun j arms h' => hb ⟨j, arms, h'⟩)
    have hstream : ∀ j c, shape = .stream j c → ∃ e, pl.control = .waitStream e := by
      rintro j c rfl
      exact waitStream_of_stream hpl hshape hkind
    rcases settleOutcome_normal hout hstream harm' harm with ⟨r, rfl, h1, h2, -, h4⟩ |
      ⟨ctrl, inv, hinv, hsucc, harmI⟩
    · refine ⟨r, ?_, h1, h2.trans hname, Or.inl h4⟩
      rw [hres]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · -- The succeeded invocation produced its result before.
      obtain ⟨hinvm, hinvr, hinvp⟩ := Delivery.mem_invocationsOf.mp hinv
      have hplat : Settle.placementAt p s inv.run inv.placement = some pl := by
        rw [hinvr, hinvp, Settle.placementAt_eq hws, hname]
        exact hpl
      obtain ⟨r, hr', h1, h2, h3⟩ :=
        reachable_succResult hr inv hinvm hsucc pl hplat (singleBody_of_kind hpl hshape hkind ctrl)
      refine ⟨r, hk.mem_results hr', h1.trans hinvr, h2.trans (hinvp.trans hname), ?_⟩
      rcases harmI with h' | h'
      · exact Or.inl h'
      · exact Or.inr (h3.trans h')

theorem reachable_valueInv {p : Definition} {s : State} (valid : p.validate = .ok ()) (h : Reachable p s) :
    ValueInv p s := by
  induction h with
  | empty => intro x hx; cases hx
  | step op hr hs ih => exact ih.step valid hr hs

end SettledAux

section SettledValue
variable {p : Definition} {s : State}

/-- (N4) A Single placement settled normally has its result, and a connection whose arm settled
    normally carries one; the converse of Round 2 `SettledInv.noEligible`. Stated for the outcome and
    per connection: `armOutcome` falls back to the outcome for an arm the settlement does not list, so a
    statement over every `Option String` arm is false (reviewers' counterexample `cex_normal.lean`). -/
theorem settled_value (valid : p.validate = .ok ()) (h : Reachable p s) :
    ∀ x ∈ s.settled, ∀ w, s.workflow? p x.run = some w → w.outputKind? p x.placement = some .single →
      (x.outcome = .normal → s.resultsOf x.run x.placement ≠ []) ∧
      (∀ (j : Nat) c, w.connections[j]? = some c → c.source = x.placement → armOutcome x c.arm = .normal →
        s.eligible x.run c ≠ []) := by
  intro x hx w hw hk
  have key := SettledAux.reachable_valueInv valid h x hx w hw hk
  refine ⟨fun hn => ?_, fun j c hc hsrc harm => ?_⟩
  · obtain ⟨r, hr, hrun, hpl, -⟩ := key none (Or.inl rfl) hn
    exact List.ne_nil_of_mem (Delivery.mem_resultsOf.mpr ⟨hr, hrun, hpl⟩)
  · obtain ⟨r, hr, hrun, hpl, harm'⟩ := key c.arm (Or.inr ⟨j, c, hc, hsrc, rfl⟩) harm
    exact List.ne_nil_of_mem (Delivery.mem_eligible.mpr ⟨hr, hrun, hpl.trans hsrc.symm, harm'⟩)

end SettledValue

end Suimon.Round3
