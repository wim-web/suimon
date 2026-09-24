import Suimon.Theorems.Round3.Conformance

/-! Helpers for [24] Round3/CoversClose.lean — task F6: where a stored result comes from.

The identity of a result names the rule that created it (each kind of identity has its own tag). The
invariant `ResultOrigin` records, for each stored result, the record that justifies it together with
the facts the containment step needs: the call of an invocation; the normal settlement of a
waitStream or Merge; an execution with a Stream output; an execution with a List output whose
invocation succeeded; a succeeded sub-workflow invocation. The justifying records are never undone
(`Delivery.Kept`), and a succeeded invocation never changes again (`Delivery.frozen`). -/

namespace Suimon.Round3
open State

namespace CoversCloseAux

variable {p : Definition} {s t : State} {op : Op}

/-- Where a stored result comes from, read from its identity. -/
def ResultOrigin (p : Definition) (s : State) (r : Result) : Prop :=
  (∃ c ∈ s.calls, c.task = none ∧ ∃ k, r.id = Key.callResult c.id k) ∨
  (r.id = Key.aggregate r.run r.placement ∧
    (∃ w pl, s.workflow? p r.run = some w ∧ w.placement? r.placement = some pl ∧
      ∃ e, pl.control = .waitStream e ∨ pl.control = .merge e) ∧
    ∃ x ∈ s.settled, x.run = r.run ∧ x.placement = r.placement ∧ x.outcome = .normal) ∨
  (∃ e ∈ s.executions, e.run = r.run ∧ e.placement = r.placement ∧
    (∃ cc, s.concurrencyOf p e = .ok cc ∧ cc.output = .stream) ∧ ∃ n k, r.id = Key.taskOutput e.id n k) ∨
  (∃ e ∈ s.executions, e.run = r.run ∧ e.placement = r.placement ∧
    (∃ cc, s.concurrencyOf p e = .ok cc ∧ cc.output = .list) ∧
    (∃ i ∈ s.invocations, i.id = e.id ∧ i.status = .succeeded) ∧ r.id = Key.list e.id) ∨
  (∃ i ∈ s.invocations, i.run = r.run ∧ i.placement = r.placement ∧ i.status = .succeeded ∧
    (∃ pl wf out, Settle.placementAt p s i.run i.placement = some pl ∧ pl.control = .call (.workflow wf out)) ∧
    r.id = Key.returned i.id)

/-- The placement of a run's workflow stays in the next state. -/
theorem placementAt_kept (K : Delivery.Kept s t) (wk' : t.WellKeyed) {path : Path} {name : String}
    {pl : Placement} (h : Settle.placementAt p s path name = some pl) : Settle.placementAt p t path name = some pl := by
  unfold Settle.placementAt at h ⊢
  cases hw : s.workflow? p path with
  | none => rw [hw] at h; cases h
  | some w => rw [hw] at h; rw [K.workflow? wk' hw]; exact h

/-- The justification of a stored result survives a step. -/
theorem ResultOrigin.kept (inv : Delivery.Inv p s) (hs : step p s op = .ok t) {r : Result}
    (h : ResultOrigin p s r) : ResultOrigin p t r := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  -- A succeeded invocation is no longer active, so the step leaves it as it is.
  have succ : ∀ i ∈ s.invocations, i.status = .succeeded → i ∈ t.invocations := by
    intro i hi hsucc
    obtain ⟨i', hi', hid, -⟩ := K.invocation i hi
    have heq := Delivery.frozen inv hs hi (by rw [hsucc]; simp) hi' hid
    rw [← heq]
    exact hi'
  rcases h with ⟨c, hc, htask, k, hid⟩ | ⟨hid, ⟨w, pl, hw, hpl, hctrl⟩, x, hx, h1, h2, h3⟩ |
      ⟨e, he, h1, h2, ⟨cc, hcc, hout⟩, n, k, hid⟩ | ⟨e, he, h1, h2, ⟨cc, hcc, hout⟩, ⟨i, hi, hie, hst⟩, hid⟩ |
      ⟨i, hi, h1, h2, hst, ⟨pl, wf, out, hpl, hctrl⟩, hid⟩
  · obtain ⟨c', hc', a1, -, a3, -⟩ := K.call c hc
    exact Or.inl ⟨c', hc', a3.trans htask, k, by rw [a1]; exact hid⟩
  · exact Or.inr (Or.inl ⟨hid, ⟨w, pl, K.workflow? wk' hw, hpl, hctrl⟩, x, K.mem_settled hx, h1, h2, h3⟩)
  · obtain ⟨e', he', a1, a2, a3, -, -⟩ := K.execution e he
    exact Or.inr (Or.inr (Or.inl ⟨e', he', a2.trans h1, a3.trans h2,
      ⟨cc, K.concurrencyOf wk' a2 a3 hcc, hout⟩, n, k, by rw [a1]; exact hid⟩))
  · obtain ⟨e', he', a1, a2, a3, -, -⟩ := K.execution e he
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e', he', a2.trans h1, a3.trans h2,
      ⟨cc, K.concurrencyOf wk' a2 a3 hcc, hout⟩, ⟨i, succ i hi hst, hie.trans a1.symm, hst⟩,
      by rw [a1]; exact hid⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, succ i hi hst, h1, h2, hst,
      ⟨pl, wf, out, placementAt_kept K wk' hpl, hctrl⟩, hid⟩)))

/-- Every step keeps every stored result justified. -/
theorem step_resultOrigin (h : Reachable p s) (ih : ∀ r ∈ s.results, ResultOrigin p s r)
    (hs : step p s op = .ok t) : ∀ r ∈ t.results, ResultOrigin p t r := by
  have inv := Delivery.Reachable.inv h
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  intro r hr
  by_cases hold : r ∈ s.results
  · exact (ih r hold).kept inv hs
  have hp := step_producer hs hr hold
  -- A result accepted from a call of an invocation is identified by that call.
  have accepted : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
      c ∈ s.calls → s.accept c index value arm = .ok s' → t.results = s'.results → ResultOrigin p t r := by
    intro c index value arm s' hc ha ht
    rcases State.accept_eq_ok.mp ha with ⟨htask, i, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · rw [ht, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd hr hold
      · obtain ⟨c', hc', h1, -, h3, -⟩ := K.call c hc
        exact Or.inl ⟨c', hc', h3.trans htask, index, by rw [h1]⟩
    · exact absurd (ht ▸ hr) hold
  cases op
  case returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact accepted (call?_eq_some hc).1 hacc (by rw [(settleOwner_update hso).results, setCall_results])
  case judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact accepted (call?_eq_some hc).1 hacc (by rw [setInvocation_results, setCall_results])
  case yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact accepted (call?_eq_some hc).1 hacc (by rw [setCall_results])
  case taskOutput eid name index value =>
    obtain ⟨-, -, e, cc, _, r0, he, hcc, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨hout, -, rfl⟩ | ⟨-, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd (by simpa using hr) hold
      · obtain ⟨hem, heid⟩ := execution?_eq_some he
        exact Or.inr (Or.inr (Or.inl ⟨e, hem, rfl, rfl, ⟨cc, K.concurrencyOf wk' rfl rfl hcc, hout⟩, name, index,
          by rw [heid]⟩))
    · exact absurd (by simpa using hr) hold
  case settle path name =>
    obtain ⟨-, -, run, w, pl, _, _, x, _, hrun, -, hw, hpl, -, -, -, hout, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact absurd hr hold
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd hr hold
      · obtain ⟨hx, hrr, hrp, hctrl⟩ := Settle.settleOutcome_aggregate hout
        obtain ⟨-, -, -, hres⟩ := settleOutcome_some hout
        obtain ⟨-, hid, -⟩ := hres _ rfl
        have hname := (Workflow.placement?_eq_some hpl).2
        refine Or.inr (Or.inl ⟨by rw [hid, hrr, hrp], ⟨w, pl, ?_, by rw [hrp, hname]; exact hpl, hctrl⟩, x,
          by simp, by rw [hx, hrr], by rw [hx, hrp], by rw [hx]⟩)
        rw [hrr]
        exact Settle.workflow?_of_run hrun hw
  case closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, -, hcc, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨-, hout, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact absurd (by simpa using hr) hold
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd hr hold
      · obtain ⟨hem, heid⟩ := execution?_eq_some he
        obtain ⟨him, hiid⟩ := invocation?_eq_some hi
        have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := him
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨{ e with complete := true }, ?_, rfl, rfl,
          ⟨cc, K.concurrencyOf wk' rfl rfl hcc, hout⟩,
          ⟨{ i with status := .succeeded }, Delivery.mem_setInvocation_self hi' _ _, by simp [hiid, heid], rfl⟩,
          by simp [heid]⟩)))
        simp only [setInvocation_executions, setExecution_executions]
        exact List.mem_map.mpr ⟨e, hem, by simp⟩
    · exact absurd (by simpa using hr) hold
  case closeRun path =>
    obtain ⟨-, -, r0, _, output, _, owner, -, -, -, -, -, hout, -, howner, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨_, _, _, -, -, -, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact absurd hr hold
        · have him := (invocation?_eq_some hi).1
          have hi' : i ∈ (s.setRun { r0 with complete := true }).invocations := him
          -- The owner of a sub-workflow run is an invocation of a sub-workflow call.
          obtain ⟨owner', howner', hcase⟩ := State.designatedOutput_eq_ok.mp hout
          rw [howner] at howner'
          cases howner'
          rcases hcase with ⟨-, i₁, pl, wf, hi₁, hpl, hctrl⟩ | ⟨_, _, _, _, htask', -⟩
          · rw [hi] at hi₁
            cases hi₁
            obtain ⟨w', hw', hplw⟩ := State.placementOf_eq_ok.mp hpl
            refine Or.inr (Or.inr (Or.inr (Or.inr ⟨{ i with status := .succeeded },
              Delivery.mem_setInvocation_self hi' _ _, rfl, rfl, rfl, ⟨pl, wf, output, ?_, hctrl⟩, rfl⟩)))
            have hp' : Settle.placementAt p s i.run i.placement = some pl := by
              rw [Settle.placementAt_eq hw']
              exact hplw
            exact placementAt_kept K wk' hp'
          · rw [htask] at htask'
            cases htask'
      all_goals exact absurd (by simpa using hr) hold
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact absurd (by simpa using hr) hold
  all_goals exact False.elim hp

/-- Every stored result of a reachable state is justified by its identity. -/
theorem reachable_resultOrigin (h : Reachable p s) : ∀ r ∈ s.results, ResultOrigin p s r := by
  induction h with
  | empty => intro r hr; simp at hr
  | step op hr hs ih => exact step_resultOrigin hr ih hs

end CoversCloseAux

end Suimon.Round3
