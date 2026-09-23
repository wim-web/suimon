import Suimon.Theorems.Round3.Conformance
import Suimon.Theorems.Round3.FrozenTasks

namespace Suimon.Round3
open State

/-! ## [15] Round3/Frozen.lean — task E3 -/

section Frozen
variable {p : Program} {s t : State}

-- `valid` is not used: the tasks of an execution with the same name are equal in every reachable state
-- (`Limit.Inv.coherent`), so no uniqueness of task names is needed.
set_option linter.unusedVariables false in
/-- Finished records never change: an invocation that is no longer active, an ended call or task, a
    completed execution with its task results, a transformed task result; and a settled placement gets no
    new invocation, result or input delivery (§10.2, §10.3). The last part rests on Round 2
    `Delivery.frozen_invocations`, `Delivery.frozen_results`, `Settle.SettledInv` and `Deliv.one`. -/
theorem step_frozen {op : Op} (valid : p.validate = .ok ()) (h : Reachable p s) (hs : step p s op = .ok t) :
    (∀ i ∈ s.invocations, i.status ≠ .active → i ∈ t.invocations) ∧
    (∀ c ∈ s.calls, c.status.ended = true → c ∈ t.calls) ∧
    (∀ e ∈ s.executions, e.complete = true → e ∈ t.executions) ∧
    (∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status.ended = true →
      ∃ e' ∈ t.executions, e'.id = e.id ∧ tk ∈ e'.tasks) ∧
    (∀ r ∈ s.taskResults, r.output ≠ .pending → r ∈ t.taskResults) ∧
    (∀ e ∈ s.executions, e.complete = true → ∀ r ∈ t.taskResults, r.execution = e.id → r ∈ s.taskResults) ∧
    (∀ e ∈ s.executions, e.complete = true → ∀ r ∈ s.taskResults, r.execution = e.id → r ∈ t.taskResults) ∧
    (∀ x ∈ s.settled, (∀ i ∈ t.invocationsOf x.run x.placement, i ∈ s.invocations) ∧
      (∀ r ∈ t.resultsOf x.run x.placement, r ∈ s.results) ∧
      ∀ w, s.workflow? p x.run = some w → ∀ j c, (j, c) ∈ w.inputs x.placement →
        ∀ d ∈ t.deliveriesOn x.run j, d ∈ s.deliveries) := by
  have inv := Delivery.Reachable.inv h
  have wk := inv.wk
  have K := inv.kept hs
  obtain ⟨dt, rt⟩ := FrozenAux.reachable_tasks h
  have good := FrozenAux.step_good inv (Limit.reachable_inv h) dt rt hs
  have trs := FrozenAux.step_taskResults hs
  -- A pending result of a task in the output of a complete execution cannot exist.
  have outputs : ∀ e ∈ s.executions, e.complete = true → ∀ r₁ ∈ s.taskResults, r₁.execution = e.id →
      r₁.output = .pending → ∀ e₁ spec, s.execution? r₁.execution = some e₁ → s.taskSpec p e₁ r₁.task = .ok spec →
      spec.output.isSome = true → False := by
    intro e he hc r₁ hr₁ hre hp₁ e₁ spec he₁ hspec hout
    obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
    obtain rfl : e₁ = e := wk.execution_eq_of_id he₁m he (he₁id.trans hre)
    obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec
    have hname : spec.name = r₁.task := by simpa using List.find?_some hfind
    exact (inv.dyn.execDone e₁ he hc).2.2 cc hcc r₁ hr₁ hre ⟨spec, List.mem_of_find?_eq_some hfind, hname, hout⟩ hp₁
  refine ⟨?_, ?_, fun e he hc => good.done e he hc (dt e he hc), good.tasks, ?_, ?_, ?_, ?_⟩
  · -- An invocation that is no longer active is left as it is (`Delivery.frozen`).
    intro i hi hna
    obtain ⟨i', hi', hid, -⟩ := K.invocation i hi
    rw [Delivery.frozen inv hs hi hna hi' hid] at hi'
    exact hi'
  · intro c hc hend
    obtain ⟨c', hc', -, -, -, -, -, hsame⟩ := K.call c hc
    rw [hsame hend] at hc'
    exact hc'
  · -- Only the output transform of a pending result changes a task result.
    intro r hr hne
    rcases trs with htr | ⟨x, htr, -⟩ | ⟨r₁, o, -, -, hr₁, hp₁, -, -, -, htr⟩
    · rw [htr]; exact hr
    · rw [htr]; exact List.mem_append_left _ hr
    · rw [htr]
      refine FrozenAux.mem_setTaskResult_of_ne hr fun hkey => hne ?_
      rw [Limit.eq_of_key wk.taskResults hr hr₁ hkey]
      exact hp₁
  · -- A complete execution has no running task call, no open task run and no pending output.
    intro e he hc r hr hre
    obtain ⟨hcalls, hruns, -⟩ := inv.dyn.execDone e he hc
    rcases trs with htr | ⟨x, htr, hx⟩ | ⟨r₁, o, e₁, spec, hr₁, hp₁, he₁, hspec, hout, htr⟩
    · rw [htr] at hr; exact hr
    · rw [htr] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · obtain rfl := List.mem_singleton.mp hr
        exfalso
        rcases hx with ⟨-, ⟨c, hc', hco, hct, hst⟩ | ⟨R, hR, hRo, hRt, hRc⟩⟩
        · have := hcalls c hc' (hco.trans hre) (by rw [hct]; simp)
          rcases hst with h' | h' <;> rw [h'] at this <;> cases this
        · have := hruns R hR (by rw [hRo, hre]) (by rw [hRt]; simp)
          rw [hRc] at this
          cases this
    · rw [htr] at hr
      rcases State.mem_setTaskResult_taskResults hr with rfl | hr
      · exact (outputs e he hc r₁ hr₁ hre hp₁ e₁ spec he₁ hspec hout).elim
      · exact hr
  · intro e he hc r hr hre
    rcases trs with htr | ⟨x, htr, -⟩ | ⟨r₁, o, e₁, spec, hr₁, hp₁, he₁, hspec, hout, htr⟩
    · rw [htr]; exact hr
    · rw [htr]; exact List.mem_append_left _ hr
    · rw [htr]
      refine FrozenAux.mem_setTaskResult_of_ne hr fun hkey => ?_
      obtain rfl : r = r₁ := Limit.eq_of_key wk.taskResults hr hr₁ hkey
      exact outputs e he hc r hr hre hp₁ e₁ spec he₁ hspec hout
  · intro x hx
    refine ⟨fun i hi => ?_, fun r hr => ?_, fun w hw j c hjc d hd => ?_⟩
    · -- The invocation is one from before, which ended, so it is unchanged.
      obtain ⟨hi, hir, hip⟩ := Delivery.mem_invocationsOf.mp hi
      obtain ⟨i₀, hi₀, hid, hir₀, hip₀, -, -⟩ := Delivery.frozen_invocations inv hs hx i hi hir hip
      have hend := inv.sett.ended x hx i₀ hi₀ (hir₀.trans hir) (hip₀.trans hip)
      rw [Delivery.frozen inv hs hi₀ (Delivery.invocationEnded_iff.mp hend).1 hi hid.symm]
      exact hi₀
    · obtain ⟨hr, hrr, hrp⟩ := Delivery.mem_resultsOf.mp hr
      exact Delivery.frozen_results inv hs hx r hr hrr hrp
    · -- A new delivery would carry an eligible result, but the settlement received all of them.
      obtain ⟨hdm, hdr, hdc⟩ := Delivery.mem_deliveriesOn.mp hd
      rcases Delivery.step_deliveries_back hs d hdm with h' | ⟨-, -, hfresh, w', c', r, hw', hc', hr, hrr, hrp, harm⟩
      · exact h'
      · exfalso
        obtain ⟨hcj, hct⟩ := Delivery.mem_inputs.mp hjc
        rw [hdr, hw] at hw'
        cases hw'
        rw [hdc, hcj] at hc'
        cases hc'
        obtain ⟨hrm, hrid⟩ := State.result?_eq_some hr
        have hdel := ((Delivery.Reachable.deliv h).delivered x hx w hw j c hcj hct).1 r
          (Delivery.mem_eligible.mpr ⟨hrm, hrr.trans hdr, hrp, harm⟩)
        rw [hdr, hdc, ← hrid] at hfresh
        rw [hfresh] at hdel
        cases hdel

end Frozen

end Suimon.Round3
