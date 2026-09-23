import Suimon.Theorems.DeliveryFinal

/-! A Single placement has at most one result in a run: it has at most one invocation, which accepts
    one result and then stops. -/

namespace Suimon.Delivery
open State

theorem accept_results {s t : State} {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : t.results = s.results ∨ ∃ x, t.results = s.results ++ [x] := by
  rcases State.accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

open State in
/-- A step accepts at most one result. --/
theorem step_results_eq {p : Program} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    t.results = s.results ∨ ∃ x, t.results = s.results ++ [x] := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact Or.inl rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact Or.inl rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact Or.inl rfl
  | returned id value =>
    obtain ⟨-, -, _, _, s', _, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    rw [(settleOwner_old hso).2.2.2.2.2.1, setCall_results]
    exact accept_results hacc
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    rw [setInvocation_results, setCall_results]
    exact accept_results hacc
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    rw [setCall_results]
    exact accept_results hacc
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact Or.inl (by rw [(settleOwner_old hso).2.2.2.2.2.1, setCall_results])
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact Or.inl (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.2.1
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact Or.inl (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.2.1
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact Or.inl (failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.2.1
    · exact Or.inl (by rw [(cancelOwner_old h).2.2.2.2.2.1, setCall_results])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact Or.inl (by rw [(cancelOwner_old h).2.2.2.2.2.1, setCall_results])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact Or.inl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Or.inl (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Or.inl rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact Or.inl (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact Or.inl rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Or.inl (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;> rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    all_goals first | exact Or.inr ⟨_, rfl⟩ | exact Or.inl rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact Or.inl rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact Or.inl rfl

theorem step_new_result_unique {p : Program} {s t : State} {op : Op} (hs : step p s op = .ok t) {r r' : Result}
    (hr : r ∈ t.results) (hnew : r ∉ s.results) (hr' : r' ∈ t.results) (hnew' : r' ∉ s.results) : r = r' := by
  rcases step_results_eq hs with h | ⟨x, h⟩
  · exact absurd (h ▸ hr) hnew
  · rw [h, List.mem_append, List.mem_singleton] at hr hr'
    rw [hr.resolve_left hnew, hr'.resolve_left hnew']

section
variable {p : Program} {s t : State} {op : Op}

/-- A placement with a Single output has at most one invocation in a run: its trigger is fixed by the
    input shape (§5.3). --/
theorem single_invocation (inv : Inv p s) {w : Workflow} {path : Path} {name : String}
    (hw : s.workflow? p path = some w) (hk : w.outputKind? p name = some .single) {i i' : Invocation}
    (hi : i ∈ s.invocationsOf path name) (hi' : i' ∈ s.invocationsOf path name) : i = i' := by
  obtain ⟨him, hir, hip⟩ := mem_invocationsOf.mp hi
  obtain ⟨him', hir', hip'⟩ := mem_invocationsOf.mp hi'
  obtain ⟨-, w₁, pl, sh, hw₁, hpl, hinvc, hsh, htrig, -⟩ := inv.own.invocations i him
  obtain ⟨-, w₂, pl₂, sh₂, hw₂, hpl₂, -, hsh₂, htrig₂, -⟩ := inv.own.invocations i' him'
  rw [hir, hw] at hw₁; cases hw₁
  rw [hir', hw] at hw₂; cases hw₂
  rw [hip] at hpl hsh
  rw [hip'] at hpl₂ hsh₂
  rw [hpl] at hpl₂; cases hpl₂
  rw [hsh] at hsh₂; cases hsh₂
  have hnostream := (single_kind hsh hk hpl hinvc).1
  refine uniq_trigger inv.own inv.wk i hi i' hi' ?_
  cases sh with
  | none => exact htrig.trans htrig₂.symm
  | entry => exact htrig.trans htrig₂.symm
  | single j c =>
    obtain ⟨src, inp, hres, htr⟩ := htrig
    obtain ⟨src', inp', hres', htr'⟩ := htrig₂
    rw [hir] at hres
    rw [hir', hres] at hres'
    cases hres'
    rw [htr, htr']
  | stream j c => exact absurd rfl (hnostream j c)
  | merge cs => exact htrig.elim

/-- A placement with a Single output that already has a result accepts no other (§5.1). --/
theorem no_second_result (inv : Inv p s) (hs : step p s op = .ok t) {w : Workflow} {path : Path} {name : String}
    (hw : s.workflow? p path = some w) (hk : w.outputKind? p name = some .single) {r r' : Result}
    (hr : r ∈ t.results) (hnew : r ∉ s.results) (hr' : r' ∈ s.results) (hrr : r.run = path) (hrp : r.placement = name)
    (hr'r : r'.run = path) (hr'p : r'.placement = name) : False := by
  rcases inv.dyn.results r' hr' with ⟨i', hi', -, hi'r, hi'p, -, hst⟩ | ⟨-, -, y, hy, hyr, hyp, -⟩
  · have hi'mem : i' ∈ s.invocationsOf path name := mem_invocationsOf.mpr ⟨hi', hi'r.trans hr'r, hi'p.trans hr'p⟩
    obtain ⟨-, w₁, pl, sh, hw₁, hpl, hinvc, hsh, -, -⟩ := inv.own.invocations i' hi'
    rw [hi'r, hr'r, hw] at hw₁; cases hw₁
    rw [hi'p, hr'p] at hpl hsh
    obtain ⟨-, hnofun, hnoconc⟩ := single_kind hsh hk hpl hinvc
    have hpl' : PlacementOf p s i' pl := ⟨w, by rw [hi'r, hr'r]; exact hw, by rw [hi'p, hr'p]; exact hpl⟩
    have hsucc : i'.status = .succeeded := by
      rcases hst with h | ⟨w₂, pl₂, hw₂, hpl₂, hk₂⟩
      · exact h
      · obtain rfl := hpl'.unique ⟨w₂, hw₂, hpl₂⟩
        rcases hk₂ with ⟨f, d, hf, hd, hkd⟩ | ⟨c, hc, hco⟩
        · exact absurd hkd (hnofun f d hf hd)
        · exact absurd hco (hnoconc c hc)
    have hna : i'.status ≠ .active := by rw [hsucc]; simp
    obtain ⟨hcalls, hruns, hexecs⟩ := inv.dyn.nonActive i' hi' hna
    rcases step_results_back hs r hr with h | ⟨-, -, -, hcase⟩
    · exact hnew h
    rcases hcase with ⟨c, hc, i, hi, hct, hst', -, -, hio, hir, hip, -⟩ |
        ⟨c, hc, i, hi, -, -, -, -, -, hct, hst', hio, -, -, -, hir, hip, -⟩ |
        ⟨c, hc, i, hi, hct, -, hstream, hio, hir, hip, -⟩ |
        ⟨e, he, cc, tr, hcc, hout, -, -, -, -, her, hep, -⟩ |
        ⟨e, he, i, hi, cc, hec, hio, -, -, her, hep, -⟩ |
        ⟨R, hR, i, hi, hRc, hRt, hRo, hir, hip, -⟩ |
        ⟨run, w₃, pl₃, shape, kind, x, hrun₃, hw₃, hpl₃, -, hsh₃, -, hout, -⟩
    · obtain rfl := single_invocation inv hw hk (mem_invocationsOf.mpr ⟨hi, hir ▸ hrr, hip ▸ hrp⟩) hi'mem
      exact (hcalls c hc hio.symm hct).1 hst'
    · obtain rfl := single_invocation inv hw hk (mem_invocationsOf.mpr ⟨hi, hir ▸ hrr, hip ▸ hrp⟩) hi'mem
      exact (hcalls c hc hio.symm hct).1 hst'
    · -- A Stream function has no Single output.
      obtain ⟨-, pl₂, hpl₂, hk₂⟩ := call_placement inv.own inv.wk hc hct hi hio
      obtain rfl := single_invocation inv hw hk (mem_invocationsOf.mpr ⟨hi, hir ▸ hrr, hip ▸ hrp⟩) hi'mem
      obtain rfl := hpl'.unique hpl₂
      rcases hk₂ with ⟨f, d, hf, hd, -, hs'⟩ | ⟨-, -, -, -, h⟩
      · rw [hstream] at hs'
        exact hnofun f d hf hd (by simpa using hs'.symm)
      · rw [hstream] at h; cases h
    · -- A concurrency with Stream output has no Single output.
      obtain ⟨i, hi, hiid, -, -, -⟩ := inv.own.executions e he
      obtain ⟨hir, hip, pl₂, cc', hpl₂, hcc', hcce⟩ := execution_placement inv.own inv.wk he hi hiid
      rw [hcc] at hcce; cases hcce
      obtain rfl := single_invocation inv hw hk (mem_invocationsOf.mpr ⟨hi, by rw [hir, ← her, hrr],
        by rw [hip, ← hep, hrp]⟩) hi'mem
      obtain rfl := hpl'.unique hpl₂
      exact hnoconc cc hcc' hout
    · obtain ⟨hir, hip, -⟩ := execution_placement inv.own inv.wk he hi hio
      obtain rfl := single_invocation inv hw hk (mem_invocationsOf.mpr ⟨hi, by rw [hir, ← her, hrr],
        by rw [hip, ← hep, hrp]⟩) hi'mem
      have := hexecs e he hio.symm
      rw [hec] at this; cases this
    · obtain rfl := single_invocation inv hw hk (mem_invocationsOf.mpr ⟨hi, hir ▸ hrr, hip ▸ hrp⟩) hi'mem
      have := hruns R hR hRo hRt
      rw [hRc] at this; cases this
    · -- An aggregate belongs to a waitStream or Merge, which is never invoked.
      obtain ⟨-, -, hctl, -⟩ := settleOutcome_res hout
      have hw₃' : s.workflow? p r.run = some w₃ := workflow?_iff.mpr ⟨run, hrun₃, hw₃⟩
      rw [hrr, hw] at hw₃'; cases hw₃'
      rw [hrp] at hpl₃
      rw [hpl] at hpl₃
      cases hpl₃
      rcases hctl with ⟨e, -, -, he, -⟩ | ⟨e, -, he, -⟩ <;> rw [he] at hinvc <;> exact hinvc
  · -- An aggregate of a settled placement: nothing is added to it.
    exact hnew (frozen_results inv hs hy r hr (by rw [hyr, hr'r, hrr]) (by rw [hyp, hr'p, hrp]))

end

end Suimon.Delivery
