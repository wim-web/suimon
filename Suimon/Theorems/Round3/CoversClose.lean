import Suimon.Theorems.Round3.CoversView
import Suimon.Theorems.Round3.CoversCloseSettle

namespace Suimon.Round3
open State

/-! ## [24] Round3/CoversClose.lean — task F6 -/

section CoversClose
variable {p : Program} {env : Env} {s s' T : State}

open CoversCloseAux in
/-- `settle`: `settle_view_agree`, then `settleOutcome_congr`, then `Stable.settled` in `T` give the
    settlement and aggregate `T` recorded; the footprint of the new settlement comes from the same view. -/
theorem covers_settle {path : Path} {name : String} (h : StepCtx p env T s (.settle path name) s') :
    Covers p T s' := by
  obtain ⟨tr, h₁⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  have hreach := h₁.reachable
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have cov := h.covers
  have us : Unstopped s := unstopped_of_step hreach h.accepted h.unstopped
  have fp := covers_footprint_step h
  obtain ⟨-, -, r, w, pl, shape, kind, x, result, hr, -, hw, hpl, -, hsh, hkind, hout, hs'⟩ :=
    Step.settle_inv h.accepted
  obtain ⟨hplm, hname⟩ := Workflow.placement?_eq_some hpl
  subst hname
  obtain ⟨hall, hxr, hxp, -⟩ := State.settleOutcome_some hout
  have agree := settle_view_agree h.valid h₁ us h₂ h.done cov hr hw hpl hsh hout
  have hws : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
  have hwT := covers_workflow? cov wkT hws
  obtain ⟨hrm, hrp⟩ := State.run?_eq_some hr
  -- `T` settled the placement (it is complete), with what its rule computes (`Stable.settled`), which
  -- is what run 1 computes (`settleOutcome_congr`).
  obtain ⟨hxT, hresT⟩ : x ∈ T.settled ∧ ∀ res, result = some res → res ∈ T.results := by
    obtain ⟨rT, hrT, c1, c2, -⟩ := cov.runs r hrm
    obtain ⟨xT, hxT⟩ := Option.isSome_iff_exists.mp
      ((saturated h.valid hT h.done).settled rT hrT w (by rw [c2]; exact hw) pl hplm)
    obtain ⟨hxTm, hxTr, hxTp⟩ := State.settled?_eq_some hxT
    obtain ⟨w', pl', shape', kind', agg, hw', hpl', hsh', hk', hout', hagg⟩ :=
      (Reachable.stable h.valid hT).settled xT hxTm
    rw [hxTr, c1, hrp, hwT] at hw'
    cases hw'
    rw [hxTp, hpl] at hpl'
    cases hpl'
    rw [hxTp, hsh] at hsh'
    cases hsh'
    rw [hxTp, hkind] at hk'
    cases hk'
    rw [hxTr, c1, hrp, ← settleOutcome_congr agree, hout, Option.some.injEq, Prod.mk.injEq] at hout'
    obtain ⟨rfl, rfl⟩ := hout'
    exact ⟨hxTm, hagg⟩
  -- The invocations of the placement in `T` are ended invocations of run 1.
  have hinvT : ∀ i ∈ T.invocations, i.run = path → i.placement = pl.name →
      i ∈ s.invocations ∧ s.invocationEnded i = true := by
    intro i hi h1 h2
    have his := agree.invocations.mem_iff.mpr (Delivery.mem_invocationsOf.mpr ⟨hi, h1, h2⟩)
    exact ⟨(Delivery.mem_invocationsOf.mp his).1, List.all_eq_true.mp hall i his⟩
  -- The frozen footprint of the new settlement.
  have fpx : (∀ i ∈ T.invocationsOf x.run x.placement, i ∈ s.invocations) ∧
      (∀ r ∈ T.resultsOf x.run x.placement, r ∈ s.results ∨ result = some r) ∧
      ∀ w', s.workflow? p x.run = some w' → ∀ j c, (j, c) ∈ w'.inputs x.placement →
        ∀ d ∈ T.deliveriesOn x.run j, d ∈ s.deliveries := by
    rw [hxr, hxp]
    refine ⟨fun i hi => ?_, fun r' hr' => ?_, fun w' hw' j c hjc d hd => ?_⟩
    · obtain ⟨hi, h1, h2⟩ := Delivery.mem_invocationsOf.mp hi
      exact (hinvT i hi h1 h2).1
    · obtain ⟨hr'm, hr'r, hr'p⟩ := Delivery.mem_resultsOf.mp hr'
      rcases results_back h.valid h₁ us h₂ h.done cov hws hpl hinvT hr'm hr'r hr'p with hold |
          ⟨hid, hctrl, x', hx', h1, h2, h3⟩
      · exact Or.inl hold
      · -- The aggregate: `T`'s normal settlement of the placement is `x`, which records it.
        right
        have hxx : x' = x := by
          have e1 := wkT.settled?_of_mem hx'
          rw [h1, h2, ← hxr, ← hxp, wkT.settled?_of_mem hxT] at e1
          exact (Option.some.inj e1).symm
        rw [hxx] at h3
        obtain ⟨res, hres, hresid⟩ := aggregate_of_normal hout h3 hctrl
        rw [hres, wkT.result_eq_of_id (hresT res hres) hr'm (hresid.trans hid.symm)]
    · rw [hws] at hw'
      cases hw'
      exact inputs_back h.valid hT cov hwT (workflow_mem hws) hplm hsh agree j c hjc d hd
  rcases hs' with ⟨rfl, rfl⟩ | ⟨res, rfl, -, rfl⟩
  · exact {
      runs := cov.runs
      invocations := cov.invocations
      calls := cov.calls
      executions := cov.executions
      results := cov.results
      taskResults := cov.taskResults
      deliveries := cov.deliveries
      settled := fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact cov.settled y hy
        · rw [List.mem_singleton.mp hy]
          exact hxT
      footprint := fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact fp.1 y hy
        · rw [List.mem_singleton.mp hy]
          refine ⟨fpx.1, fun r' hr' => ?_, fpx.2.2⟩
          rcases fpx.2.1 r' hr' with h' | h'
          · exact h'
          · cases h'
      execution := fp.2 }
  · exact {
      runs := cov.runs
      invocations := cov.invocations
      calls := cov.calls
      executions := cov.executions
      results := fun r' hr' => by
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact cov.results r' hr'
        · rw [List.mem_singleton.mp hr']
          exact hresT res rfl
      taskResults := cov.taskResults
      deliveries := cov.deliveries
      settled := fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact cov.settled y hy
        · rw [List.mem_singleton.mp hy]
          exact hxT
      footprint := fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact fp.1 y hy
        · rw [List.mem_singleton.mp hy]
          refine ⟨fpx.1, fun r' hr' => ?_, fpx.2.2⟩
          rcases fpx.2.1 r' hr' with h' | h'
          · exact List.mem_append_left _ h'
          · cases h'
            exact List.mem_append_right _ (List.mem_singleton_self _)
      execution := fp.2 }

open CoversCloseAux in
/-- `closeExecution`: `closeExecution_view_agree`, `listValue_perm` and `Stable.execution` in `T`. -/
theorem covers_closeExecution {eid : String} (h : StepCtx p env T s (.closeExecution eid) s') : Covers p T s' := by
  obtain ⟨tr, h₁⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  have hreach := h₁.reachable
  have hT := h₂.reachable
  have wkS := hreach.wellKeyed
  have wkT := hT.wellKeyed
  have cov := h.covers
  have fp := covers_footprint_step h
  have back := closeExecution_view_agree h
  obtain ⟨-, -, e, cc, i, he, -, hcc, hended, hpend, hi, hcases⟩ := Step.closeExecution_inv h.accepted
  obtain ⟨hem, heid⟩ := execution?_eq_some he
  obtain ⟨him, hiid⟩ := invocation?_eq_some hi
  subst heid
  -- `T` completed the execution with the same tasks, which all ended in run 1.
  obtain ⟨eT, heT, a1, a2, a3, a4, a5, a6, -⟩ := cov.executions e hem
  have hTE : eT = { e with complete := true } := by
    refine execution_ext a1 a2 a3 a4 ?_ ((saturated h.valid hT h.done).executions eT heT).1
    exact tasks_eq_of_names a5 fun t ht t' ht' hn =>
      (a6 t ht t' ht' hn).2 (Delivery.taskEnded_iff.mp (List.all_eq_true.mp hended t ht)).1
  subst hTE
  -- `T`'s invocation of the execution differs from run 1's only in its status: a concurrency
  -- invocation carries no arm.
  obtain ⟨iT, hiT, b1, b2, b3, b4, b5, -⟩ := cov.invocations i him
  obtain ⟨w, pl, hw, hpl, hctl⟩ := Delivery.concurrencyOf_iff.mp hcc
  obtain ⟨i₁, hi₁, hi₁id, hi₁r, hi₁p, -⟩ := (Settle.reachable hreach).1.execOwner e hem
  have hii : i₁ = i := wkS.invocation_eq_of_id hi₁ him (hi₁id.trans hiid.symm)
  rw [hii] at hi₁r hi₁p
  have hnb : ∀ j arms, pl.control ≠ .branch j arms := fun j arms hb => by rw [hctl] at hb; cases hb
  have harm : i.arm = none :=
    arm_none (Delivery.Reachable.inv hreach) him (by rw [hi₁r]; exact hw) (by rw [hi₁p]; exact hpl) hnb
  have harmT : iT.arm = none := arm_none (Delivery.Reachable.inv hT) hiT
    (by rw [b2, hi₁r]; exact covers_workflow? cov wkT hw) (by rw [b3, hi₁p]; exact hpl) hnb
  have hccT : T.concurrencyOf p { e with complete := true } = .ok cc := covers_concurrencyOf cov wkT rfl rfl hcc
  have hiT' : T.invocation? ({ e with complete := true } : Execution).id = some iT := by
    show T.invocation? e.id = some iT
    rw [← hiid, ← b1]
    exact wkT.invocation?_of_mem hiT
  have hstab := (Reachable.stable h.valid hT).execution _ heT rfl cc iT hccT hiT'
  -- Run 1 transformed every included result, and `T` has no other one (the view).
  have hdone : ∀ x ∈ includedOutputs s e.id cc, x.output ≠ .pending := by
    intro x hx
    simpa using List.all_eq_true.mp hpend x hx
  -- What the step records, by case; the status is the one `T` recorded.
  obtain ⟨st, hstT, hsInv, hsExec, hsRes, hsRuns, hsCalls, hsTR, hsDel, hsSet⟩ :
      ∃ st, iT.status = st ∧ s'.invocations = (s.setInvocation { i with status := st }).invocations ∧
        s'.executions = (s.setExecution { e with complete := true }).executions ∧
        (∀ r ∈ s'.results, r ∈ s.results ∨ r ∈ T.results) ∧ s'.runs = s.runs ∧ s'.calls = s.calls ∧
        s'.taskResults = s.taskResults ∧ s'.deliveries = s.deliveries ∧ s'.settled = s.settled := by
    have hskip : ∀ b, allIncludedSkipped { e with complete := true } cc = b →
        (e.tasks.filter fun ts => ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains ts.name).all
          (·.status == .skipped) = b := fun b hb => hb
    rcases hcases with ⟨hsk, rfl⟩ | ⟨hsk, hout, -, rfl⟩ | ⟨hsk, hout, rfl⟩
    · rcases hstab with ⟨-, hst⟩ | ⟨hsk', -⟩
      · exact ⟨.skipped, hst, rfl, rfl, fun r hr => Or.inl hr, rfl, rfl, rfl, rfl, rfl⟩
      · rw [hskip _ hsk'] at hsk
        cases hsk
    · rcases hstab with ⟨hsk', -⟩ | ⟨-, hst, hlist⟩
      · rw [hskip _ hsk'] at hsk
        cases hsk
      · refine ⟨.succeeded, hst, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
        rcases List.mem_append.mp hr with hr | hr
        · exact Or.inl hr
        · right
          rw [List.mem_singleton.mp hr]
          have hv : listValue ((includedOutputs s e.id cc).filterMap (·.output.value?)) =
              listValue ((includedOutputs T e.id cc).filterMap (·.output.value?)) :=
            listValue_perm ((includedOutputs_perm cov wkS wkT hdone back).filterMap _)
          have hmem : listResult { e with complete := true }
              (listValue ((includedOutputs T e.id cc).filterMap (·.output.value?))) ∈ T.results := hlist hout
          rw [← hv] at hmem
          exact hmem
    · rcases hstab with ⟨hsk', -⟩ | ⟨-, hst, -⟩
      · rw [hskip _ hsk'] at hsk
        cases hsk
      · exact ⟨.succeeded, hst, rfl, rfl, fun r hr => Or.inl hr, rfl, rfl, rfl, rfl, rfl⟩
  have hiTeq : iT = { i with status := st } := invocation_ext b1 b2 b3 b4 b5 hstT (harmT.trans harm.symm)
  exact {
    runs := fun r hr => cov.runs r (hsRuns ▸ hr)
    invocations := fun x hx => by
      rw [hsInv] at hx
      rcases mem_setInvocation_invocations hx with rfl | hx
      · exact ⟨iT, hiT, b1, b2, b3, b4, b5, fun _ => hiTeq⟩
      · exact cov.invocations x hx
    calls := fun c hc => cov.calls c (hsCalls ▸ hc)
    executions := fun x hx => by
      rw [hsExec] at hx
      rcases mem_setExecution_executions hx with rfl | hx
      · exact exec_self (Limit.reachable_inv hT) heT
      · exact cov.executions x hx
    results := fun r hr => by
      rcases hsRes r hr with hr | hr
      · exact cov.results r hr
      · exact hr
    taskResults := fun r hr => cov.taskResults r (hsTR ▸ hr)
    deliveries := fun d hd => cov.deliveries d (hsDel ▸ hd)
    settled := fun x hx => cov.settled x (hsSet ▸ hx)
    footprint := fun x hx => fp.1 x (hsSet ▸ hx)
    execution := fun x hx hc r hr hre => by
      rw [hsExec] at hx
      rcases mem_setExecution_executions hx with rfl | hx
      · rw [hsTR]
        exact back r hr hre
      · exact fp.2 x hx hc r hr hre }
open CoversCloseAux in
/-- `closeRun`: the output's settlement is in `T` (`Covers.settled`), and so is its unique result
    (`Covers.footprint` + `Deliv.one`); `Stable.run` in `T` gives what `T`'s `closeRun` wrote. -/
theorem covers_closeRun {path : Path} (h : StepCtx p env T s (.closeRun path) s') : Covers p T s' := by
  obtain ⟨tr, h₁⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  have hreach := h₁.reachable
  have hT := h₂.reachable
  have wkS := hreach.wellKeyed
  have wkT := hT.wellKeyed
  have cov := h.covers
  have fp := covers_footprint_step h
  obtain ⟨-, -, r, w, output, x, owner, hr, hrc, -, hw, -, hout, hx, howner, hcases⟩ :=
    Step.closeRun_inv h.accepted
  obtain ⟨hrm, hrp⟩ := State.run?_eq_some hr
  obtain ⟨hxm, hxr, hxp⟩ := State.settled?_eq_some hx
  -- `T` completed the same run and recorded what its rule computes (`Stable.run`).
  obtain ⟨rT, hrT, c1, c2, c3, c4, c5⟩ := cov.runs r hrm
  have hstab := (Reachable.stable h.valid hT).run rT hrT ((saturated h.valid hT h.done).runs rT hrT) owner output x
    (c4.trans howner) (covers_designatedOutput cov wkT c4 c5 hout)
    (by rw [c1, hrp, ← hxr, ← hxp]; exact wkT.settled?_of_mem (cov.settled x hxm))
  -- The value of the output is that of its only result, the same in both runs (a Single output).
  have hws : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
  have hwT := covers_workflow? cov wkT hws
  obtain ⟨-, hk⟩ := run_output h.valid hreach hrm hout hw
  have value : ∀ v, ((s.resultsOf path output).head?).map (·.value) = some v →
      ∀ res ∈ T.resultsOf rT.path output, res.value = v := by
    intro v hv res hres
    rw [c1, hrp] at hres
    cases hl : s.resultsOf path output with
    | nil => rw [hl] at hv; cases hv
    | cons h₀ rest =>
      rw [hl] at hv
      have hv' : h₀.value = v := by simpa using hv
      have h₀m : h₀ ∈ s.resultsOf path output := by rw [hl]; exact List.mem_cons_self
      obtain ⟨h₀s, h₀r, h₀p⟩ := Delivery.mem_resultsOf.mp h₀m
      obtain ⟨resm, resr, resp⟩ := Delivery.mem_resultsOf.mp hres
      have hid := (Delivery.Reachable.deliv hT).one w path output hwT hk res resm h₀ (cov.results h₀ h₀s)
        resr resp h₀r h₀p
      rw [wkT.result_eq_of_id resm (cov.results h₀ h₀s) hid]
      exact hv'
  -- The closed run keeps its creation fields.
  have runsOk : ∀ r' ∈ (s.setRun { r with complete := true }).runs, ∃ r'' ∈ T.runs, r''.path = r'.path ∧
      r''.workflow = r'.workflow ∧ r''.input = r'.input ∧ r''.owner = r'.owner ∧ r''.task = r'.task := by
    intro r' hr'
    rcases mem_setRun_runs hr' with rfl | hr'
    · exact ⟨rT, hrT, c1, c2, c3, c4, c5⟩
    · exact cov.runs r' hr'
  rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
  · -- A sub-workflow run: its invocation takes the status of the output. The invocation of `T` differs
    -- only in its status, since an invocation of a sub-workflow call carries no arm.
    rw [c5, htask] at hstab
    obtain ⟨iT, hiT, hstT, hresT⟩ := hstab
    obtain ⟨him, hiid⟩ := invocation?_eq_some hi
    obtain ⟨hiTm, hiTid⟩ := invocation?_eq_some hiT
    obtain ⟨iT', hiT', b1, b2, b3, b4, b5, -⟩ := cov.invocations i him
    have hii : iT' = iT := wkT.invocation_eq_of_id hiT' hiTm (b1.trans (hiid.trans hiTid.symm))
    rw [hii] at b1 b2 b3 b4 b5
    obtain ⟨i₁, pl, wf, hi₁, hpl, hctrl⟩ : ∃ i₁ pl wf, s.invocation? owner = some i₁ ∧
        s.placementOf p i₁.run i₁.placement = .ok pl ∧ pl.control = .call (.workflow wf output) := by
      obtain ⟨owner', howner', hcase⟩ := State.designatedOutput_eq_ok.mp hout
      rw [howner] at howner'
      cases howner'
      rcases hcase with ⟨-, hcase⟩ | ⟨_, _, _, _, htask', -⟩
      · exact hcase
      · rw [htask] at htask'
        cases htask'
    have hii₁ : i₁ = i := Option.some.inj (hi₁.symm.trans hi)
    rw [hii₁] at hpl
    obtain ⟨w₀, hw₀, hpl₀⟩ := State.placementOf_eq_ok.mp hpl
    have hnb : ∀ j arms, pl.control ≠ .branch j arms := fun j arms hb => by rw [hctrl] at hb; cases hb
    have harm := arm_none (Delivery.Reachable.inv hreach) him hw₀ hpl₀ hnb
    have harmT := arm_none (Delivery.Reachable.inv hT) hiTm (by rw [b2]; exact covers_workflow? cov wkT hw₀)
      (by rw [b3]; exact hpl₀) hnb
    have hiTeq : iT = { i with status := closedStatus x.outcome } :=
      invocation_ext b1 b2 b3 b4 b5 hstT (harmT.trans harm.symm)
    -- What the step records, by case.
    obtain ⟨hsInv, hsRes, hsRuns, hsExec, hsCalls, hsTR, hsDel, hsSet⟩ :
        s'.invocations = (s.setInvocation { i with status := closedStatus x.outcome }).invocations ∧
        (∀ r' ∈ s'.results, r' ∈ s.results ∨ r' ∈ T.results) ∧
        s'.runs = (s.setRun { r with complete := true }).runs ∧ s'.executions = s.executions ∧
        s'.calls = s.calls ∧ s'.taskResults = s.taskResults ∧ s'.deliveries = s.deliveries ∧
        s'.settled = s.settled := by
      rcases hcases with ⟨hn, v, hv, -, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩
      · refine ⟨by rw [hn]; rfl, fun r' hr' => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact Or.inl hr'
        · right
          rw [List.mem_singleton.mp hr']
          obtain ⟨res, hres, hmem⟩ := hresT hn
          rw [value v hv res hres, hiTeq] at hmem
          exact hmem
      all_goals exact ⟨by rw [hn]; rfl, fun r' hr' => Or.inl hr', rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact {
      runs := fun r' hr' => runsOk r' (hsRuns ▸ hr')
      invocations := fun y hy => by
        rw [hsInv] at hy
        rcases mem_setInvocation_invocations hy with rfl | hy
        · exact ⟨iT, hiTm, b1, b2, b3, b4, b5, fun _ => hiTeq⟩
        · exact cov.invocations y hy
      calls := fun c hc => cov.calls c (hsCalls ▸ hc)
      executions := fun e he => cov.executions e (hsExec ▸ he)
      results := fun r' hr' => by
        rcases hsRes r' hr' with hr' | hr'
        · exact cov.results r' hr'
        · exact hr'
      taskResults := fun r' hr' => cov.taskResults r' (hsTR ▸ hr')
      deliveries := fun d hd => cov.deliveries d (hsDel ▸ hd)
      settled := fun y hy => cov.settled y (hsSet ▸ hy)
      footprint := fun y hy => fp.1 y (hsSet ▸ hy)
      execution := fun e he hc r' hr' hre => fp.2 e (hsExec ▸ he) hc r' hr' hre }
  · -- A task run: its task takes the status of the output. The task of `T` differs only in its status:
    -- it began (it has a run), so both runs read the same input.
    rw [c5, htask] at hstab
    obtain ⟨eT, tsT, heT, htsT, hstT, hresT⟩ := hstab
    obtain ⟨hem, heid⟩ := execution?_eq_some he
    obtain ⟨heTm, heTid⟩ := execution?_eq_some heT
    obtain ⟨eT', heT', a1, a2, a3, a4, a5, a6, -⟩ := cov.executions e hem
    have hee : eT' = eT := wkT.execution_eq_of_id heT' heTm (a1.trans (heid.trans heTid.symm))
    rw [hee] at a1 a2 a3 a4 a5 a6
    have htsm : ts ∈ e.tasks := List.mem_of_find?_eq_some hts
    have htsn : ts.name = name := by simpa using List.find?_some hts
    have htsTm : tsT ∈ eT.tasks := List.mem_of_find?_eq_some htsT
    have htsTn : tsT.name = name := by simpa using List.find?_some htsT
    have hbegun : ts.status ≠ .pending := by
      have lim := Limit.reachable_inv hreach
      have hh := lim.runs r hrm owner name howner htask
      rw [← heid, ← htsn] at hh
      exact (lim.status_of hem htsm hh).1
    have htsTeq : tsT = { ts with status := closedTaskStatus x.outcome } :=
      task_ext (htsTn.trans htsn.symm) ((a6 ts htsm tsT htsTm (htsTn.trans htsn.symm)).1 hbegun) hstT
    -- The execution is open, since its task run is.
    have hec : e.complete = false := by
      obtain ⟨e₁, he₁, he₁o, he₁c⟩ := (Settle.reachable hreach).2.1.taskRunOpen r hrm name htask hrc
      have he₁e : e₁ = e :=
        wkS.execution_eq_of_id he₁ hem (Option.some.inj (he₁o.symm.trans (howner.trans (by rw [heid]))))
      rw [he₁e] at he₁c
      exact he₁c
    -- What the step records, by case.
    obtain ⟨hsExec, hsTR, hsRuns, hsInv, hsRes, hsCalls, hsDel, hsSet⟩ :
        s'.executions = (s.setTask e { ts with status := closedTaskStatus x.outcome }).executions ∧
        (∀ r' ∈ s'.taskResults, r' ∈ s.taskResults ∨ ∃ r'' ∈ T.taskResults, r''.execution = r'.execution ∧
          r''.task = r'.task ∧ r''.index = r'.index ∧ r''.value = r'.value ∧ r'.output = .pending) ∧
        s'.runs = (s.setRun { r with complete := true }).runs ∧ s'.invocations = s.invocations ∧
        s'.results = s.results ∧ s'.calls = s.calls ∧ s'.deliveries = s.deliveries ∧ s'.settled = s.settled := by
      rcases hcases with ⟨hn, v, hv, -, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩
      · refine ⟨by rw [hn]; rfl, fun r' hr' => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact Or.inl hr'
        · right
          rw [List.mem_singleton.mp hr']
          obtain ⟨res, hres, tr', htr', t1, t2, t3, t4⟩ := hresT hn
          exact ⟨tr', htr', t1.trans heid.symm, t2, t3, t4.trans (value v hv res hres), rfl⟩
      all_goals exact ⟨by rw [hn]; rfl, fun r' hr' => Or.inl hr', rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- The execution with the closed task: names are kept, and the closed task is `T`'s.
    have hnames : (withTask e { ts with status := closedTaskStatus x.outcome }).tasks.map (·.name) =
        e.tasks.map (·.name) := by
      rw [withTask_tasks, List.map_map]
      refine List.map_congr_left fun y _ => ?_
      simp only [Function.comp_apply]
      split
      · rename_i hyn
        exact (beq_iff_eq.mp hyn).symm
      · rfl
    exact {
      runs := fun r' hr' => runsOk r' (hsRuns ▸ hr')
      invocations := fun y hy => cov.invocations y (hsInv ▸ hy)
      calls := fun c hc => cov.calls c (hsCalls ▸ hc)
      executions := fun y hy => by
        rw [hsExec, State.setTask_eq] at hy
        rcases mem_setExecution_executions hy with rfl | hy
        · refine ⟨eT, heTm, a1, a2, a3, a4, a5.trans hnames.symm, fun t ht t' ht' htn => ?_, fun hc => ?_⟩
          · rw [withTask_tasks] at ht
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
            by_cases hyn : (y.name == ({ ts with status := closedTaskStatus x.outcome } : TaskState).name) = true
            · rw [ite_eq_left hyn] at htn ⊢
              have ht'T : t' = tsT := (Limit.reachable_inv hT).coherent eT heTm t' ht' tsT htsTm
                (htn.trans (htsn.trans htsTn.symm))
              rw [ht'T, htsTeq]
              exact ⟨fun _ => rfl, fun _ => rfl⟩
            · rw [ite_eq_right hyn] at htn ⊢
              exact a6 y hy t' ht' htn
          · rw [withTask_complete, hec] at hc
            cases hc
        · exact cov.executions y hy
      results := fun r' hr' => cov.results r' (hsRes ▸ hr')
      taskResults := fun r' hr' => by
        rcases hsTR r' hr' with hr' | ⟨r'', hr'', t1, t2, t3, t4, t5⟩
        · exact cov.taskResults r' hr'
        · exact ⟨r'', hr'', t1, t2, t3, t4, fun hne => absurd t5 hne⟩
      deliveries := fun d hd => cov.deliveries d (hsDel ▸ hd)
      settled := fun y hy => cov.settled y (hsSet ▸ hy)
      footprint := fun y hy => fp.1 y (hsSet ▸ hy)
      execution := fun y hy hc r' hr' hre => by
        rw [hsExec, State.setTask_eq] at hy
        rcases mem_setExecution_executions hy with rfl | hy
        · rw [withTask_complete, hec] at hc
          cases hc
        · exact fp.2 y hy hc r' hr' hre }

end CoversClose

end Suimon.Round3
