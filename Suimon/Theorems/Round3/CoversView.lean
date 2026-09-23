import Suimon.Theorems.Round3.Covers
import Suimon.Theorems.Round3.ShapeFits
import Suimon.Theorems.Round3.ProgressInv
import Suimon.Theorems.Round3.CoversViewSettle

namespace Suimon.Round3
open State

/-! ## [21] Round3/CoversView.lean — task F3 -/

section CoversView
variable {p : Program} {env : Env} {s s' T : State}

/-- At a `settle` of run 1 (state `s`), the view of the placement agrees with the complete run 2 (state
    `T`), shape by shape. Forward inclusions come from `Covers`. Backward ones: for a Stream input, from
    the settle guard (every eligible result delivered, every delivered value invoked) and
    `Covers.footprint` of the settled source; for a Single input, from the one result of a Single source
    (Round 2 `Deliv.one`) or, without a delivery, from `SettledInv.noEligible` in `T`. -/
theorem settle_view_agree {tr tr₂ : List Op} {path : Path} {r : Run} {w : Workflow} {pl : Placement}
    {shape : Workflow.Shape} {kind : Kind} {x : Settled} {agg : Option Result}
    (valid : p.validate = .ok ()) (h₁ : Conforming p env tr s) (us : Unstopped s)
    (h₂ : Conforming p env tr₂ T) (done : Done T) (cov : Covers p T s)
    (hr : s.run? path = some r) (hw : p.workflow? r.workflow = some w) (hpl : w.placement? pl.name = some pl)
    (hshape : w.shape? p pl.name = some shape) (hout : s.settleOutcome path pl shape kind = some (x, agg)) :
    SettleViewAgree s T path pl shape := by
  have hs := h₁.reachable
  have hT := h₂.reachable
  have wkS := hs.wellKeyed
  have wkT := hT.wellKeyed
  have invT := Delivery.Reachable.inv hT
  have sat := saturated valid hT done
  have hwS : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
  have hwT : T.workflow? p path = some w := CoversViewAux.covers_workflow? cov wkT hwS
  obtain ⟨hall, -, -, -⟩ := State.settleOutcome_some hout
  have ended_s : ∀ i ∈ s.invocationsOf path pl.name, s.invocationEnded i = true :=
    fun i hi => List.all_eq_true.mp hall i hi
  have hdone := Delivery.settleOutcome_input hout
  -- The invocations of the placement in `s` ended, so `T` has them unchanged.
  have fwd : ∀ i ∈ s.invocationsOf path pl.name, i ∈ T.invocationsOf path pl.name := by
    intro i hi
    obtain ⟨him, hir, hip⟩ := Delivery.mem_invocationsOf.mp hi
    obtain ⟨i', hi', -, -, -, -, -, heq⟩ := cov.invocations i him
    rw [heq (Delivery.invocationEnded_iff.mp (ended_s i hi)).1] at hi'
    exact Delivery.mem_invocationsOf.mpr ⟨hi', hir, hip⟩
  -- The input connections, by shape.
  have input : match (generalizing := false) shape with
      | .none | .entry => True
      | .single j c => s.resolveSingle path j c = T.resolveSingle path j c
      | .stream j c => s.streamEnd? path j c = T.streamEnd? path j c ∧
          (s.deliveriesOn path j).Perm (T.deliveriesOn path j)
      | .merge cs => ∀ jc ∈ cs, s.resolveSingle path jc.1 jc.2 = T.resolveSingle path jc.1 jc.2 := by
    cases shape with
    | none => trivial
    | entry => trivial
    | single j c =>
      obtain ⟨-, hcj, -, hk⟩ := Delivery.shape?_single hshape
      exact CoversViewAux.resolveSingle_covers hT cov hwT hcj hk hdone.1
    | stream j c =>
      obtain ⟨-, hcj, -, -⟩ := Delivery.shape?_stream hshape
      obtain ⟨hsettled, hall', -⟩ := hdone
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsettled
      obtain ⟨elig, back'⟩ := CoversViewAux.stream_back hT cov hwT hcj hy hall'
      refine ⟨?_, ?_⟩
      · rw [Delivery.streamEnd?_eq_some.mpr ⟨y, hy, hall', rfl⟩]
        refine (Delivery.streamEnd?_eq_some.mpr ⟨y, CoversViewAux.covers_settled? cov wkT hy, fun r hr => ?_,
          rfl⟩).symm
        obtain ⟨d, hd, h1, h2, h3⟩ := elig r hr
        have hdT := wkT.delivery?_of_mem (cov.deliveries d hd)
        rw [h1, h2, h3] at hdT
        rw [hdT]
        rfl
      · refine (List.perm_ext_iff_of_nodup (StableAux.nodup_filter' _ (StableAux.nodup_of_map' wkS.deliveries))
          (StableAux.nodup_filter' _ (StableAux.nodup_of_map' wkT.deliveries))).mpr fun d =>
            ⟨fun hd => ?_, fun hd => ?_⟩
        · obtain ⟨hdm, hdr, hdj⟩ := Delivery.mem_deliveriesOn.mp hd
          exact Delivery.mem_deliveriesOn.mpr ⟨cov.deliveries d hdm, hdr, hdj⟩
        · obtain ⟨-, hdr, hdj⟩ := Delivery.mem_deliveriesOn.mp hd
          exact Delivery.mem_deliveriesOn.mpr ⟨back' d hd, hdr, hdj⟩
    | merge cs =>
      -- The inputs of a Merge are Single (`shape_fits`).
      intro jc hjc
      obtain ⟨sh, k, hsh, -, -, -, -, hmerge⟩ := shape_fits valid w (Program.workflow?_eq_some hw).1 pl
        (Workflow.placement?_eq_some hpl).1
      rw [hshape] at hsh
      cases hsh
      obtain ⟨hcs, hsingle⟩ := hmerge cs rfl
      have hjc' : jc ∈ w.inputs pl.name := hcs ▸ hjc
      exact CoversViewAux.resolveSingle_covers hT cov hwT (Delivery.mem_inputs.mp hjc').1 (hsingle jc hjc)
        (hdone jc hjc)
  -- `T` invoked the placement only with triggers that `s` used as well; triggers identify invocations.
  have back : ∀ i ∈ T.invocationsOf path pl.name, i ∈ s.invocationsOf path pl.name := by
    intro i' hi'
    obtain ⟨him', hir', hip'⟩ := Delivery.mem_invocationsOf.mp hi'
    have same : ∀ i ∈ s.invocationsOf path pl.name, i.trigger = i'.trigger → i' ∈ s.invocationsOf path pl.name :=
      fun i hi ht => Settle.inv_unique (Settle.reachable hT).1 wkT (fwd i hi) hi' ht ▸ hi
    obtain ⟨-, w', pl', sh, hw', hpl', hinv, hsh, htrig, -⟩ := invT.own.invocations i' him'
    rw [hir', hwT] at hw'
    cases hw'
    rw [hip', hpl] at hpl'
    cases hpl'
    rw [hip', hshape] at hsh
    cases hsh
    rw [hir'] at htrig
    cases shape with
    | none =>
      obtain ⟨i, hi, ht⟩ := hdone
      exact same i hi (ht.trans htrig.symm)
    | entry =>
      obtain ⟨i, hi, ht⟩ := hdone
      exact same i hi (ht.trans htrig.symm)
    | single j c =>
      obtain ⟨src, inp, hres, ht⟩ := htrig
      obtain ⟨i, hi, hti⟩ := hdone.2 src inp
        ((show s.resolveSingle path j c = T.resolveSingle path j c from input) ▸ hres)
      exact same i hi (hti.trans ht.symm)
    | stream j c =>
      obtain ⟨src, d, ht, hd, hne⟩ := htrig
      obtain ⟨hdm, hdr, hdj, hds⟩ := delivery?_eq_some hd
      have hdS : d ∈ s.deliveriesOn path j :=
        (show s.streamEnd? path j c = T.streamEnd? path j c ∧ (s.deliveriesOn path j).Perm (T.deliveriesOn path j)
          from input).2.mem_iff.mpr (Delivery.mem_deliveriesOn.mpr ⟨hdm, hdr, hdj⟩)
      obtain ⟨i, hi, hti⟩ := hdone.2.2 (CoversViewAux.not_waitStream_of_invocable hinv) d hdS hne
      exact same i hi (hti.trans (hds.symm ▸ ht.symm))
    | merge cs => exact htrig.elim
  -- A result with an arm is the result of a judge call, which ended in `s` and is the same call in `T`
  -- (`CallConform` in both runs), so `s` has it as well.
  have armed : ∀ y ∈ T.resultsOf path pl.name, y.arm.isSome = true → y ∈ s.results := by
    intro y hy harm
    obtain ⟨hym, hyr, hyp⟩ := Delivery.mem_resultsOf.mp hy
    obtain ⟨hid, c, hc, hcid, hct⟩ := CoversViewAux.reachable_armedKeys hT y hym (by
      intro hn; rw [hn] at harm; cases harm)
    have ccT := (callConform valid h₂ (Or.inr done) c hc).1
    obtain ⟨-, i, hi, hir, hip, -⟩ := ccT.values y hym 0 (by rw [hid, hcid])
    obtain ⟨him, hiid⟩ := invocation?_eq_some hi
    have hiS := back i (Delivery.mem_invocationsOf.mpr ⟨him, hir.symm.trans hyr, hip.symm.trans hyp⟩)
    obtain ⟨himS, hirS, hipS⟩ := Delivery.mem_invocationsOf.mp hiS
    -- The placement is a function call or a branch.
    obtain ⟨hcidown, i₁, hi₁, hi₁id, pl₁, hpl₁, hctl⟩ := (Settle.reachable hT).1.callNone c hc hct
    obtain rfl : i = i₁ := wkT.invocation_eq_of_id him hi₁ (hiid.trans hi₁id.symm)
    rw [Settle.placementAt_eq (by rw [hirS]; exact hwT), hipS, hpl] at hpl₁
    cases hpl₁
    have hbody : (∃ f, pl.control = .call (.function f)) ∨ (∃ j arms, pl.control = .branch j arms) := by
      rcases hctl with ⟨f, -, hf, -⟩ | ⟨j, arms, hb, -⟩
      · exact Or.inl ⟨f, hf⟩
      · exact Or.inr ⟨j, arms, hb⟩
    obtain ⟨c₀, hc₀, hc₀id, hc₀o, hc₀t⟩ := (invocation_body hs i himS w pl (by rw [hirS]; exact hwS)
      (by rw [hipS]; exact hpl)).1 hbody
    have hend := (Delivery.invocationEnded_iff.mp (ended_s i hiS)).2.1 c₀ hc₀ hc₀o hc₀t
    obtain ⟨c₀', hc₀', -, -, -, -, -, -, -, -, heq⟩ := cov.calls c₀ hc₀
    rw [heq hend] at hc₀'
    obtain rfl : c₀ = c := wkT.call_eq_of_id hc₀' hc (hc₀id.trans (hiid.trans hcidown.symm))
    have ccS := (callConform valid h₁ us c₀ hc₀).1
    obtain ⟨y₀, hy₀, hy₀id⟩ := (ccS.results 0).mpr ((ccT.results 0).mp ⟨y, hym, by rw [hid, hcid]⟩)
    have e : y₀ = y := wkT.result_eq_of_id (cov.results y₀ hy₀) hym (by rw [hy₀id, hid, hcid])
    exact e ▸ hy₀
  refine ⟨?_, StableAux.triggers_nodup hs _ _, fun i hi => ?_, ?_, input⟩
  · exact (List.perm_ext_iff_of_nodup (StableAux.invocationsOf_nodup wkS _ _)
      (StableAux.invocationsOf_nodup wkT _ _)).mpr fun i => ⟨fwd i, back i⟩
  · -- Everything in `T` ended.
    rw [ended_s i hi]
    exact (Delivery.invocationEnded_iff.mpr ⟨(Delivery.invocationEnded_iff.mp (ended_s i hi)).1,
      fun c hc _ _ => sat.calls c hc, fun r hr _ _ => sat.runs r hr, fun e he _ => (sat.executions e he).1⟩).symm
  · rw [CoversViewAux.filterMap_arm, CoversViewAux.filterMap_arm (T.resultsOf path pl.name)]
    have nd : ∀ u : State, u.WellKeyed → ((u.resultsOf path pl.name).filter (·.arm.isSome)).Nodup :=
      fun u wk => StableAux.nodup_filter' _ (StableAux.nodup_filter' _ (StableAux.nodup_of_map' wk.results))
    refine List.Perm.filterMap _ ((List.perm_ext_iff_of_nodup (nd s wkS) (nd T wkT)).mpr fun y => ?_)
    rw [List.mem_filter, List.mem_filter]
    constructor
    · rintro ⟨hy, ha⟩
      obtain ⟨hym, hyr, hyp⟩ := Delivery.mem_resultsOf.mp hy
      exact ⟨Delivery.mem_resultsOf.mpr ⟨cov.results y hym, hyr, hyp⟩, ha⟩
    · rintro ⟨hy, ha⟩
      obtain ⟨-, hyr, hyp⟩ := Delivery.mem_resultsOf.mp hy
      exact ⟨Delivery.mem_resultsOf.mpr ⟨armed y hy ha, hyr, hyp⟩, ha⟩

/-- At a `closeExecution` of run 1, the complete run 2 has no task result of the execution beyond run
    1's: each comes from a task call that ended in run 1 (identical in both, `CallConform` in both) or
    from a task run that completed in run 1 (its `closeRun` read the same settlement), and its output is
    transformed in both or in neither. -/
theorem closeExecution_view_agree {eid : String} (h : StepCtx p env T s (.closeExecution eid) s') :
    ∀ r ∈ T.taskResults, r.execution = eid → r ∈ s.taskResults := by
  obtain ⟨tr, h₁⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  have valid := h.valid
  have hs := h₁.reachable
  have hT := h₂.reachable
  have wkS := hs.wellKeyed
  have wkT := hT.wellKeyed
  have us : Unstopped s := unstopped_of_step hs h.accepted h.unstopped
  have cov := h.covers
  have ownS := (Settle.reachable hs).1
  have ownT := (Settle.reachable hT).1
  obtain ⟨-, -, e, cc, -, he, -, hcc, htasks, houts, -, -⟩ := Step.closeExecution_inv h.accepted
  obtain ⟨hem, heid⟩ := execution?_eq_some he
  intro r hr hre
  -- What `T` says about `r` (`TaskResultShape`), and the execution of `T` for `e`.
  obtain ⟨e', he', he'id, spec, hspec', hso, hbody⟩ := CoversViewAux.reachable_taskResultShape valid hT r hr
  obtain ⟨e'', he'', a1, a2, a3, -, a5, a6, -⟩ := cov.executions e hem
  obtain rfl : e'' = e' := wkT.execution_eq_of_id he'' he' (a1.trans (heid.trans (hre.symm.trans he'id.symm)))
  obtain ⟨w, pl, hwS, -, -⟩ := Delivery.concurrencyOf_iff.mp hcc
  have hwT := CoversViewAux.covers_workflow? cov wkT hwS
  have hspec : s.taskSpec p e r.task = .ok spec := by
    rw [← CoversViewAux.taskSpec_eq_of_workflow? (by rw [a2, hwT, hwS]) a3]
    exact hspec'
  -- The task of `r` in `e`: it ended (the guard), and `T` has it unchanged.
  obtain ⟨e₂, he₂, he₂id, t₂, ht₂, ht₂n, -⟩ := (Limit.reachable_inv hT).results r hr
  obtain rfl : e'' = e₂ := wkT.execution_eq_of_id he'' he₂ (a1.trans (heid.trans (hre.symm.trans he₂id.symm)))
  have hname : r.task ∈ e.tasks.map (·.name) := by
    rw [← a5]
    exact List.mem_map.mpr ⟨t₂, ht₂, ht₂n⟩
  obtain ⟨ts₀, hts₀, hts₀n⟩ := List.mem_map.mp hname
  obtain ⟨hended, hnact, hnocancel, -⟩ := Delivery.taskEnded_iff.mp (List.all_eq_true.mp htasks ts₀ hts₀)
  have hsame : ∀ t' ∈ e''.tasks, t'.name = ts₀.name → t' = ts₀ := fun t' ht' hn => (a6 ts₀ hts₀ t' ht' hn).2 hended
  have hnp : ts₀.status ≠ .pending := fun h' => by rw [h'] at hended; cases hended
  have hnr : ts₀.status ≠ .ready := fun h' => by rw [h'] at hended; cases hended
  rw [← hts₀n] at hspec hspec'
  -- A task result of `s` under the key of `r`.
  obtain ⟨r₀, hr₀, k1, k2, k3⟩ : ∃ r₀ ∈ s.taskResults, r₀.execution = eid ∧ r₀.task = r.task ∧ r₀.index = r.index := by
    cases hb : spec.body with
    | function f =>
      by_cases hnb : NotBegun s e ts₀.name
      · -- The task failed its input transform in `s` (`TaskConform.begun`), so with the same behavior it
        -- never began in `T` (`TaskConform.input`), and `T` has no result of it (`Prov.taskResultSrc`).
        exfalso
        obtain ⟨hfailed, hin⟩ := (taskConform valid h₁ us).begun e hem ts₀ hts₀ hnp hnr hnb
        obtain ⟨tid, hdecl⟩ := (CoversViewAux.reachable_taskStatusInv hs).failed e hem ts₀ hts₀ hfailed hnb spec hspec
        have hts₀T : ts₀ ∈ e''.tasks := hsame t₂ ht₂ (ht₂n.trans hts₀n.symm) ▸ ht₂
        have hinT := (taskConform valid h₂ (Or.inr h.done)).input e'' he'' ts₀ hts₀T spec hspec'
          (by rw [hfailed]; exact fun h' => by cases h')
        rw [hdecl] at hinT
        simp only at hinT
        rw [a1] at hinT
        rcases hinT with ⟨-, -, -, hnbT⟩ | ⟨v, hv, -⟩
        · rcases (Settle.reachable hT).2.2.1.taskResultSrc r hr with ⟨c, hc, hco, hct⟩ | ⟨R, hR, hRo, hRt, -⟩
          · have hkey := (ownT.callTask c hc r.task hct).1
            have hc' := wkT.call?_of_mem hc
            rw [hkey, hco, hre, ← heid, ← a1, ← hts₀n, hnbT.1] at hc'
            cases hc'
          · exact hnbT.2 R hR ⟨by rw [hRo, hre, ← heid, a1], by rw [hRt, hts₀n]⟩
        · rw [hin] at hv
          cases hv
      · -- The task began in `s` with its call (a run would mean a workflow body), and the call ended, so
        -- it is the same call in `T`; `CallConform` in both runs gives the same result indices.
        cases hc₀ : s.call? (Key.task e.id ts₀.name) with
        | none =>
          obtain ⟨R, hR, hRo, hRt⟩ : ∃ R ∈ s.runs, R.owner = some e.id ∧ R.task = some ts₀.name :=
            Classical.byContradiction fun hno => hnb ⟨hc₀, fun R hR hRR => hno ⟨R, hR, hRR⟩⟩
          obtain ⟨e₃, he₃, he₃o, -, spec₃, wf, out, hspec₃, hbody₃⟩ := ownS.runTask R hR ts₀.name hRt
          obtain rfl : e₃ = e := wkS.execution_eq_of_id he₃ hem (Option.some.inj (he₃o.symm.trans hRo))
          rw [Settle.taskSpec_det hspec₃ hspec, hb] at hbody₃
          cases hbody₃
        | some c₀ =>
          obtain ⟨hc₀m, hc₀id⟩ := call?_eq_some hc₀
          obtain ⟨name', hct⟩ : ∃ name', c₀.task = some name' := by
            cases hct : c₀.task with
            | none =>
              exfalso
              obtain ⟨hid, i, hi, hiid, -⟩ := ownS.callNone c₀ hc₀m hct
              rw [hc₀id, ← hiid, ownS.invId i hi] at hid
              exact CoversViewAux.invocation_ne_task hid.symm
            | some name' => exact ⟨name', rfl⟩
          obtain ⟨ho, hn'⟩ := CoversViewAux.task_inj ((ownS.callTask c₀ hc₀m name' hct).1.symm.trans hc₀id)
          have hend : c₀.status.ended = true := by
            cases hst : c₀.status with
            | running =>
              exact absurd ((Delivery.Reachable.inv hs).dyn.taskActive c₀ hc₀m name' hct (Or.inl hst) e hem ho.symm
                ts₀ hts₀ hn'.symm) hnact
            | fetching =>
              exact absurd ((Delivery.Reachable.inv hs).dyn.taskActive c₀ hc₀m name' hct (Or.inr hst) e hem ho.symm
                ts₀ hts₀ hn'.symm) hnact
            | cancelling => exact absurd hst (hnocancel c₀ hc₀m ho (by rw [hct, hn']))
            | _ => rfl
          obtain ⟨c₀', hc₀', -, -, -, -, -, -, -, -, heq⟩ := cov.calls c₀ hc₀m
          rw [heq hend] at hc₀'
          have ccS := (callConform valid h₁ us c₀ hc₀m).1
          have ccT := (callConform valid h₂ (Or.inr h.done) c₀ hc₀').1
          obtain ⟨r₀, hr₀, b1, b2, b3⟩ := (ccS.taskResults name' hct r.index).mpr
            ((ccT.taskResults name' hct r.index).mp ⟨r, hr, by rw [hre, ← heid, ho], by rw [hn', hts₀n], rfl⟩)
          exact ⟨r₀, hr₀, by rw [b1, ho, heid], by rw [b2, hn', hts₀n], b3⟩
    | workflow wf out =>
      -- The index-0 result of a task run: the task succeeded, identically in `s`, which recorded it.
      rcases hbody with ⟨f, hf⟩ | ⟨hidx, ts, hts, htsn, htss⟩
      · rw [hf] at hb
        cases hb
      obtain rfl : ts = ts₀ := hsame ts hts (htsn.trans hts₀n.symm)
      obtain ⟨r₀, hr₀, b1, b2, b3⟩ := (CoversViewAux.reachable_taskStatusInv hs).succeeded e hem ts hts₀ htss spec
        hspec (fun f hf => by rw [hb] at hf; cases hf)
      exact ⟨r₀, hr₀, by rw [b1, heid], by rw [b2, hts₀n], by rw [b3, hidx]⟩
  -- `T` has `r₀` under that key, which is `r`; its output is transformed in both runs or in neither.
  obtain ⟨r', hr', c1, c2, c3, c4, c5⟩ := cov.taskResults r₀ hr₀
  have e' : r' = r := Limit.eq_of_key wkT.taskResults hr' hr (by
    show (r'.execution, r'.task, r'.index) = (r.execution, r.task, r.index)
    rw [c1, c2, c3, k1, k2, k3, hre])
  subst e'
  by_cases hp : r₀.output = .pending
  · -- A pending result in `s` belongs to a task outside the output (the guard), so it is pending in `T`.
    have hnot : spec.output.isSome = false := by
      cases hsome : spec.output.isSome with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨cc', hcc', hfind⟩ := State.taskSpec_eq_ok.mp hspec
        obtain rfl : cc' = cc := Settle.concurrencyOf_det hcc' hcc
        have hmem : r₀ ∈ s.taskResults.filter fun x => x.execution == eid &&
            ((cc'.tasks.filter (·.output.isSome)).map (·.name)).contains x.task := by
          refine List.mem_filter.mpr ⟨hr₀, ?_⟩
          simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_map, List.mem_filter]
          refine ⟨k1, spec, ⟨List.mem_of_find?_eq_some hfind, hsome⟩, ?_⟩
          rw [k2, ← hts₀n]
          simpa using List.find?_some hfind
        have := List.all_eq_true.mp houts r₀ hmem
        rw [hp] at this
        cases this
    have hpT : r'.output = .pending := by
      refine Decidable.byContradiction fun hne => ?_
      rw [hso hne] at hnot
      cases hnot
    rw [CoversViewAux.taskResult_ext c1 c2 c3 c4 (hpT.trans hp.symm)]
    exact hr₀
  · rw [c5 hp]
    exact hr₀

end CoversView

end Suimon.Round3
