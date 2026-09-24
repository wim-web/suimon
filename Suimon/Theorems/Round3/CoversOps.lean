import Suimon.Theorems.Round3.CoversView
import Suimon.Theorems.Round3.CoversOpsBase

namespace Suimon.Round3
open State

/-! ## [22] Round3/CoversOps.lean — task F4

The containment step of every operation that neither reports a call nor closes something. Each lemma
must also keep the frozen footprints of what `s` already closed (`step_frozen`). -/

section CoversOps
variable {p : Definition} {env : Env} {s s' T : State}

theorem covers_start {input : Option Value} (h : StepCtx p env T s (.start input) s') : Covers p T s' := by
  obtain ⟨tr, hrun⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv h.accepted
  obtain rfl : s = {} := (Delivery.Reachable.inv hrun.reachable).fresh hst
  -- The root run of `T` runs the main workflow on the same input.
  obtain ⟨rT, hrT, -⟩ := Delivery.root_of_done h.done
  obtain ⟨hrTm, hrTp⟩ := State.run?_eq_some hrT
  obtain ⟨hw, hin, ho, htk⟩ := CoversOpsAux.Conforming.root h₂ rT hrTm hrTp
  have hconf : input = env.input := h.conforms
  refine ⟨fun r hr => ?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨rT, hrTm, hrTp, hw, hin.trans hconf.symm, ho, htk⟩
theorem covers_fetch {id : String} (h : StepCtx p env T s (.fetch id) s') : Covers p T s' := by
  obtain ⟨-, -, c, hc, -, h4, rfl⟩ := Step.fetch_inv h.accepted
  have cov := h.covers
  refine CoversOpsAux.covers_mk h cov.runs cov.invocations (fun x hx => ?_) cov.executions cov.results
    cov.taskResults cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
  rcases State.mem_setCall_calls hx with rfl | hx
  · obtain ⟨c', hc', a1, a2, a3, a4, a5, a6, a7, a8, -⟩ := cov.calls c (State.call?_eq_some hc).1
    exact ⟨c', hc', a1, a2, a3, a4, a5, a6, a7, a8, fun hend => by simp [CallStatus.ended] at hend⟩
  · exact cov.calls x hx
/-- A cancel stops the workflow, so it never leads to an unstopped state. -/
theorem covers_cancel (h : StepCtx p env T s .cancel s') : Covers p T s' := by
  obtain ⟨tr, hrun⟩ := h.run
  obtain ⟨hst, ⟨hrunning, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv h.accepted
  · exfalso
    rcases h.unstopped with hr | hd
    · simp at hr
    · exact CoversOpsAux.not_done_of_running hrun.reachable hst hrunning rfl hd
  · have cov := h.covers
    exact CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls cov.executions cov.results cov.taskResults
      cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
theorem covers_conclude (h : StepCtx p env T s .conclude s') : Covers p T s' := by
  have cov := h.covers
  obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv h.accepted
  · refine CoversOpsAux.covers_mk h (fun x hx => ?_) cov.invocations cov.calls cov.executions cov.results
      cov.taskResults cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
    rcases State.mem_setRun_runs hx with rfl | hx
    · exact cov.runs r (State.run?_eq_some hr).1
    · exact cov.runs x hx
  · exact CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls cov.executions cov.results cov.taskResults
      cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
/-- `invoke` adds an invocation `T` has: `Saturated.invoked` finds it for the same trigger, whose input is
    the same by `InputStable` (the trigger's delivery is the same record); its call, run or execution is
    created with it in both runs. -/
theorem covers_invoke {path : Path} {name : String} {trigger : Option ResultId}
    (h : StepCtx p env T s (.invoke path name trigger) s') : Covers p T s' := by
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have invT := Delivery.Reachable.inv hT
  have CT := CoversOpsAux.Reachable.created hT
  have cov := h.covers
  obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, hinput, rfl, -, -, hbody⟩ := Step.invoke_inv h.accepted
  obtain ⟨-, hrp⟩ := State.run?_eq_some hr
  obtain ⟨hplm, hpln⟩ := Workflow.placement?_eq_some hpl
  have hwT : T.workflow? p path = some w :=
    CoversOpsAux.covers_workflow? cov wkT (Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩)
  obtain ⟨rT, hrT, hrTw, hrTin, -, -⟩ := CoversOpsAux.covers_run cov wkT hr
  obtain ⟨hrTm, hrTp⟩ := State.run?_eq_some hrT
  have hinputT : Step.invocationInput p T rT w name trigger = .ok input :=
    CoversOpsAux.covers_invocationInput cov hT (hrTp.trans hrp.symm) hrTin (hrp ▸ hwT) hinput
  -- `T` invoked the placement for the same trigger (`Saturated.invoked`).
  have hinv : Settle.invocable pl.control = true := by
    rcases hbody with ⟨f, -, hf, -⟩ | ⟨j, arms, hb, -⟩ | ⟨wf, out, hwf, -⟩ | ⟨c, hc, -⟩
    · rw [hf]; rfl
    · rw [hb]; rfl
    · rw [hwf]; rfl
    · rw [hc]; rfl
  have hsat := (saturated h.valid hT h.done).invoked rT hrTm w (hrTw ▸ hw) pl hplm hinv
  rw [hpln, hrTp] at hsat
  obtain ⟨i', hi'm, hi'run, hi'pl, hi'tr⟩ :
      ∃ i' ∈ T.invocations, i'.run = path ∧ i'.placement = name ∧ i'.trigger = trigger := by
    rcases Step.invocationInput_inv hinput with ⟨hsh, rfl, -⟩ | ⟨hsh, rfl, -⟩ | ⟨j, c, src, hsh, rfl, hres⟩ |
        ⟨j, c, src, d, hsh, rfl, hd, hout⟩
    · rw [hsh] at hsat
      obtain ⟨i', hi', htr⟩ := hsat
      obtain ⟨hm, h1, h2⟩ := Delivery.mem_invocationsOf.mp hi'
      exact ⟨i', hm, h1, h2, htr⟩
    · rw [hsh] at hsat
      obtain ⟨i', hi', htr⟩ := hsat
      obtain ⟨hm, h1, h2⟩ := Delivery.mem_invocationsOf.mp hi'
      exact ⟨i', hm, h1, h2, htr⟩
    · rw [hsh] at hsat
      obtain ⟨-, hc, -, hk⟩ := Delivery.shape?_single hsh
      rw [hrp] at hres
      obtain ⟨i', hi', htr⟩ := hsat src input (CoversOpsAux.covers_resolveSingle cov hT hwT hc hk hres)
      obtain ⟨hm, h1, h2⟩ := Delivery.mem_invocationsOf.mp hi'
      exact ⟨i', hm, h1, h2, htr⟩
    · rw [hsh] at hsat
      obtain ⟨hdm, hdr, hdj, hds⟩ := State.delivery?_eq_some hd
      have hdT : d ∈ T.deliveriesOn path j :=
        Delivery.mem_deliveriesOn.mpr ⟨cov.deliveries d hdm, hdr.trans hrp, hdj⟩
      have hnf : d.outcome ≠ .failed := by
        rcases hout with ⟨v, hv, -⟩ | ⟨hv, -⟩ <;> rw [hv] <;> exact fun h => nomatch h
      obtain ⟨i', hi', htr⟩ := hsat d hdT hnf
      obtain ⟨hm, h1, h2⟩ := Delivery.mem_invocationsOf.mp hi'
      exact ⟨i', hm, h1, h2, htr.trans (congrArg some hds)⟩
  have hi'id : i'.id = Key.invocation path name trigger := by
    rw [(invT.own.invocations i' hi'm).1, hi'run, hi'pl, hi'tr]
  -- Its input is the one run 1 computed (`InputStable` of `T`).
  have hi'in : i'.input = input := by
    obtain ⟨r₂, w₂, hr₂, hw₂, hin₂⟩ := Reachable.inputStable h.valid hT i' hi'm
    rw [hi'run, hrT] at hr₂
    cases hr₂
    rw [hrTw, hw] at hw₂
    cases hw₂
    rw [hi'pl, hi'tr, hinputT] at hin₂
    exact (Except.ok.inj hin₂).symm
  have hwi : T.workflow? p i'.run = some w := by rw [hi'run]; exact hwT
  have hpli : w.placement? i'.placement = some pl := by rw [hi'pl]; exact hpl
  have newInv : ∀ x ∈ s.invocations ++
      [{ id := Key.invocation path name trigger, run := path, placement := name, trigger, input }],
      ∃ i ∈ T.invocations, i.id = x.id ∧ i.run = x.run ∧ i.placement = x.placement ∧ i.trigger = x.trigger ∧
        i.input = x.input ∧ (x.status ≠ .active → i = x) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact cov.invocations x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨i', hi'm, hi'id, hi'run, hi'pl, hi'tr, hi'in, fun hna => absurd rfl hna⟩
  have body := invocation_body hT i' hi'm w pl hwi hpli
  -- The call of a function or a judge: its fields come from the placement (`CallOwned`, `Created`).
  have callOf : ∀ c' ∈ T.calls, c'.id = i'.id → c'.owner = i'.id → c'.task = none →
      c'.input = input ∧ c'.timeout = pl.timeout ∧ c'.policy = pl.policy ∧
      ((∃ f decl, pl.control = .call (.function f) ∧ p.function? f = some decl ∧ c'.target = .function f ∧
          c'.stream = (decl.output.kind == .stream)) ∨
       (∃ j arms, pl.control = .branch j arms ∧ c'.target = .judge j ∧ c'.stream = false)) := by
    intro c' hc'm hc'id hc'o hc't
    obtain ⟨hcin, hcpol⟩ := CT.invCall c' hc'm hc't i' hi'm hc'o.symm
    obtain ⟨hto, hpo⟩ := hcpol w pl hwi hpli
    refine ⟨hcin.trans hi'in, hto, hpo, ?_⟩
    rcases invT.own.calls c' hc'm with ⟨-, -, i₂, hi₂, hi₂id, w₂, pl₂, hw₂, hpl₂, hcase⟩ | ⟨name', ht', -⟩
    · obtain rfl : i₂ = i' := wkT.invocation_eq_of_id hi₂ hi'm (hi₂id.trans hc'o)
      rw [hwi] at hw₂
      cases hw₂
      rw [hpli] at hpl₂
      cases hpl₂
      exact hcase
    · rw [hc't] at ht'
      cases ht'
  rcases hbody with ⟨f, decl, hf, hdecl, -, rfl⟩ | ⟨judge, arms, hb, -, rfl⟩ | ⟨wf, out, hwf, -, rfl⟩ |
      ⟨c, hc, -, rfl⟩
  · -- A function call: `T` created the same call.
    obtain ⟨c', hc'm, hc'id, hc'o, hc't⟩ := body.1 (Or.inl ⟨f, hf⟩)
    obtain ⟨hcin, hto, hpo, hcase⟩ := callOf c' hc'm hc'id hc'o hc't
    obtain ⟨htg, hstr⟩ : c'.target = .function f ∧ c'.stream = (decl.output.kind == .stream) := by
      rcases hcase with ⟨f₂, d₂, hf₂, hd₂, htg, hstr⟩ | ⟨j, arms, hb, -⟩
      · rw [hf] at hf₂
        cases hf₂
        rw [hdecl] at hd₂
        cases hd₂
        exact ⟨htg, hstr⟩
      · rw [hf] at hb
        cases hb
    refine CoversOpsAux.covers_mk h cov.runs newInv (fun x hx => ?_) cov.executions cov.results cov.taskResults
      cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact cov.calls x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨c', hc'm, hc'id.trans hi'id, hc'o.trans hi'id, hc't, htg, hcin, hstr, hto, hpo, fun hend => nomatch hend⟩
  · -- A branch: `T` created the same judge call.
    obtain ⟨c', hc'm, hc'id, hc'o, hc't⟩ := body.1 (Or.inr ⟨judge, arms, hb⟩)
    obtain ⟨hcin, hto, hpo, hcase⟩ := callOf c' hc'm hc'id hc'o hc't
    obtain ⟨htg, hstr⟩ : c'.target = .judge judge ∧ c'.stream = false := by
      rcases hcase with ⟨f₂, d₂, hf₂, -⟩ | ⟨j, arms', hb', htg, hstr⟩
      · rw [hb] at hf₂
        cases hf₂
      · rw [hb] at hb'
        cases hb'
        exact ⟨htg, hstr⟩
    refine CoversOpsAux.covers_mk h cov.runs newInv (fun x hx => ?_) cov.executions cov.results cov.taskResults
      cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact cov.calls x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨c', hc'm, hc'id.trans hi'id, hc'o.trans hi'id, hc't, htg, hcin, hstr, hto, hpo, fun hend => nomatch hend⟩
  · -- A sub-workflow call: `T` created the same run.
    obtain ⟨r', hr'm, hr'p, hr'o, hr't, hr'w⟩ := body.2.1 wf out hwf
    have hr'in := CT.invRun r' hr'm hr't i' hi'm hr'o
    refine CoversOpsAux.covers_mk h (fun x hx => ?_) newInv cov.calls cov.executions cov.results cov.taskResults
      cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact cov.runs x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨r', hr'm, by rw [hr'p, hi'run, hi'id], hr'w, hr'in.trans hi'in, by rw [hr'o, hi'id], hr't⟩
  · -- A concurrency: `T` created the same execution, with the same tasks.
    obtain ⟨e', he'm, he'id⟩ := body.2.2 c hc
    obtain ⟨i₂, hi₂, hi₂id, hi₂run, hi₂pl, -⟩ := invT.own.executions e' he'm
    obtain rfl : i₂ = i' := wkT.invocation_eq_of_id hi₂ hi'm (hi₂id.trans he'id)
    have he'in := CT.exec e' he'm i₂ hi₂ he'id.symm
    have hccT : T.concurrencyOf p e' = .ok c :=
      Delivery.concurrencyOf_iff.mpr ⟨w, pl, by rw [← hi₂run]; exact hwi, by rw [← hi₂pl]; exact hpli, hc⟩
    have hnames := CT.names e' he'm c hccT
    have sat := saturated h.valid hT h.done
    have tcT := taskConform h.valid h₂ (Or.inr h.done)
    refine CoversOpsAux.covers_mk h cov.runs newInv cov.calls (fun x hx => ?_) cov.results cov.taskResults
      cov.deliveries rfl ?_
    · rcases List.mem_append.mp hx with hx | hx
      · exact cov.executions x hx
      · rw [List.mem_singleton.mp hx]
        refine ⟨e', he'm, he'id.trans hi'id, hi₂run.symm.trans hi'run, hi₂pl.symm.trans hi'pl, he'in.trans hi'in,
          by rw [hnames, List.map_map]; rfl, fun t ht t' ht' hn => ?_, fun hcomp => nomatch hcomp⟩
        obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp ht
        refine ⟨fun hnp => ?_, fun hend => ?_⟩
        · -- The concurrency takes no input, so no task has a declared input transform: `T`'s task has none.
          have hci : c.input = none := by
            cases hci : c.input
            · rfl
            · rw [hci] at hnp
              exact absurd rfl hnp
          obtain ⟨spec, hfind⟩ : ∃ spec, c.tasks.find? (·.name == t'.name) = some spec := by
            rcases hf : c.tasks.find? (·.name == t'.name) with _ | spec
            · exact absurd (by rw [hn]; exact beq_self_eq_true _) (List.find?_eq_none.mp hf ts hts)
            · exact ⟨spec, hf⟩
          have hspecm := List.mem_of_find?_eq_some hfind
          have hne : t'.status ≠ .pending := by
            intro hp
            have := (sat.executions e' he'm).2 t' ht'
            rw [hp] at this
            cases this
          have hm := tcT.input e' he'm t' ht' spec (State.taskSpec_eq_ok.mpr ⟨c, hccT, hfind⟩) hne
          cases hsi : spec.input with
          | none => rw [hsi] at hm; exact hm
          | some tf =>
            cases tf with
            | discard => rw [hsi] at hm; exact hm
            | declared tid =>
              have := RunConformAux.declared_input h.valid hccT hspecm hsi
              rw [hci] at this
              cases this
        · revert hend
          split <;> exact fun h => nomatch h
    · intro x hx hcomp
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨x, hx, rfl, hcomp⟩
      · rw [List.mem_singleton.mp hx] at hcomp
        cases hcomp
theorem covers_deliver {path : Path} {j : Nat} {source : ResultId} {value : Option Value}
    (h : StepCtx p env T s (.deliver path j source value) s') : Covers p T s' := by
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have cov := h.covers
  obtain ⟨-, -, w, c, outcome, hdt, hout, rfl⟩ := Step.deliver_inv h.accepted
  refine CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls cov.executions cov.results cov.taskResults
    (fun d hd => ?_) rfl fun e he hc => ⟨e, he, rfl, hc⟩
  rcases List.mem_append.mp hd with hd | hd
  · exact cov.deliveries d hd
  · rw [List.mem_singleton.mp hd]
    -- `T` delivered the same result on the same connection, with the behavior's answer.
    obtain ⟨dT, hdTm, hdTr, hdTj, hdTs, hconf⟩ := CoversOpsAux.covers_delivery h hdt
    have hsame : dT.outcome = outcome := by
      rcases hout with ⟨tid, v, htr, rfl, rfl⟩ | ⟨htr, rfl, rfl⟩
      · have hv : env.behavior.transform path j source = some v := h.conforms v rfl
        rw [htr] at hconf
        simp only [hv] at hconf
        exact hconf
      · rw [htr] at hconf
        exact hconf
    obtain ⟨dr, dc, ds, dout⟩ := dT
    simp only at hdTr hdTj hdTs hsame
    rw [← hdTr, ← hdTj, ← hdTs, ← hsame]
    exact hdTm
theorem covers_transformFailed {path : Path} {j : Nat} {source : ResultId}
    (h : StepCtx p env T s (.transformFailed path j source) s') : Covers p T s' := by
  have cov := h.covers
  obtain ⟨hst, hrunning, w, c, tid, target, hdt, htr, -, hs'⟩ := Step.transformFailed_inv h.accepted
  have hpol := CoversOpsAux.StepCtx.policy h hs' rfl hst hrunning
  rw [hpol, State.fail_continue] at hs'
  subst hs'
  refine CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls cov.executions cov.results cov.taskResults
    (fun d hd => ?_) rfl fun e he hc => ⟨e, he, rfl, hc⟩
  rcases List.mem_append.mp hd with hd | hd
  · exact cov.deliveries d hd
  · rw [List.mem_singleton.mp hd]
    -- `T` delivered the same result on the same connection, and its transform failed there as well.
    obtain ⟨dT, hdTm, hdTr, hdTj, hdTs, hconf⟩ := CoversOpsAux.covers_delivery h hdt
    have hnone : env.behavior.transform path j source = none := h.conforms
    rw [htr] at hconf
    simp only [hnone] at hconf
    obtain ⟨dr, dc, ds, dout⟩ := dT
    simp only at hdTr hdTj hdTs hconf
    rw [← hdTr, ← hdTj, ← hdTs, ← hconf]
    exact hdTm
theorem covers_taskInput {eid name : String} {value : Option Value}
    (h : StepCtx p env T s (.taskInput eid name value) s') : Covers p T s' := by
  obtain ⟨tr, hrun⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have cov := h.covers
  obtain ⟨-, -, e, ts, spec, he, hts, hpend, hspec, hin, rfl⟩ := Step.taskInput_inv h.accepted
  obtain ⟨hem, heid⟩ := State.execution?_eq_some he
  have htsm := List.mem_of_find?_eq_some hts
  have hname := Delivery.find?_name_of_task hts
  have hopen := CoversOpsAux.open_of_task hrun.reachable hem htsm (by rw [hpend]; rfl)
  have sat := saturated h.valid hT h.done
  have tc := taskConform h.valid h₂ (Or.inr h.done)
  refine CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls
    (CoversOpsAux.covers_setTask cov hem hopen fun e' he' hid hrun' hpl _ t' ht' hn =>
      ⟨fun _ => ?_, fun hend => by cases hend⟩)
    cov.results cov.taskResults cov.deliveries rfl (CoversOpsAux.complete_setTask hem)
  -- `T`'s copy of the task took the behavior's input as well.
  have hn' : t'.name = name := hn.trans hname
  have hspecT : T.taskSpec p e' t'.name = .ok spec := by
    rw [hn']
    exact CoversOpsAux.covers_taskSpec cov wkT hrun' hpl hspec
  have hne : t'.status ≠ .pending := by
    intro hp
    have := (sat.executions e' he').2 t' ht'
    rw [hp] at this
    cases this
  have hm := tc.input e' he' t' ht' spec hspecT hne
  rcases hin with ⟨tid, v, hsi, rfl⟩ | ⟨hsi, rfl⟩
  · rw [hsi] at hm
    have hv : env.behavior.taskInput eid name = some v := h.conforms v rfl
    rw [hid, heid, hn', hv] at hm
    rcases hm with ⟨h1, -⟩ | ⟨v', h1, h2⟩
    · cases h1
    · cases h1
      exact h2
  · rw [hsi] at hm
    exact hm
theorem covers_taskInputFailed {eid name : String}
    (h : StepCtx p env T s (.taskInputFailed eid name) s') : Covers p T s' := by
  obtain ⟨tr, hrun⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have cov := h.covers
  obtain ⟨hst, hrunning, e, ts, spec, tid, he, hts, hpend, hspec, hsi, hs'⟩ := Step.taskInputFailed_inv h.accepted
  have hpol := CoversOpsAux.StepCtx.policy h hs' rfl hst hrunning
  rw [hpol, State.fail_continue] at hs'
  subst hs'
  obtain ⟨hem, heid⟩ := State.execution?_eq_some he
  have htsm := List.mem_of_find?_eq_some hts
  have hname := Delivery.find?_name_of_task hts
  have hopen := CoversOpsAux.open_of_task hrun.reachable hem htsm (by rw [hpend]; rfl)
  have hinput : ts.input = none := (CoversOpsAux.Reachable.created hrun.reachable).pending e hem ts htsm hpend
  have sat := saturated h.valid hT h.done
  have tc := taskConform h.valid h₂ (Or.inr h.done)
  have hnone : env.behavior.taskInput eid name = none := h.conforms
  refine CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls
    (CoversOpsAux.covers_setTask cov hem hopen fun e' he' hid hrun' hpl _ t' ht' hn => ?_)
    cov.results cov.taskResults cov.deliveries rfl (CoversOpsAux.complete_setTask hem)
  -- `T`'s copy of the task failed its input transform as well.
  have hn' : t'.name = name := hn.trans hname
  have hspecT : T.taskSpec p e' t'.name = .ok spec := by
    rw [hn']
    exact CoversOpsAux.covers_taskSpec cov wkT hrun' hpl hspec
  have hne : t'.status ≠ .pending := by
    intro hp
    have := (sat.executions e' he').2 t' ht'
    rw [hp] at this
    cases this
  have hm := tc.input e' he' t' ht' spec hspecT hne
  rw [hsi] at hm
  rw [hid, heid, hn', hnone] at hm
  rcases hm with ⟨-, hfail, hinp, -⟩ | ⟨v, h1, -⟩
  · have ht' : t' = { ts with status := .failed } := by
      obtain ⟨n1, i1, st1⟩ := t'
      obtain ⟨n2, i2, st2⟩ := ts
      simp only at hn hinp hfail hinput ⊢
      rw [hn, hinp, hfail, hinput]
    exact ⟨fun _ => by rw [ht'], fun _ => ht'⟩
  · cases h1
/-- `beginTask` adds a task call or run that `T` has: the task ended in `T`, did not fail its input
    (`TaskConform.input` with the same behavior), hence began (`TaskConform.begun`). Which task got a
    free slot first is irrelevant. -/
theorem covers_beginTask {eid name : String} (h : StepCtx p env T s (.beginTask eid name) s') : Covers p T s' := by
  obtain ⟨tr, hrun⟩ := h.run
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have invT := Delivery.Reachable.inv hT
  have CT := CoversOpsAux.Reachable.created hT
  have cov := h.covers
  obtain ⟨-, -, e, cc, ts, spec, he, hopen, -, hts, hready, -, hspec, hbody⟩ := Step.beginTask_inv h.accepted
  obtain ⟨hem, heid⟩ := State.execution?_eq_some he
  have htsm := List.mem_of_find?_eq_some hts
  have hname := Delivery.find?_name_of_task hts
  -- The task of `T`: it ended, with the input of run 1.
  obtain ⟨eT, heTm, -, heTid, heTrun, heTpl, heTnames, heTtasks⟩ := CoversOpsAux.covers_execution cov wkT hem
  obtain ⟨tT, htTm, htTn⟩ := CoversOpsAux.task_of_names heTnames htsm
  have htTn' : tT.name = name := htTn.trans hname
  have htTin : tT.input = ts.input := (heTtasks ts htsm tT htTm htTn).1 (by rw [hready]; exact fun h => nomatch h)
  have hspecT : T.taskSpec p eT name = .ok spec := CoversOpsAux.covers_taskSpec cov wkT heTrun heTpl hspec
  -- It began: a task that fails without beginning has a declared input transform (`Created.failed`), and
  -- the task of run 1, ready, got a value from it, so it did not fail in `T`.
  have began : ¬ NotBegun T eT name := by
    intro hnb
    have hend : tT.status.ended = true := ((saturated h.valid hT h.done).executions eT heTm).2 tT htTm
    have hnp : tT.status ≠ .pending := fun hp => by rw [hp] at hend; cases hend
    have hnr : tT.status ≠ .ready := fun hp => by rw [hp] at hend; cases hend
    obtain ⟨hfail, hnoneT⟩ := (taskConform h.valid h₂ (Or.inr h.done)).begun eT heTm tT htTm hnp hnr
      (by rw [htTn']; exact hnb)
    rcases CT.failed eT heTm tT htTm hfail with hj | ⟨spec', tid, hspec', hin'⟩
    · exact hj (by rw [htTn']; exact hnb)
    · rw [htTn', hspecT] at hspec'
      cases hspec'
      have hm := (taskConform h.valid hrun (CoversOpsAux.StepCtx.unstopped₀ h)).input e hem ts htsm spec
        (by rw [hname]; exact hspec) (by rw [hready]; exact fun h => nomatch h)
      rw [hin'] at hm
      rcases hm with ⟨-, hf, -⟩ | ⟨v, hv, -⟩
      · rw [hready] at hf
        cases hf
      · rw [htTn', heTid] at hnoneT
        rw [hname, hnoneT] at hv
        cases hv
  have began' : (∃ c', T.call? (Key.task eT.id name) = some c') ∨
      ∃ r ∈ T.runs, r.owner = some eT.id ∧ r.task = some name := by
    rcases hc : T.call? (Key.task eT.id name) with _ | c'
    · refine Or.inr ?_
      by_cases hr : ∃ r ∈ T.runs, r.owner = some eT.id ∧ r.task = some name
      · exact hr
      · exact absurd ⟨hc, fun r hr' hro => hr ⟨r, hr', hro⟩⟩ began
    · exact Or.inl ⟨c', rfl⟩
  -- A call of `T` under the task's identity is the task's call.
  have taskCall : ∀ c', T.call? (Key.task eT.id name) = some c' →
      c' ∈ T.calls ∧ c'.id = Key.task e.id name ∧ c'.owner = e.id ∧ c'.task = some name := by
    intro c' hc'
    obtain ⟨hc'm, hc'id⟩ := State.call?_eq_some hc'
    rw [heTid] at hc'id
    rcases invT.own.calls c' hc'm with ⟨-, hio, i, hi, hid, -⟩ | ⟨name', ht', hid', -⟩
    · exfalso
      rw [← hid, (invT.own.invocations i hi).1] at hio
      exact RunConformAux.invocation_ne_task (hio.symm.trans hc'id)
    · obtain ⟨ho, hn⟩ := RunConformAux.task_inj (hid'.symm.trans hc'id)
      exact ⟨hc'm, hc'id, ho, by rw [ht', hn]⟩
  rcases hbody with ⟨f, decl, hf, hdecl, -, rfl⟩ | ⟨wf, out, hwf, -, rfl⟩
  · -- A function body: `T` began the task with the same call.
    obtain ⟨c', hc'⟩ : ∃ c', T.call? (Key.task eT.id name) = some c' := by
      rcases began' with hc | ⟨r, hr, ho, htask⟩
      · exact hc
      · obtain ⟨-, h2⟩ := CT.taskRun r hr name htask eT heTm ho
        obtain ⟨out', hout'⟩ := h2 spec hspecT
        rw [hf] at hout'
        cases hout'
    obtain ⟨hc'm, hc'id, hc'o, hc't⟩ := taskCall c' hc'
    obtain ⟨h1, h2⟩ := CT.taskCall c' hc'm name hc't eT heTm (heTid.trans hc'o.symm)
    obtain ⟨hto, hpo, f', decl', hf', hdecl', htg, hstr⟩ := h2 spec hspecT
    rw [hf] at hf'
    cases hf'
    rw [hdecl] at hdecl'
    cases hdecl'
    refine CoversOpsAux.covers_mk h cov.runs cov.invocations (fun x hx => ?_)
      (CoversOpsAux.covers_setTask cov hem hopen fun e' he' hid hrun' hpl a6 t' ht' hn =>
        ⟨fun _ => (a6 ts htsm t' ht' hn).1 (by rw [hready]; exact fun h => nomatch h), fun hend => nomatch hend⟩)
      cov.results cov.taskResults cov.deliveries rfl (CoversOpsAux.complete_setTask hem)
    rcases List.mem_append.mp hx with hx | hx
    · exact cov.calls x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨c', hc'm, hc'id, hc'o, hc't, htg, (h1 tT htTm htTn').trans htTin, hstr, hto, hpo,
        fun hend => nomatch hend⟩
  · -- A workflow body: `T` began the task with the same run.
    obtain ⟨r', hr'm, hr'o, hr't⟩ : ∃ r ∈ T.runs, r.owner = some eT.id ∧ r.task = some name := by
      rcases began' with ⟨c', hc'⟩ | hr
      · obtain ⟨hc'm, -, hc'o, hc't⟩ := taskCall c' hc'
        obtain ⟨-, h2⟩ := CT.taskCall c' hc'm name hc't eT heTm (heTid.trans hc'o.symm)
        obtain ⟨-, -, f', -, hf', -⟩ := h2 spec hspecT
        rw [hwf] at hf'
        cases hf'
      · exact hr
    obtain ⟨h1, h2⟩ := CT.taskRun r' hr'm name hr't eT heTm hr'o
    obtain ⟨out', hout'⟩ := h2 spec hspecT
    rw [hwf] at hout'
    cases hout'
    -- Its path is the task's (`RunOwned`).
    have hr'p : r'.path = e.run ++ [State.taskId e.id name] := by
      rcases invT.own.runs r' hr'm with ⟨ho, -⟩ | ⟨ht, -⟩ | ⟨name', ht, e₃, he₃, ho₃, hp₃, -⟩
      · rw [hr'o] at ho
        cases ho
      · rw [hr't] at ht
        cases ht
      · rw [hr't] at ht
        cases ht
        rw [hr'o] at ho₃
        obtain rfl : e₃ = eT := wkT.execution_eq_of_id he₃ heTm (Option.some.inj ho₃).symm
        rw [hp₃, heTrun, heTid]
        rfl
    refine CoversOpsAux.covers_mk h (fun x hx => ?_) cov.invocations cov.calls
      (CoversOpsAux.covers_setTask cov hem hopen fun e' he' hid hrun' hpl a6 t' ht' hn =>
        ⟨fun _ => (a6 ts htsm t' ht' hn).1 (by rw [hready]; exact fun h => nomatch h), fun hend => nomatch hend⟩)
      cov.results cov.taskResults cov.deliveries rfl (CoversOpsAux.complete_setTask hem)
    rcases List.mem_append.mp hx with hx | hx
    · exact cov.runs x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨r', hr'm, hr'p, rfl, (h1 tT htTm htTn').trans htTin, by rw [hr'o, heTid], hr't⟩
theorem covers_taskOutput {eid name : String} {index : Nat} {value : Value}
    (h : StepCtx p env T s (.taskOutput eid name index value) s') : Covers p T s' := by
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have cov := h.covers
  obtain ⟨-, -, e, c, spec, r, he, hc, hspec, hout, hr, -, hcase⟩ := Step.taskOutput_inv h.accepted
  have hv : env.behavior.taskOutput eid name index = some value := h.conforms
  obtain ⟨o, hoT, hnp, hov, hof⟩ := CoversOpsAux.covers_taskResult h he hspec hout hr
  -- `T` transformed the result into the behavior's value.
  have ho : o = .value value := by
    cases o with
    | pending => exact absurd rfl hnp
    | value v =>
      have := hov v rfl
      rw [hv] at this
      cases this
      rfl
    | failed =>
      have := hof rfl
      rw [hv] at this
      cases this
  subst ho
  have hts := CoversOpsAux.covers_setTaskResult cov hoT
  rcases hcase with ⟨hstream, -, rfl⟩ | ⟨-, rfl⟩
  · refine CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls cov.executions (fun x hx => ?_) hts
      cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact cov.results x hx
    · rw [List.mem_singleton.mp hx]
      -- The Stream output of `T` holds the transformed value (`OutputResults`).
      have hk : r.execution = eid ∧ r.task = name ∧ r.index = index := by
        simpa [and_assoc] using List.find?_some hr
      obtain ⟨hem, heid⟩ := State.execution?_eq_some he
      obtain ⟨eT, heTm, heT, heTid, heTrun, heTpl, -⟩ := CoversOpsAux.covers_execution cov wkT hem
      have hccT := CoversOpsAux.covers_concurrencyOf cov wkT heTrun heTpl hc
      have hres := (Reachable.outputResults hT).1 _ hoT value rfl eT c (by rw [hk.1, ← heid]; exact heT) hccT
        hstream
      simp only [hk.2.1, hk.2.2, heTid, heid, heTrun, heTpl] at hres
      exact hres
  · exact CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls cov.executions cov.results hts
      cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩
theorem covers_taskOutputFailed {eid name : String} {index : Nat}
    (h : StepCtx p env T s (.taskOutputFailed eid name index) s') : Covers p T s' := by
  have cov := h.covers
  obtain ⟨hst, hrunning, e, spec, r, he, hspec, hout, hr, -, hs'⟩ := Step.taskOutputFailed_inv h.accepted
  have hpol := CoversOpsAux.StepCtx.policy h hs' rfl hst hrunning
  rw [hpol, State.fail_continue] at hs'
  subst hs'
  have hnone : env.behavior.taskOutput eid name index = none := h.conforms
  obtain ⟨o, hoT, hnp, hov, -⟩ := CoversOpsAux.covers_taskResult h he hspec hout hr
  -- `T`'s transform of the result failed as well.
  have ho : o = .failed := by
    cases o with
    | pending => exact absurd rfl hnp
    | value v =>
      have := hov v rfl
      rw [hnone] at this
      cases this
    | failed => rfl
  subst ho
  exact CoversOpsAux.covers_mk h cov.runs cov.invocations cov.calls cov.executions cov.results
    (CoversOpsAux.covers_setTaskResult cov hoT) cov.deliveries rfl fun e he hc => ⟨e, he, rfl, hc⟩

end CoversOps

end Suimon.Round3
