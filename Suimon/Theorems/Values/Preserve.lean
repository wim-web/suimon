import Suimon.Theorems.Values.Steps

/-! # Typed values: conforming executions keep the invariant

Each operation of a conforming execution of a valid definition keeps `Typed` (`step_typed`), so every
state of such an execution holds only values of the types their places declare
(`Conforming.typed`), and every value it holds has a type (`Conforming.values_typed`). -/

namespace Suimon.Values
open Round3 State

variable {τ : ValueTyping} {p : Definition} {env : Env}

/-- Every operation of a conforming execution keeps the invariant. -/
theorem step_typed (valid : p.validate = .ok ()) (lists : τ.Lists) (typed : TypedEnv p env τ)
    {tr : List Op} {s t : State} {op : Op} (hconf : Conforming p env tr s) (h : Typed τ p s)
    (hop : Conforms env s op) (hs : step p s op = .ok t) : Typed τ p t := by
  have hr := hconf.reachable
  have wk := hr.wellKeyed
  have inv := Delivery.Reachable.inv hr
  have normal := Definition.normal_of_validate valid
  cases op with
  | start input =>
    obtain ⟨hst, -, w, hw, hin, rfl⟩ := Step.start_inv hs
    obtain rfl : s = {} := inv.fresh hst
    have hinput : input = env.input := hop
    refine ⟨fun r hr' => ?_, nofun, nofun, nofun, nofun, nofun, nofun⟩
    rw [List.mem_singleton.mp hr']
    refine ⟨w, hw, ?_⟩
    cases he : w.input with
    | none =>
      rw [he] at hin
      cases input with
      | none => trivial
      | some v => simp at hin
    | some e =>
      rw [he] at hin
      cases input with
      | none => simp at hin
      | some v => exact typed.input w e v hw he hinput.symm
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hrun, -, hw, hpl, hinput, rfl, -, -, hcases⟩ := Step.invoke_inv hs
    obtain ⟨x, hx, hfits⟩ := invocationInput_typed valid h hrun hw hpl hinput
    have hws : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hrun, hw⟩
    have hinv : InvocationTyped τ p s
        { id := Key.invocation path name trigger, run := path, placement := name, trigger, input } :=
      ⟨w, pl, x, hws, hpl, hx, hfits⟩
    rcases hcases with ⟨f, decl, hctl, hdecl, -, rfl⟩ | ⟨judge, arms, hctl, -, rfl⟩ | ⟨wf, out, hctl, -, rfl⟩ |
        ⟨c, hctl, -, rfl⟩
    · refine (h.appendInvocation hinv).appendCall ?_
      rw [hctl] at hx
      simp only [Definition.inputType, Definition.bodyInput, hdecl, Option.map_some, Option.some.injEq] at hx
      subst hx
      exact ⟨decl, hdecl, hfits⟩
    · refine (h.appendInvocation hinv).appendCall ?_
      rw [hctl] at hx
      simp only [Definition.inputType] at hx
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact ⟨j, hj, hfits⟩
    · refine (h.appendInvocation hinv).appendRun ?_
      rw [hctl] at hx
      simp only [Definition.inputType, Definition.bodyInput] at hx
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hx
      exact ⟨w', hw', hfits⟩
    · refine (h.appendInvocation hinv).appendExecution ?_
      rw [hctl] at hx
      simp only [Definition.inputType, Option.some.injEq] at hx
      subst hx
      refine ⟨c, Delivery.concurrencyOf_iff.mpr ⟨w, pl, hws, hpl, hctl⟩, hfits, fun tk htk hst spec hspec => ?_,
        fun tk htk v hv => ?_⟩
      · obtain ⟨ts, -, rfl⟩ := List.mem_map.mp htk
        have hci : c.input = none := by
          cases hc' : c.input with
          | none => rfl
          | some _ => simp [hc'] at hst
        have hwm := (Definition.workflow?_eq_some hw).1
        have hplm := (Workflow.placement?_eq_some hpl).1
        obtain ⟨-, -, -, -, -, -, htasks⟩ := ((normal.workflows w hwm).placements pl hplm).concurrency c hctl
        obtain ⟨input', hb, hmatch⟩ := (htasks spec (List.mem_of_find?_eq_some hspec)).input
        simp only [hci] at hmatch
        exact ⟨input', hb, by rw [hmatch.1]; trivial⟩
      · -- A new task holds no input yet.
        obtain ⟨ts, -, rfl⟩ := List.mem_map.mp htk
        cases hv
  | fetch id =>
    obtain ⟨-, -, c, hc, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.setCall (State.call?_eq_some hc).1 rfl rfl
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, -, htarget, hacc, hso⟩ := Step.returned_inv hs
    obtain ⟨c', hc', -, hend⟩ := hop
    rw [hc] at hc'
    cases hc'
    obtain ⟨hcm, hcid⟩ := State.call?_eq_some hc
    obtain ⟨decl, hdecl, hfits⟩ : ∃ decl, p.function? f = some decl ∧ τ.Fits c.input decl.input := by
      have := h.calls c hcm
      unfold CallTyped at this
      rw [htarget] at this
      exact this
    have hv := (typed.function tr s hconf c hcm f decl htarget hdecl hfits).2 value (by rw [hcid]; exact hend)
    have h' := h.acceptFunction hr hcm htarget hdecl hv hacc
    have hcm' : c ∈ s'.calls := by rw [(State.accept_frame hacc).2.2.2.2.2.1]; exact hcm
    exact (h'.setCall (c' := { c with status := .returned }) hcm' rfl rfl).settleOwner
      ((wk.accept hacc).setCall _) hso (by simp)
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, -, -, htask, hi, hpl, hctl, -, hacc, rfl⟩ :=
      Step.judged_inv hs
    have hcm := (State.call?_eq_some hc).1
    have him := (State.invocation?_eq_some hi).1
    obtain ⟨w, hw, hplw⟩ := State.placementOf_eq_ok.mp hpl
    obtain ⟨w', pl', x, hw', hpl', hx, hfits⟩ := h.invocations i him
    rw [hw] at hw'
    cases hw'
    rw [hplw] at hpl'
    cases hpl'
    rw [hctl] at hx
    simp only [Definition.inputType] at hx
    obtain ⟨jd, hjd, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨v, hiv, hv⟩ : ∃ v, i.input = some v ∧ τ.HasType v jd.input := by
      cases hin : i.input with
      | none =>
        rw [hin] at hfits
        exact hfits.elim
      | some v =>
        rw [hin] at hfits
        exact ⟨v, rfl, hfits⟩
    -- A branch passes on its input, which has the judge's input type (§7.1).
    have h1 : Typed τ p s' := h.accept hacc
      (fun _ i' hi' => by
        rw [hi] at hi'
        cases hi'
        exact ⟨w, pl, jd.input, hw, hplw, by rw [hctl]; simp [Definition.resultType, Definition.localResult, hjd],
          by rw [hiv]; exact hv⟩)
      (fun name hn => by rw [htask] at hn; cases hn)
    have hframe := State.accept_frame hacc
    have hcm' : c ∈ s'.calls := by rw [hframe.2.2.2.2.2.1]; exact hcm
    have him' : i ∈ (s'.setCall { c with status := .returned }).invocations := by
      rw [setCall_invocations, hframe.2.2.2.2.1]; exact him
    exact (h1.setCall (c' := { c with status := .returned }) hcm' rfl rfl).setInvocation
      (i' := { i with status := .succeeded, arm := some arm }) him' rfl rfl rfl
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, hstream, -, hacc, rfl⟩ := Step.yielded_inv hs
    obtain ⟨c', hc', hyield⟩ := hop
    rw [hc] at hc'
    cases hc'
    obtain ⟨hcm, hcid⟩ := State.call?_eq_some hc
    obtain ⟨f, htarget⟩ := target_function_of_stream hr hcm hstream
    obtain ⟨decl, hdecl, hfits⟩ : ∃ decl, p.function? f = some decl ∧ τ.Fits c.input decl.input := by
      have := h.calls c hcm
      unfold CallTyped at this
      rw [htarget] at this
      exact this
    have hmem : value ∈ (env.behavior.script c.id).yields := by
      rw [hcid]
      exact List.mem_of_getElem? hyield
    have hv := (typed.function tr s hconf c hcm f decl htarget hdecl hfits).1 value hmem
    have h' := h.acceptFunction hr hcm htarget hdecl hv hacc
    have hcm' : c ∈ s'.calls := by rw [(State.accept_frame hacc).2.2.2.2.2.1]; exact hcm
    exact h'.setCall (c' := { c with status := .running, yields := c.yields + 1 }) hcm' rfl rfl
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    exact (h.setCall (c' := { c with status := .returned }) (State.call?_eq_some hc).1 rfl rfl).settleOwner
      (wk.setCall _) hso (by simp)
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact h.failCall wk (State.call?_eq_some hc).1 hf
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    exact h.failCall wk (State.call?_eq_some hc).1 hf
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.failCall wk (State.call?_eq_some hc).1 hf
    · exact (h.setCall (c' := { c with status := .cancelled }) (State.call?_eq_some hc).1 rfl rfl).cancelOwner
        (wk.setCall _) ho
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact (h.setCall (c' := { c with status := .cancelled }) (State.call?_eq_some hc).1 rfl rfl).cancelOwner
      (wk.setCall _) ho
  | deliver path index source value =>
    obtain ⟨-, -, w, c, outcome, hdt, hcases, rfl⟩ := Step.deliver_inv hs
    obtain ⟨hw, hc, ⟨r, hr', hrrun, hrpl, -⟩, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
    refine h.appendDelivery ?_
    obtain ⟨run, -, hwf⟩ := Delivery.workflow?_iff.mp hw
    have hwm := (Definition.workflow?_eq_some hwf).1
    obtain ⟨src, dst, hsrc, hdst, -, -, produced, input, hprod, hinput, hfitsT⟩ :=
      ((normal.workflows w hwm).connections c (List.mem_of_getElem? hc)).ends
    refine ⟨w, c, dst, input, hw, hc, hdst, hinput, ?_⟩
    rcases hcases with ⟨tid, v, htr, rfl, rfl⟩ | ⟨htr, rfl, rfl⟩
    · rw [htr] at hfitsT
      cases input with
      | none => exact hfitsT.elim
      | some T =>
        obtain ⟨t, ht, htin, htout⟩ := hfitsT
        obtain ⟨hrm, hrid⟩ := State.result?_eq_some hr'
        -- The source result has the source's result type, which the transform takes (§4.2).
        obtain ⟨w', pl', T', hw', hpl', hT', hv'⟩ := h.results r hrm
        rw [hrrun, hw] at hw'
        cases hw'
        rw [hrpl, hsrc] at hpl'
        cases hpl'
        rw [hprod] at hT'
        cases hT'
        have hvt := typed.transform tr s hconf path w index c tid t hw hc htr ht r hrm hrrun hrpl (htin ▸ hv') v
          (by rw [hrid]; exact hop v rfl)
        show τ.HasType v T
        rw [← htout]
        exact hvt
    · rw [htr] at hfitsT
      cases input with
      | none => rfl
      | some T => exact hfitsT.elim
  | transformFailed path index source =>
    obtain ⟨-, -, w, c, tid, target, hdt, -, htarget, rfl⟩ := Step.transformFailed_inv hs
    obtain ⟨hw, hc, -, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
    obtain ⟨run, -, hwf⟩ := Delivery.workflow?_iff.mp hw
    obtain ⟨input, hinput⟩ :=
      inputType_isSome valid (Definition.workflow?_eq_some hwf).1 (Workflow.placement?_eq_some htarget).1
    exact (h.appendDelivery (d := { run := path, connection := index, source, outcome := .failed })
      ⟨w, c, target, input, hw, hc, htarget, hinput, trivial⟩).fail _ _
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, hts, -, hspec, hcases, rfl⟩ := Step.taskInput_inv hs
    obtain ⟨hem, heid⟩ := State.execution?_eq_some he
    have htsn : ts.name = name := (find?_key_eq_some hts).2
    obtain ⟨cc₀, hcc₀, hfind⟩ := State.taskSpec_eq_ok.mp hspec
    -- The task becomes ready with the value it takes, and keeps that value whatever its status later.
    suffices key : ∃ input, p.bodyInput spec.body = some input ∧ τ.Fits value input by
      have hfind' : cc₀.tasks.find? (·.name == ts.name) = some spec := by rw [htsn]; exact hfind
      refine h.setTask wk hem (fun _ cc spec' hcc hspec' => ?_) (fun v hv cc hcc => ?_)
      · obtain rfl : cc₀ = cc := by rw [hcc₀] at hcc; exact Except.ok.inj hcc
        obtain rfl : spec' = spec := Option.some.inj (hspec'.symm.trans hfind')
        exact key
      · obtain rfl : cc₀ = cc := by rw [hcc₀] at hcc; exact Except.ok.inj hcc
        obtain ⟨input, hb, hfits⟩ := key
        have hv' : value = some v := hv
        subst hv'
        obtain ⟨T, rfl, hT⟩ := ValueTyping.fits_some.mp hfits
        exact ⟨spec, T, hfind', hb, hT⟩
    -- The value fits the input of the task's body.
    obtain ⟨w, pl, hw, hpl, hctl⟩ := Delivery.concurrencyOf_iff.mp hcc₀
    obtain ⟨run, -, hwf⟩ := Delivery.workflow?_iff.mp hw
    have hwm := (Definition.workflow?_eq_some hwf).1
    have hplm := (Workflow.placement?_eq_some hpl).1
    obtain ⟨-, -, -, -, -, -, htasks⟩ := ((normal.workflows w hwm).placements pl hplm).concurrency cc₀ hctl
    obtain ⟨input, hb, hmatch⟩ := (htasks spec (List.mem_of_find?_eq_some hfind)).input
    refine ⟨input, hb, ?_⟩
    cases hci : cc₀.input with
    | none =>
      rw [hci] at hmatch
      rcases hcases with ⟨tid, v, hin, -⟩ | ⟨hin, -⟩ <;> rw [hmatch.2] at hin <;> cases hin
    | some source =>
      rw [hci] at hmatch
      obtain ⟨transform, htrans, hfitsT⟩ := hmatch
      rcases hcases with ⟨tid, v, hin, rfl⟩ | ⟨hin, rfl⟩
      · rw [hin] at htrans
        cases htrans
        cases input with
        | none => exact hfitsT.elim
        | some T =>
          obtain ⟨t, ht, htin, htout⟩ := hfitsT
          -- The execution's input has the concurrency's input type, which the transform takes (§8.1).
          obtain ⟨cc', hcc', hfitsE, -⟩ := h.executions e hem
          obtain rfl : cc' = cc₀ := by rw [hcc₀] at hcc'; exact (Except.ok.inj hcc').symm
          rw [hci] at hfitsE
          obtain ⟨u, heu, hu⟩ : ∃ u, e.input = some u ∧ τ.HasType u source := by
            cases hein : e.input with
            | none =>
              rw [hein] at hfitsE
              exact hfitsE.elim
            | some u =>
              rw [hein] at hfitsE
              exact ⟨u, rfl, hfitsE⟩
          have hvt := typed.taskInput tr s hconf e hem name spec tid t u hspec hin ht heu (htin ▸ hu) v
            (by rw [heid]; exact hop v rfl)
          show τ.HasType v T
          rw [← htout]
          exact hvt
      · rw [hin] at htrans
        cases htrans
        cases input with
        | none => trivial
        | some T => exact hfitsT.elim
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, hts, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (h.setTaskStatus wk (State.execution?_eq_some he).1 (find?_key_eq_some hts).1 (by decide)).fail _ _
  | beginTask eid name =>
    obtain ⟨-, -, e, c, ts, spec, he, -, hc, hts, hready, -, hspec, hcases⟩ := Step.beginTask_inv hs
    have hem := (State.execution?_eq_some he).1
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    obtain ⟨cc, hcc, -, htasks, -⟩ := h.executions e hem
    obtain rfl : cc = c := by rw [hc] at hcc; exact (Except.ok.inj hcc).symm
    obtain ⟨cc₀, hcc₀, hfind⟩ := State.taskSpec_eq_ok.mp hspec
    obtain rfl : cc₀ = cc := by rw [hcc₀] at hc; exact Except.ok.inj hc
    -- A task begins with the input it holds while ready (§8.1).
    obtain ⟨input, hb, hfits⟩ := htasks ts htsm hready spec (by rw [htsn]; exact hfind)
    have h1 := h.setTaskStatus wk hem htsm (status := .active) (by decide)
    rcases hcases with ⟨f, decl, hbody, hdecl, -, rfl⟩ | ⟨wf, out, hbody, -, rfl⟩
    · refine h1.appendCall ?_
      rw [hbody] at hb
      simp only [Definition.bodyInput, hdecl, Option.map_some, Option.some.injEq] at hb
      subst hb
      exact ⟨decl, hdecl, hfits⟩
    · refine h1.appendRun ?_
      rw [hbody] at hb
      simp only [Definition.bodyInput] at hb
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨w', hw', hfits⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, c, spec, r, he, hc, hspec, hout, hr', -, hcases⟩ := Step.taskOutput_inv hs
    obtain ⟨hem, heid⟩ := State.execution?_eq_some he
    have hrm := List.mem_of_find?_eq_some hr'
    have hrkey : r.execution = eid ∧ r.task = name ∧ r.index = index := by
      simpa [and_assoc] using List.find?_some hr'
    obtain ⟨cc₀, hcc₀, hfind⟩ := State.taskSpec_eq_ok.mp hspec
    obtain rfl : cc₀ = c := by rw [hcc₀] at hc; exact Except.ok.inj hc
    obtain ⟨id, hid⟩ := Option.isSome_iff_exists.mp hout
    obtain ⟨w, pl, hw, hpl, hctl⟩ := Delivery.concurrencyOf_iff.mp hcc₀
    obtain ⟨run, -, hwf⟩ := Delivery.workflow?_iff.mp hw
    have hwm := (Definition.workflow?_eq_some hwf).1
    have hplm := (Workflow.placement?_eq_some hpl).1
    obtain ⟨-, -, -, -, -, -, htasks⟩ := ((normal.workflows w hwm).placements pl hplm).concurrency cc₀ hctl
    obtain ⟨t, ht, hbodyT, htout⟩ := (htasks spec (List.mem_of_find?_eq_some hfind)).output id hid
    -- The task result has the element type of the body, which the output transform takes (§8.3).
    obtain ⟨e', he', he'id, cc', spec', T, hcc', hspec', hT, hv, -⟩ := h.taskResults r hrm
    obtain rfl : e' = e := wk.execution_eq_of_id he' hem (he'id.trans (hrkey.1.trans heid.symm))
    obtain rfl : cc' = cc₀ := by rw [hcc₀] at hcc'; exact (Except.ok.inj hcc').symm
    obtain rfl : spec' = spec := by
      rw [hrkey.2.1, hfind] at hspec'
      exact (Option.some.inj hspec').symm
    rw [hbodyT] at hT
    cases hT
    have hvalue : τ.HasType value cc'.element := by
      rw [← htout]
      refine typed.taskOutput tr s hconf e' he' r hrm he'id.symm spec' id t (by rw [hrkey.2.1]; exact hspec) hid ht hv
        value ?_
      rw [he'id, hrkey.1, hrkey.2.1, hrkey.2.2]
      exact hop
    have h1 := h.setTaskResult (r' := { r with output := .value value }) hrm rfl rfl rfl
      fun v hv' e₂ he₂ he₂id c₂ hc₂ => by
        simp only [TaskOutput.value.injEq] at hv'
        subst hv'
        obtain rfl : e₂ = e' := wk.execution_eq_of_id he₂ he' (he₂id.trans he'id.symm)
        obtain rfl : c₂ = cc' := by rw [hcc₀] at hc₂; exact (Except.ok.inj hc₂).symm
        exact hvalue
    rcases hcases with ⟨hstream, -, rfl⟩ | ⟨-, rfl⟩
    · refine h1.appendResult ⟨w, pl, cc'.element, hw, hpl, ?_, hvalue⟩
      rw [hctl]
      simp [Definition.resultType, Definition.localResult, hstream]
    · exact h1
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, e, spec, r, -, -, -, hr', -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (h.setTaskResult (r' := { r with output := .failed }) (List.mem_of_find?_eq_some hr') rfl rfl rfl
      fun v hv => by cases hv).fail _ _
  | settle path name =>
    obtain ⟨-, -, run, w, pl, shape, kind, x, result, hrun, -, hw, hpl, -, hshape, -, hout, hcases⟩ :=
      Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact h.of_records rfl rfl rfl rfl rfl rfl rfl
    · exact (h.appendResult (settle_result_typed lists h hrun hw hpl hshape hout)).of_records
        rfl rfl rfl rfl rfl rfl rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, c, i, he, -, hc, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    obtain ⟨hem, heid⟩ := State.execution?_eq_some he
    have him := (State.invocation?_eq_some hi).1
    have h1 := h.setExecution wk hem (e' := { e with complete := true }) rfl rfl rfl rfl rfl
    rcases hcases with ⟨-, rfl⟩ | ⟨-, hlist, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h1.setInvocation (i' := { i with status := .skipped }) him rfl rfl rfl
    · have h2 := h1.setInvocation (i' := { i with status := .succeeded }) him rfl rfl rfl
      refine h2.appendResult ?_
      obtain ⟨w, pl, hw, hpl, hctl⟩ := Delivery.concurrencyOf_iff.mp hc
      refine ⟨w, pl, .list c.element, hw, hpl, ?_, lists _ _ fun v hv => ?_⟩
      · rw [hctl]
        simp [Definition.resultType, Definition.localResult, hlist]
      · -- Each element of the list is a transformed output of a task of this execution (§8.3).
        obtain ⟨x, hx, hxv⟩ := List.mem_filterMap.mp hv
        obtain ⟨hxm, hxe⟩ := List.mem_filter.mp hx
        have hxid : x.execution = eid := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hxe
          exact hxe.1
        obtain ⟨e', he', he'id, c', -, -, hc', -, -, -, hxout⟩ := h.taskResults x hxm
        obtain rfl : e' = e := wk.execution_eq_of_id he' hem (he'id.trans (hxid.trans heid.symm))
        obtain rfl : c' = c := by rw [hc] at hc'; exact (Except.ok.inj hc').symm
        refine hxout v ?_
        cases hxo : x.output with
        | pending => simp [hxo, TaskOutput.value?] at hxv
        | failed => simp [hxo, TaskOutput.value?] at hxv
        | value v' =>
          simp only [hxo, TaskOutput.value?, Option.some.injEq] at hxv
          rw [hxv]
    · exact h1.setInvocation (i' := { i with status := .succeeded }) him rfl rfl rfl
  | closeRun path =>
    obtain ⟨-, -, r, w, output, x, owner, hrun, -, -, hw, -, hdes, -, howner, hcases⟩ := Step.closeRun_inv hs
    obtain ⟨hrm, hrpath⟩ := State.run?_eq_some hrun
    have K1 : Keeps p s (s.setRun { r with complete := true }) := Keeps.setRun wk hrm rfl rfl
    have h1 := h.setRun wk hrm (r' := { r with complete := true }) rfl rfl rfl
    have wk1 : (s.setRun { r with complete := true }).WellKeyed := wk.setRun _
    -- The value a run returns is a result of its designated endpoint (§4.5).
    have hvalue : ∀ v, ((s.resultsOf path output).head?).map (·.value) = some v →
        ∃ pl T, w.placement? output = some pl ∧ p.resultType pl.control = some T ∧ τ.HasType v T := by
      intro v hv
      obtain ⟨rr, hrr, rfl⟩ := Option.map_eq_some_iff.mp hv
      obtain ⟨hrrm, hrrrun, hrrpl⟩ := Delivery.mem_resultsOf.mp (List.mem_of_mem_head? hrr)
      obtain ⟨w', pl', T', hw', hpl', hT', hv'⟩ := h.results rr hrrm
      have hws : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hrun, hw⟩
      rw [hrrrun, hws] at hw'
      cases hw'
      rw [hrrpl] at hpl'
      exact ⟨pl', T', hpl', hT', hv'⟩
    obtain ⟨owner', howner', hdcase⟩ := State.designatedOutput_eq_ok.mp hdes
    rw [howner] at howner'
    cases howner'
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
    · obtain ⟨him, hiid⟩ := State.invocation?_eq_some hi
      rcases hcases with ⟨-, v, hv, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine (h1.setInvocation (i' := { i with status := .succeeded }) him rfl rfl rfl).appendResult ?_
        rcases hdcase with ⟨-, i', pl, wf, hi', hpl, hctl⟩ | ⟨name', -, -, -, htask', -⟩
        · obtain rfl : i' = i := Option.some.inj (hi'.symm.trans hi)
          obtain ⟨wi, hwi, hplwi⟩ := State.placementOf_eq_ok.mp hpl
          -- The run runs the workflow the invoking placement calls.
          have hwf : r.workflow = wf :=
            run_workflow_of_call hr hrm him (by rw [howner, hiid]) htask hwi hplwi hctl
          obtain ⟨run', -, hwfi⟩ := Delivery.workflow?_iff.mp hwi
          obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp
            (bodyElement_isSome valid (Definition.workflow?_eq_some hwfi).1 (Workflow.placement?_eq_some hplwi).1
              (Or.inl hctl))
          obtain ⟨plc, Tc, hplc, hTc, hvc⟩ := hvalue v hv
          have hTT := bodyElement_workflow hT (hwf ▸ hw) hplc hTc
          have hres : ResultTyped τ p s
              { id := Key.returned i'.id, run := i'.run, placement := i'.placement, producer := i'.id,
                value := v } :=
            ⟨wi, pl, T, hwi, hplwi, by rw [hctl]; exact hT, hTT ▸ hvc⟩
          exact hres.keep (K1.trans (Keeps.of_eq rfl rfl))
        · rw [htask] at htask'
          cases htask'
      · exact h1.setInvocation (i' := { i with status := .skipped }) him rfl rfl rfl
      · exact h1.setInvocation (i' := { i with status := .failed }) him rfl rfl rfl
      · exact h1.setInvocation (i' := { i with status := .upstreamFailed }) him rfl rfl rfl
    · obtain ⟨hem, heid⟩ := State.execution?_eq_some he
      have hem1 : e ∈ (s.setRun { r with complete := true }).executions := hem
      have htsm := (find?_key_eq_some hts).1
      rcases hcases with ⟨-, v, hv, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · have K2 := K1.trans (Keeps.setExecution wk1 hem1 (e' := withTask e { ts with status := .succeeded }) rfl rfl rfl)
        refine (h1.setTaskStatus wk1 hem1 htsm (status := .succeeded) (by decide)).appendTaskResult ?_
        rcases hdcase with ⟨htask', -⟩ | ⟨name', e', spec, wf, htask', he', hspec, hbody⟩
        · rw [htask] at htask'
          cases htask'
        · obtain rfl : name' = name := Option.some.inj (htask'.symm.trans htask)
          rw [he] at he'
          cases he'
          -- The task's body calls the workflow that the run runs.
          obtain ⟨-, hrw⟩ := (CoversOpsAux.Reachable.created hr).taskRun r hrm name' htask e hem
            (by rw [howner, heid])
          obtain ⟨out, hbody'⟩ := hrw spec hspec
          rw [hbody] at hbody'
          simp only [Body.workflow.injEq] at hbody'
          obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec
          obtain ⟨we, ple, hwe, hple, hctle⟩ := Delivery.concurrencyOf_iff.mp hcc
          obtain ⟨rune, -, hwfe⟩ := Delivery.workflow?_iff.mp hwe
          obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp
            (bodyElement_isSome valid (Definition.workflow?_eq_some hwfe).1 (Workflow.placement?_eq_some hple).1
              (Or.inr ⟨cc, spec, hctle, List.mem_of_find?_eq_some hfind, hbody⟩))
          obtain ⟨plc, Tc, hplc, hTc, hvc⟩ := hvalue v hv
          have hTT := bodyElement_workflow hT (hbody'.1 ▸ hw) hplc hTc
          have hres : TaskResultTyped τ p s { execution := e.id, task := name', index := 0, value := v } :=
            ⟨e, hem, rfl, cc, spec, T, hcc, hfind, by rw [hbody]; exact hT, hTT ▸ hvc, fun _ h => by cases h⟩
          exact hres.keep K2 rfl rfl rfl fun _ h => h
      · exact h1.setTaskStatus wk1 hem1 htsm (by decide)
      · exact h1.setTaskStatus wk1 hem1 htsm (by decide)
      · exact h1.setTaskStatus wk1 hem1 htsm (by decide)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.stop.of_records rfl rfl rfl rfl rfl rfl rfl
    · exact h.of_records rfl rfl rfl rfl rfl rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, w, hr', -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact (h.setRun wk (State.run?_eq_some hr').1 (r' := { r with complete := true }) rfl rfl rfl).of_records
        rfl rfl rfl rfl rfl rfl rfl
    · exact h.endUnfinished.of_records rfl rfl rfl rfl rfl rfl rfl

/-- Every state of a conforming execution of a valid definition holds only values of the types their
    places declare, when the outside world keeps its typing contracts. -/
theorem Conforming.typed (valid : p.validate = .ok ()) (lists : τ.Lists) (typed : TypedEnv p env τ)
    {tr : List Op} {s : State} (h : Conforming p env tr s) : Typed τ p s := by
  induction h with
  | nil => exact Typed.empty
  | snoc hc hop hs _ ih => exact step_typed valid lists typed hc ih hop hs

/-- Every value that a state of such an execution holds has a type, whatever the status of the record
    that holds it: a task that a stop left not started still holds an input of its body's input
    type. -/
theorem Conforming.values_typed (valid : p.validate = .ok ()) (lists : τ.Lists) (typed : TypedEnv p env τ)
    {tr : List Op} {s : State} (h : Conforming p env tr s) : ∀ v ∈ s.values, ∃ T, τ.HasType v T :=
  (Conforming.typed valid lists typed h).values_typed

end Suimon.Values
