import Suimon.Theorems.SettleClosed

/-! Every step keeps the settlement invariant, and all four layers hold in every reachable state. -/

namespace Suimon.Settle

open State

variable {p : Definition} {s t : State}

namespace SettledInv

theorem empty : SettledInv p {} where
  ended := by simp
  closed := by simp
  noEligible := by simp
  waitValue := by simp

theorem root {m : String} {input : Option Value} :
    SettledInv p { started := true, runs := [{ path := [], workflow := m, input }] } where
  ended := by simp
  closed := by simp
  noEligible := by simp
  waitValue := by simp

/-! ### Settled placements get no new invocation and no new result -/

/-- An invocation with a running call belongs to a placement that has not settled. --/
theorem unsettled_of_call (h : SettledInv p s) {c : Call} (hc : c ∈ s.calls) (htc : c.task = none)
    (hrun : c.status = .running ∨ c.status = .fetching) {i : Invocation} (hi : i ∈ s.invocations)
    (hio : i.id = c.owner) : s.settled? i.run i.placement = none := by
  cases hs : s.settled? i.run i.placement with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨hx, hxr, hxp⟩ := settled?_eq_some hs
    have hend := h.ended x hx i (mem_invocationsOf.mpr ⟨hi, hxr.symm, hxp.symm⟩)
    have := (invocationEnded_iff.mp hend).2.1 c hc hio.symm htc
    rcases hrun with hr | hr <;> rw [hr] at this <;> cases this

/-- The invocation of an open execution belongs to a placement that has not settled. --/
theorem unsettled_of_exec (h : SettledInv p s) {e : Execution} (he : e ∈ s.executions) (hec : e.complete = false)
    {i : Invocation} (hi : i ∈ s.invocations) (hie : i.id = e.id) : s.settled? i.run i.placement = none := by
  cases hs : s.settled? i.run i.placement with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨hx, hxr, hxp⟩ := settled?_eq_some hs
    have hend := h.ended x hx i (mem_invocationsOf.mpr ⟨hi, hxr.symm, hxp.symm⟩)
    have := (invocationEnded_iff.mp hend).2.2.2 e he hie.symm
    rw [hec] at this
    cases this

/-- The invocation of an open sub-workflow run belongs to a placement that has not settled. --/
theorem unsettled_of_run (h : SettledInv p s) {r : Run} (hr : r ∈ s.runs) (hrc : r.complete = false)
    (htask : r.task = none) {i : Invocation} (hi : i ∈ s.invocations) (hro : r.owner = some i.id) :
    s.settled? i.run i.placement = none := by
  cases hs : s.settled? i.run i.placement with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨hx, hxr, hxp⟩ := settled?_eq_some hs
    have hend := h.ended x hx i (mem_invocationsOf.mpr ⟨hi, hxr.symm, hxp.symm⟩)
    have := (invocationEnded_iff.mp hend).2.2.1 r hr hro htask
    rw [hrc] at this
    cases this

/-- A settled placement takes no new invocation: its input is closed (§10.3). --/
theorem invoke_fresh (h : SettledInv p s) {path : Path} {name : String} {trigger : Option ResultId} {r : Run}
    {w : Workflow} {pl : Placement} {input : Option Value} (hr : s.run? path = some r) (hw : p.workflow? r.workflow = some w)
    (hpl : w.placement? name = some pl) (hinv : invocable pl.control = true)
    (hinput : Step.invocationInput p s r w name trigger = .ok input)
    (hdup : ∀ i ∈ s.invocationsOf path name, i.trigger ≠ trigger) : s.settled? path name = none := by
  cases hs : s.settled? path name with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨hx, hxr, hxp⟩ := settled?_eq_some hs
    obtain ⟨w0, pl0, hw0, hpl0, hcl⟩ := h.closed x hx
    have hwf := workflow?_of_run hr hw
    rw [hxr, hwf] at hw0
    cases hw0
    rw [hxp, hpl] at hpl0
    cases hpl0
    unfold Closed at hcl
    rw [hxp] at hcl
    have hrp := (run?_eq_some hr).2
    have hdup' : ∀ j ∈ s.invocationsOf x.run name, j.trigger ≠ trigger := by
      rw [hxr]; exact hdup
    rcases Step.invocationInput_inv hinput with ⟨hsh, htr, -⟩ | ⟨hsh, htr, -⟩ | ⟨i, c, src, hsh, htr, hres⟩ |
      ⟨i, c, src, d, hsh, htr, hd, hout⟩
    · rw [hsh] at hcl
      obtain ⟨j, hj, hjt⟩ := hcl hinv
      exact hdup' j hj (hjt.trans htr.symm)
    · rw [hsh] at hcl
      obtain ⟨j, hj, hjt⟩ := hcl hinv
      exact hdup' j hj (hjt.trans htr.symm)
    · rw [hsh] at hcl
      obtain ⟨j, hj, hjt⟩ := hcl.1 src input (by rw [hxr, ← hrp]; exact hres)
      exact hdup' j hj (hjt.trans htr.symm)
    · rw [hsh] at hcl
      have hdm := delivery?_eq_some hd
      have hnf : d.outcome ≠ .failed := by
        rcases hout with ⟨v, hv, -⟩ | ⟨hv, -⟩ <;> rw [hv] <;> simp
      obtain ⟨j, hj, hjt⟩ := hcl.2.2 hinv d
        (mem_deliveriesOn.mpr ⟨hdm.1, hdm.2.1.trans (hrp.trans hxr.symm), hdm.2.2.1⟩) hnf
      exact hdup' j hj (hjt.trans (by rw [hdm.2.2.2, htr]))

end SettledInv

/-! ### Facts of composite updates -/

namespace Facts

theorem settleOwner (hn : (s.invocations.map (·.id)).Nodup) {c : Call}
    (hact : c.task = none → ∀ i, s.invocation? c.owner = some i → i.status = .active)
    {inv : InvocationStatus} {task : TaskStatus} (h : s.settleOwner c inv task = .ok t) : Facts p s t := by
  rcases settleOwner_eq_ok.mp h with ⟨htc, i, hi, rfl⟩ | ⟨_, e, _, -, he, -, rfl⟩
  · exact setInvocation hn (invocation?_eq_some hi).1 rfl (hact htc i hi)
  · exact setTask (execution?_eq_some he).1

theorem cancelOwner (hn : (s.invocations.map (·.id)).Nodup) {c : Call} (h : s.cancelOwner c = .ok t) :
    Facts p s t := by
  rcases cancelOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, e, _, -, he, -, rfl⟩ <;> split
  · rename_i hact
    exact setInvocation hn (invocation?_eq_some hi).1 rfl hact
  · exact refl
  · exact setTask (execution?_eq_some he).1
  · exact refl

/-- A running or fetching call ends and its active owner is settled. --/
theorem afterCall (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls)
    (hrun : c.status = .running ∨ c.status = .fetching)
    (hact : c.task = none → ∃ i ∈ s.invocations, i.id = c.owner ∧ i.status = .active)
    {status : CallStatus} {inv : InvocationStatus}
    {task : TaskStatus} (h : (s.setCall { c with status }).settleOwner c inv task = .ok t) : Facts p s t := by
  have hne : c.status.ended = false := by rcases hrun with hr | hr <;> rw [hr] <;> rfl
  refine (Facts.setCall (c' := { c with status }) hc rfl rfl hne).trans (settleOwner wk.invocations ?_ h)
  intro htc i hi
  obtain ⟨j, hj, hjo, hja⟩ := hact htc
  have hi' := invocation?_eq_some hi
  rw [wk.invocation_eq_of_id hj hi'.1 (hjo.trans hi'.2.symm)] at hja
  exact hja

theorem afterCancel (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) (hcan : c.status = .cancelling)
    (h : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) : Facts p s t :=
  (Facts.setCall (c' := { c with status := .cancelled }) hc rfl rfl (by rw [hcan]; rfl)).trans
    (cancelOwner wk.invocations h)

end Facts

namespace SettledInv

/-- One new result, of a placement that is not a waitStream. --/
theorem newResult {r0 : Result} (hres : t.results = s.results ++ [r0])
    (hr0 : ∀ w pl, t.workflow? p r0.run = some w → w.placement? r0.placement = some pl → ∀ e, pl.control ≠ .waitStream e) :
    ∀ r ∈ t.results, r ∉ s.results → ∀ w pl, t.workflow? p r.run = some w → w.placement? r.placement = some pl →
      ∀ e, pl.control ≠ .waitStream e := by
  intro r hr hn
  rw [hres] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact absurd hr hn
  · rw [List.mem_singleton.mp hr]; exact hr0

theorem noNewResult (hres : t.results = s.results) :
    ∀ r ∈ t.results, r ∉ s.results → ∀ w pl, t.workflow? p r.run = some w → w.placement? r.placement = some pl →
      ∀ e, pl.control ≠ .waitStream e :=
  fun _ hr hn => absurd (hres ▸ hr) hn

/-- Every step keeps the settlement invariant. --/
theorem step (h : SettledInv p s) (prov : Prov p s) (act : Active p s) (own : Own p s) (wk : s.WellKeyed)
    (h0 : s = {} ∨ s.started = true) {op : Op} (hs : step p s op = .ok t) : SettledInv p t := by
  cases op with
  | start input =>
    obtain ⟨hns, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h0 with rfl | h0
    · exact root
    · simp [h0] at hns
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, hinput, rfl, hdup, hfresh, hcases⟩ := Step.invoke_inv hs
    have hinv : invocable pl.control = true := by
      rcases hcases with ⟨_, _, hc, -⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, hc, -⟩ | ⟨_, hc, -⟩ <;> simp [invocable, hc]
    have hnew := h.invoke_fresh hr hw hpl hinv hinput hdup
    let inv : Invocation := { id := Key.invocation path name trigger, run := path, placement := name, trigger, input }
    have f1 : Facts p s { s with invocations := s.invocations ++ [inv] } := Facts.appendInvocation hnew
    -- The new invocation owns what it creates, and it is no invocation of a settled placement.
    have hown : ∀ x ∈ s.settled, ∀ i ∈ ({ s with invocations := s.invocations ++ [inv] } : State).invocationsOf
        x.run x.placement, inv.id ≠ i.id := by
      intro x hx i hi heq
      rw [mem_invocationsOf] at hi
      rcases List.mem_append.mp hi.1 with hi' | hi'
      · exact invocation?_eq_none_iff.mp hfresh (List.mem_map.mpr ⟨i, hi', heq.symm⟩)
      · have hii := List.mem_singleton.mp hi'
        rw [hii] at hi
        have h1 : x.run = path := hi.2.1.symm
        have h2 : x.placement = name := hi.2.2.symm
        have := wk.settled?_of_mem hx
        rw [h1, h2, hnew] at this
        cases this
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨judge, arms, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩ | ⟨cc, -, -, rfl⟩
    · exact h.of_facts own prov wk (f1.trans (Facts.appendCall fun _ x hx i hi => hown x hx i hi)) rfl
        (noNewResult rfl)
    · exact h.of_facts own prov wk (f1.trans (Facts.appendCall fun _ x hx i hi => hown x hx i hi)) rfl
        (noNewResult rfl)
    · exact h.of_facts own prov wk (f1.trans (Facts.appendRun fun _ o ho x hx i hi => by
        rw [← Option.some.inj ho]; exact hown x hx i hi)) rfl (noNewResult rfl)
    · exact h.of_facts own prov wk (f1.trans (Facts.appendExecution fun x hx i hi => hown x hx i hi)) rfl
        (noNewResult rfl)
  | fetch id =>
    obtain ⟨-, -, c, hc, -, hst, rfl⟩ := Step.fetch_inv hs
    exact h.of_facts own prov wk (Facts.setCall (call?_eq_some hc).1 rfl rfl (by rw [hst]; rfl)) rfl
      (noNewResult rfl)
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, hst, -, hacc, hso⟩ := Step.returned_inv hs
    have hc0 := (call?_eq_some hc).1
    rcases accept_eq_ok.mp hacc with ⟨htc, i, hi, -, rfl⟩ | ⟨name, htc, -, rfl⟩
    · have hi' := invocation?_eq_some hi
      have hres := h.unsettled_of_call hc0 htc (Or.inl hst) hi'.1 hi'.2
      have f := (Facts.appendResult (p := p) (r := ⟨Key.callResult c.id 0, i.run, i.placement, c.id, none, value⟩)
        hres).trans (Facts.afterCall (wk.accept hacc) hc0 (Or.inl hst) (fun h => act.callActive c hc0 h (Or.inl hst))
          hso)
      refine h.of_facts own prov wk f (by rw [(settleOwner_update hso).settled]; rfl)
        (newResult (r0 := ⟨Key.callResult c.id 0, i.run, i.placement, c.id, none, value⟩) ?_ ?_)
      · rw [(settleOwner_update hso).results]; rfl
      · exact fun w pl hwt hpl e => not_wait_of_inv own f.workflows hi'.1 hwt hpl e
    · have f := (Facts.of_records (p := p) (s := s)
        (t := { s with taskResults := s.taskResults ++ [{ execution := c.owner, task := name, index := 0, value }] })
        rfl rfl rfl rfl rfl rfl rfl).trans (Facts.afterCall (wk.accept hacc) hc0 (Or.inl hst)
          (fun h => act.callActive c hc0 h (Or.inl hst)) hso)
      exact h.of_facts own prov wk f (by rw [(settleOwner_update hso).settled]; rfl)
        (noNewResult (by rw [(settleOwner_update hso).results]; rfl))
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, hst, -, htc, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hc0 := (call?_eq_some hc).1
    have hi' := invocation?_eq_some hi
    obtain ⟨j', hj', hjo, hja⟩ := act.callActive c hc0 htc (Or.inl hst)
    have : j' = i := wk.invocation_eq_of_id hj' hi'.1 (hjo.trans hi'.2.symm)
    subst this
    rcases accept_eq_ok.mp hacc with ⟨-, i0, hi0, -, rfl⟩ | ⟨_, htc', -, -⟩
    · have : i0 = j' := by rw [hi] at hi0; exact (Option.some.inj hi0).symm
      subst this
      have hres := h.unsettled_of_call hc0 htc (Or.inl hst) hj' hjo
      have wk1 := wk.accept hacc
      have f := ((Facts.appendResult (p := p)
        (r := ⟨Key.callResult c.id 0, i0.run, i0.placement, c.id, some arm, i0.input.getD ""⟩) hres).trans
        (Facts.setCall (c' := { c with status := .returned }) hc0 rfl rfl (by rw [hst]; rfl))).trans
        (Facts.setInvocation (i := i0) (i' := { i0 with status := .succeeded, arm := some arm })
          (by exact wk1.invocations) (by exact hj') rfl hja)
      exact h.of_facts own prov wk f rfl (newResult rfl fun w pl hwt hpl e =>
        not_wait_of_inv own f.workflows hj' hwt hpl e)
    · rw [htc] at htc'; cases htc'
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, hst, hacc, rfl⟩ := Step.yielded_inv hs
    have hc0 := (call?_eq_some hc).1
    rcases accept_eq_ok.mp hacc with ⟨htc, i, hi, -, rfl⟩ | ⟨name, htc, -, rfl⟩
    · have hi' := invocation?_eq_some hi
      have hres := h.unsettled_of_call hc0 htc (Or.inr hst) hi'.1 hi'.2
      have f := (Facts.appendResult (p := p)
        (r := ⟨Key.callResult c.id c.yields, i.run, i.placement, c.id, none, value⟩) hres).trans
        (Facts.setCall (c' := { c with status := .running, yields := c.yields + 1 }) hc0 rfl rfl (by rw [hst]; rfl))
      exact h.of_facts own prov wk f rfl (newResult rfl fun w pl hwt hpl e =>
        not_wait_of_inv own f.workflows hi'.1 hwt hpl e)
    · have f := (Facts.of_records (p := p) (s := s)
        (t := { s with taskResults := s.taskResults ++ [{ execution := c.owner, task := name, index := c.yields, value }] })
        rfl rfl rfl rfl rfl rfl rfl).trans
        (Facts.setCall (c' := { c with status := .running, yields := c.yields + 1 }) hc0 rfl rfl (by rw [hst]; rfl))
      exact h.of_facts own prov wk f rfl (noNewResult rfl)
  | ended id =>
    obtain ⟨-, -, c, hc, -, hst, hso⟩ := Step.ended_inv hs
    exact h.of_facts own prov wk (Facts.afterCall wk (call?_eq_some hc).1 (Or.inr hst)
      (fun h => act.callActive c (call?_eq_some hc).1 h (Or.inr hst)) hso)
      (by rw [(settleOwner_update hso).settled]; rfl) (noNewResult (by rw [(settleOwner_update hso).results]; rfl))
  | failed id =>
    obtain ⟨-, -, c, hc, hrun, hf⟩ := Step.failed_inv hs
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact h.of_facts own prov wk ((Facts.afterCall wk (call?_eq_some hc).1 hrun
        (fun h => act.callActive c (call?_eq_some hc).1 h hrun) hso).trans Facts.fail)
      (by simp [(settleOwner_update hso).settled]) (noNewResult (by simp [(settleOwner_update hso).results]))
  | timedOut id element =>
    obtain ⟨-, -, c, hc, hcond, hf⟩ := Step.timedOut_inv hs
    have hrun : c.status = .running ∨ c.status = .fetching := by
      rcases hcond with ⟨-, h1, -⟩ | ⟨-, h1, -⟩
      · exact Or.inr h1
      · exact h1
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact h.of_facts own prov wk ((Facts.afterCall wk (call?_eq_some hc).1 hrun
        (fun h => act.callActive c (call?_eq_some hc).1 h hrun) hso).trans Facts.fail)
      (by simp [(settleOwner_update hso).settled]) (noNewResult (by simp [(settleOwner_update hso).results]))
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨hrun, hf⟩ | ⟨hcan, ho⟩⟩ := Step.lost_inv hs
    · obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
      exact h.of_facts own prov wk ((Facts.afterCall wk (call?_eq_some hc).1 hrun
        (fun h => act.callActive c (call?_eq_some hc).1 h hrun) hso).trans Facts.fail)
        (by simp [(settleOwner_update hso).settled]) (noNewResult (by simp [(settleOwner_update hso).results]))
    · exact h.of_facts own prov wk (Facts.afterCancel wk (call?_eq_some hc).1 hcan ho)
        (by rw [(cancelOwner_update ho).settled]; rfl) (noNewResult (by rw [(cancelOwner_update ho).results]; rfl))
  | terminated id =>
    obtain ⟨-, -, c, hc, hcan, ho⟩ := Step.terminated_inv hs
    exact h.of_facts own prov wk (Facts.afterCancel wk (call?_eq_some hc).1 hcan ho)
      (by rw [(cancelOwner_update ho).settled]; rfl) (noNewResult (by rw [(cancelOwner_update ho).results]; rfl))
  | deliver path index source value =>
    obtain ⟨-, -, w, c, outcome, hdt, -, rfl⟩ := Step.deliver_inv hs
    obtain ⟨hw, hc, ⟨r, hr, h1, h2, h3⟩, hfresh⟩ := Step.deliveryTarget_eq_ok.mp hdt
    have hr' := result?_eq_some hr
    have hfits := h.deliveryFits (d := { run := path, connection := index, source, outcome }) hfresh
      ⟨w, hw, c, hc, r, hr'.1, hr'.2, h1, h2, by rcases h3 with h3 | h3 <;> simp [h3]⟩
    exact h.of_facts own prov wk (Facts.appendDelivery hfits) rfl (noNewResult rfl)
  | transformFailed path index source =>
    obtain ⟨-, -, w, c, tid, target, hdt, -, -, rfl⟩ := Step.transformFailed_inv hs
    obtain ⟨hw, hc, ⟨r, hr, h1, h2, h3⟩, hfresh⟩ := Step.deliveryTarget_eq_ok.mp hdt
    have hr' := result?_eq_some hr
    have hfits := h.deliveryFits (d := { run := path, connection := index, source, outcome := .failed }) hfresh
      ⟨w, hw, c, hc, r, hr'.1, hr'.2, h1, h2, by rcases h3 with h3 | h3 <;> simp [h3]⟩
    exact h.of_facts own prov wk ((Facts.appendDelivery hfits).trans Facts.fail) (by simp) (noNewResult (by simp))
  | taskInput eid name value =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.of_facts own prov wk (Facts.setTask (execution?_eq_some he).1) rfl (noNewResult rfl)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact h.of_facts own prov wk ((Facts.setTask (execution?_eq_some he).1).trans Facts.fail) (by simp)
      (noNewResult (by simp))
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    have f1 := Facts.setTask (p := p) (ts := { ts with status := .active }) (execution?_eq_some he).1
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact h.of_facts own prov wk (f1.trans (Facts.appendCall fun h => by simp at h)) rfl (noNewResult rfl)
    · exact h.of_facts own prov wk (f1.trans (Facts.appendRun fun h => by simp at h)) rfl (noNewResult rfl)
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, cc, spec, r, he, hcc0, hspec, hout, hr, hpend, hcases⟩ := Step.taskOutput_inv hs
    have he' := execution?_eq_some he
    have f1 := Facts.of_records (p := p) (s := s) (t := s.setTaskResult { r with output := .value value })
      rfl rfl rfl rfl rfl rfl rfl
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · -- The execution is open, so its placement has not settled.
      have hrk : r.execution = eid ∧ r.task = name ∧ r.index = index := by
        simpa [and_assoc] using List.find?_some hr
      have hin : name ∈ included cc := by
        rw [taskSpec_eq_ok] at hspec
        obtain ⟨cc', hcc', hfind⟩ := hspec
        rw [concurrencyOf_det hcc' hcc0] at hfind
        obtain ⟨hmem, hn⟩ := find?_key_eq_some hfind
        exact List.mem_map.mpr ⟨spec, List.mem_filter.mpr ⟨hmem, hout⟩, hn⟩
      have hopen : e.complete = false := by
        cases hc : e.complete
        · rfl
        · exact absurd hpend (act.completeOutputs e he'.1 hc r (List.mem_of_find?_eq_some hr)
            (hrk.1.trans he'.2.symm) cc hcc0 (by rw [hrk.2.1]; exact hin))
      obtain ⟨i, hi, hie, hir, hip, -⟩ := own.execOwner e he'.1
      have hres := h.unsettled_of_exec he'.1 hopen hi hie
      rw [hir, hip] at hres
      have f := f1.trans (Facts.appendResult (p := p) (s := s.setTaskResult { r with output := .value value })
        (r := ⟨Key.taskOutput eid name index, e.run, e.placement, eid, none, value⟩) hres)
      exact h.of_facts own prov wk f rfl (newResult rfl fun w pl hwt hpl e' =>
        not_wait_of_inv own f.workflows hi (hir ▸ hwt) (hip ▸ hpl) e')
    · exact h.of_facts own prov wk f1 rfl (noNewResult rfl)
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact h.of_facts own prov wk ((Facts.of_records (p := p) (s := s) (t := s.setTaskResult { r with output := .failed })
      rfl rfl rfl rfl rfl rfl rfl).trans Facts.fail) (by simp) (noNewResult (by simp))
  | settle path name =>
    obtain ⟨-, -, r, w, pl, shape, kind, x, result, hr, -, hw, hpl, hfresh, hshape, hkind, hout, hcases⟩ :=
      Step.settle_inv hs
    have hwf := workflow?_of_run hr hw
    have hpln : pl.name = name := (Workflow.placement?_eq_some hpl).2
    obtain ⟨hall, hxrun, hxpl, -⟩ := settleOutcome_some hout
    rw [hpln] at hxpl hall
    have hcl := settle_closed hpl hshape hout
    have hne := settle_noEligible h prov own wk hwf hpl hfresh hshape hkind hout
    -- The new settlement: its invocations ended, its input closed, its missing results.
    have newEnded : ∀ i ∈ s.invocationsOf x.run x.placement, s.invocationEnded i = true := by
      rw [hxrun, hxpl]
      exact fun i hi => List.all_eq_true.mp hall i hi
    rcases hcases with ⟨rfl, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · have f : Facts p s { s with settled := s.settled ++ [x] } :=
        { Facts.refl (p := p) (s := s) with settled := ⟨[x], rfl⟩ }
      exact {
        ended := fun x' hx' i hi => by
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact h.ended_mono wk f x' hx' i hi
          · rw [List.mem_singleton.mp hx'] at hi
            exact newEnded i hi
        closed := fun x' hx' => by
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact h.closed_mono f x' hx'
          · rw [List.mem_singleton.mp hx']
            exact ⟨w, pl, by rw [hxrun]; exact hwf, by rw [hxpl]; exact hpl,
              hcl.mono f.invocations f.settled f.results ⟨[], by simp, by simp⟩⟩
        noEligible := fun x' hx' arm harm r' hr' => by
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact h.noEligible_mono wk f x' hx' arm harm r' hr'
          · rw [List.mem_singleton.mp hx'] at harm hr'
            rw [hxrun, hxpl] at hr'
            exact hne arm harm r' hr'
        waitValue := h.waitValue_mono own prov f (noNewResult rfl) }
    · obtain ⟨hxv, hresr, hresp, e, hwe⟩ := settleOutcome_aggregate hout
      have hresfresh : s.settled? res.run res.placement = none := by rw [hresr, hresp, hpln]; exact hfresh
      have f : Facts p s { s with settled := s.settled ++ [x], results := s.results ++ [res] } :=
        { Facts.refl (p := p) (s := s) with
          settled := ⟨[x], rfl⟩
          results := ⟨[res], rfl, fun r' hr' => by rw [List.mem_singleton.mp hr']; exact hresfresh⟩ }
      exact {
        ended := fun x' hx' i hi => by
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact h.ended_mono wk f x' hx' i hi
          · rw [List.mem_singleton.mp hx'] at hi
            exact newEnded i hi
        closed := fun x' hx' => by
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact h.closed_mono f x' hx'
          · rw [List.mem_singleton.mp hx']
            exact ⟨w, pl, by rw [hxrun]; exact hwf, by rw [hxpl]; exact hpl,
              hcl.mono f.invocations f.settled f.results ⟨[], by simp, by simp⟩⟩
        noEligible := fun x' hx' arm harm r' hr' => by
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact h.noEligible_mono wk f x' hx' arm harm r' hr'
          · -- A settlement with a result is normal on every arm.
            rw [List.mem_singleton.mp hx', hxv, armOutcome_nil rfl] at harm
            exact absurd rfl harm
        waitValue := by
          intro r' hr' w' pl' i' c' hw' hpl' hwait hsh'
          rcases List.mem_append.mp hr' with hr' | hr'
          · exact h.waitValue r' hr' w' pl' i' c' hw' hpl' hwait hsh'
          · rw [List.mem_singleton.mp hr'] at hw' hpl' hsh' ⊢
            rw [hresr] at hw'
            have : w' = w := by
              have : s.workflow? p path = some w' := hw'
              rw [hwf] at this
              exact (Option.some.inj this).symm
            subst this
            rw [hresp, hpln, hpl] at hpl'
            cases hpl'
            obtain ⟨e', he'⟩ := hwait
            obtain ⟨i, c, o, hshi, -, ⟨-, -, hnone⟩ | ⟨-, hsome⟩⟩ := settleOutcome_waitStream hout he'
            · cases hnone
            · cases hsome
              rw [hpln, hshape, hshi] at hsh'
              cases hsh'
              rfl }
  | closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, hec, -, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    have he' := execution?_eq_some he
    have hi' := invocation?_eq_some hi
    obtain ⟨j, hj, hje, hja⟩ := act.execActive e he'.1 hec
    have : j = i := wk.invocation_eq_of_id hj hi'.1 (hje.trans (he'.2.trans hi'.2.symm))
    subst this
    have f1 := Facts.setExecution (p := p) (e' := { e with complete := true }) he'.1 rfl (fun _ => rfl)
    have wk1 : (s.setExecution { e with complete := true }).WellKeyed := wk.setExecution _
    have f2 := fun (st : InvocationStatus) => f1.trans
      (Facts.setInvocation (i := j) (i' := { j with status := st }) wk1.invocations hj rfl hja)
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h.of_facts own prov wk (f2 .skipped) rfl (noNewResult rfl)
    · obtain ⟨i3, hi3, hi3e, hi3r, hi3p, -⟩ := own.execOwner e he'.1
      have : i3 = j := wk.invocation_eq_of_id hi3 hj (hi3e.trans hje.symm)
      subst this
      have hres := h.unsettled_of_exec he'.1 hec hj hje
      rw [hi3r, hi3p] at hres
      have f := (f2 .succeeded).trans (Facts.appendResult (p := p) (r := ⟨Key.list eid, e.run, e.placement, eid, none,
        listValue ((s.taskResults.filter fun x => x.execution == eid &&
          ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains x.task).filterMap (·.output.value?))⟩) hres)
      exact h.of_facts own prov wk f rfl (newResult rfl fun w pl hwt hpl e' =>
        not_wait_of_inv own f.workflows hj (hi3r ▸ hwt) (hi3p ▸ hpl) e')
    · exact h.of_facts own prov wk (f2 .succeeded) rfl (noNewResult rfl)
  | closeRun path =>
    obtain ⟨-, -, r, w, output, x, owner, hr, hrc, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
    have hr0 := (run?_eq_some hr).1
    have f1 := Facts.setRun (p := p) (r' := { r with complete := true }) hr' rfl (fun _ => rfl)
    have wk1 : (s.setRun { r with complete := true }).WellKeyed := wk.setRun _
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
    · have hi' := invocation?_eq_some hi
      obtain ⟨j, hj, hjo, hja⟩ := act.runActive r hr0 owner howner htask hrc
      have : j = i := wk.invocation_eq_of_id hj hi'.1 (hjo.trans hi'.2.symm)
      subst this
      have f2 := fun (st : InvocationStatus) => f1.trans
        (Facts.setInvocation (i := j) (i' := { j with status := st }) wk1.invocations hj rfl hja)
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · have hres := h.unsettled_of_run hr0 hrc htask hj (howner.trans (by rw [hjo]))
        have f := (f2 .succeeded).trans (Facts.appendResult (p := p)
          (r := ⟨Key.returned j.id, j.run, j.placement, j.id, none, v⟩) hres)
        exact h.of_facts own prov wk f rfl (newResult rfl fun w pl hwt hpl e =>
          not_wait_of_inv own f.workflows hj hwt hpl e)
      · exact h.of_facts own prov wk (f2 _) rfl (noNewResult rfl)
      · exact h.of_facts own prov wk (f2 _) rfl (noNewResult rfl)
      · exact h.of_facts own prov wk (f2 _) rfl (noNewResult rfl)
    · have he' := execution?_eq_some he
      have f2 := fun (st : TaskStatus) => f1.trans (Facts.setTask (s := s.setRun { r with complete := true })
        (ts := { ts with status := st }) he'.1)
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact h.of_facts own prov wk ((f2 .succeeded).trans (Facts.of_records rfl rfl rfl rfl rfl rfl rfl)) rfl
          (noNewResult rfl)
      · exact h.of_facts own prov wk (f2 _) rfl (noNewResult rfl)
      · exact h.of_facts own prov wk (f2 _) rfl (noNewResult rfl)
      · exact h.of_facts own prov wk (f2 _) rfl (noNewResult rfl)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.of_facts own prov wk (Facts.stop.trans (Facts.of_records rfl rfl rfl rfl rfl rfl rfl)) rfl
        (noNewResult rfl)
    · exact h.of_facts own prov wk (Facts.of_records rfl rfl rfl rfl rfl rfl rfl) rfl (noNewResult rfl)
  | conclude =>
    obtain ⟨-, ⟨-, r, w, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
      exact h.of_facts own prov wk ((Facts.setRun (r' := { r with complete := true }) hr' rfl (fun _ => rfl)).trans
        (Facts.of_records rfl rfl rfl rfl rfl rfl rfl)) rfl (noNewResult rfl)
    · exact h.of_facts own prov wk (Facts.of_records rfl rfl rfl rfl rfl rfl rfl) rfl (noNewResult rfl)

end SettledInv

/-- All four layers of the settlement invariant hold in every reachable state. --/
theorem reachable {p : Definition} {s : State} (h : Reachable p s) :
    Own p s ∧ Active p s ∧ Prov p s ∧ SettledInv p s := by
  induction h with
  | empty => exact ⟨Own.empty, Active.empty, Prov.empty, SettledInv.empty⟩
  | step op hr hs ih =>
    obtain ⟨own, act, prov, sinv⟩ := ih
    have wk := hr.wellKeyed
    have h0 := hr.eq_empty_or_started
    exact ⟨own.step wk h0 hs, act.step own wk h0 hs, prov.step act own wk h0 hs, sinv.step prov act own wk h0 hs⟩

end Suimon.Settle
