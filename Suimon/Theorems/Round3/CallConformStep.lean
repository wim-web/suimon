import Suimon.Theorems.Round3.CallConformReports

/-! Helpers for [14] Round3/CallConform.lean — task E2.

One step of a conforming execution from a running state to an unstopped state keeps `CallInv`. A step
that stops (a failure under the stop policy, or the caller's cancel) does not lead to an unstopped
state, so the stop never cancels a call here. -/

namespace Suimon.Round3
open State

namespace CallConformAux

variable {p : Definition} {env : Env} {s t : State}

/-- A task that has not begun has no call, so storing it keeps the owner of every call. -/
theorem Facts.ownerKept_setTask (F : Facts p s) {e : Execution} {ts ts' : TaskState}
    (he : s.execution? e.id = some e) (hts : ts ∈ e.tasks) (hnb : ¬Limit.Begun ts.status) (hname : ts'.name = ts.name)
    {c : Call} (hc : c ∈ s.calls) : OwnerKept s (s.setTask e ts') c :=
  OwnerKept.setTask he fun name' hn hid heq => F.limit.no_call (execution?_eq_some he).1 hts hnb c hc
    (by rw [hn, ← heq, hname]) hid.symm

/-- A report that fails a call under the continue policy: `failed`, `timedOut`, or `lost` of a call
    that runs or fetches. -/
theorem failCall_step (F : Facts p s) (inv : CallInv env s) (K : Delivery.Kept s t) (wk : t.WellKeyed)
    {c₀ : Call} {st : CallStatus} {fl : Failure} {s' : State}
    (hc₀ : c₀ ∈ s.calls) (hrun : c₀.status = .running ∨ c₀.status = .fetching) (hst : st ≠ .returned)
    (hfailed : st = .failed → (env.behavior.script c₀.id).Final c₀ ∧ (env.behavior.script c₀.id).ending = .failed)
    (hlost : st = .lost → (env.behavior.script c₀.id).Final c₀ ∧ (env.behavior.script c₀.id).ending = .lost)
    (hcancelled : st = .cancelling ∨ st = .cancelled →
      (env.behavior.script c₀.id).Final c₀ ∧ ∃ el, (env.behavior.script c₀.id).ending = .timedOut el)
    (hso : (s.setCall { c₀ with status := st }).settleOwner c₀ .failed .failed = .ok s')
    (ht : t = { s' with failures := s'.failures ++ [fl] }) : CallInv env t := by
  subst ht
  have U := settleOwner_update hso
  have hold : c₀.status ≠ .returned := by rcases hrun with h | h <;> simp [h]
  have hres : ({ s' with failures := s'.failures ++ [fl] } : State).results = s.results := by
    simp [U.results]
  have htr : ({ s' with failures := s'.failures ++ [fl] } : State).taskResults = s.taskResults := by
    simp [U.taskResults]
  refine inv.step K wk (fun c hc => ?_) (fun r hr => Or.inl (hres ▸ hr))
  have hc' : c ∈ (s.setCall { c₀ with status := st }).calls := by rw [← U.calls]; exact hc
  rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc, hne⟩
  · refine Or.inr ⟨callConform_setStatus (inv.calls c₀ hc₀).1 K wk (Frame.of_eq hres htr) hold (fun _ => hst)
      (fun h => absurd h hst) hfailed hlost hcancelled, ?_⟩
    exact ownerConform_frame (ownerConform_failed hst hso) (OwnerKept.of_eq rfl rfl)
  · exact Or.inl ⟨hc, Frame.of_eq hres htr,
      (OwnerKept.setCall.trans (OwnerKept.settleOwner (F.owner_ne hc hc₀ hne) hso)).trans
        (OwnerKept.of_eq rfl rfl)⟩

/-- A cancelling call terminates (`terminated`, or `lost` of a cancelling call). -/
theorem cancelled_step (F : Facts p s) (inv : CallInv env s) (K : Delivery.Kept s t) (wk : t.WellKeyed)
    {c₀ : Call} (hc₀ : c₀ ∈ s.calls) (hcanc : c₀.status = .cancelling)
    (ho : (s.setCall { c₀ with status := .cancelled }).cancelOwner c₀ = .ok t) : CallInv env t := by
  have U := cancelOwner_update ho
  obtain ⟨h1, h2⟩ := inv.calls c₀ hc₀
  have hres : t.results = s.results := by simp [U.results]
  have htr : t.taskResults = s.taskResults := by simp [U.taskResults]
  refine inv.step K wk (fun c hc => ?_) (fun r hr => Or.inl (hres ▸ hr))
  have hc' : c ∈ (s.setCall { c₀ with status := .cancelled }).calls := by rw [← U.calls]; exact hc
  rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc, hne⟩
  · exact Or.inr ⟨callConform_setStatus h1 K wk (Frame.of_eq hres htr) (by simp [hcanc]) (fun _ => by simp)
      (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun _ => h1.cancelled (Or.inl hcanc)),
      ownerConform_cancelled h2 hcanc ho⟩
  · exact Or.inl ⟨hc, Frame.of_eq hres htr,
      OwnerKept.setCall.trans (OwnerKept.cancelOwner (F.owner_ne hc hc₀ hne) ho)⟩

/-- One step of a conforming execution from a running state to an unstopped state keeps the invariant. -/
theorem step_callInv (hr : Reachable p s) (inv : CallInv env s) {op : Op} (hconf : Conforms env s op)
    (hs : step p s op = .ok t) (running : s.status = .running) (us : Unstopped t) : CallInv env t := by
  have F := facts hr
  have K : Delivery.Kept s t :=
    Delivery.step_kept F.wk (hr.eq_empty_or_started.imp (fun h => by rw [h]) id) hs
  have wk : t.WellKeyed := step_wellKeyed F.wk hs
  -- A step that keeps every call.
  have keep : t.calls = s.calls → (∀ c ∈ s.calls, Frame s t c ∧ OwnerKept s t c) →
      (∀ r ∈ t.results, r ∈ s.results ∨ ∀ x k, r.id ≠ Key.callResult x k) → CallInv env t :=
    fun hc hF hres => inv.step K wk (fun c h => Or.inl ⟨hc ▸ h, hF c (hc ▸ h)⟩)
      (fun r h => (hres r h).imp id Or.inl)
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases hr.eq_empty_or_started with rfl | h
    · exact ⟨fun c hc => by simp at hc, fun r hr => by simp at hr⟩
    · rw [h] at hst
      cases hst
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨f, decl, -, -, hcall, rfl⟩ | ⟨judge, arms, -, hcall, rfl⟩ | ⟨wf, out, -, -, rfl⟩ |
        ⟨cc, -, -, rfl⟩
    · refine inv.step K wk (fun c hc => ?_) (fun r hr => Or.inl hr)
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inl ⟨hc, Frame.of_eq rfl rfl, OwnerKept.append ⟨_, rfl⟩ ⟨[], by simp⟩⟩
      · rw [List.mem_singleton.mp hc]
        exact Or.inr (newCall_conform inv hcall rfl rfl rfl fun name hn => by cases hn)
    · refine inv.step K wk (fun c hc => ?_) (fun r hr => Or.inl hr)
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inl ⟨hc, Frame.of_eq rfl rfl, OwnerKept.append ⟨_, rfl⟩ ⟨[], by simp⟩⟩
      · rw [List.mem_singleton.mp hc]
        exact Or.inr (newCall_conform inv hcall rfl rfl rfl fun name hn => by cases hn)
    · exact keep rfl (fun c _ => ⟨Frame.of_eq rfl rfl, OwnerKept.append ⟨_, rfl⟩ ⟨[], by simp⟩⟩)
        (fun r hr => Or.inl hr)
    · exact keep rfl (fun c _ => ⟨Frame.of_eq rfl rfl, OwnerKept.append ⟨_, rfl⟩ ⟨_, rfl⟩⟩) (fun r hr => Or.inl hr)
  | fetch id =>
    obtain ⟨-, -, c₀, hc₀, hstream, hrun, rfl⟩ := Step.fetch_inv hs
    have hc₀m := (call?_eq_some hc₀).1
    refine inv.step K wk (fun c hc => ?_) (fun r hr => Or.inl hr)
    rcases Limit.mem_setCall_iff hc with rfl | ⟨hc, -⟩
    · exact Or.inr ⟨callConform_setStatus (inv.calls c₀ hc₀m).1 K wk (Frame.of_eq rfl rfl) (by simp [hrun])
        (fun _ => by simp) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by simp at h),
        fun h => by simp at h, fun h => by simp at h⟩
    · exact Or.inl ⟨hc, Frame.of_eq rfl rfl, OwnerKept.of_eq rfl rfl⟩
  | returned id value =>
    obtain ⟨-, -, c₀, f, s₁, hc₀, hstream, hrun, -, hacc, hso⟩ := Step.returned_inv hs
    obtain ⟨c, hc, hfinal, hend⟩ := hconf
    rw [hc₀] at hc
    cases hc
    obtain ⟨hc₀m, rfl⟩ := call?_eq_some hc₀
    have U := settleOwner_update hso
    have A := accept_frame hacc
    refine inv.step K wk (fun c hc => ?_) (fun r hr => ?_)
    · have hc' : c ∈ (s.setCall { c₀ with status := .returned }).calls := by
        rw [setCall_calls, ← A.2.2.2.2.2.1, ← setCall_calls, ← U.calls]
        exact hc
      rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc, hne⟩
      · exact Or.inr (returned_conform inv hc₀m hstream hrun hfinal hend hacc hso)
      · have hown := F.owner_ne hc hc₀m hne
        exact Or.inl ⟨hc,
          (Frame.accept hacc hne hown).trans (Frame.setCall.trans (Frame.of_eq U.results U.taskResults)),
          (OwnerKept.of_eq A.2.2.2.2.1 A.2.2.2.2.2.2.1).trans
            (OwnerKept.setCall.trans (OwnerKept.settleOwner hown hso))⟩
    · rw [U.results, setCall_results] at hr
      rcases accept_eq_ok.mp hacc with ⟨-, i, -, -, rfl⟩ | ⟨name, -, -, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Or.inl hr
        · exact Or.inr (Or.inr ⟨c₀, hc₀m, 0, rfl⟩)
      · exact Or.inl hr
  | judged id arm =>
    obtain ⟨-, -, c₀, j, i, pl, judge, arms, s₁, hc₀, hrun, hj, hn, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    obtain ⟨c, hc, hfinal, hend⟩ := hconf
    rw [hc₀] at hc
    cases hc
    obtain ⟨hc₀m, rfl⟩ := call?_eq_some hc₀
    have hstream := F.stream_of_judge hc₀m hn hj
    have A := accept_frame hacc
    refine inv.step K wk (fun c hc => ?_) (fun r hr => ?_)
    · have hc' : c ∈ (s.setCall { c₀ with status := .returned }).calls := by
        rw [setCall_calls, ← A.2.2.2.2.2.1, ← setCall_calls]
        exact hc
      rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc, hne⟩
      · exact Or.inr (judged_conform inv hc₀m hstream hrun hn hi hfinal hend hacc)
      · have hown := F.owner_ne hc hc₀m hne
        refine Or.inl ⟨hc, (Frame.accept hacc hne hown).trans (Frame.setCall.trans Frame.setInvocation),
          (OwnerKept.of_eq A.2.2.2.2.1 A.2.2.2.2.2.2.1).trans
            (OwnerKept.setCall.trans (OwnerKept.setInvocation fun hn' h => ?_))⟩
        exact hown (hn'.trans hn.symm) (h.symm.trans (invocation?_eq_some hi).2)
    · simp only [setInvocation_results, setCall_results] at hr
      rcases accept_eq_ok.mp hacc with ⟨-, i', -, -, rfl⟩ | ⟨name, hn', -, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Or.inl hr
        · exact Or.inr (Or.inr ⟨c₀, hc₀m, 0, rfl⟩)
      · exact Or.inl hr
  | yielded id value =>
    obtain ⟨-, -, c₀, s₁, hc₀, hstream, -, hacc, rfl⟩ := Step.yielded_inv hs
    obtain ⟨c, hc, hy⟩ := hconf
    rw [hc₀] at hc
    cases hc
    obtain ⟨hc₀m, rfl⟩ := call?_eq_some hc₀
    have A := accept_frame hacc
    refine inv.step K wk (fun c hc => ?_) (fun r hr => ?_)
    · have hc' : c ∈ (s.setCall { c₀ with status := .running, yields := c₀.yields + 1 }).calls := by
        rw [setCall_calls, ← A.2.2.2.2.2.1, ← setCall_calls]
        exact hc
      rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc, hne⟩
      · exact Or.inr (yielded_conform inv hc₀m hstream hy hacc)
      · have hown := F.owner_ne hc hc₀m hne
        exact Or.inl ⟨hc, (Frame.accept hacc hne hown).trans Frame.setCall,
          (OwnerKept.of_eq A.2.2.2.2.1 A.2.2.2.2.2.2.1).trans OwnerKept.setCall⟩
    · rw [setCall_results] at hr
      rcases accept_eq_ok.mp hacc with ⟨-, i, -, -, rfl⟩ | ⟨name, -, -, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Or.inl hr
        · exact Or.inr (Or.inr ⟨c₀, hc₀m, c₀.yields, rfl⟩)
      · exact Or.inl hr
  | ended id =>
    obtain ⟨-, -, c₀, hc₀, hstream, hfetch, hso⟩ := Step.ended_inv hs
    obtain ⟨c, hc, hfinal, hend⟩ := hconf
    rw [hc₀] at hc
    cases hc
    obtain ⟨hc₀m, rfl⟩ := call?_eq_some hc₀
    have U := settleOwner_update hso
    have hres : t.results = s.results := by simp [U.results]
    have htr : t.taskResults = s.taskResults := by simp [U.taskResults]
    refine inv.step K wk (fun c hc => ?_) (fun r hr => Or.inl (hres ▸ hr))
    have hc' : c ∈ (s.setCall { c₀ with status := .returned }).calls := by rw [← U.calls]; exact hc
    rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc, hne⟩
    · exact Or.inr ⟨callConform_setStatus (inv.calls c₀ hc₀m).1 K wk (Frame.of_eq hres htr) (by simp [hfetch])
        (fun h => by simp [hstream] at h) (fun _ => ⟨hfinal, hstream, hend⟩) (fun h => by cases h)
        (fun h => by cases h) (fun h => by simp at h), ownerConform_returned hso⟩
    · exact Or.inl ⟨hc, Frame.of_eq hres htr,
        OwnerKept.setCall.trans (OwnerKept.settleOwner (F.owner_ne hc hc₀m hne) hso)⟩
  | failed id =>
    obtain ⟨-, -, c₀, hc₀, hrun, hf⟩ := Step.failed_inv hs
    obtain ⟨c, hc, hfinal, hend⟩ := hconf
    rw [hc₀] at hc
    cases hc
    obtain ⟨hc₀m, rfl⟩ := call?_eq_some hc₀
    obtain ⟨fl, s', -, hso, ht⟩ := failCall_eq_ok.mp hf
    cases hpol : c₀.policy
    · rw [hpol] at ht
      exact (stop_excluded hr running us (by rw [ht]; rfl)
        (by rw [ht, fail_runs, (settleOwner_update hso).runs]; rfl)).elim
    · rw [hpol] at ht
      exact failCall_step F inv K wk hc₀m hrun (by simp) (fun _ => ⟨hfinal, hend⟩) (fun h => by cases h)
        (fun h => by simp at h) hso ht
  | timedOut id element =>
    obtain ⟨-, -, c₀, hc₀, hcond, hf⟩ := Step.timedOut_inv hs
    obtain ⟨c, hc, hfinal, hend⟩ := hconf
    rw [hc₀] at hc
    cases hc
    obtain ⟨hc₀m, rfl⟩ := call?_eq_some hc₀
    have hrun : c₀.status = .running ∨ c₀.status = .fetching := by
      rcases hcond with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact Or.inr h
      · exact h
    obtain ⟨fl, s', -, hso, ht⟩ := failCall_eq_ok.mp hf
    cases hpol : c₀.policy
    · rw [hpol] at ht
      exact (stop_excluded hr running us (by rw [ht]; rfl)
        (by rw [ht, fail_runs, (settleOwner_update hso).runs]; rfl)).elim
    · rw [hpol] at ht
      exact failCall_step F inv K wk hc₀m hrun (by simp) (fun h => by cases h) (fun h => by cases h)
        (fun _ => ⟨hfinal, element, hend⟩) hso ht
  | lost id =>
    obtain ⟨-, -, c₀, hc₀, ⟨hrun, hf⟩ | ⟨hcanc, ho⟩⟩ := Step.lost_inv hs
    · obtain ⟨c, hc, hconf'⟩ := hconf
      rw [hc₀] at hc
      cases hc
      obtain ⟨hc₀m, rfl⟩ := call?_eq_some hc₀
      have hlost : (env.behavior.script c₀.id).Final c₀ ∧ (env.behavior.script c₀.id).ending = .lost := by
        rcases hconf' with h | h
        · rcases hrun with h' | h' <;> rw [h'] at h <;> cases h
        · exact h
      obtain ⟨fl, s', -, hso, ht⟩ := failCall_eq_ok.mp hf
      cases hpol : c₀.policy
      · rw [hpol] at ht
        exact (stop_excluded hr running us (by rw [ht]; rfl)
          (by rw [ht, fail_runs, (settleOwner_update hso).runs]; rfl)).elim
      · rw [hpol] at ht
        exact failCall_step F inv K wk hc₀m hrun (by simp) (fun h => by cases h) (fun _ => hlost)
          (fun h => by simp at h) hso ht
    · exact cancelled_step F inv K wk (call?_eq_some hc₀).1 hcanc ho
  | terminated id =>
    obtain ⟨-, -, c₀, hc₀, hcanc, ho⟩ := Step.terminated_inv hs
    exact cancelled_step F inv K wk (call?_eq_some hc₀).1 hcanc ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact keep rfl (fun c _ => ⟨Frame.of_eq rfl rfl, OwnerKept.of_eq rfl rfl⟩) (fun r hr => Or.inl hr)
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, target, -, -, -, ht⟩ := Step.transformFailed_inv hs
    cases hpol : target.policy
    · rw [hpol] at ht
      subst ht
      exact (stop_excluded hr running us rfl rfl).elim
    · rw [hpol] at ht
      subst ht
      exact keep rfl (fun c _ => ⟨Frame.of_eq rfl rfl, OwnerKept.of_eq rfl rfl⟩) (fun r hr => Or.inl hr)
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    have he' : s.execution? e.id = some e := by rw [(execution?_eq_some he).2]; exact he
    exact keep rfl (fun c hc => ⟨Frame.of_eq rfl rfl,
      F.ownerKept_setTask he' (List.mem_of_find?_eq_some hts) (fun h => h.1 hpend) (by rfl) hc⟩) (fun r hr => Or.inl hr)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, hts, hpend, -, -, ht⟩ := Step.taskInputFailed_inv hs
    have he' : s.execution? e.id = some e := by rw [(execution?_eq_some he).2]; exact he
    cases hpol : spec.policy
    · rw [hpol] at ht
      subst ht
      exact (stop_excluded hr running us rfl rfl).elim
    · rw [hpol] at ht
      subst ht
      exact keep rfl (fun c hc => ⟨Frame.of_eq rfl rfl,
        (F.ownerKept_setTask he' (List.mem_of_find?_eq_some hts) (fun h => h.1 hpend) (by rfl) hc).trans
          (OwnerKept.of_eq rfl rfl)⟩) (fun r hr => Or.inl hr)
  | beginTask eid name =>
    obtain ⟨-, -, e, cc, ts, spec, he, -, -, hts, hready, -, -, hcases⟩ := Step.beginTask_inv hs
    have he' : s.execution? e.id = some e := by rw [(execution?_eq_some he).2]; exact he
    have hem := (execution?_eq_some he).1
    have htsm := List.mem_of_find?_eq_some hts
    have hname : ts.name = name := Delivery.find?_name_of_task hts
    have hnb : ¬Limit.Begun ts.status := fun h => h.2 hready
    rcases hcases with ⟨f, decl, -, -, hcall, rfl⟩ | ⟨wf, out, -, -, rfl⟩
    · refine inv.step K wk (fun c hc => ?_) (fun r hr => Or.inl hr)
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inl ⟨hc, Frame.of_eq rfl rfl,
          (F.ownerKept_setTask he' htsm hnb (by rfl) hc).trans (OwnerKept.of_eq rfl rfl)⟩
      · rw [List.mem_singleton.mp hc]
        refine Or.inr (newCall_conform inv hcall rfl rfl rfl fun name' hn r hr he'' ht => ?_)
        cases hn
        exact F.no_taskResult hem htsm hnb r hr he'' (ht.trans hname.symm)
    · exact keep rfl (fun c hc => ⟨Frame.of_eq rfl rfl,
        (F.ownerKept_setTask he' htsm hnb (by rfl) hc).trans (OwnerKept.of_eq rfl rfl)⟩) (fun r hr => Or.inl hr)
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, cc, spec, r₀, he, -, -, -, hr₀, -, hcases⟩ := Step.taskOutput_inv hs
    have hr₀m := List.mem_of_find?_eq_some hr₀
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · refine keep rfl (fun c _ => ⟨(Frame.setTaskResult hr₀m).trans
        (Frame.appendResult rfl (fun _ => taskOutput_ne_callResult) rfl), OwnerKept.of_eq rfl rfl⟩) (fun r hr => ?_)
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr fun _ _ => taskOutput_ne_callResult
    · exact keep rfl (fun c _ => ⟨Frame.setTaskResult hr₀m, OwnerKept.of_eq rfl rfl⟩) (fun r hr => Or.inl hr)
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, e, spec, r₀, he, -, -, hr₀, -, ht⟩ := Step.taskOutputFailed_inv hs
    have hr₀m := List.mem_of_find?_eq_some hr₀
    cases hpol : spec.policy
    · rw [hpol] at ht
      subst ht
      exact (stop_excluded hr running us rfl rfl).elim
    · rw [hpol] at ht
      subst ht
      exact keep rfl (fun c _ => ⟨(Frame.setTaskResult hr₀m).trans (Frame.of_eq rfl rfl), OwnerKept.of_eq rfl rfl⟩)
        (fun r hr => Or.inl hr)
  | settle path name =>
    obtain ⟨-, -, run, w, pl, shape, kind, x, result, -, -, -, -, -, -, -, hout, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact keep rfl (fun c _ => ⟨Frame.of_eq rfl rfl, OwnerKept.of_eq rfl rfl⟩) (fun r hr => Or.inl hr)
    · have hid := ((settleOutcome_some hout).2.2.2 res rfl).2.1
      refine keep rfl (fun c _ => ⟨Frame.appendResult rfl (fun _ => by rw [hid]; exact aggregate_ne_callResult) rfl,
        OwnerKept.of_eq rfl rfl⟩) (fun r hr => ?_)
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr fun _ _ => by rw [hid]; exact aggregate_ne_callResult
  | closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, -, -, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    have hem := (execution?_eq_some he).1
    have heid := (execution?_eq_some he).2
    have hiid := (invocation?_eq_some hi).2
    -- The invocation of an execution is not the owner of a call of an invocation.
    have owners : ∀ c ∈ s.calls, ∀ st,
        OwnerKept s ((s.setExecution { e with complete := true }).setInvocation { i with status := st }) c := by
      intro c hc st
      refine (OwnerKept.setExecution (e := e) (e' := { e with complete := true }) (by rw [heid]; exact he)
        rfl rfl).trans
        (OwnerKept.setInvocation fun hn h => ?_)
      exact F.keys.disjoint c hc
        (List.mem_map.mpr ⟨e, hem, heid.trans (hiid.symm.trans (h.trans (F.id_of_none hc hn).symm))⟩)
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact keep rfl (fun c hc => ⟨Frame.of_eq rfl rfl, owners c hc _⟩) (fun r hr => Or.inl hr)
    · refine keep rfl (fun c hc => ⟨Frame.appendResult rfl (fun _ => list_ne_callResult) rfl,
        (owners c hc _).trans (OwnerKept.of_eq rfl rfl)⟩) (fun r hr => ?_)
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr fun _ _ => list_ne_callResult
    · exact keep rfl (fun c hc => ⟨Frame.of_eq rfl rfl, owners c hc _⟩) (fun r hr => Or.inl hr)
  | closeRun path =>
    obtain ⟨-, -, run, w, output, x, owner, hrun, -, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    have hrunm := (run?_eq_some hrun).1
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
    · -- The owner of a sub-workflow run is not the owner of a call.
      have owners : ∀ c ∈ s.calls, ∀ st,
          OwnerKept s ((s.setRun { run with complete := true }).setInvocation { i with status := st }) c := by
        intro c hc st
        refine OwnerKept.setRun.trans (OwnerKept.setInvocation fun hn h => ?_)
        exact (F.keys.owners run hrunm owner howner).2 c hc
          ((F.id_of_none hc hn).trans (h.symm.trans (invocation?_eq_some hi).2))
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine keep rfl (fun c hc => ⟨Frame.appendResult rfl (fun _ => returned_ne_callResult) rfl,
          (owners c hc _).trans (OwnerKept.of_eq rfl rfl)⟩) (fun r hr => ?_)
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Or.inl hr
        · exact Or.inr fun _ _ => returned_ne_callResult
      all_goals exact keep rfl (fun c hc => ⟨Frame.of_eq rfl rfl, owners c hc _⟩) (fun r hr => Or.inl hr)
    · -- A task with a workflow body has no call.
      have heid : e.id = owner := (execution?_eq_some he).2
      have hname : ts.name = name := Delivery.find?_name_of_task hts
      have apart : ∀ c ∈ s.calls, ∀ name', c.task = some name' → e.id = c.owner → name ≠ name' := by
        intro c hc name' hn hid heq
        subst heq
        exact F.limit.apart c hc run hrunm name hn htask (by rw [howner, ← heid, hid])
      have owners : ∀ c ∈ s.calls, ∀ st,
          OwnerKept s ((s.setRun { run with complete := true }).setTask e { ts with status := st }) c := by
        intro c hc st
        exact OwnerKept.setRun.trans (OwnerKept.setTask (by rw [heid]; exact he)
          fun name' hn hid h => apart c hc name' hn hid (hname ▸ h))
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact keep rfl (fun c hc => ⟨Frame.appendTaskResult rfl (fun name' hn hid => apart c hc name' hn hid) rfl,
          (owners c hc _).trans (OwnerKept.of_eq rfl rfl)⟩) (fun r hr => Or.inl hr)
      all_goals exact keep rfl (fun c hc => ⟨Frame.of_eq rfl rfl, owners c hc _⟩) (fun r hr => Or.inl hr)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨hst, -⟩⟩ := Step.cancel_inv hs
    · exact (stop_excluded hr running us rfl rfl).elim
    · rw [running] at hst
      cases hst
  | conclude =>
    obtain ⟨-, ⟨-, r, w, -, -, -, rfl⟩ | ⟨hst, -, -⟩⟩ := Step.conclude_inv hs
    · exact keep rfl (fun c _ => ⟨Frame.of_eq rfl rfl, OwnerKept.of_eq rfl rfl⟩) (fun r hr => Or.inl hr)
    · rw [running] at hst
      cases hst

/-- `CallInv` holds along a conforming execution until it stops. -/
theorem conforming_callInv {tr : List Op} (h : Conforming p env tr s) (us : Unstopped s) : CallInv env s := by
  revert us
  induction h with
  | nil => exact fun _ => CallInv.empty
  | @snoc tr s₀ t₀ op hprev hconf hs _ ih =>
    intro us
    have hr := hprev.reachable
    have us₀ := unstopped_prev hs us
    exact step_callInv hr (ih us₀) hconf hs (running_of_unstopped hr us₀ hs) us

end CallConformAux

end Suimon.Round3
