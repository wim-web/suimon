import Suimon.Theorems.DeliveryOwners

/-! Every step keeps the status invariant `Dyn`. -/

namespace Suimon.Delivery
open State

section
variable {p : Definition} {s t : State} {op : Op}

/-- Controls of different kinds. --/
theorem control_ne_workflow {pl : Placement} {wf out : String}
    (h : (∃ f, pl.control = .call (.function f)) ∨ ∃ j arms, pl.control = .branch j arms) :
    pl.control ≠ .call (.workflow wf out) := by
  rcases h with ⟨f, h⟩ | ⟨j, arms, h⟩ <;> rw [h] <;> simp

theorem control_ne_concurrency {pl : Placement} {c : Concurrency}
    (h : (∃ f, pl.control = .call (.function f)) ∨ ∃ j arms, pl.control = .branch j arms) :
    pl.control ≠ .concurrency c := by
  rcases h with ⟨f, h⟩ | ⟨j, arms, h⟩ <;> rw [h] <;> simp

/-- An invocation that is no longer active has stopped all it owns. --/
theorem step_nonActive (inv : Inv p s) (hs : step p s op = .ok t) :
    ∀ i ∈ t.invocations, i.status ≠ .active →
      (∀ c ∈ t.calls, c.owner = i.id → c.task = none → c.status ≠ .running ∧ c.status ≠ .fetching) ∧
      (∀ r ∈ t.runs, r.owner = some i.id → r.task = none → r.complete = true) ∧
      (∀ e ∈ t.executions, e.id = i.id → e.complete = true) := by
  intro i hi hna
  rcases step_invocations_back hs i hi with ⟨i₀, hi₀, hid, -, -, -, -⟩ | hnew
  · have oldCall : ∀ c ∈ t.calls, c.owner = i.id → c.task = none → CallOld s c := fun c hc ho ht =>
      call_of_old_owner hs hc ht hi₀ (ho.trans hid.symm)
    have oldRun : ∀ r ∈ t.runs, r.owner = some i.id → r.task = none → RunOld s r := fun r hr ho ht =>
      run_of_old_owner hs (runs_nil_or_started inv) hr ht hi₀ (by rw [ho, hid])
    have oldExec : ∀ e ∈ t.executions, e.id = i.id → ExecOld s e := fun e he heid =>
      execution_of_old_id hs he hi₀ (heid.trans hid.symm)
    rcases step_invocation_change inv.wk hs hi₀ hi hid.symm with rfl | ⟨-, -, -, -, -, hc⟩
    · -- Unchanged: what it owns was stopped already.
      obtain ⟨hcalls, hruns, hexecs⟩ := inv.dyn.nonActive i hi₀ hna
      refine ⟨fun c hc ho ht => ?_, fun r hr ho ht => ?_, fun e he heid => ?_⟩
      · obtain ⟨c₀, hc₀, -, cowner, ctask, -, -, crun⟩ := oldCall c hc ho ht
        obtain ⟨h1, h2⟩ := hcalls c₀ hc₀ (cowner.trans ho) (ctask.trans ht)
        exact ⟨fun h => (crun (Or.inl h)).elim h1 h2, fun h => (crun (Or.inr h)).elim h1 h2⟩
      · obtain ⟨r₀, hr₀, -, -, -, rowner, rtask, hcomp⟩ := oldRun r hr ho ht
        exact hcomp (hruns r₀ hr₀ (rowner.trans ho) (rtask.trans ht))
      · obtain ⟨e₀, he₀, eid, -, -, -, hcomp⟩ := oldExec e he heid
        exact hcomp (hexecs e₀ he₀ (eid.trans heid))
    · rcases hc with ⟨c, hc, hco, hct, hcalls, -, -⟩ | ⟨e, he, heid, -, -, hexec⟩ | ⟨R, hR, hRo, hRt, -, -, hruns⟩
      · -- Settled through its call: a function call or branch owns only that call.
        obtain ⟨hcid, pl, hpl, hk⟩ := call_placement inv.own inv.wk hc hct hi₀ hco.symm
        have hkind : (∃ f, pl.control = .call (.function f)) ∨ ∃ j arms, pl.control = .branch j arms := by
          rcases hk with ⟨f, d, hf, -⟩ | ⟨j, arms, hb, -⟩
          · exact Or.inl ⟨f, hf⟩
          · exact Or.inr ⟨j, arms, hb⟩
        refine ⟨fun c' hc' ho ht => ?_, fun r hr ho ht => ?_, fun e he heid => ?_⟩
        · obtain ⟨c₀, hc₀, cid, cowner, ctask, -⟩ := oldCall c' hc' ho ht
          obtain ⟨hc₀id, -⟩ := call_placement inv.own inv.wk hc₀ (ctask.trans ht) hi₀ (by rw [cowner, ho, hid])
          exact hcalls c' hc' (cid.symm.trans (hc₀id.trans (cowner.trans (ho.trans (hid.symm.trans
            (hco.symm.trans hcid.symm))))))
        · obtain ⟨r₀, hr₀, -, -, -, rowner, rtask, -⟩ := oldRun r hr ho ht
          obtain ⟨-, pl', hpl', wf, out, hwf⟩ :=
            run_placement inv.own inv.wk hr₀ (rtask.trans ht) hi₀ (by rw [rowner, ho, hid])
          obtain rfl := hpl.unique hpl'
          exact absurd hwf (control_ne_workflow hkind)
        · obtain ⟨e₀, he₀, eid, -, -, -, -⟩ := oldExec e he heid
          obtain ⟨-, -, pl', c', hpl', hcc, -⟩ :=
            execution_placement inv.own inv.wk he₀ hi₀ (by rw [eid, heid, hid])
          obtain rfl := hpl.unique hpl'
          exact absurd hcc (control_ne_concurrency hkind)
      · -- Closed through its execution: a concurrency invocation owns only that execution.
        obtain ⟨-, -, pl, cc, hpl, hcc, -⟩ := execution_placement inv.own inv.wk he hi₀ heid.symm
        refine ⟨fun c' hc' ho ht => ?_, fun r hr ho ht => ?_, fun e' he' heid' => ?_⟩
        · obtain ⟨c₀, hc₀, -, cowner, ctask, -⟩ := oldCall c' hc' ho ht
          obtain ⟨-, pl', hpl', hk⟩ := call_placement inv.own inv.wk hc₀ (ctask.trans ht) hi₀ (by rw [cowner, ho, hid])
          obtain rfl := hpl.unique hpl'
          rcases hk with ⟨f, d, hf, -⟩ | ⟨j, arms, hb, -⟩
          · rw [hf] at hcc; cases hcc
          · rw [hb] at hcc; cases hcc
        · obtain ⟨r₀, hr₀, -, -, -, rowner, rtask, -⟩ := oldRun r hr ho ht
          obtain ⟨-, pl', hpl', wf, out, hwf⟩ :=
            run_placement inv.own inv.wk hr₀ (rtask.trans ht) hi₀ (by rw [rowner, ho, hid])
          obtain rfl := hpl.unique hpl'
          rw [hwf] at hcc; cases hcc
        · exact hexec e' he' (heid'.trans (hid.symm.trans heid.symm))
      · -- Closed through its sub-run: a sub-workflow invocation owns only that run.
        obtain ⟨hRp, pl, hpl, wf, out, hwf⟩ := run_placement inv.own inv.wk hR hRt hi₀ hRo
        refine ⟨fun c' hc' ho ht => ?_, fun r hr ho ht => ?_, fun e' he' heid' => ?_⟩
        · obtain ⟨c₀, hc₀, -, cowner, ctask, -⟩ := oldCall c' hc' ho ht
          obtain ⟨-, pl', hpl', hk⟩ := call_placement inv.own inv.wk hc₀ (ctask.trans ht) hi₀ (by rw [cowner, ho, hid])
          obtain rfl := hpl.unique hpl'
          rcases hk with ⟨f, d, hf, -⟩ | ⟨j, arms, hb, -⟩
          · rw [hf] at hwf; cases hwf
          · rw [hb] at hwf; cases hwf
        · obtain ⟨r₀, hr₀, rpath, -, -, rowner, rtask, -⟩ := oldRun r hr ho ht
          obtain ⟨hr₀p, -⟩ := run_placement inv.own inv.wk hr₀ (rtask.trans ht) hi₀ (by rw [rowner, ho, hid])
          exact hruns r hr (by rw [← rpath, hr₀p, hRp])
        · obtain ⟨e₀, he₀, eid, -, -, -, -⟩ := oldExec e' he' heid'
          obtain ⟨-, -, pl', c', hpl', hcc, -⟩ :=
            execution_placement inv.own inv.wk he₀ hi₀ (by rw [eid, heid', hid])
          obtain rfl := hpl.unique hpl'
          rw [hwf] at hcc; cases hcc
  · exact absurd hnew.active hna

/-- A running or fetching task call keeps its task active. --/
theorem step_taskActive (inv : Inv p s) (hs : step p s op = .ok t) :
    ∀ c ∈ t.calls, ∀ name, c.task = some name → (c.status = .running ∨ c.status = .fetching) →
      ∀ e ∈ t.executions, e.id = c.owner → ∀ tk ∈ e.tasks, tk.name = name → tk.status = .active := by
  have wk' := step_wellKeyed inv.wk hs
  intro c hc name htask hrun e he heid tk htk hname
  rcases step_calls_back hs c hc with ⟨c₀, hc₀, cid, cowner, ctask, -, -, crun⟩ | ⟨-, -, hcase⟩
  · have hrun₀ := crun hrun
    obtain ⟨e₀, he₀, he₀id⟩ : ∃ e₀ ∈ s.executions, e₀.id = c₀.owner := by
      rcases inv.own.calls c₀ hc₀ with ⟨ht, -⟩ | ⟨_, _, _, e₀, he₀, he₀o, -⟩
      · rw [ctask, htask] at ht; cases ht
      · exact ⟨e₀, he₀, he₀o⟩
    have hid : e.id = e₀.id := by rw [heid, he₀id, cowner]
    have A := inv.dyn.taskActive c₀ hc₀ name (ctask.trans htask) hrun₀ e₀ he₀ he₀id
    obtain ⟨tk₀, htk₀, tname, hst⟩ := step_task_change inv.wk hs he₀ he hid tk htk
    rcases hst with hst | hch
    · rw [hst]; exact A tk₀ htk₀ (tname.trans hname)
    · rcases hch with ⟨c', hc', hc'o, hc't, hc's⟩ | ⟨R, hR, hRo, hRt, -⟩ | ⟨ts, hts, hp⟩ | hp
      · -- The task's call stopped; it is this call.
        have e1 := task_body_function inv.own inv.wk hc' hc't he₀ hc'o.symm
        have e2 := task_body_function inv.own inv.wk hc₀ (ctask.trans htask) he₀ he₀id
        have hcc : c.id = c'.id := by rw [← cid, e2.1, e1.1, tname, hname]
        obtain ⟨h1, h2⟩ := hc's c hc hcc
        rcases hrun with h | h
        · exact absurd h h1
        · exact absurd h h2
      · -- A task has no run besides its call.
        exact (task_call_run inv.own inv.wk hc₀ hR (ctask.trans htask) (by rw [hRt, tname, hname])
          (by rw [hRo, he₀id])).elim
      · have := A ts (List.mem_of_find?_eq_some hts) (by rw [find?_name_of_task hts, tname, hname])
        rcases hp with hp | hp <;> rw [hp] at this <;> cases this
      · have := A tk₀ htk₀ (tname.trans hname)
        rcases hp with hp | hp <;> rw [hp] at this <;> cases this
  · rcases hcase with ⟨ht, -⟩ | ⟨name', e₁, ts, spec, f, ht, hkey, he₁, -, hts, -, -, -, hmem, -⟩
    · rw [htask] at ht; cases ht
    · rw [htask] at ht
      cases ht
      obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
      obtain rfl : e = withTask e₁ { ts with status := .active } :=
        wk'.execution_eq_of_id he hmem (by rw [heid, ← he₁id]; rfl)
      rcases mem_withTask htk with rfl | ⟨-, hne⟩
      · rfl
      · exact absurd (hname.trans (find?_name_of_task hts).symm) hne

theorem included_iff {c : Concurrency} {name : String} :
    ((c.tasks.filter (·.output.isSome)).map (·.name)).contains name = true ↔
      ∃ spec ∈ c.tasks, spec.name = name ∧ spec.output.isSome := by
  simp only [List.contains_iff_mem, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨spec, ⟨hs, ho⟩, hn⟩
    exact ⟨spec, hs, hn, ho⟩
  · rintro ⟨spec, hs, hn, ho⟩
    exact ⟨spec, ⟨hs, ho⟩, hn⟩

/-- A complete execution stopped its tasks and transformed its output (§8.3). --/
theorem step_execDone (inv : Inv p s) (hs : step p s op = .ok t) :
    ∀ e ∈ t.executions, e.complete = true →
      (∀ c ∈ t.calls, c.owner = e.id → c.task ≠ none → c.status.ended = true) ∧
      (∀ r ∈ t.runs, r.owner = some e.id → r.task ≠ none → r.complete = true) ∧
      (∀ c, t.concurrencyOf p e = .ok c → ∀ r ∈ t.taskResults, r.execution = e.id →
        (∃ spec ∈ c.tasks, spec.name = r.task ∧ spec.output.isSome) → r.output ≠ .pending) := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  intro e he hcomp
  rcases step_executions_back hs e he with ⟨e₀, he₀, eid, erun, epl, -, -⟩ | ⟨-, hc, -⟩
  · obtain ⟨i, hi, hiid, hir, hip, cc, hcc⟩ := inv.own.executions e₀ he₀
    have hcc' : t.concurrencyOf p e = .ok cc := K.concurrencyOf wk' erun.symm epl.symm hcc
    rcases step_execution_completed inv.wk hs he₀ he eid.symm with hsame | ⟨cc', hcc2, hended, hout, htc, htr, httr⟩
    · -- Complete before the step: nothing of it restarts.
      have hc₀ : e₀.complete = true := hsame ▸ hcomp
      obtain ⟨C1, C2, C3⟩ := inv.dyn.execDone e₀ he₀ hc₀
      refine ⟨fun c hc ho ht => ?_, fun r hr ho ht => ?_, fun c' hc' r hr hre hinc => ?_⟩
      · rcases step_calls_back hs c hc with ⟨c₀, hc₀', cid, cowner, ctask, -⟩ | ⟨-, -, hcase⟩
        · have hend := C1 c₀ hc₀' (by rw [cowner, ho, eid]) (by rw [ctask]; exact ht)
          obtain ⟨c'', hc'', hid'', -, -, -, -, hsame'⟩ := K.call c₀ hc₀'
          obtain rfl := hsame' hend
          obtain rfl := wk'.call_eq_of_id hc hc'' (cid.symm.trans hid''.symm)
          exact hend
        · rcases hcase with ⟨ht', -⟩ | ⟨name, e₁, ts, spec, f, -, -, he₁, hc₁, -⟩
          · exact absurd ht' ht
          · obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
            obtain rfl := inv.wk.execution_eq_of_id he₁m he₀ (by rw [he₁id, ho, eid])
            rw [hc₀] at hc₁; cases hc₁
      · rcases step_runs_back (runs_nil_or_started inv) hs r hr with ⟨r₀, hr₀, -, -, -, rowner, rtask, hrc⟩ |
            ⟨-, -, hcase⟩
        · exact hrc (C2 r₀ hr₀ (by rw [rowner, ho, eid]) (by rw [rtask]; exact ht))
        · rcases hcase with ⟨-, ho', -⟩ | ⟨ht', -⟩ | ⟨name, e₁, ts, spec, wf, out, -, ho', he₁, hc₁, -⟩
          · rw [ho] at ho'; cases ho'
          · exact absurd ht' ht
          · obtain ⟨he₁m, -⟩ := execution?_eq_some he₁
            have h1 : e₁.id = e₀.id := by
              have := ho'.symm.trans ho
              rw [Option.some.injEq] at this
              rw [this, eid]
            obtain rfl := inv.wk.execution_eq_of_id he₁m he₀ h1
            rw [hc₀] at hc₁; cases hc₁
      · rw [hcc'] at hc'
        cases hc'
        rcases step_taskResults_back hs r hr with ⟨r₀, hr₀, rexec, rtask, -, rout⟩ | ⟨-, hsrc⟩
        · have h := C3 cc hcc r₀ hr₀ (by rw [rexec, hre, eid]) (by rw [rtask]; exact hinc)
          rw [rout h]
          exact h
        · rcases hsrc with ⟨c'', hc'', hco, hct, hrun⟩ | ⟨R, hR, hRo, hRt, hRc⟩
          · have h := C1 c'' hc'' (by rw [hco, hre, eid]) (by rw [hct]; simp)
            rcases hrun with h' | h' <;> simp [h', CallStatus.ended] at h
          · have h := C2 R hR (by rw [hRo, hre, eid]) (by rw [hRt]; simp)
            rw [hRc] at h; cases h
    · -- Closed by this step, after its tasks ended and its outputs were transformed.
      refine ⟨fun c hc ho ht => ?_, fun r hr ho ht => ?_, fun c' hc' r hr hre hinc => ?_⟩
      · rw [htc] at hc
        cases hname : c.task with
        | none => exact absurd hname ht
        | some name =>
          obtain ⟨-, ⟨tk, htk, htkn⟩, -⟩ := task_body_function inv.own inv.wk hc hname he₀ (by rw [ho, eid])
          obtain ⟨-, hna, hncan, -⟩ := taskEnded_iff.mp (List.all_eq_true.mp hended tk htk)
          cases hst : c.status
          · exact absurd (inv.dyn.taskActive c hc name hname (Or.inl hst) e₀ he₀ (by rw [ho, eid]) tk htk htkn) hna
          · exact absurd (inv.dyn.taskActive c hc name hname (Or.inr hst) e₀ he₀ (by rw [ho, eid]) tk htk htkn) hna
          · exact absurd hst (hncan c hc (by rw [ho, eid]) (by rw [hname, htkn]))
          all_goals rfl
      · rw [htr] at hr
        cases hname : r.task with
        | none => exact absurd hname ht
        | some name =>
          obtain ⟨⟨tk, htk, htkn⟩, -⟩ := task_body_workflow inv.own inv.wk hr hname he₀ (by rw [ho, eid])
          exact (taskEnded_iff.mp (List.all_eq_true.mp hended tk htk)).2.2.2 r hr (by rw [ho, eid])
            (by rw [hname, htkn])
      · rw [httr] at hr
        rw [hcc'] at hc'
        cases hc'
        rw [hcc] at hcc2
        cases hcc2
        have h := List.all_eq_true.mp hout r (List.mem_filter.mpr ⟨hr, by
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨by rw [hre, eid], included_iff.mpr hinc⟩⟩)
        simpa using h
  · rw [hc] at hcomp; cases hcomp

theorem StreamSource.kept (K : Kept s t) (wk' : t.WellKeyed) {i i' : Invocation} (h : StreamSource p s i)
    (hrun : i'.run = i.run) (hpl : i'.placement = i.placement) : StreamSource p t i' := by
  obtain ⟨w, pl, hw, hplc, hk⟩ := h
  exact ⟨w, pl, hrun ▸ K.workflow? wk' hw, hpl ▸ hplc, hk⟩

/-- A step changes the arm of an invocation only for a branch. --/
theorem arm_kept (inv : Inv p s) (hs : step p s op = .ok t) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hi' : i' ∈ t.invocations) (hid : i'.id = i.id) {pl : Placement} (hpl : PlacementOf p s i pl)
    (hnb : ∀ j arms, pl.control ≠ .branch j arms) : i'.arm = i.arm := by
  rcases step_invocation_change inv.wk hs hi hi' hid with rfl | ⟨-, -, -, -, -, hc⟩
  · rfl
  · rcases hc with ⟨-, -, -, -, -, -, ha | ⟨j, arms, w, pl', hw, hpl', hb⟩⟩ | ⟨-, -, -, -, ha, -⟩ | ⟨-, -, -, -, -, ha, -⟩
    · exact ha
    · obtain rfl := hpl.unique ⟨w, hw, hpl'⟩
      exact absurd hb (hnb j arms)
    · exact ha
    · exact ha

/-- Every result belongs to the invocation that produced it, or is an aggregate. --/
theorem step_results (inv : Inv p s) (hs : step p s op = .ok t) : ∀ r ∈ t.results, ResultOwned p t r := by
  have K := inv.kept hs
  have wk' := step_wellKeyed inv.wk hs
  intro r hr
  rcases step_results_back hs r hr with hr₀ | ⟨-, -, -, hcase⟩
  · rcases inv.dyn.results r hr₀ with ⟨i, hi, hip, hir, hipl, hia, hst⟩ | ⟨hp, ha, x, hx, hxr, hxp, hxo, hxa⟩
    · obtain ⟨i', hi', a1, a2, a3, -, -⟩ := K.invocation i hi
      by_cases hact : i.status = .active
      · -- A running invocation owns results only when they stream; its placement is no branch.
        have hss : StreamSource p s i := by
          rcases hst with h | h
          · rw [hact] at h; cases h
          · exact h
        obtain ⟨w, pl, hw, hplc, hk⟩ := hss
        have hnb : ∀ j arms, pl.control ≠ .branch j arms := by
          intro j arms h
          rcases hk with ⟨f, d, hf, -⟩ | ⟨c, hc, -⟩
          · rw [hf] at h; cases h
          · rw [hc] at h; cases h
        have harm := arm_kept inv hs hi hi' a1 ⟨w, hw, hplc⟩ hnb
        exact Or.inl ⟨i', hi', by rw [a1, hip], by rw [a2, hir], by rw [a3, hipl], by rw [harm, hia],
          Or.inr (StreamSource.kept K wk' ⟨w, pl, hw, hplc, hk⟩ a2 a3)⟩
      · obtain rfl := frozen inv hs hi hact hi' a1
        exact Or.inl ⟨i', hi', hip, hir, hipl, hia, hst.imp id fun h => StreamSource.kept K wk' h rfl rfl⟩
    · exact Or.inr ⟨hp, ha, x, K.mem_settled hx, hxr, hxp, hxo, hxa⟩
  · rcases hcase with ⟨c, hc, i, hi, hct, -, -, ⟨f, hf⟩, hio, hrr, hrp, hrprod, hra, hmem⟩ |
        ⟨c, hc, i, hi, arm, j, arms, w, pl, hct, -, hio, -, -, -, hrr, hrp, hrprod, hra, hmem⟩ |
        ⟨c, hc, i, hi, hct, -, hstream, hio, hrr, hrp, hrprod, hra⟩ |
        ⟨e, he, cc, tr, hcc, hout, -, -, -, -, hrr, hrp, hrprod, hra⟩ |
        ⟨e, he, i, hi, cc, -, hio, hcc, -, hrr, hrp, hrprod, hra, hmem⟩ |
        ⟨R, hR, i, hi, -, hRt, hRo, hrr, hrp, hrprod, hra, hmem⟩ |
        ⟨run, w, pl, shape, kind, x, hrun, hw, hpl, -, -, -, hout, hx⟩
    · -- returned: its invocation succeeded; a function call records no arm.
      obtain ⟨hcid, pl, hpl, hk⟩ := call_placement inv.own inv.wk hc hct hi hio
      have hnb : ∀ j arms, pl.control ≠ .branch j arms := by
        rcases hk with ⟨f', d, hf', -⟩ | ⟨j, arms, hb, htgt, -⟩
        · intro j arms h; rw [hf'] at h; cases h
        · rw [hf] at htgt; cases htgt
      have harm := arm_none inv.own hi hpl hnb
      exact Or.inl ⟨_, hmem, by rw [hrprod, hcid, hio], hrr.symm, hrp.symm, by rw [hra]; exact harm, Or.inl rfl⟩
    · -- judged: its invocation succeeded with the chosen arm.
      obtain ⟨hcid, -⟩ := call_placement inv.own inv.wk hc hct hi hio
      exact Or.inl ⟨_, hmem, by rw [hrprod, hcid, hio], hrr.symm, hrp.symm, hra.symm, Or.inl rfl⟩
    · -- yielded: a Stream function call.
      obtain ⟨hcid, pl, ⟨w, hw, hplc⟩, hk⟩ := call_placement inv.own inv.wk hc hct hi hio
      obtain ⟨f, d, hf, hd, -, hs'⟩ : ∃ f d, pl.control = .call (.function f) ∧ p.function? f = some d ∧
          c.target = .function f ∧ c.stream = (d.output.kind == .stream) := by
        rcases hk with h | ⟨-, -, -, -, h⟩
        · exact h
        · rw [hstream] at h; cases h
      have hkind : d.output.kind = .stream := by
        rw [hstream] at hs'; simpa using hs'.symm
      obtain ⟨i', hi', a1, a2, a3, -, -⟩ := K.invocation i hi
      have hnb : ∀ j arms, pl.control ≠ .branch j arms := fun j arms h => by rw [hf] at h; cases h
      have harm := arm_kept inv hs hi hi' a1 ⟨w, hw, hplc⟩ hnb
      exact Or.inl ⟨i', hi', by rw [a1, hrprod, hcid, hio], by rw [a2, hrr], by rw [a3, hrp],
        by rw [harm, arm_none inv.own hi ⟨w, hw, hplc⟩ hnb, hra],
        Or.inr (StreamSource.kept K wk' ⟨w, pl, hw, hplc, Or.inl ⟨f, d, hf, hd, hkind⟩⟩ a2 a3)⟩
    · -- a task output of a Stream concurrency.
      obtain ⟨i, hi, hiid, -, -, -⟩ := inv.own.executions e he
      obtain ⟨hir, hip, pl, cc', ⟨w, hw, hplc⟩, hcc', hcce⟩ := execution_placement inv.own inv.wk he hi hiid
      rw [hcc] at hcce
      cases hcce
      obtain ⟨i', hi', a1, a2, a3, -, -⟩ := K.invocation i hi
      have hnb : ∀ j arms, pl.control ≠ .branch j arms := fun j arms h => by rw [hcc'] at h; cases h
      have harm := arm_kept inv hs hi hi' a1 ⟨w, hw, hplc⟩ hnb
      exact Or.inl ⟨i', hi', by rw [a1, hiid, hrprod], by rw [a2, hir, hrr], by rw [a3, hip, hrp],
        by rw [harm, arm_none inv.own hi ⟨w, hw, hplc⟩ hnb, hra],
        Or.inr (StreamSource.kept K wk' ⟨w, pl, hw, hplc, Or.inr ⟨cc, hcc', hout⟩⟩ a2 a3)⟩
    · -- the list of a concurrency: its invocation succeeded.
      obtain ⟨hir, hip, pl, cc', hpl, hcc', -⟩ := execution_placement inv.own inv.wk he hi hio
      have hnb : ∀ j arms, pl.control ≠ .branch j arms := fun j arms h => by rw [hcc'] at h; cases h
      exact Or.inl ⟨_, hmem, by rw [hrprod]; exact hio, by rw [hrr, hir], by rw [hrp, hip],
        by rw [hra]; exact arm_none (i := i) inv.own hi hpl hnb, Or.inl rfl⟩
    · -- the result a sub-workflow returned: its invocation succeeded.
      obtain ⟨-, pl, hpl, wf, out, hwf⟩ := run_placement inv.own inv.wk hR hRt hi hRo
      have hnb : ∀ j arms, pl.control ≠ .branch j arms := fun j arms h => by rw [hwf] at h; cases h
      exact Or.inl ⟨_, hmem, hrprod.symm, hrr.symm, hrp.symm, by rw [hra]; exact arm_none (i := i) inv.own hi hpl hnb,
        Or.inl rfl⟩
    · -- an aggregate recorded with its settlement.
      obtain ⟨hxo, hxa, -, -, hrrun, hrpl, hrprod, hra⟩ := settleOutcome_res hout
      obtain ⟨-, hxrun, hxpl, -⟩ := State.settleOutcome_some hout
      have hname := (Workflow.placement?_eq_some hpl).2
      exact Or.inr ⟨by rw [hrprod, hrrun, hrpl], hra, x, hx, by rw [hxrun, hrrun], by rw [hxpl, hrpl], hxo, hxa⟩

theorem step_dyn (inv : Inv p s) (hs : step p s op = .ok t) : Dyn p t :=
  ⟨step_nonActive inv hs, step_taskActive inv hs, step_execDone inv hs, step_results inv hs⟩

end

end Suimon.Delivery
