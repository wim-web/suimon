import Suimon.Theorems.Round3.Conformance

/-! An invariant for `calm_progress` (task C2): a run of a task runs the workflow its task's body
    names. Round 2 `Settle.Own.runTask` records a workflow body but not which workflow, and
    `closeRun` needs it to find the designated output among the run's placements. -/

namespace Suimon.Round3.CalmAux
open State Settle

/-- A run of a task runs the workflow its task's body names. -/
def TaskRunWf (p : Definition) (s : State) : Prop :=
  ∀ r ∈ s.runs, ∀ name, r.task = some name → ∃ e ∈ s.executions, r.owner = some e.id ∧
    ∃ spec out, s.taskSpec p e name = .ok spec ∧ spec.body = .workflow r.workflow out

namespace TaskRunWf
variable {p : Definition} {s t : State}

theorem empty : TaskRunWf p {} := fun _ hr => nomatch hr

/-- Old runs keep their key, old executions keep theirs, and every new task run is justified. -/
theorem of_extend (h : TaskRunWf p s) (hw : KeepsWorkflows p s t)
    (hexec : ∀ e ∈ s.executions, ∃ e' ∈ t.executions, execKey e' = execKey e)
    (hruns : ∀ r ∈ t.runs, (∃ r₀ ∈ s.runs, runKey r₀ = runKey r) ∨
      (∀ name, r.task = some name → ∃ e ∈ t.executions, r.owner = some e.id ∧
        ∃ spec out, t.taskSpec p e name = .ok spec ∧ spec.body = .workflow r.workflow out)) :
    TaskRunWf p t := by
  intro r hr name htask
  rcases hruns r hr with ⟨r₀, hr₀, hkey⟩ | hnew
  · obtain ⟨-, hwf, hown, htk⟩ := runKey_eq.mp hkey
    obtain ⟨e₀, he₀, heo, spec, out, hspec, hbody⟩ := h r₀ hr₀ name (htk ▸ htask)
    obtain ⟨e', he', hk'⟩ := hexec e₀ he₀
    obtain ⟨hid, hrun, hpl, -⟩ := execKey_eq.mp hk'
    exact ⟨e', he', by rw [← hown, heo, hid], spec, out, hw.taskSpec hrun hpl hspec, hwf ▸ hbody⟩
  · exact hnew name htask

theorem of_sameKeys (h : TaskRunWf p s) (hk : SameKeys p s t) : TaskRunWf p t :=
  h.of_extend hk.workflows (fun _ he => exists_of_map_eq hk.executions he)
    (fun _ hr => Or.inl (exists_of_map_eq hk.runs.symm hr))

/-- Steps that add records other than runs and executions. -/
theorem of_same (h : TaskRunWf p s) (hr : t.runs = s.runs) (he : t.executions = s.executions) : TaskRunWf p t :=
  h.of_extend (KeepsWorkflows.of_runs hr) (fun e he' => ⟨e, he ▸ he', rfl⟩)
    (fun r hr' => Or.inl ⟨r, hr ▸ hr', rfl⟩)

/-- Every step keeps the invariant. -/
theorem step (h : TaskRunWf p s) (wk : s.WellKeyed) {op : Op} (hs : Suimon.step p s op = .ok t) :
    TaskRunWf p t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    intro r hr name htask
    simp only [List.mem_singleton] at hr
    subst hr
    simp at htask
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, rfl, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨f, decl, hc, hdecl, -, rfl⟩ | ⟨judge, arms, hc, -, rfl⟩ | ⟨wf, out, hc, -, rfl⟩ |
      ⟨cc, hc, -, rfl⟩
    · exact h.of_same rfl rfl
    · exact h.of_same rfl rfl
    · refine h.of_extend (KeepsWorkflows.of_append rfl) (fun e he => ⟨e, he, rfl⟩) (fun x hx => ?_)
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · rw [List.mem_singleton.mp hx]
        exact Or.inr fun _ h => nomatch h
    · exact h.of_extend (KeepsWorkflows.of_runs rfl)
        (fun e he => ⟨e, List.mem_append_left _ he, rfl⟩) (fun x hx => Or.inl ⟨x, hx, rfl⟩)
  | fetch id =>
    obtain ⟨-, -, c, hc, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.of_sameKeys (SameKeys.setCall wk.calls (call?_eq_some hc).1 rfl)
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have k1 : SameKeys p s s' := SameKeys.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    have k2 := k1.trans (SameKeys.setCall (c' := { c with status := .returned }) (k1.calls_nodup wk.calls) hc' rfl)
    exact h.of_sameKeys (k2.trans (SameKeys.settleOwner (k2.invocations_nodup wk.invocations)
      (k2.executions_nodup wk.executions) hso))
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, -, -, -, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have k1 : SameKeys p s s' := SameKeys.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    have k2 := k1.trans (SameKeys.setCall (c' := { c with status := .returned }) (k1.calls_nodup wk.calls) hc' rfl)
    have hi' : i ∈ (s'.setCall { c with status := .returned }).invocations := by
      rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]; exact (invocation?_eq_some hi).1
    exact h.of_sameKeys (k2.trans (SameKeys.setInvocation (k2.invocations_nodup wk.invocations) hi' rfl))
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    have k1 : SameKeys p s s' := SameKeys.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact h.of_sameKeys (k1.trans (SameKeys.setCall (k1.calls_nodup wk.calls) hc' rfl))
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    have k1 := SameKeys.setCall (p := p) (c' := { c with status := .returned }) wk.calls (call?_eq_some hc).1 rfl
    exact h.of_sameKeys (k1.trans (SameKeys.settleOwner (k1.invocations_nodup wk.invocations)
      (k1.executions_nodup wk.executions) hso))
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact h.of_sameKeys (SameKeys.failCall wk (call?_eq_some hc).1 hf)
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    exact h.of_sameKeys (SameKeys.failCall wk (call?_eq_some hc).1 hf)
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.of_sameKeys (SameKeys.failCall wk (call?_eq_some hc).1 hf)
    · have k1 := SameKeys.setCall (p := p) (c' := { c with status := .cancelled }) wk.calls (call?_eq_some hc).1 rfl
      exact h.of_sameKeys (k1.trans (SameKeys.cancelOwner (k1.invocations_nodup wk.invocations)
        (k1.executions_nodup wk.executions) ho))
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    have k1 := SameKeys.setCall (p := p) (c' := { c with status := .cancelled }) wk.calls (call?_eq_some hc).1 rfl
    exact h.of_sameKeys (k1.trans (SameKeys.cancelOwner (k1.invocations_nodup wk.invocations)
      (k1.executions_nodup wk.executions) ho))
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.of_same rfl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact h.of_sameKeys ((SameKeys.of_records (s := s)
      (t := { s with deliveries := s.deliveries ++ [{ run := path, connection := index, source, outcome := .failed }] })
      rfl rfl rfl rfl).trans SameKeys.fail)
  | taskInput eid name value =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.of_sameKeys (SameKeys.setTask wk.executions (execution?_eq_some he).1)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact h.of_sameKeys ((SameKeys.setTask wk.executions (execution?_eq_some he).1).trans SameKeys.fail)
  | beginTask eid name =>
    obtain ⟨-, -, e, cc, ts, spec, he, -, -, -, -, -, hspec, hcases⟩ := Step.beginTask_inv hs
    have he' := (execution?_eq_some he).1
    have k1 := SameKeys.setTask (p := p) (ts := { ts with status := .active }) wk.executions he'
    have h1 := h.of_sameKeys k1
    have hmem : withTask e { ts with status := .active } ∈ (s.setTask e { ts with status := .active }).executions :=
      mem_replace_self he' rfl
    rcases hcases with ⟨f, decl, hbody, -, -, rfl⟩ | ⟨wf, out, hbody, -, rfl⟩
    · exact h1.of_same rfl rfl
    · refine h1.of_extend (KeepsWorkflows.of_append rfl) (fun e₁ he₁ => ⟨e₁, he₁, rfl⟩) (fun x hx => ?_)
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · rw [List.mem_singleton.mp hx]
        refine Or.inr fun name' h' => ?_
        simp only [Option.some.injEq] at h'
        subst h'
        exact ⟨_, hmem, rfl, spec, out, (k1.workflows.trans (KeepsWorkflows.of_append rfl)).taskSpec rfl rfl hspec,
          hbody⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact h.of_same rfl rfl
    · exact h.of_sameKeys SameKeys.setTaskResult
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact h.of_sameKeys (SameKeys.setTaskResult.trans SameKeys.fail)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact h.of_same rfl rfl
    · exact h.of_same rfl rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, -, -, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    have k1 := SameKeys.setExecution (p := p) (e' := { e with complete := true }) wk.executions
      (execution?_eq_some he).1 rfl
    have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (invocation?_eq_some hi).1
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h.of_sameKeys (k1.trans (SameKeys.setInvocation (k1.invocations_nodup wk.invocations) hi' rfl))
    · exact (h.of_sameKeys (k1.trans (SameKeys.setInvocation (i' := { i with status := .succeeded })
        (k1.invocations_nodup wk.invocations) hi' rfl))).of_same rfl rfl
    · exact h.of_sameKeys (k1.trans (SameKeys.setInvocation (k1.invocations_nodup wk.invocations) hi' rfl))
  | closeRun path =>
    obtain ⟨-, -, r, w, output, x, owner, hr, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
    have k1 := SameKeys.setRun (p := p) (r' := { r with complete := true }) wk.runs hr' rfl
    rcases hcases with ⟨-, i, hi, hcases⟩ | ⟨name, e, ts, -, he, -, hcases⟩
    · have hi' : i ∈ (s.setRun { r with complete := true }).invocations := (invocation?_eq_some hi).1
      have k2 := fun (st : InvocationStatus) =>
        k1.trans (SameKeys.setInvocation (i' := { i with status := st }) (k1.invocations_nodup wk.invocations) hi' rfl)
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (h.of_sameKeys (k2 .succeeded)).of_same rfl rfl
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
    · have he' : e ∈ (s.setRun { r with complete := true }).executions := (execution?_eq_some he).1
      have k2 := fun (st : TaskStatus) =>
        k1.trans (SameKeys.setTask (ts := { ts with status := st }) (k1.executions_nodup wk.executions) he')
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (h.of_sameKeys (k2 .succeeded)).of_same rfl rfl
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.of_sameKeys (SameKeys.stop.trans (SameKeys.of_records rfl rfl rfl rfl))
    · exact h.of_same rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, w, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
      exact h.of_sameKeys ((SameKeys.setRun (r' := { r with complete := true }) wk.runs hr' rfl).trans
        (SameKeys.of_records rfl rfl rfl rfl))
    · exact h.of_sameKeys (SameKeys.endUnfinished.trans (SameKeys.of_records rfl rfl rfl rfl))

end TaskRunWf

theorem Reachable.taskRunWf {p : Definition} {s : State} (h : Reachable p s) : TaskRunWf p s := by
  induction h with
  | empty => exact TaskRunWf.empty
  | step op hr hs ih => exact ih.step hr.wellKeyed hs

end Suimon.Round3.CalmAux
