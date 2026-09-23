import Suimon.Theorems.SettleFrame

/-! Layer 1 of the settlement invariant: ownership of calls, runs and executions, and the placement
    of each invocation, are kept by every step. -/

namespace Suimon.Settle

open State

variable {p : Program} {s t : State}

namespace Own

theorem empty : Own p {} where
  callNone := by simp
  execOwner := by simp
  runNone := by simp
  callTask := by simp
  runTask := by simp
  invId := by simp
  invPlaced := by simp

/-- Ownership only depends on the keys of the records and on the workflows of the runs. --/
theorem of_keys (h : Own p s) (hw : KeepsWorkflows p s t)
    (hc : t.calls.map callKey = s.calls.map callKey) (hi : t.invocations.map invKey = s.invocations.map invKey)
    (he : t.executions.map execKey = s.executions.map execKey) (hr : t.runs.map runKey = s.runs.map runKey) :
    Own p t where
  callNone := by
    intro c' hc' htask
    obtain ⟨c, hc0, hk⟩ := exists_of_map_eq hc.symm hc'
    simp only [callKey_eq] at hk
    obtain ⟨hid, howner, htask', hstream⟩ := hk
    obtain ⟨hco, i, hi0, hio, pl, hpl, hctrl⟩ := h.callNone c hc0 (htask'.trans htask)
    obtain ⟨i', hi', hk'⟩ := exists_of_map_eq hi hi0
    simp only [invKey_eq] at hk'
    obtain ⟨hid', hrun', hpl', -⟩ := hk'
    refine ⟨?_, i', hi', ?_, pl, ?_, ?_⟩
    · rw [← hid, ← howner]; exact hco
    · rw [hid', hio, howner]
    · rw [hrun', hpl']; exact hw.placementAt hpl
    · rw [← hstream]; exact hctrl
  execOwner := by
    intro e' he'
    obtain ⟨e, he0, hk⟩ := exists_of_map_eq he.symm he'
    simp only [execKey_eq] at hk
    obtain ⟨hid, hrun, hplace, hnames⟩ := hk
    obtain ⟨i, hi0, hie, hir, hip, pl, cc, hpl, hcc, hn⟩ := h.execOwner e he0
    obtain ⟨i', hi', hk'⟩ := exists_of_map_eq hi hi0
    simp only [invKey_eq] at hk'
    obtain ⟨hid', hrun', hpl', -⟩ := hk'
    refine ⟨i', hi', by rw [hid', hie, hid], by rw [hrun', hir, hrun], by rw [hpl', hip, hplace], pl, cc, ?_, hcc,
      by rw [← hnames, hn]⟩
    rw [← hrun, ← hplace]
    exact hw.placementAt hpl
  runNone := by
    intro r' hr' o howner htask
    obtain ⟨r, hr0, hk⟩ := exists_of_map_eq hr.symm hr'
    simp only [runKey_eq] at hk
    obtain ⟨hpath, -, howner', htask'⟩ := hk
    obtain ⟨i, hi0, hio, hipath, pl, wf, out, hpl, hctrl⟩ := h.runNone r hr0 o (howner'.trans howner) (htask'.trans htask)
    obtain ⟨i', hi', hk'⟩ := exists_of_map_eq hi hi0
    simp only [invKey_eq] at hk'
    obtain ⟨hid', hrun', hpl', -⟩ := hk'
    refine ⟨i', hi', by rw [hid', hio], by rw [← hpath, hipath, hrun', hid'], pl, wf, out, ?_, hctrl⟩
    rw [hrun', hpl']
    exact hw.placementAt hpl
  callTask := by
    intro c' hc' name htask
    obtain ⟨c, hc0, hk⟩ := exists_of_map_eq hc.symm hc'
    simp only [callKey_eq] at hk
    obtain ⟨hid, howner, htask', -⟩ := hk
    obtain ⟨hkey, e, he0, heo, spec, f, hspec, hbody⟩ := h.callTask c hc0 name (htask'.trans htask)
    obtain ⟨e', he', hk'⟩ := exists_of_map_eq he he0
    simp only [execKey_eq] at hk'
    obtain ⟨hid', hrun', hpl', -⟩ := hk'
    refine ⟨by rw [← hid, ← howner]; exact hkey, e', he', by rw [hid', heo, howner], spec, f, ?_, hbody⟩
    exact hw.taskSpec hrun' hpl' hspec
  runTask := by
    intro r' hr' name htask
    obtain ⟨r, hr0, hk⟩ := exists_of_map_eq hr.symm hr'
    simp only [runKey_eq] at hk
    obtain ⟨hpath, -, howner, htask'⟩ := hk
    obtain ⟨e, he0, heo, hepath, spec, wf, out, hspec, hbody⟩ := h.runTask r hr0 name (htask'.trans htask)
    obtain ⟨e', he', hk'⟩ := exists_of_map_eq he he0
    simp only [execKey_eq] at hk'
    obtain ⟨hid', hrun', hpl', -⟩ := hk'
    refine ⟨e', he', by rw [← howner, heo, hid'], by rw [← hpath, hepath, hrun', hid'], spec, wf, out, ?_, hbody⟩
    exact hw.taskSpec hrun' hpl' hspec
  invId := by
    intro i' hi'
    obtain ⟨i, hi0, hk⟩ := exists_of_map_eq hi.symm hi'
    simp only [invKey_eq] at hk
    obtain ⟨hid, hrun, hpl, htrig⟩ := hk
    rw [← hid, ← hrun, ← hpl, ← htrig]
    exact h.invId i hi0
  invPlaced := by
    intro i' hi'
    obtain ⟨i, hi0, hk⟩ := exists_of_map_eq hi.symm hi'
    simp only [invKey_eq] at hk
    obtain ⟨-, hrun, hpl, -⟩ := hk
    obtain ⟨w, pl, hw0, hpl0, hinv⟩ := h.invPlaced i hi0
    exact ⟨w, pl, by rw [← hrun]; exact hw _ _ hw0, by rw [← hpl]; exact hpl0, hinv⟩

/-- Recording a new invocation keeps ownership. --/
theorem appendInvocation (h : Own p s) {i : Invocation} (hid : i.id = Key.invocation i.run i.placement i.trigger)
    (hpl : ∃ w pl, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧ invocable pl.control = true) :
    Own p { s with invocations := s.invocations ++ [i] } where
  callNone := by
    intro c hc htask
    obtain ⟨hco, i', hi', rest⟩ := h.callNone c hc htask
    exact ⟨hco, i', List.mem_append_left _ hi', rest⟩
  execOwner := by
    intro e he
    obtain ⟨i', hi', rest⟩ := h.execOwner e he
    exact ⟨i', List.mem_append_left _ hi', rest⟩
  runNone := by
    intro r hr o howner htask
    obtain ⟨i', hi', rest⟩ := h.runNone r hr o howner htask
    exact ⟨i', List.mem_append_left _ hi', rest⟩
  callTask := h.callTask
  runTask := h.runTask
  invId := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.invId x hx
    · rw [List.mem_singleton.mp hx]; exact hid
  invPlaced := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.invPlaced x hx
    · rw [List.mem_singleton.mp hx]; exact hpl

/-- Recording a new call keeps ownership. --/
theorem appendCall (h : Own p s) {c : Call}
    (hnone : c.task = none → c.id = c.owner ∧ ∃ i ∈ s.invocations, i.id = c.owner ∧ ∃ pl,
      placementAt p s i.run i.placement = some pl ∧
      ((∃ f decl, pl.control = .call (.function f) ∧ p.function? f = some decl ∧
          c.stream = (decl.output.kind == .stream)) ∨
       (∃ j arms, pl.control = .branch j arms ∧ c.stream = false)))
    (hsome : ∀ name, c.task = some name → c.id = Key.task c.owner name ∧
      ∃ e ∈ s.executions, e.id = c.owner ∧ ∃ spec f, s.taskSpec p e name = .ok spec ∧ spec.body = .function f) :
    Own p { s with calls := s.calls ++ [c] } where
  callNone := by
    intro x hx htask
    rcases List.mem_append.mp hx with hx | hx
    · exact h.callNone x hx htask
    · rw [List.mem_singleton.mp hx] at htask ⊢; exact hnone htask
  execOwner := h.execOwner
  runNone := h.runNone
  callTask := by
    intro x hx name htask
    rcases List.mem_append.mp hx with hx | hx
    · exact h.callTask x hx name htask
    · rw [List.mem_singleton.mp hx] at htask ⊢; exact hsome name htask
  runTask := h.runTask
  invId := h.invId
  invPlaced := h.invPlaced

/-- Recording a new execution keeps ownership. --/
theorem appendExecution (h : Own p s) {e : Execution}
    (he : ∃ i ∈ s.invocations, i.id = e.id ∧ i.run = e.run ∧ i.placement = e.placement ∧
      ∃ pl cc, placementAt p s e.run e.placement = some pl ∧ pl.control = .concurrency cc ∧
        e.tasks.map (·.name) = cc.tasks.map (·.name)) :
    Own p { s with executions := s.executions ++ [e] } where
  callNone := h.callNone
  execOwner := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.execOwner x hx
    · rw [List.mem_singleton.mp hx]; exact he
  runNone := h.runNone
  callTask := by
    intro c hc name htask
    obtain ⟨hkey, e', he', rest⟩ := h.callTask c hc name htask
    exact ⟨hkey, e', List.mem_append_left _ he', rest⟩
  runTask := by
    intro r hr name htask
    obtain ⟨e', he', rest⟩ := h.runTask r hr name htask
    exact ⟨e', List.mem_append_left _ he', rest⟩
  invId := h.invId
  invPlaced := h.invPlaced

/-- Recording a new run keeps ownership. --/
theorem appendRun (h : Own p s) {r : Run}
    (hnone : ∀ o, r.owner = some o → r.task = none → ∃ i ∈ s.invocations, i.id = o ∧
      r.path = i.run ++ [i.id] ∧ ∃ pl wf out, placementAt p s i.run i.placement = some pl ∧
        pl.control = .call (.workflow wf out))
    (hsome : ∀ name, r.task = some name → ∃ e ∈ s.executions, r.owner = some e.id ∧
      r.path = e.run ++ [Key.task e.id name] ∧ ∃ spec wf out, s.taskSpec p e name = .ok spec ∧
        spec.body = .workflow wf out) :
    Own p { s with runs := s.runs ++ [r] } := by
  have hw : KeepsWorkflows p s { s with runs := s.runs ++ [r] } := KeepsWorkflows.of_append rfl
  exact {
    callNone := by
      intro c hc htask
      obtain ⟨hco, i, hi, hio, pl, hpl, rest⟩ := h.callNone c hc htask
      exact ⟨hco, i, hi, hio, pl, hw.placementAt hpl, rest⟩
    execOwner := by
      intro e he
      obtain ⟨i, hi, h1, h2, h3, pl, cc, hpl, rest⟩ := h.execOwner e he
      exact ⟨i, hi, h1, h2, h3, pl, cc, hw.placementAt hpl, rest⟩
    runNone := by
      intro x hx o howner htask
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, hio, hpath, pl, wf, out, hpl, hctrl⟩ := h.runNone x hx o howner htask
        exact ⟨i, hi, hio, hpath, pl, wf, out, hw.placementAt hpl, hctrl⟩
      · rw [List.mem_singleton.mp hx] at howner htask ⊢
        obtain ⟨i, hi, hio, hpath, pl, wf, out, hpl, hctrl⟩ := hnone o howner htask
        exact ⟨i, hi, hio, hpath, pl, wf, out, hw.placementAt hpl, hctrl⟩
    callTask := by
      intro c hc name htask
      obtain ⟨hkey, e, he, heo, spec, f, hspec, hbody⟩ := h.callTask c hc name htask
      exact ⟨hkey, e, he, heo, spec, f, hw.taskSpec rfl rfl hspec, hbody⟩
    runTask := by
      intro x hx name htask
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨e, he, heo, hpath, spec, wf, out, hspec, hbody⟩ := h.runTask x hx name htask
        exact ⟨e, he, heo, hpath, spec, wf, out, hw.taskSpec rfl rfl hspec, hbody⟩
      · rw [List.mem_singleton.mp hx] at htask ⊢
        obtain ⟨e, he, heo, hpath, spec, wf, out, hspec, hbody⟩ := hsome name htask
        exact ⟨e, he, heo, hpath, spec, wf, out, hw.taskSpec rfl rfl hspec, hbody⟩
    invId := h.invId
    invPlaced := by
      intro i hi
      obtain ⟨w, pl, hw0, hpl, hinv⟩ := h.invPlaced i hi
      exact ⟨w, pl, hw _ _ hw0, hpl, hinv⟩ }

theorem of_sameKeys (h : Own p s) (hk : SameKeys p s t) : Own p t :=
  h.of_keys hk.workflows hk.calls hk.invocations hk.executions hk.runs

/-- Only the root run exists at the start. --/
theorem root {m : String} {input : Option Value} :
    Own p { started := true, runs := [{ path := [], workflow := m, input }] } where
  callNone := by simp
  execOwner := by simp
  runNone := by simp
  callTask := by simp
  runTask := by simp
  invId := by simp
  invPlaced := by simp

/-- Every step keeps ownership. --/
theorem step (h : Own p s) (wk : s.WellKeyed) (h0 : s = {} ∨ s.started = true) {op : Op}
    (hs : step p s op = .ok t) : Own p t := by
  cases op with
  | start input =>
    obtain ⟨hns, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h0 with rfl | h0
    · exact root
    · simp [h0] at hns
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, rfl, -, -, hcases⟩ := Step.invoke_inv hs
    have hwf : s.workflow? p path = some w := workflow?_of_run hr hw
    have hplat : placementAt p s path name = some pl := by rw [placementAt_eq hwf, hpl]
    have hinv : invocable pl.control = true := by
      rcases hcases with ⟨_, _, hc, -⟩ | ⟨_, _, hc, -⟩ | ⟨_, _, hc, -⟩ | ⟨_, hc, -⟩ <;> simp [invocable, hc]
    let inv : Invocation := { id := Key.invocation path name trigger, run := path, placement := name, trigger, input }
    have h1 := h.appendInvocation (i := inv) rfl ⟨w, pl, hwf, hpl, hinv⟩
    have hmem : inv ∈ s.invocations ++ [inv] := List.mem_append_right _ (List.mem_singleton_self _)
    rcases hcases with ⟨f, decl, hc, hdecl, -, rfl⟩ | ⟨judge, arms, hc, -, rfl⟩ | ⟨wf, out, hc, -, rfl⟩ |
      ⟨cc, hc, -, rfl⟩
    · exact h1.appendCall (fun _ => ⟨rfl, inv, hmem, rfl, pl, hplat, Or.inl ⟨f, decl, hc, hdecl, rfl⟩⟩)
        (fun _ h => by simp at h)
    · exact h1.appendCall (fun _ => ⟨rfl, inv, hmem, rfl, pl, hplat, Or.inr ⟨judge, arms, hc, rfl⟩⟩)
        (fun _ h => by simp at h)
    · exact h1.appendRun (fun o ho _ => ⟨inv, hmem, (Option.some.inj ho).symm ▸ rfl, rfl, pl, wf, out, hplat, hc⟩)
        (fun _ h => by simp at h)
    · exact h1.appendExecution ⟨inv, hmem, rfl, rfl, rfl, pl, cc, hplat, hc, by simp [List.map_map, Function.comp_def]⟩
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
    exact h.of_sameKeys (SameKeys.of_records rfl rfl rfl rfl)
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
    have hspec' : (s.setTask e { ts with status := .active }).taskSpec p (withTask e { ts with status := .active }) name =
        .ok spec := k1.workflows.taskSpec rfl rfl hspec
    rcases hcases with ⟨f, decl, hbody, -, -, rfl⟩ | ⟨wf, out, hbody, -, rfl⟩
    · exact h1.appendCall (fun h => by simp at h)
        (fun name' h' => by
          simp only [Option.some.injEq] at h'
          subst h'
          exact ⟨rfl, _, hmem, rfl, spec, f, hspec', hbody⟩)
    · exact h1.appendRun (fun _ _ h => by simp at h)
        (fun name' h' => by
          simp only [Option.some.injEq] at h'
          subst h'
          exact ⟨_, hmem, rfl, rfl, spec, wf, out, hspec', hbody⟩)
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact h.of_sameKeys (SameKeys.of_records rfl rfl rfl rfl)
    · exact h.of_sameKeys SameKeys.setTaskResult
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact h.of_sameKeys (SameKeys.setTaskResult.trans SameKeys.fail)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact h.of_sameKeys (SameKeys.of_records rfl rfl rfl rfl)
    · exact h.of_sameKeys (SameKeys.of_records rfl rfl rfl rfl)
  | closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, -, -, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
    have k1 := SameKeys.setExecution (p := p) (e' := { e with complete := true }) wk.executions
      (execution?_eq_some he).1 rfl
    have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (invocation?_eq_some hi).1
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h.of_sameKeys (k1.trans (SameKeys.setInvocation (k1.invocations_nodup wk.invocations) hi' rfl))
    · exact h.of_sameKeys ((k1.trans (SameKeys.setInvocation (i' := { i with status := .succeeded })
        (k1.invocations_nodup wk.invocations) hi' rfl)).trans (SameKeys.of_records rfl rfl rfl rfl))
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
      · exact h.of_sameKeys ((k2 .succeeded).trans (SameKeys.of_records rfl rfl rfl rfl))
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
    · have he' : e ∈ (s.setRun { r with complete := true }).executions := (execution?_eq_some he).1
      have k2 := fun (st : TaskStatus) =>
        k1.trans (SameKeys.setTask (ts := { ts with status := st }) (k1.executions_nodup wk.executions) he')
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact h.of_sameKeys ((k2 .succeeded).trans (SameKeys.of_records rfl rfl rfl rfl))
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
      · exact h.of_sameKeys (k2 _)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.of_sameKeys (SameKeys.stop.trans (SameKeys.of_records rfl rfl rfl rfl))
    · exact h.of_sameKeys (SameKeys.of_records rfl rfl rfl rfl)
  | conclude =>
    obtain ⟨-, ⟨-, r, w, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
      exact h.of_sameKeys ((SameKeys.setRun (r' := { r with complete := true }) wk.runs hr' rfl).trans
        (SameKeys.of_records rfl rfl rfl rfl))
    · exact h.of_sameKeys (SameKeys.of_records rfl rfl rfl rfl)

/-! ### What ownership excludes -/

section Exclusion
variable (h : Own p s) (wk : s.WellKeyed)
include h wk

omit h in
/-- The placement of the invocation with a given identity. --/
theorem placementAt_of_id {i i' : Invocation} (hi : i ∈ s.invocations) (hi' : i' ∈ s.invocations)
    (hid : i.id = i'.id) : placementAt p s i.run i.placement = placementAt p s i'.run i'.placement := by
  rw [wk.invocation_eq_of_id hi hi' hid]

/-- The invocation of a call is a function call or a branch, never a concurrency. --/
theorem call_not_exec {c : Call} (hc : c ∈ s.calls) (htask : c.task = none) {e : Execution}
    (he : e ∈ s.executions) : e.id ≠ c.owner := by
  intro heq
  obtain ⟨-, i, hi, hio, pl, hpl, hctrl⟩ := h.callNone c hc htask
  obtain ⟨i', hi', hie, hir, hip, pl', cc, hpl', hcc, -⟩ := h.execOwner e he
  have : placementAt p s i.run i.placement = placementAt p s i'.run i'.placement :=
    placementAt_of_id wk hi hi' (by rw [hio, hie, heq])
  rw [hpl, hir, hip, hpl'] at this
  cases this
  rcases hctrl with ⟨_, _, hc', -⟩ | ⟨_, _, hc', -⟩ <;> rw [hcc] at hc' <;> cases hc'

/-- The invocation of a call owns no sub-workflow run. --/
theorem call_not_run {c : Call} (hc : c ∈ s.calls) (htask : c.task = none) {r : Run} (hr : r ∈ s.runs)
    (hrt : r.task = none) : r.owner ≠ some c.owner := by
  intro heq
  obtain ⟨-, i, hi, hio, pl, hpl, hctrl⟩ := h.callNone c hc htask
  obtain ⟨i', hi', hio', -, pl', wf, out, hpl', hc'⟩ := h.runNone r hr c.owner heq hrt
  have : placementAt p s i.run i.placement = placementAt p s i'.run i'.placement :=
    placementAt_of_id wk hi hi' (by rw [hio, hio'])
  rw [hpl, hpl'] at this
  cases this
  rcases hctrl with ⟨_, _, hcc, -⟩ | ⟨_, _, hcc, -⟩ <;> rw [hc'] at hcc <;> cases hcc

/-- An execution's invocation owns no sub-workflow run. --/
theorem exec_not_run {e : Execution} (he : e ∈ s.executions) {r : Run} (hr : r ∈ s.runs) (hrt : r.task = none) :
    r.owner ≠ some e.id := by
  intro heq
  obtain ⟨i, hi, hie, hir, hip, pl, cc, hpl, hcc, -⟩ := h.execOwner e he
  obtain ⟨i', hi', hio', -, pl', wf, out, hpl', hc'⟩ := h.runNone r hr e.id heq hrt
  have : placementAt p s i.run i.placement = placementAt p s i'.run i'.placement :=
    placementAt_of_id wk hi hi' (by rw [hie, hio'])
  rw [hir, hip, hpl, hpl'] at this
  cases this
  rw [hcc] at hc'
  cases hc'

/-- An invocation has at most one call. --/
theorem call_unique {c c' : Call} (hc : c ∈ s.calls) (hc' : c' ∈ s.calls) (htask : c.task = none)
    (htask' : c'.task = none) (howner : c.owner = c'.owner) : c = c' :=
  wk.call_eq_of_id hc hc' (by rw [(h.callNone c hc htask).1, (h.callNone c' hc' htask').1, howner])

/-- A task has at most one call. --/
theorem taskCall_unique {c c' : Call} {name : String} (hc : c ∈ s.calls) (hc' : c' ∈ s.calls)
    (htask : c.task = some name) (htask' : c'.task = some name) (howner : c.owner = c'.owner) : c = c' :=
  wk.call_eq_of_id hc hc' (by rw [(h.callTask c hc name htask).1, (h.callTask c' hc' name htask').1, howner])

/-- An invocation has at most one sub-workflow run. --/
theorem run_unique {r r' : Run} {o : String} (hr : r ∈ s.runs) (hr' : r' ∈ s.runs) (ho : r.owner = some o)
    (ho' : r'.owner = some o) (ht : r.task = none) (ht' : r'.task = none) : r = r' := by
  obtain ⟨i, hi, hio, hpath, -⟩ := h.runNone r hr o ho ht
  obtain ⟨i', hi', hio', hpath', -⟩ := h.runNone r' hr' o ho' ht'
  have : i = i' := wk.invocation_eq_of_id hi hi' (hio.trans hio'.symm)
  subst this
  exact wk.run_eq_of_path hr hr' (hpath.trans hpath'.symm)

/-- A task has at most one run. --/
theorem taskRun_unique {r r' : Run} {name : String} (hr : r ∈ s.runs) (hr' : r' ∈ s.runs)
    (ht : r.task = some name) (ht' : r'.task = some name) (ho : r.owner = r'.owner) : r = r' := by
  obtain ⟨e, he, heo, hpath, -⟩ := h.runTask r hr name ht
  obtain ⟨e', he', heo', hpath', -⟩ := h.runTask r' hr' name ht'
  have : e = e' := wk.execution_eq_of_id he he' (Option.some.inj (heo.symm.trans (ho.trans heo')))
  subst this
  exact wk.run_eq_of_path hr hr' (hpath.trans hpath'.symm)

/-- A task has a call or a run, never both. --/
theorem taskCall_not_run {c : Call} {name : String} (hc : c ∈ s.calls) (htask : c.task = some name) {r : Run}
    (hr : r ∈ s.runs) (hrt : r.task = some name) (ho : r.owner = some c.owner) : False := by
  obtain ⟨-, e, he, heo, spec, f, hspec, hbody⟩ := h.callTask c hc name htask
  obtain ⟨e', he', heo', -, spec', wf, out, hspec', hbody'⟩ := h.runTask r hr name hrt
  have : e = e' := wk.execution_eq_of_id he he' (by rw [heo, ← Option.some.inj (ho.symm.trans heo')])
  subst this
  rw [taskSpec_det hspec hspec'] at hbody
  rw [hbody] at hbody'
  cases hbody'

omit wk in
/-- The concurrency of an execution, whose tasks it lists. --/
theorem exec_concurrency {e : Execution} (he : e ∈ s.executions) :
    ∃ cc, s.concurrencyOf p e = .ok cc ∧ e.tasks.map (·.name) = cc.tasks.map (·.name) := by
  obtain ⟨-, -, -, -, -, pl, cc, hpl, hcc, hn⟩ := h.execOwner e he
  refine ⟨cc, ?_, hn⟩
  rw [concurrencyOf_eq_ok]
  refine ⟨pl, ?_, hcc⟩
  rw [placementOf_eq_ok]
  simp only [placementAt, Option.bind_eq_some_iff] at hpl
  exact hpl

end Exclusion

end Own

end Suimon.Settle
