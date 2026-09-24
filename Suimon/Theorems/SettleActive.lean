import Suimon.Theorems.SettleOwn

/-! Layer 2 of the settlement invariant: what keeps an invocation, a task or an execution active
    is kept by every step. -/

namespace Suimon.Settle

open State

variable {p : Definition} {s t : State}

/-- All runs keep their workflows, in both directions. --/
def SameWorkflows (p : Definition) (s t : State) : Prop := ∀ path, t.workflow? p path = s.workflow? p path

theorem SameWorkflows.of_runs (h : t.runs = s.runs) : SameWorkflows p s t := fun path => by
  simp [State.workflow?, State.run?, h]

theorem SameWorkflows.setRun {r r' : Run} (hr : s.run? r'.path = some r) (hw : r'.workflow = r.workflow) :
    SameWorkflows p s (s.setRun r') := fun path => by
  simp only [State.workflow?]
  rw [run?_setRun]
  by_cases hp : r'.path = path
  · subst hp
    simp [hr, hw]
  · simp [hp]

theorem SameWorkflows.concurrencyOf (h : SameWorkflows p s t) {e : Execution} :
    t.concurrencyOf p e = s.concurrencyOf p e := by
  unfold State.concurrencyOf State.placementOf
  rw [h e.run]

theorem SameWorkflows.taskSpec (h : SameWorkflows p s t) {e : Execution} {name : String} :
    t.taskSpec p e name = s.taskSpec p e name := by
  simp only [State.taskSpec, h.concurrencyOf]

theorem withTask_find? {e : Execution} {ts : TaskState} {n : String} :
    (withTask e ts).tasks.find? (·.name == n) =
      if ts.name = n then (e.tasks.find? (·.name == n)).map (fun _ => ts) else e.tasks.find? (·.name == n) :=
  find?_map_replace_key

namespace Active

theorem empty : Active p {} where
  callActive := by simp
  execActive := by simp
  runActive := by simp
  taskCallActive := by simp
  taskRunOpen := by simp
  completeOutputs := by simp
  activeArm := by simp

/-- Only the records matter. --/
theorem of_records (h : Active p s) (hr : t.runs = s.runs) (hi : t.invocations = s.invocations)
    (hc : t.calls = s.calls) (he : t.executions = s.executions) (htr : t.taskResults = s.taskResults) :
    Active p t := by
  have hw : SameWorkflows p s t := SameWorkflows.of_runs hr
  exact {
    callActive := by rw [hc, hi]; exact h.callActive
    execActive := by rw [he, hi]; exact h.execActive
    runActive := by rw [hr, hi]; exact h.runActive
    taskCallActive := by rw [hc, he]; exact h.taskCallActive
    taskRunOpen := by rw [hr, he]; exact h.taskRunOpen
    completeOutputs := by
      intro e hem hc' tr htr' hid cc hcc
      rw [he] at hem
      rw [htr] at htr'
      rw [hw.concurrencyOf] at hcc
      exact h.completeOutputs e hem hc' tr htr' hid cc hcc
    activeArm := by rw [hi]; exact h.activeArm }

theorem stop (h : Active p s) : Active p s.stop where
  callActive := fun c hc _ hrun => by
    have := stop_calls_quiet hc
    rcases hrun with hrun | hrun
    · exact absurd hrun this.1
    · exact absurd hrun this.2
  execActive := by
    intro e he hc
    obtain ⟨e0, he0, rfl⟩ := mem_stop_executions.mp he
    exact h.execActive e0 he0 hc
  runActive := h.runActive
  taskCallActive := fun c hc _ _ hrun => by
    have := stop_calls_quiet hc
    rcases hrun with hrun | hrun
    · exact absurd hrun this.1
    · exact absurd hrun this.2
  taskRunOpen := by
    intro r hr name ht hc
    obtain ⟨e, he, heo, hec⟩ := h.taskRunOpen r hr name ht hc
    exact ⟨stopExecution e, mem_stop_executions.mpr ⟨e, he, rfl⟩, heo, hec⟩
  completeOutputs := by
    intro e he hc tr htr hid cc hcc
    obtain ⟨e0, he0, rfl⟩ := mem_stop_executions.mp he
    have hcc' : s.concurrencyOf p e0 = .ok cc := by
      rw [← (SameWorkflows.of_runs (p := p) (s := s) (t := s.stop) rfl).concurrencyOf]
      exact hcc
    exact h.completeOutputs e0 he0 hc tr htr hid cc hcc'
  activeArm := h.activeArm

theorem fail (h : Active p s) {f : Failure} {policy : Policy} : Active p (s.fail f policy) := by
  have h' : Active p { s with failures := s.failures ++ [f] } := h.of_records rfl rfl rfl rfl rfl
  cases policy
  · exact h'.stop
  · exact h'

/-- A call keeps running only if it was running. --/
theorem setCall (h : Active p s) {c c' : Call} (hc : c ∈ s.calls) (howner : c'.owner = c.owner)
    (htask : c'.task = c.task)
    (hrun : c'.status = .running ∨ c'.status = .fetching → c.status = .running ∨ c.status = .fetching) :
    Active p (s.setCall c') where
  callActive := by
    intro x hx ht hr
    rcases mem_replace hx with rfl | ⟨hx, -⟩
    · rw [howner]; exact h.callActive c hc (htask ▸ ht) (hrun hr)
    · exact h.callActive x hx ht hr
  execActive := h.execActive
  runActive := h.runActive
  taskCallActive := by
    intro x hx name ht hr
    rcases mem_replace hx with rfl | ⟨hx, -⟩
    · rw [howner]; exact h.taskCallActive c hc name (htask ▸ ht) (hrun hr)
    · exact h.taskCallActive x hx name ht hr
  taskRunOpen := h.taskRunOpen
  completeOutputs := h.completeOutputs
  activeArm := h.activeArm

/-- A task result of an open execution. --/
theorem appendTaskResult (h : Active p s) (wk : s.WellKeyed) {tr : TaskResult} {e : Execution}
    (he : e ∈ s.executions) (hid : e.id = tr.execution) (hopen : e.complete = false) :
    Active p { s with taskResults := s.taskResults ++ [tr] } where
  callActive := h.callActive
  execActive := h.execActive
  runActive := h.runActive
  taskCallActive := h.taskCallActive
  taskRunOpen := h.taskRunOpen
  completeOutputs := by
    intro e' he' hc x hx hxid cc hcc
    rcases List.mem_append.mp hx with hx | hx
    · exact h.completeOutputs e' he' hc x hx hxid cc hcc
    · rw [List.mem_singleton.mp hx] at hxid
      rw [wk.execution_eq_of_id he' he (hxid.symm.trans hid.symm), hopen] at hc
      cases hc
  activeArm := h.activeArm

/-- A transformed task result. --/
theorem setTaskResult (h : Active p s) {r : TaskResult} (hr : r.output ≠ .pending) :
    Active p (s.setTaskResult r) where
  callActive := h.callActive
  execActive := h.execActive
  runActive := h.runActive
  taskCallActive := h.taskCallActive
  taskRunOpen := h.taskRunOpen
  completeOutputs := by
    intro e he hc x hx hxid cc hcc hin
    rcases mem_map_replace hx with rfl | hx
    · exact hr
    · exact h.completeOutputs e he hc x hx hxid cc hcc hin
  activeArm := h.activeArm

/-- An invocation stops being active once nothing of it runs. --/
theorem setInvocation_off (h : Active p s) {i i' : Invocation} (hid : i'.id = i.id) (hoff : i'.status ≠ .active)
    (hcalls : ∀ c ∈ s.calls, c.task = none → c.owner = i.id → c.status ≠ .running ∧ c.status ≠ .fetching)
    (hexecs : ∀ e ∈ s.executions, e.id = i.id → e.complete = true)
    (hruns : ∀ r ∈ s.runs, r.owner = some i.id → r.task = none → r.complete = true) :
    Active p (s.setInvocation i') := by
  -- An active invocation other than `i` is kept.
  have keep : ∀ j ∈ s.invocations, j.status = .active → j.id ≠ i.id → j ∈ (s.setInvocation i').invocations :=
    fun j hj _ hne => mem_replace_of_mem hj (by rw [hid]; exact hne)
  exact {
    callActive := by
      intro c hc ht hr
      obtain ⟨j, hj, hjo, hja⟩ := h.callActive c hc ht hr
      refine ⟨j, keep j hj hja fun heq => ?_, hjo, hja⟩
      have := hcalls c hc ht (hjo ▸ heq)
      rcases hr with hr | hr
      · exact this.1 hr
      · exact this.2 hr
    execActive := by
      intro e he hc
      obtain ⟨j, hj, hje, hja⟩ := h.execActive e he hc
      refine ⟨j, keep j hj hja fun heq => ?_, hje, hja⟩
      rw [hexecs e he (hje ▸ heq)] at hc
      cases hc
    runActive := by
      intro r hr o ho ht hc
      obtain ⟨j, hj, hjo, hja⟩ := h.runActive r hr o ho ht hc
      refine ⟨j, keep j hj hja fun heq => ?_, hjo, hja⟩
      rw [hruns r hr (by rw [ho, ← hjo, heq]) ht] at hc
      cases hc
    taskCallActive := h.taskCallActive
    taskRunOpen := h.taskRunOpen
    completeOutputs := h.completeOutputs
    activeArm := by
      intro j hj hja
      rcases mem_replace hj with rfl | ⟨hj, -⟩
      · exact absurd hja hoff
      · exact h.activeArm j hj hja }

/-- A task changes status; it leaves the active status only when no call of it runs. --/
theorem setTask (h : Active p s) (wk : s.WellKeyed) {e : Execution} {ts : TaskState} (he : e ∈ s.executions)
    (hcalls : ts.status ≠ .active → ∀ c ∈ s.calls, c.owner = e.id → c.task = some ts.name →
      c.status ≠ .running ∧ c.status ≠ .fetching) :
    Active p (s.setTask e ts) := by
  have hmem : withTask e ts ∈ (s.setTask e ts).executions := mem_replace_self he rfl
  -- Every execution of the new state is the updated `e` or another old one.
  have back : ∀ x ∈ (s.setTask e ts).executions, x = withTask e ts ∨ (x ∈ s.executions ∧ x.id ≠ e.id) :=
    fun x hx => mem_replace hx
  have fwd : ∀ x ∈ s.executions, x.id ≠ e.id → x ∈ (s.setTask e ts).executions :=
    fun x hx hne => mem_replace_of_mem hx hne
  have hw : SameWorkflows p s (s.setTask e ts) := SameWorkflows.of_runs rfl
  exact {
    callActive := h.callActive
    execActive := by
      intro x hx hc
      rcases back x hx with rfl | ⟨hx, -⟩
      · exact h.execActive e he hc
      · exact h.execActive x hx hc
    runActive := h.runActive
    taskCallActive := by
      intro c hc name ht hr
      obtain ⟨x, hx, hxo, hxc, ts', hts', hact⟩ := h.taskCallActive c hc name ht hr
      by_cases hxe : x.id = e.id
      · have := wk.execution_eq_of_id hx he hxe
        subst this
        refine ⟨withTask x ts, hmem, hxo, hxc, ?_⟩
        rw [withTask_find?]
        by_cases hn : ts.name = name
        · subst hn
          refine ⟨ts, by simp [hts'], ?_⟩
          by_cases hna : ts.status = .active
          · exact hna
          · have := hcalls hna c hc hxo.symm ht
            rcases hr with hr | hr
            · exact absurd hr this.1
            · exact absurd hr this.2
        · exact ⟨ts', by simp [hn, hts'], hact⟩
      · exact ⟨x, fwd x hx hxe, hxo, hxc, ts', hts', hact⟩
    taskRunOpen := by
      intro r hr name ht hc
      obtain ⟨x, hx, hxo, hxc⟩ := h.taskRunOpen r hr name ht hc
      by_cases hxe : x.id = e.id
      · have := wk.execution_eq_of_id hx he hxe
        subst this
        exact ⟨withTask x ts, hmem, hxo, hxc⟩
      · exact ⟨x, fwd x hx hxe, hxo, hxc⟩
    completeOutputs := by
      intro x hx hc tr htr hid cc hcc
      rw [hw.concurrencyOf] at hcc
      rcases back x hx with rfl | ⟨hx, -⟩
      · exact h.completeOutputs e he hc tr htr hid cc hcc
      · exact h.completeOutputs x hx hc tr htr hid cc hcc
    activeArm := h.activeArm }

/-- A run completes. --/
theorem setRun_complete (h : Active p s) {r : Run} (hr : s.run? r.path = some r) :
    Active p (s.setRun { r with complete := true }) := by
  have hw : SameWorkflows p s (s.setRun { r with complete := true }) := SameWorkflows.setRun hr rfl
  exact {
    callActive := h.callActive
    execActive := h.execActive
    runActive := by
      intro x hx o ho ht hc
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · cases hc
      · exact h.runActive x hx o ho ht hc
    taskCallActive := h.taskCallActive
    taskRunOpen := by
      intro x hx name ht hc
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · cases hc
      · exact h.taskRunOpen x hx name ht hc
    completeOutputs := by
      intro e he hc tr htr hid cc hcc
      rw [hw.concurrencyOf] at hcc
      exact h.completeOutputs e he hc tr htr hid cc hcc
    activeArm := h.activeArm }

theorem appendInvocation (h : Active p s) {i : Invocation} (ha : i.status = .active → i.arm = none) :
    Active p { s with invocations := s.invocations ++ [i] } where
  callActive := fun c hc ht hr => by
    obtain ⟨j, hj, rest⟩ := h.callActive c hc ht hr
    exact ⟨j, List.mem_append_left _ hj, rest⟩
  execActive := fun e he hc => by
    obtain ⟨j, hj, rest⟩ := h.execActive e he hc
    exact ⟨j, List.mem_append_left _ hj, rest⟩
  runActive := fun r hr o ho ht hc => by
    obtain ⟨j, hj, rest⟩ := h.runActive r hr o ho ht hc
    exact ⟨j, List.mem_append_left _ hj, rest⟩
  taskCallActive := h.taskCallActive
  taskRunOpen := h.taskRunOpen
  completeOutputs := h.completeOutputs
  activeArm := fun j hj hja => by
    rcases List.mem_append.mp hj with hj | hj
    · exact h.activeArm j hj hja
    · rw [List.mem_singleton.mp hj] at hja ⊢; exact ha hja

theorem appendCall (h : Active p s) {c : Call}
    (hnone : c.task = none → c.status = .running ∨ c.status = .fetching →
      ∃ i ∈ s.invocations, i.id = c.owner ∧ i.status = .active)
    (hsome : ∀ name, c.task = some name → c.status = .running ∨ c.status = .fetching →
      ∃ e ∈ s.executions, e.id = c.owner ∧ e.complete = false ∧
        ∃ ts, e.tasks.find? (·.name == name) = some ts ∧ ts.status = .active) :
    Active p { s with calls := s.calls ++ [c] } where
  callActive := fun x hx ht hr => by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.callActive x hx ht hr
    · rw [List.mem_singleton.mp hx] at ht hr ⊢; exact hnone ht hr
  execActive := h.execActive
  runActive := h.runActive
  taskCallActive := fun x hx name ht hr => by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.taskCallActive x hx name ht hr
    · rw [List.mem_singleton.mp hx] at ht hr ⊢; exact hsome name ht hr
  taskRunOpen := h.taskRunOpen
  completeOutputs := h.completeOutputs
  activeArm := h.activeArm

theorem appendExecution (h : Active p s) {e : Execution} (hnew : e.complete = false)
    (hopen : ∃ i ∈ s.invocations, i.id = e.id ∧ i.status = .active) :
    Active p { s with executions := s.executions ++ [e] } where
  callActive := h.callActive
  execActive := fun x hx hc => by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.execActive x hx hc
    · rw [List.mem_singleton.mp hx]; exact hopen
  runActive := h.runActive
  taskCallActive := fun c hc name ht hr => by
    obtain ⟨x, hx, rest⟩ := h.taskCallActive c hc name ht hr
    exact ⟨x, List.mem_append_left _ hx, rest⟩
  taskRunOpen := fun r hr name ht hc => by
    obtain ⟨x, hx, rest⟩ := h.taskRunOpen r hr name ht hc
    exact ⟨x, List.mem_append_left _ hx, rest⟩
  completeOutputs := fun x hx hc tr htr hid cc hcc => by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.completeOutputs x hx hc tr htr hid cc hcc
    · rw [List.mem_singleton.mp hx, hnew] at hc; cases hc
  activeArm := h.activeArm

theorem appendRun (h : Active p s) (hcc : ∀ e ∈ s.executions, ∃ cc, s.concurrencyOf p e = .ok cc) {r : Run}
    (hnone : ∀ o, r.owner = some o → r.task = none → r.complete = false →
      ∃ i ∈ s.invocations, i.id = o ∧ i.status = .active)
    (hsome : ∀ name, r.task = some name → r.complete = false →
      ∃ e ∈ s.executions, r.owner = some e.id ∧ e.complete = false) :
    Active p { s with runs := s.runs ++ [r] } := by
  have hw : KeepsWorkflows p s { s with runs := s.runs ++ [r] } := KeepsWorkflows.of_append rfl
  exact {
    callActive := h.callActive
    execActive := h.execActive
    runActive := fun x hx o ho ht hc => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h.runActive x hx o ho ht hc
      · rw [List.mem_singleton.mp hx] at ho ht hc; exact hnone o ho ht hc
    taskCallActive := h.taskCallActive
    taskRunOpen := fun x hx name ht hc => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h.taskRunOpen x hx name ht hc
      · rw [List.mem_singleton.mp hx] at ht hc ⊢; exact hsome name ht hc
    completeOutputs := fun e he hc tr htr hid cc hcc' => by
      obtain ⟨cc0, hcc0⟩ := hcc e he
      have := hw.concurrencyOf rfl rfl hcc0
      rw [concurrencyOf_det hcc' this]
      exact h.completeOutputs e he hc tr htr hid cc0 hcc0
    activeArm := h.activeArm }

theorem taskEnded_status {e : Execution} {ts : TaskState} (h : s.taskEnded e ts = true) : ts.status.ended = true := by
  simp only [State.taskEnded, Bool.and_eq_true] at h
  exact h.1.1

theorem taskEnded_runs {e : Execution} {ts : TaskState} (h : s.taskEnded e ts = true) :
    ∀ r ∈ s.runs, r.owner = some e.id → r.task = some ts.name → r.complete = true := by
  simp only [State.taskEnded, Bool.and_eq_true, List.all_eq_true, List.mem_filter, beq_iff_eq] at h
  exact fun r hr ho ht => h.2 r ⟨hr, ho, ht⟩

/-- An execution closes after all its tasks ended and its outputs were transformed. --/
theorem setExecution_close (h : Active p s) (own : Own p s) (wk : s.WellKeyed) {e : Execution}
    (he : e ∈ s.executions) {cc : Concurrency} (hcc : s.concurrencyOf p e = .ok cc)
    (hended : e.tasks.all (s.taskEnded e) = true)
    (houts : ∀ tr ∈ s.taskResults, tr.execution = e.id → tr.task ∈ included cc → tr.output ≠ .pending) :
    Active p (s.setExecution { e with complete := true }) := by
  have hw : SameWorkflows p s (s.setExecution { e with complete := true }) := SameWorkflows.of_runs rfl
  have fwd : ∀ x ∈ s.executions, x.id ≠ e.id → x ∈ (s.setExecution { e with complete := true }).executions :=
    fun x hx hne => mem_replace_of_mem hx hne
  exact {
    callActive := h.callActive
    execActive := fun x hx hc => by
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · cases hc
      · exact h.execActive x hx hc
    runActive := h.runActive
    taskCallActive := fun c hc name ht hr => by
      obtain ⟨x, hx, hxo, hxc, ts, hts, hact⟩ := h.taskCallActive c hc name ht hr
      by_cases hxe : x.id = e.id
      · have := wk.execution_eq_of_id hx he hxe
        subst this
        have := taskEnded_status (List.all_eq_true.mp hended ts (List.mem_of_find?_eq_some hts))
        rw [hact] at this
        cases this
      · exact ⟨x, fwd x hx hxe, hxo, hxc, ts, hts, hact⟩
    taskRunOpen := fun r hr name ht hc => by
      obtain ⟨x, hx, hxo, hxc⟩ := h.taskRunOpen r hr name ht hc
      by_cases hxe : x.id = e.id
      · have := wk.execution_eq_of_id hx he hxe
        subst this
        exfalso
        obtain ⟨x', hx', hxo', -, spec, -, -, hspec, -⟩ := own.runTask r hr name ht
        have : x' = x := wk.execution_eq_of_id hx' hx (Option.some.inj (hxo'.symm.trans hxo))
        subst this
        obtain ⟨cc', hcc', hnames⟩ := own.exec_concurrency hx'
        rw [taskSpec_eq_ok] at hspec
        obtain ⟨cc'', hcc'', hfind⟩ := hspec
        rw [concurrencyOf_det hcc'' hcc'] at hfind
        have hname : name ∈ x'.tasks.map (·.name) := by
          rw [hnames]
          obtain ⟨hmem, hn⟩ := find?_key_eq_some hfind
          exact List.mem_map.mpr ⟨spec, hmem, hn⟩
        obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hname
        have := taskEnded_runs (List.all_eq_true.mp hended ts hts) r hr hxo ht
        rw [hc] at this
        cases this
      · exact ⟨x, fwd x hx hxe, hxo, hxc⟩
    completeOutputs := fun x hx hc tr htr hid cc' hcc' => by
      rw [hw.concurrencyOf] at hcc'
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · have : s.concurrencyOf p e = .ok cc' := hcc'
        rw [concurrencyOf_det this hcc]
        exact houts tr htr hid
      · exact h.completeOutputs x hx hc tr htr hid cc' hcc'
    activeArm := h.activeArm }

/-- A call ends and its owner is settled with a final status. --/
theorem afterCall (h : Active p s) (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls)
    {status : CallStatus} (hst : status ≠ .running ∧ status ≠ .fetching)
    {inv : InvocationStatus} {task : TaskStatus} (hinv : inv ≠ .active)
    (ho : (s.setCall { c with status }).settleOwner c inv task = .ok t) : Active p t := by
  have h1 : Active p (s.setCall { c with status }) := h.setCall hc rfl rfl (fun hr => by
    rcases hr with hr | hr
    · exact absurd hr hst.1
    · exact absurd hr hst.2)
  -- The only call of the owner is `c`, which no longer runs.
  have quiet : ∀ x ∈ (s.setCall { c with status }).calls, x.owner = c.owner → x.task = c.task →
      x.status ≠ .running ∧ x.status ≠ .fetching := by
    intro x hx hxo hxt
    rcases mem_replace hx with rfl | ⟨hx, hne⟩
    · exact hst
    · exfalso
      apply hne
      cases htc : c.task with
      | none => rw [own.call_unique wk hx hc (hxt.trans htc) htc hxo]
      | some name => rw [own.taskCall_unique wk hx hc (hxt.trans htc) htc hxo]
  rcases settleOwner_eq_ok.mp ho with ⟨htc, i, hi, rfl⟩ | ⟨name, e, ts, htc, he, hts, rfl⟩
  · have hi' := invocation?_eq_some hi
    refine h1.setInvocation_off rfl hinv (fun x hx hxt hxo => quiet x hx (hxo.trans hi'.2) (hxt.trans htc.symm))
      (fun e he heq => absurd (heq.trans hi'.2) (own.call_not_exec wk hc htc he))
      (fun r hr ho ht => absurd (ho.trans (by rw [hi'.2])) (own.call_not_run wk hc htc hr ht))
  · have he' := execution?_eq_some he
    refine h1.setTask (by exact wk.setCall _) he'.1 (fun _ x hx hxo hxt => quiet x hx (hxo.trans he'.2) ?_)
    rw [hxt, htc]
    simp [(find?_key_eq_some hts).2]

/-- A cancelled call terminates and its active owner ends as cancelled. --/
theorem afterCancel (h : Active p s) (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls)
    (ho : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) : Active p t := by
  have h1 : Active p (s.setCall { c with status := .cancelled }) := h.setCall hc rfl rfl (fun hr => by
    rcases hr with hr | hr <;> cases hr)
  have quiet : ∀ x ∈ (s.setCall { c with status := .cancelled }).calls, x.owner = c.owner → x.task = c.task →
      x.status ≠ .running ∧ x.status ≠ .fetching := by
    intro x hx hxo hxt
    rcases mem_replace hx with rfl | ⟨hx, hne⟩
    · simp
    · exfalso
      apply hne
      cases htc : c.task with
      | none => rw [own.call_unique wk hx hc (hxt.trans htc) htc hxo]
      | some name => rw [own.taskCall_unique wk hx hc (hxt.trans htc) htc hxo]
  rcases cancelOwner_eq_ok.mp ho with ⟨htc, i, hi, rfl⟩ | ⟨name, e, ts, htc, he, hts, rfl⟩
  · have hi' := invocation?_eq_some hi
    split
    · exact h1.setInvocation_off rfl (by simp)
        (fun x hx hxt hxo => quiet x hx (hxo.trans hi'.2) (hxt.trans htc.symm))
        (fun e he heq => absurd (heq.trans hi'.2) (own.call_not_exec wk hc htc he))
        (fun r hr ho ht => absurd (ho.trans (by rw [hi'.2])) (own.call_not_run wk hc htc hr ht))
    · exact h1
  · have he' := execution?_eq_some he
    split
    · refine h1.setTask (by exact wk.setCall _) he'.1 (fun _ x hx hxo hxt => quiet x hx (hxo.trans he'.2) ?_)
      rw [hxt, htc]
      simp [(find?_key_eq_some hts).2]
    · exact h1

/-- A task that is not active has no running call. --/
theorem quiet_of_inactive (h : Active p s) (wk : s.WellKeyed) {e : Execution} (he : e ∈ s.executions)
    {name : String} {ts : TaskState} (hts : e.tasks.find? (·.name == name) = some ts) (hna : ts.status ≠ .active) :
    ∀ c ∈ s.calls, c.owner = e.id → c.task = some name → c.status ≠ .running ∧ c.status ≠ .fetching := by
  intro c hc hco hct
  by_cases hr : c.status = .running ∨ c.status = .fetching
  · exfalso
    obtain ⟨x, hx, hxo, -, ts', hts', hact⟩ := h.taskCallActive c hc name hct hr
    have : x = e := wk.execution_eq_of_id hx he (hxo.trans hco)
    subst this
    rw [hts] at hts'
    cases hts'
    exact hna hact
  · exact ⟨fun h1 => hr (Or.inl h1), fun h2 => hr (Or.inr h2)⟩

/-- Only the root run exists at the start. --/
theorem root {m : String} {input : Option Value} :
    Active p { started := true, runs := [{ path := [], workflow := m, input }] } where
  callActive := by simp
  execActive := by simp
  runActive := by simp
  taskCallActive := by simp
  taskRunOpen := by simp
  completeOutputs := by simp
  activeArm := by simp

/-- Every step keeps what keeps owners active, until the conclusion: after a stop, the conclusion ends
    the invocations of open executions and runs (`State.endUnfinished`). --/
theorem step (h : Active p s) (own : Own p s) (wk : s.WellKeyed) (h0 : s = {} ∨ s.started = true) {op : Op}
    (hs : step p s op = .ok t) (ht : t.status.terminal = false) : Active p t := by
  have hcc : ∀ e ∈ s.executions, ∃ cc, s.concurrencyOf p e = .ok cc :=
    fun e he => (own.exec_concurrency he).imp fun _ h => h.1
  cases op with
  | start input =>
    obtain ⟨hns, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h0 with rfl | h0
    · exact root
    · simp [h0] at hns
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, rfl, -, hfresh, hcases⟩ := Step.invoke_inv hs
    let inv : Invocation := { id := Key.invocation path name trigger, run := path, placement := name, trigger, input }
    have h1 := h.appendInvocation (i := inv) (fun _ => rfl)
    have hmem : inv ∈ s.invocations ++ [inv] := List.mem_append_right _ (List.mem_singleton_self _)
    rcases hcases with ⟨f, decl, hc, hdecl, -, rfl⟩ | ⟨judge, arms, hc, -, rfl⟩ | ⟨wf, out, hc, -, rfl⟩ |
      ⟨cc, hc, -, rfl⟩
    · exact h1.appendCall (fun _ _ => ⟨inv, hmem, rfl, rfl⟩) (fun _ h => by simp at h)
    · exact h1.appendCall (fun _ _ => ⟨inv, hmem, rfl, rfl⟩) (fun _ h => by simp at h)
    · exact h1.appendRun hcc (fun o ho _ _ => ⟨inv, hmem, (Option.some.inj ho).symm ▸ rfl, rfl⟩)
        (fun _ h => by simp at h)
    · exact h1.appendExecution rfl ⟨inv, hmem, rfl, rfl⟩
  | fetch id =>
    obtain ⟨-, -, c, hc, -, hst, rfl⟩ := Step.fetch_inv hs
    exact h.setCall (call?_eq_some hc).1 rfl rfl (fun _ => Or.inl hst)
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, hst, -, hacc, hso⟩ := Step.returned_inv hs
    have hc0 := (call?_eq_some hc).1
    have hcl : s'.calls = s.calls := (accept_frame hacc).2.2.2.2.2.1
    have h1 : Active p s' := by
      rcases accept_eq_ok.mp hacc with ⟨-, i, -, -, rfl⟩ | ⟨name, htc, -, rfl⟩
      · exact h.of_records rfl rfl rfl rfl rfl
      · obtain ⟨e, he, heo, hec, -⟩ := h.taskCallActive c hc0 name htc (Or.inl hst)
        exact h.appendTaskResult wk he heo hec
    exact h1.afterCall (own.of_sameKeys (SameKeys.accept hacc)) (wk.accept hacc) (by rw [hcl]; exact hc0)
      (status := .returned) (by simp) (inv := .succeeded) (by simp) hso
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, hst, -, htc, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hc0 := (call?_eq_some hc).1
    have hi' := invocation?_eq_some hi
    obtain ⟨-, -, -, hr, hin, hcl, hex, -, -, -⟩ := accept_frame hacc
    have h1 : Active p s' := by
      rcases accept_eq_ok.mp hacc with ⟨-, _, -, -, rfl⟩ | ⟨_, htc', -, -⟩
      · exact h.of_records rfl rfl rfl rfl rfl
      · rw [htc] at htc'; cases htc'
    have hc1 : c ∈ s'.calls := by rw [hcl]; exact hc0
    have h2 : Active p (s'.setCall { c with status := .returned }) :=
      h1.setCall hc1 rfl rfl (fun hr => by rcases hr with hr | hr <;> cases hr)
    refine h2.setInvocation_off (i := i) rfl (by simp) ?_ ?_ ?_
    · intro x hx hxt hxo
      rcases mem_replace hx with rfl | ⟨hx, hne⟩
      · simp
      · rw [hcl] at hx
        exact absurd (by rw [own.call_unique wk hx hc0 hxt htc (hxo.trans hi'.2)]) hne
    · intro e he heq
      rw [setCall_executions, hex] at he
      exact absurd (heq.trans hi'.2) (own.call_not_exec wk hc0 htc he)
    · intro r hr' ho ht
      rw [setCall_runs, hr] at hr'
      exact absurd (ho.trans (by rw [hi'.2])) (own.call_not_run wk hc0 htc hr' ht)
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, hst, hacc, rfl⟩ := Step.yielded_inv hs
    have hc0 := (call?_eq_some hc).1
    have hcl : s'.calls = s.calls := (accept_frame hacc).2.2.2.2.2.1
    have h1 : Active p s' := by
      rcases accept_eq_ok.mp hacc with ⟨-, i, -, -, rfl⟩ | ⟨name, htc, -, rfl⟩
      · exact h.of_records rfl rfl rfl rfl rfl
      · obtain ⟨e, he, heo, hec, -⟩ := h.taskCallActive c hc0 name htc (Or.inr hst)
        exact h.appendTaskResult wk he heo hec
    exact h1.setCall (c := c) (by rw [hcl]; exact hc0) rfl rfl (fun _ => Or.inr hst)
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    exact h.afterCall own wk (call?_eq_some hc).1 (status := .returned) (by simp) (inv := .succeeded) (by simp) hso
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact (h.afterCall own wk (call?_eq_some hc).1 (status := .failed) (by simp) (inv := .failed) (by simp) hso).fail
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact (h.afterCall own wk (call?_eq_some hc).1 (status := .cancelling) (by simp) (inv := .failed) (by simp)
      hso).fail
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
      exact (h.afterCall own wk (call?_eq_some hc).1 (status := .lost) (by simp) (inv := .failed) (by simp)
        hso).fail
    · exact h.afterCancel own wk (call?_eq_some hc).1 ho
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact h.afterCancel own wk (call?_eq_some hc).1 ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.of_records rfl rfl rfl rfl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact (h.of_records (t := { s with deliveries := s.deliveries ++ _ }) rfl rfl rfl rfl rfl).fail
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    have he' := execution?_eq_some he
    refine h.setTask wk he'.1 fun _ => ?_
    rw [show ({ ts with status := .ready, input := value } : TaskState).name = name from (find?_key_eq_some hts).2]
    exact h.quiet_of_inactive wk he'.1 hts (by rw [hpend]; simp)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, hts, hpend, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    have he' := execution?_eq_some he
    refine (h.setTask wk he'.1 fun _ => ?_).fail
    rw [show ({ ts with status := .failed } : TaskState).name = name from (find?_key_eq_some hts).2]
    exact h.quiet_of_inactive wk he'.1 hts (by rw [hpend]; simp)
  | beginTask eid name =>
    obtain ⟨-, -, e, cc, ts, spec, he, hec, -, hts, -, -, -, hcases⟩ := Step.beginTask_inv hs
    have he' := execution?_eq_some he
    have hname : ts.name = name := (find?_key_eq_some hts).2
    have h1 : Active p (s.setTask e { ts with status := .active }) := h.setTask wk he'.1 (fun hna => absurd rfl hna)
    have k1 := SameKeys.setTask (p := p) (ts := { ts with status := .active }) wk.executions he'.1
    have hmem : withTask e { ts with status := .active } ∈ (s.setTask e { ts with status := .active }).executions :=
      mem_replace_self he'.1 rfl
    have hfind : (withTask e { ts with status := .active }).tasks.find? (·.name == name) =
        some { ts with status := .active } := by
      rw [withTask_find?]
      simp [hname, hts]
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩
    · exact h1.appendCall (fun h => by simp at h) (fun name' h' _ => by
        simp only [Option.some.injEq] at h'
        subst h'
        exact ⟨_, hmem, rfl, hec, _, hfind, rfl⟩)
    · exact h1.appendRun (fun x hx => ((own.of_sameKeys k1).exec_concurrency hx).imp fun _ h => h.1)
        (fun _ _ h => by simp at h) (fun name' h' _ => by
          simp only [Option.some.injEq] at h'
          subst h'
          exact ⟨_, hmem, rfl, hec⟩)
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, cc, spec, r, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    have h1 : Active p (s.setTaskResult { r with output := .value value }) := h.setTaskResult (by simp)
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact h1.of_records rfl rfl rfl rfl rfl
    · exact h1
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (h.setTaskResult (r := { r with output := .failed }) (by simp)).fail
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact h.of_records rfl rfl rfl rfl rfl
    · exact h.of_records rfl rfl rfl rfl rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, hec, hcc0, hended, houts, hi, hcases⟩ := Step.closeExecution_inv hs
    have he' := execution?_eq_some he
    have hi' := invocation?_eq_some hi
    have houts' : ∀ tr ∈ s.taskResults, tr.execution = e.id → tr.task ∈ included cc → tr.output ≠ .pending := by
      intro tr htr hid hin
      have hmem : tr ∈ s.taskResults.filter fun x => x.execution == eid &&
          ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains x.task := by
        rw [List.mem_filter]
        refine ⟨htr, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
        exact ⟨hid.trans he'.2, hin⟩
      have := List.all_eq_true.mp houts tr hmem
      simpa using this
    have h1 := h.setExecution_close own wk he'.1 hcc0 hended houts'
    have hoff : ∀ st : InvocationStatus, st ≠ .active →
        Active p ((s.setExecution { e with complete := true }).setInvocation { i with status := st }) :=
      fun st hst => h1.setInvocation_off (i := i) rfl hst
        (fun c hc htc hco => absurd (by rw [hco, hi'.2, he'.2]) (own.call_not_exec wk hc htc he'.1))
        (fun x hx hid => by
          rcases mem_replace hx with rfl | ⟨-, hne⟩
          · rfl
          · exact absurd (hid.trans (hi'.2.trans he'.2.symm)) hne)
        (fun r hr ho ht => absurd (by rw [ho, hi'.2, he'.2]) (own.exec_not_run wk he'.1 hr ht))
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact hoff .skipped (by simp)
    · exact (hoff .succeeded (by simp)).of_records rfl rfl rfl rfl rfl
    · exact hoff .succeeded (by simp)
  | closeRun path =>
    obtain ⟨-, -, r, w, output, x, owner, hr, hrc, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
    have hr0 := (run?_eq_some hr).1
    have h1 := h.setRun_complete hr'
    have wk1 : (s.setRun { r with complete := true }).WellKeyed := wk.setRun _
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
    · have hi' := invocation?_eq_some hi
      have hoff : ∀ st : InvocationStatus, st ≠ .active →
          Active p ((s.setRun { r with complete := true }).setInvocation { i with status := st }) :=
        fun st hst => h1.setInvocation_off (i := i) rfl hst
          (fun c hc htc hco => absurd (by rw [howner, ← hi'.2, hco]) (own.call_not_run wk hc htc hr0 htask))
          (fun e he hid => absurd (by rw [howner, ← hi'.2, hid]) (own.exec_not_run wk he hr0 htask))
          (fun r2 hr2 ho ht => by
            rcases mem_replace hr2 with rfl | ⟨hr2, hne⟩
            · rfl
            · exact absurd (by rw [own.run_unique wk hr2 hr0 ho (howner.trans (by rw [hi'.2])) ht htask]) hne)
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (hoff .succeeded (by simp)).of_records rfl rfl rfl rfl rfl
      · exact hoff _ (by simp)
      · exact hoff _ (by simp)
      · exact hoff _ (by simp)
    · have he' := execution?_eq_some he
      have hname : ts.name = name := (find?_key_eq_some hts).2
      have hset : ∀ st : TaskStatus,
          Active p ((s.setRun { r with complete := true }).setTask e { ts with status := st }) := by
        intro st
        refine h1.setTask wk1 he'.1 fun _ c hc hco hct => ?_
        exfalso
        exact own.taskCall_not_run wk hc (hct.trans (by rw [← hname])) hr0 htask (by rw [howner, hco, he'.2])
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · obtain ⟨e2, he2, he2o, he2c⟩ := h.taskRunOpen r hr0 name htask hrc
        have : e2 = e := wk.execution_eq_of_id he2 he'.1 (Option.some.inj (he2o.symm.trans (howner.trans (by
          rw [he'.2]))))
        subst this
        exact (hset .succeeded).appendTaskResult (wk1.setTask _ _) (mem_replace_self he'.1 rfl) rfl he2c
      · exact hset _
      · exact hset _
      · exact hset _
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.stop.of_records rfl rfl rfl rfl rfl
    · exact h.of_records rfl rfl rfl rfl rfl
  | conclude =>
    rw [step_conclude_terminal hs] at ht
    cases ht

end Active

end Suimon.Settle
