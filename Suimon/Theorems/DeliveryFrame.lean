import Suimon.Theorems.DeliverySettleOutcome

/-! What every accepted step keeps: stored records keep their identity and the fields fixed at
    creation, and completion, ended calls and transformed task outputs are never undone. -/

namespace Suimon.Delivery
open State

/-- Records of `s` survive in `t` with their fixed fields; completion, ended calls and transformed
    task outputs stay. --/
structure Kept (s t : State) : Prop where
  grows : s.Grows t
  run : ∀ r ∈ s.runs, ∃ r' ∈ t.runs, r'.path = r.path ∧ r'.workflow = r.workflow ∧ r'.input = r.input ∧
    r'.owner = r.owner ∧ r'.task = r.task ∧ (r.complete = true → r'.complete = true)
  invocation : ∀ i ∈ s.invocations, ∃ i' ∈ t.invocations, i'.id = i.id ∧ i'.run = i.run ∧
    i'.placement = i.placement ∧ i'.trigger = i.trigger ∧ i'.input = i.input
  call : ∀ c ∈ s.calls, ∃ c' ∈ t.calls, c'.id = c.id ∧ c'.owner = c.owner ∧ c'.task = c.task ∧
    c'.target = c.target ∧ c'.stream = c.stream ∧ (c.status.ended = true → c' = c)
  execution : ∀ e ∈ s.executions, ∃ e' ∈ t.executions, e'.id = e.id ∧ e'.run = e.run ∧
    e'.placement = e.placement ∧ e'.tasks.map (·.name) = e.tasks.map (·.name) ∧
    (e.complete = true → e'.complete = true)
  taskResult : ∀ r ∈ s.taskResults, ∃ r' ∈ t.taskResults, r'.execution = r.execution ∧ r'.task = r.task ∧
    r'.index = r.index ∧ (r.output ≠ .pending → r'.output = r.output)

namespace Kept

theorem refl (s : State) : Kept s s :=
  ⟨State.Grows.refl s, fun r hr => ⟨r, hr, rfl, rfl, rfl, rfl, rfl, id⟩,
    fun i hi => ⟨i, hi, rfl, rfl, rfl, rfl, rfl⟩, fun c hc => ⟨c, hc, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    fun e he => ⟨e, he, rfl, rfl, rfl, rfl, id⟩, fun r hr => ⟨r, hr, rfl, rfl, rfl, fun _ => rfl⟩⟩

theorem trans {s t u : State} (h₁ : Kept s t) (h₂ : Kept t u) : Kept s u where
  grows := h₁.grows.trans h₂.grows
  run r hr := by
    obtain ⟨r', hr', a1, a2, a3, a4, a5, a6⟩ := h₁.run r hr
    obtain ⟨r'', hr'', b1, b2, b3, b4, b5, b6⟩ := h₂.run r' hr'
    exact ⟨r'', hr'', b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, fun h => b6 (a6 h)⟩
  invocation i hi := by
    obtain ⟨i', hi', a1, a2, a3, a4, a5⟩ := h₁.invocation i hi
    obtain ⟨i'', hi'', b1, b2, b3, b4, b5⟩ := h₂.invocation i' hi'
    exact ⟨i'', hi'', b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩
  call c hc := by
    obtain ⟨c', hc', a1, a2, a3, a4, a5, a6⟩ := h₁.call c hc
    obtain ⟨c'', hc'', b1, b2, b3, b4, b5, b6⟩ := h₂.call c' hc'
    refine ⟨c'', hc'', b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, fun h => ?_⟩
    obtain rfl := a6 h
    exact b6 h
  execution e he := by
    obtain ⟨e', he', a1, a2, a3, a4, a5⟩ := h₁.execution e he
    obtain ⟨e'', he'', b1, b2, b3, b4, b5⟩ := h₂.execution e' he'
    exact ⟨e'', he'', b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, fun h => b5 (a5 h)⟩
  taskResult r hr := by
    obtain ⟨r', hr', a1, a2, a3, a4⟩ := h₁.taskResult r hr
    obtain ⟨r'', hr'', b1, b2, b3, b4⟩ := h₂.taskResult r' hr'
    refine ⟨r'', hr'', b1.trans a1, b2.trans a2, b3.trans a3, fun h => ?_⟩
    have h' := a4 h
    rw [b4 (h' ▸ h), h']

/-- Steps that only append to the record lists. --/
theorem of_lists {s t : State} (hr : ∃ l, t.runs = s.runs ++ l) (hi : ∃ l, t.invocations = s.invocations ++ l)
    (hc : ∃ l, t.calls = s.calls ++ l) (he : ∃ l, t.executions = s.executions ++ l)
    (hres : ∃ l, t.results = s.results ++ l) (htr : ∃ l, t.taskResults = s.taskResults ++ l)
    (hd : ∃ l, t.deliveries = s.deliveries ++ l) (hs : ∃ l, t.settled = s.settled ++ l)
    (hf : ∃ l, t.failures = s.failures ++ l) : Kept s t := by
  obtain ⟨lr, hr⟩ := hr
  obtain ⟨li, hi⟩ := hi
  obtain ⟨lc, hc⟩ := hc
  obtain ⟨le, he⟩ := he
  obtain ⟨lres, hres⟩ := hres
  obtain ⟨ltr, htr⟩ := htr
  obtain ⟨ld, hd⟩ := hd
  obtain ⟨ls, hs⟩ := hs
  obtain ⟨lf, hf⟩ := hf
  refine ⟨⟨⟨lres, hres.symm⟩, ⟨ld, hd.symm⟩, ⟨ls, hs.symm⟩, ⟨lf, hf.symm⟩, ⟨li.map (·.id), by simp [hi]⟩,
    ⟨lc.map (·.id), by simp [hc]⟩, ⟨le.map (·.id), by simp [he]⟩,
    ⟨ltr.map fun r => (r.execution, r.task, r.index), by simp [htr]⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun r h => ⟨r, by rw [hr]; exact List.mem_append_left _ h, rfl, rfl, rfl, rfl, rfl, id⟩
  · exact fun i h => ⟨i, by rw [hi]; exact List.mem_append_left _ h, rfl, rfl, rfl, rfl, rfl⟩
  · exact fun c h => ⟨c, by rw [hc]; exact List.mem_append_left _ h, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · exact fun e h => ⟨e, by rw [he]; exact List.mem_append_left _ h, rfl, rfl, rfl, rfl, id⟩
  · exact fun r h => ⟨r, by rw [htr]; exact List.mem_append_left _ h, rfl, rfl, rfl, fun _ => rfl⟩

theorem of_eq {s t : State} (hr : t.runs = s.runs) (hi : t.invocations = s.invocations) (hc : t.calls = s.calls)
    (he : t.executions = s.executions) (hres : t.results = s.results) (htr : t.taskResults = s.taskResults)
    (hd : t.deliveries = s.deliveries) (hs : t.settled = s.settled) (hf : ∃ l, t.failures = s.failures ++ l) :
    Kept s t :=
  of_lists ⟨[], by simp [hr]⟩ ⟨[], by simp [hi]⟩ ⟨[], by simp [hc]⟩ ⟨[], by simp [he]⟩ ⟨[], by simp [hres]⟩
    ⟨[], by simp [htr]⟩ ⟨[], by simp [hd]⟩ ⟨[], by simp [hs]⟩ hf

theorem stop (s : State) : Kept s s.stop where
  grows := State.grows_stop
  run r hr := ⟨r, hr, rfl, rfl, rfl, rfl, rfl, id⟩
  invocation i hi := ⟨i, hi, rfl, rfl, rfl, rfl, rfl⟩
  call c hc := by
    refine ⟨stopCall c, State.mem_stop_calls.mpr ⟨c, hc, rfl⟩, by simp, by simp, by simp, ?_, ?_, fun h => ?_⟩
    · unfold stopCall; split <;> rfl
    · unfold stopCall; split <;> rfl
    · unfold stopCall
      have : (c.status == .running || c.status == .fetching) = false := by
        cases hs : c.status <;> simp_all [CallStatus.ended]
      simp [this]
  execution e he := by
    refine ⟨stopExecution e, State.mem_stop_executions.mpr ⟨e, he, rfl⟩, rfl, rfl, rfl, ?_, id⟩
    simp only [stopExecution, List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    split <;> rfl
  taskResult r hr := ⟨r, hr, rfl, rfl, rfl, fun _ => rfl⟩

theorem fail (s : State) (f : Failure) (policy : Policy) : Kept s (s.fail f policy) := by
  have h : Kept s { s with failures := s.failures ++ [f] } := of_eq rfl rfl rfl rfl rfl rfl rfl rfl ⟨[f], rfl⟩
  cases policy
  · exact h.trans (stop _)
  · exact h

theorem setRun {s : State} (wk : s.WellKeyed) {r : Run} (hr : r ∈ s.runs) (c : Bool) (hc : r.complete = true → c = true) :
    Kept s (s.setRun { r with complete := c }) where
  grows := State.grows_setRun
  run x hx := by
    by_cases hp : x.path = r.path
    · obtain rfl : x = r := wk.run_eq_of_path hx hr hp
      refine ⟨{ x with complete := c }, ?_, rfl, rfl, rfl, rfl, rfl, hc⟩
      simp only [State.setRun_runs]
      exact List.mem_map.mpr ⟨x, hx, by simp⟩
    · refine ⟨x, ?_, rfl, rfl, rfl, rfl, rfl, id⟩
      simp only [State.setRun_runs]
      exact List.mem_map.mpr ⟨x, hx, by simp [hp]⟩
  invocation i hi := ⟨i, hi, rfl, rfl, rfl, rfl, rfl⟩
  call c hc := ⟨c, hc, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  execution e he := ⟨e, he, rfl, rfl, rfl, rfl, id⟩
  taskResult r hr := ⟨r, hr, rfl, rfl, rfl, fun _ => rfl⟩

theorem setInvocation {s : State} {i i' : Invocation} (hid : i'.id = i.id) (hrun : i'.run = i.run)
    (hpl : i'.placement = i.placement) (htr : i'.trigger = i.trigger) (hin : i'.input = i.input)
    (wk : s.WellKeyed) (hi : i ∈ s.invocations) : Kept s (s.setInvocation i') where
  grows := State.grows_setInvocation
  run r hr := ⟨r, hr, rfl, rfl, rfl, rfl, rfl, id⟩
  invocation x hx := by
    by_cases hp : x.id = i.id
    · obtain rfl : x = i := wk.invocation_eq_of_id hx hi hp
      refine ⟨i', ?_, hid, hrun, hpl, htr, hin⟩
      simp only [State.setInvocation_invocations]
      exact List.mem_map.mpr ⟨x, hx, by simp [hid]⟩
    · refine ⟨x, ?_, rfl, rfl, rfl, rfl, rfl⟩
      simp only [State.setInvocation_invocations]
      exact List.mem_map.mpr ⟨x, hx, by simp [hid, hp]⟩
  call c hc := ⟨c, hc, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  execution e he := ⟨e, he, rfl, rfl, rfl, rfl, id⟩
  taskResult r hr := ⟨r, hr, rfl, rfl, rfl, fun _ => rfl⟩

theorem setCall {s : State} {c c' : Call} (hid : c'.id = c.id) (howner : c'.owner = c.owner) (htask : c'.task = c.task)
    (htarget : c'.target = c.target) (hstream : c'.stream = c.stream) (hne : c.status.ended = false)
    (wk : s.WellKeyed) (hc : c ∈ s.calls) : Kept s (s.setCall c') where
  grows := State.grows_setCall
  run r hr := ⟨r, hr, rfl, rfl, rfl, rfl, rfl, id⟩
  invocation i hi := ⟨i, hi, rfl, rfl, rfl, rfl, rfl⟩
  call x hx := by
    by_cases hp : x.id = c.id
    · obtain rfl : x = c := wk.call_eq_of_id hx hc hp
      refine ⟨c', ?_, hid, howner, htask, htarget, hstream, fun h => by simp [hne] at h⟩
      simp only [State.setCall_calls]
      exact List.mem_map.mpr ⟨x, hx, by simp [hid]⟩
    · refine ⟨x, ?_, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
      simp only [State.setCall_calls]
      exact List.mem_map.mpr ⟨x, hx, by simp [hid, hp]⟩
  execution e he := ⟨e, he, rfl, rfl, rfl, rfl, id⟩
  taskResult r hr := ⟨r, hr, rfl, rfl, rfl, fun _ => rfl⟩

theorem setExecution {s : State} {e e' : Execution} (hid : e'.id = e.id) (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) (hnames : e'.tasks.map (·.name) = e.tasks.map (·.name))
    (hc : e.complete = true → e'.complete = true) (wk : s.WellKeyed) (he : e ∈ s.executions) :
    Kept s (s.setExecution e') where
  grows := State.grows_setExecution
  run r hr := ⟨r, hr, rfl, rfl, rfl, rfl, rfl, id⟩
  invocation i hi := ⟨i, hi, rfl, rfl, rfl, rfl, rfl⟩
  call c hc := ⟨c, hc, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  execution x hx := by
    by_cases hp : x.id = e.id
    · obtain rfl : x = e := wk.execution_eq_of_id hx he hp
      refine ⟨e', ?_, hid, hrun, hpl, hnames, hc⟩
      simp only [State.setExecution_executions]
      exact List.mem_map.mpr ⟨x, hx, by simp [hid]⟩
    · refine ⟨x, ?_, rfl, rfl, rfl, rfl, id⟩
      simp only [State.setExecution_executions]
      exact List.mem_map.mpr ⟨x, hx, by simp [hid, hp]⟩
  taskResult r hr := ⟨r, hr, rfl, rfl, rfl, fun _ => rfl⟩

theorem withTask_names (e : Execution) (t : TaskState) : (withTask e t).tasks.map (·.name) = e.tasks.map (·.name) := by
  simp only [withTask_tasks, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  split
  · rename_i h
    exact (beq_iff_eq.mp h).symm
  · rfl

theorem setTask {s : State} {e : Execution} (ts : TaskState) (wk : s.WellKeyed) (he : e ∈ s.executions) :
    Kept s (s.setTask e ts) :=
  setExecution (e := e) (e' := withTask e ts) rfl rfl rfl (withTask_names e ts) id wk he

theorem setTaskResult {s : State} {r : TaskResult} (o : TaskOutput) (wk : s.WellKeyed) (hr : r ∈ s.taskResults)
    (hp : r.output = .pending) : Kept s (s.setTaskResult { r with output := o }) where
  grows := State.grows_setTaskResult
  run x hx := ⟨x, hx, rfl, rfl, rfl, rfl, rfl, id⟩
  invocation i hi := ⟨i, hi, rfl, rfl, rfl, rfl, rfl⟩
  call c hc := ⟨c, hc, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  execution e he := ⟨e, he, rfl, rfl, rfl, rfl, id⟩
  taskResult x hx := by
    by_cases hk : x.execution = r.execution ∧ x.task = r.task ∧ x.index = r.index
    · have hkey : (x.execution, x.task, x.index) = (r.execution, r.task, r.index) := by
        rw [hk.1, hk.2.1, hk.2.2]
      obtain rfl : x = r := by
        have h1 := find?_eq_some_of_nodup wk.taskResults hx
          (P := fun y => (y.execution, y.task, y.index) == (r.execution, r.task, r.index)) (fun y => by simp [hkey])
        have h2 := find?_eq_some_of_nodup wk.taskResults hr
          (P := fun y => (y.execution, y.task, y.index) == (r.execution, r.task, r.index)) (fun y => by simp)
        exact Option.some.inj (h1.symm.trans h2)
      refine ⟨{ x with output := o }, ?_, rfl, rfl, rfl, fun h => absurd hp h⟩
      simp only [State.setTaskResult_taskResults]
      exact List.mem_map.mpr ⟨x, hx, by simp⟩
    · refine ⟨x, ?_, rfl, rfl, rfl, fun _ => rfl⟩
      simp only [State.setTaskResult_taskResults]
      refine List.mem_map.mpr ⟨x, hx, ?_⟩
      have : (x.execution == r.execution && x.task == r.task && x.index == r.index) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        by_cases h1 : x.execution = r.execution
        · by_cases h2 : x.task = r.task
          · exact Or.inr fun h3 => hk ⟨h1, h2, h3⟩
          · exact Or.inl (Or.inr h2)
        · exact Or.inl (Or.inl h1)
      simp [this]

end Kept

section Ops
variable {s t : State}

theorem accept_kept {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : Kept s t := by
  rcases State.accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
  · exact Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩
      ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
  · exact Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨_, rfl⟩
      ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩

theorem settleOwner_kept (wk : s.WellKeyed) {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : s.settleOwner c inv task = .ok t) : Kept s t := by
  rcases State.settleOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, e, ts, -, he, -, rfl⟩
  · exact Kept.setInvocation (i := i) rfl rfl rfl rfl rfl wk (State.invocation?_eq_some hi).1
  · exact Kept.setTask _ wk (State.execution?_eq_some he).1

theorem cancelOwner_kept (wk : s.WellKeyed) {c : Call} (h : s.cancelOwner c = .ok t) : Kept s t := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, e, ts, -, he, -, rfl⟩ <;> split
  · exact Kept.setInvocation (i := i) rfl rfl rfl rfl rfl wk (State.invocation?_eq_some hi).1
  · exact Kept.refl s
  · exact Kept.setTask _ wk (State.execution?_eq_some he).1
  · exact Kept.refl s

theorem setCall_status_kept (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) (hne : c.status.ended = false)
    (status : CallStatus) : Kept s (s.setCall { c with status }) :=
  Kept.setCall (c := c) rfl rfl rfl rfl rfl hne wk hc

theorem failCall_kept (wk : s.WellKeyed) {c : Call} {status : CallStatus} {cause : Cause} (hc : c ∈ s.calls)
    (hne : c.status.ended = false) (h : s.failCall c status cause = .ok t) : Kept s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  exact (setCall_status_kept wk hc hne status).trans
    ((settleOwner_kept (wk.setCall _) hso).trans (Kept.fail _ _ _))

end Ops

theorem ended_of_running {c : Call} (h : c.status = .running ∨ c.status = .fetching) : c.status.ended = false := by
  rcases h with h | h <;> simp [h, CallStatus.ended]

open State in
/-- Every accepted step keeps the records of the state before it. --/
theorem step_kept {p : Program} {s t : State} {op : Op} (wk : s.WellKeyed) (hfresh : s.runs = [] ∨ s.started = true)
    (hs : step p s op = .ok t) : Kept s t := by
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    -- Before the start there are no runs to keep.
    have hnil : s.runs = [] := hfresh.resolve_right (by simp [hst])
    exact Kept.of_lists ⟨[{ path := [], workflow := p.main, input }], by simp [hnil]⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
      ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact Kept.of_lists ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
    · exact Kept.of_lists ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
    · exact Kept.of_lists ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
    · exact Kept.of_lists ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
  | fetch id =>
    obtain ⟨-, -, c, hc, -, h4, rfl⟩ := Step.fetch_inv hs
    exact setCall_status_kept wk (call?_eq_some hc).1 (ended_of_running (Or.inl h4)) _
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, h4, -, hacc, hso⟩ := Step.returned_inv hs
    have k1 := accept_kept hacc
    have wk' := wk.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact k1.trans ((setCall_status_kept wk' hc' (ended_of_running (Or.inl h4)) _).trans
      (settleOwner_kept (wk'.setCall _) hso))
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', hc, h3, -, -, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have k1 := accept_kept hacc
    have wk' := wk.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    have hi' : i ∈ (s'.setCall { c with status := .returned }).invocations := by
      rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1]; exact (invocation?_eq_some hi).1
    exact k1.trans ((setCall_status_kept wk' hc' (ended_of_running (Or.inl h3)) _).trans
      (Kept.setInvocation (i := i) rfl rfl rfl rfl rfl (wk'.setCall _) hi'))
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, h4, hacc, rfl⟩ := Step.yielded_inv hs
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact (accept_kept hacc).trans
      (Kept.setCall (c := c) rfl rfl rfl rfl rfl (ended_of_running (Or.inr h4)) (wk.accept hacc) hc')
  | ended id =>
    obtain ⟨-, -, c, hc, -, h4, hso⟩ := Step.ended_inv hs
    exact (setCall_status_kept wk (call?_eq_some hc).1 (ended_of_running (Or.inr h4)) _).trans
      (settleOwner_kept (wk.setCall _) hso)
  | failed id =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.failed_inv hs
    exact failCall_kept wk (call?_eq_some hc).1 (ended_of_running h3) h
  | timedOut id element =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.timedOut_inv hs
    refine failCall_kept wk (call?_eq_some hc).1 ?_ h
    rcases h3 with ⟨-, h3, -⟩ | ⟨-, h3, -⟩
    · exact ended_of_running (Or.inr h3)
    · exact ended_of_running h3
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨h3, h⟩ | ⟨h3, h⟩⟩ := Step.lost_inv hs
    · exact failCall_kept wk (call?_eq_some hc).1 (ended_of_running h3) h
    · exact (setCall_status_kept wk (call?_eq_some hc).1 (by simp [h3, CallStatus.ended]) _).trans
        (cancelOwner_kept (wk.setCall _) h)
  | terminated id =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.terminated_inv hs
    exact (setCall_status_kept wk (call?_eq_some hc).1 (by simp [h3, CallStatus.ended]) _).trans
      (cancelOwner_kept (wk.setCall _) h)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
      ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact (Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
      ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩).trans (Kept.fail _ _ _)
  | taskInput eid name value =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Kept.setTask _ wk (execution?_eq_some he).1
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (Kept.setTask _ wk (execution?_eq_some he).1).trans (Kept.fail _ _ _)
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    have k := Kept.setTask { ts with status := .active } wk (execution?_eq_some he).1
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact k.trans (Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩)
    · exact k.trans (Kept.of_lists ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩)
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, r, -, -, -, -, hr, h4, h⟩ := Step.taskOutput_inv hs
    have k := Kept.setTaskResult (.value value) wk (List.mem_of_find?_eq_some hr) h4
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact k.trans (Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩)
    · exact k
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, hr, h4, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (Kept.setTaskResult .failed wk (List.mem_of_find?_eq_some hr) h4).trans (Kept.fail _ _ _)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩
    · exact Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i, he, -, -, -, -, hi, h⟩ := Step.closeExecution_inv hs
    have k1 := Kept.setExecution (e := e) (e' := { e with complete := true }) rfl rfl rfl rfl (fun _ => rfl) wk
      (execution?_eq_some he).1
    have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (invocation?_eq_some hi).1
    have k2 := k1.trans (Kept.setInvocation (i := i) (i' := { i with status := .skipped }) rfl rfl rfl rfl rfl
      (wk.setExecution _) hi')
    have k3 := k1.trans (Kept.setInvocation (i := i) (i' := { i with status := .succeeded }) rfl rfl rfl rfl rfl
      (wk.setExecution _) hi')
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact k2
    · exact k3.trans (Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨_, rfl⟩
        ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩)
    · exact k3
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, h3, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    have k1 := Kept.setRun wk (run?_eq_some hr).1 true (fun _ => rfl)
    have wk1 := wk.setRun { r with complete := true }
    rcases h with ⟨-, i, hi, h⟩ | ⟨_, e, ts, -, he, -, h⟩
    · have hi' : i ∈ (s.setRun { r with complete := true }).invocations := (invocation?_eq_some hi).1
      have k2 : ∀ st, Kept s ((s.setRun { r with complete := true }).setInvocation { i with status := st }) :=
        fun st => k1.trans (Kept.setInvocation (i := i) rfl rfl rfl rfl rfl wk1 hi')
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (k2 .succeeded).trans (Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨_, rfl⟩
          ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩)
      all_goals exact k2 _
    · have he' : e ∈ (s.setRun { r with complete := true }).executions := (execution?_eq_some he).1
      have k2 : ∀ st, Kept s ((s.setRun { r with complete := true }).setTask e { ts with status := st }) :=
        fun st => k1.trans (Kept.setTask _ wk1 he')
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (k2 .succeeded).trans (Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
          ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩)
      all_goals exact k2 _
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact (Kept.stop s).trans (Kept.of_eq rfl rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp⟩)
    · exact Kept.of_eq rfl rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp⟩
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact (Kept.setRun wk (run?_eq_some hr).1 true (fun _ => rfl)).trans
        (Kept.of_eq rfl rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp⟩)
    · exact Kept.of_eq rfl rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp⟩

/-! ### Lookups that a step keeps -/

theorem workflow?_iff {p : Program} {s : State} {path : Path} {w : Workflow} :
    s.workflow? p path = some w ↔ ∃ r, s.run? path = some r ∧ p.workflow? r.workflow = some w := by
  unfold State.workflow?
  exact option_bind_eq_some

theorem concurrencyOf_iff {p : Program} {s : State} {e : Execution} {c : Concurrency} :
    s.concurrencyOf p e = .ok c ↔
      ∃ w pl, s.workflow? p e.run = some w ∧ w.placement? e.placement = some pl ∧ pl.control = .concurrency c := by
  rw [State.concurrencyOf_eq_ok]
  simp only [State.placementOf_eq_ok]
  constructor
  · rintro ⟨pl, ⟨w, hw, hpl⟩, hc⟩
    exact ⟨w, pl, hw, hpl, hc⟩
  · rintro ⟨w, pl, hw, hpl, hc⟩
    exact ⟨pl, ⟨w, hw, hpl⟩, hc⟩

/-- The concurrency spec of an execution depends only on its run and placement. --/
theorem concurrencyOf_congr {p : Program} {s : State} {e e' : Execution} (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) : s.concurrencyOf p e' = s.concurrencyOf p e := by
  unfold State.concurrencyOf
  rw [hrun, hpl]

theorem taskSpec_congr {p : Program} {s : State} {e e' : Execution} {name : String} (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) : s.taskSpec p e' name = s.taskSpec p e name := by
  unfold State.taskSpec
  rw [concurrencyOf_congr hrun hpl]

namespace Kept
variable {s t : State}

theorem run? (hk : Kept s t) (wk : t.WellKeyed) {path : Path} {r : Run} (h : s.run? path = some r) :
    ∃ r', t.run? path = some r' ∧ r'.workflow = r.workflow ∧ r'.input = r.input ∧ r'.owner = r.owner ∧
      r'.task = r.task ∧ (r.complete = true → r'.complete = true) := by
  obtain ⟨hr, rfl⟩ := State.run?_eq_some h
  obtain ⟨r', hr', a1, a2, a3, a4, a5, a6⟩ := hk.run r hr
  exact ⟨r', a1 ▸ wk.run?_of_mem hr', a2, a3, a4, a5, a6⟩

theorem workflow? (hk : Kept s t) (wk : t.WellKeyed) {p : Program} {path : Path} {w : Workflow}
    (h : s.workflow? p path = some w) : t.workflow? p path = some w := by
  obtain ⟨r, hr, hw⟩ := workflow?_iff.mp h
  obtain ⟨r', hr', hwf, -⟩ := hk.run? wk hr
  exact workflow?_iff.mpr ⟨r', hr', hwf ▸ hw⟩

theorem concurrencyOf (hk : Kept s t) (wk : t.WellKeyed) {p : Program} {e e' : Execution} {c : Concurrency}
    (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (h : s.concurrencyOf p e = .ok c) :
    t.concurrencyOf p e' = .ok c := by
  obtain ⟨w, pl, hw, hpl', hc⟩ := concurrencyOf_iff.mp h
  exact concurrencyOf_iff.mpr ⟨w, pl, hrun ▸ hk.workflow? wk hw, hpl ▸ hpl', hc⟩

theorem taskSpec (hk : Kept s t) (wk : t.WellKeyed) {p : Program} {e e' : Execution} {name : String}
    {spec : TaskSpec} (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (h : s.taskSpec p e name = .ok spec) :
    t.taskSpec p e' name = .ok spec := by
  obtain ⟨c, hc, hf⟩ := State.taskSpec_eq_ok.mp h
  exact State.taskSpec_eq_ok.mpr ⟨c, hk.concurrencyOf wk hrun hpl hc, hf⟩

theorem settled? (hk : Kept s t) {path : Path} {name : String} {x : Settled} (h : s.settled? path name = some x) :
    t.settled? path name = some x :=
  hk.grows.settled?_eq_some h

theorem delivery? (hk : Kept s t) {path : Path} {j : Nat} {src : ResultId} {d : Delivery}
    (h : s.delivery? path j src = some d) : t.delivery? path j src = some d :=
  hk.grows.delivery?_eq_some h

theorem mem_results (hk : Kept s t) {r : Result} (h : r ∈ s.results) : r ∈ t.results := hk.grows.mem_results h
theorem mem_settled (hk : Kept s t) {x : Settled} (h : x ∈ s.settled) : x ∈ t.settled := hk.grows.mem_settled h
theorem mem_deliveries (hk : Kept s t) {d : Delivery} (h : d ∈ s.deliveries) : d ∈ t.deliveries :=
  hk.grows.mem_deliveries h

/-- An invocation of `s` is found in `t` under its identity, in the same run and placement. --/
theorem mem_invocationsOf (hk : Kept s t) {i : Invocation} (h : i ∈ s.invocations) :
    ∃ i' ∈ t.invocations, i'.id = i.id ∧ i'.run = i.run ∧ i'.placement = i.placement ∧ i'.trigger = i.trigger :=
  let ⟨i', hi', a1, a2, a3, a4, _⟩ := hk.invocation i h
  ⟨i', hi', a1, a2, a3, a4⟩

end Kept

end Suimon.Delivery
