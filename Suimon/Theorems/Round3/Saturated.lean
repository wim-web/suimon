import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## [19] Round3/Saturated.lean — task F1 -/

section SaturatedSection
variable {p : Definition} {T : State}

/-- What a complete run has done: everything it could (§13.3). -/
structure Saturated (p : Definition) (T : State) : Prop where
  runs : ∀ r ∈ T.runs, r.complete = true
  calls : ∀ c ∈ T.calls, c.status.ended = true
  executions : ∀ e ∈ T.executions, e.complete = true ∧ ∀ t ∈ e.tasks, t.status.ended = true
  settled : ∀ r ∈ T.runs, ∀ w, p.workflow? r.workflow = some w → ∀ pl ∈ w.placements,
    (T.settled? r.path pl.name).isSome
  delivered : ∀ r ∈ T.results, ∀ w, T.workflow? p r.run = some w → ∀ j c, w.connections[j]? = some c →
    c.source = r.placement → (c.arm = none ∨ c.arm = r.arm) → (T.delivery? r.run j r.id).isSome
  invoked : ∀ r ∈ T.runs, ∀ w, p.workflow? r.workflow = some w → ∀ pl ∈ w.placements,
    Settle.invocable pl.control = true →
    match w.shape? p pl.name with
    | some .none | some .entry => ∃ i ∈ T.invocationsOf r.path pl.name, i.trigger = none
    | some (.single j c) => ∀ src v, T.resolveSingle r.path j c = .value src v →
        ∃ i ∈ T.invocationsOf r.path pl.name, i.trigger = some src
    | some (.stream j _) => Settle.Triggered T r.path pl.name j
    | _ => True
  outputs : ∀ e ∈ T.executions, ∀ c, T.concurrencyOf p e = .ok c → ∀ r ∈ T.taskResults, r.execution = e.id →
    (∃ spec ∈ c.tasks, spec.name = r.task ∧ spec.output.isSome) → r.output ≠ .pending

/-! ### The tasks of a completed execution ended

`closeExecution` requires every task of the execution to have ended, and no later step reopens one:
`beginTask` needs an open execution, `taskInput` a pending task, `stop` only ends tasks, and every
other change of a task status ends the task. -/

/-- Every task of a completed execution ended. -/
private def TasksEnded (s : State) : Prop :=
  ∀ e ∈ s.executions, e.complete = true → ∀ ts ∈ e.tasks, ts.status.ended = true

private theorem TasksEnded.of_executions {s t : State} (h : TasksEnded s) (he : t.executions = s.executions) :
    TasksEnded t :=
  fun e hm => h e (he ▸ hm)

private theorem TasksEnded.setExecution {s : State} {e : Execution} (h : TasksEnded s)
    (he : e.complete = true → ∀ ts ∈ e.tasks, ts.status.ended = true) : TasksEnded (s.setExecution e) := by
  intro x hx hc
  rcases mem_setExecution_executions hx with rfl | hx
  · exact he hc
  · exact h x hx hc

/-- Storing a task of a stored execution keeps the invariant if the execution is open or the new
    status ends the task. -/
private theorem TasksEnded.setTask {s : State} {e : Execution} {ts : TaskState} (h : TasksEnded s)
    (he : e ∈ s.executions) (hts : e.complete = true → ts.status.ended = true) : TasksEnded (s.setTask e ts) := by
  rw [setTask_eq]
  refine h.setExecution fun hc x hx => ?_
  rw [withTask_complete] at hc
  rw [withTask_tasks] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  split
  · exact hts hc
  · exact h e he hc y hy

/-- The conclusion after a stop ends every task. -/
private theorem TasksEnded.endUnfinished {s : State} : TasksEnded s.endUnfinished := by
  intro x hx _ ts hts
  obtain ⟨e, -, rfl⟩ := mem_endUnfinished_executions.mp hx
  rw [endExecution_tasks, List.mem_map] at hts
  obtain ⟨ts₀, -, rfl⟩ := hts
  exact endTask_ended

private theorem TasksEnded.stop {s : State} (h : TasksEnded s) : TasksEnded s.stop := by
  intro x hx hc
  obtain ⟨e, he, rfl⟩ := mem_stop_executions.mp hx
  intro ts hts
  simp only [stopExecution, List.mem_map] at hts
  obtain ⟨y, hy, rfl⟩ := hts
  split
  · rfl
  · exact h e he hc y hy

private theorem TasksEnded.fail {s : State} {f : Failure} {policy : Policy} (h : TasksEnded s) :
    TasksEnded (s.fail f policy) := by
  cases policy
  · rw [fail_stop]
    exact TasksEnded.stop (h.of_executions rfl)
  · rw [fail_continue]
    exact h.of_executions rfl

private theorem TasksEnded.accept {s t : State} {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : TasksEnded s) (ha : s.accept c index value arm = .ok t) : TasksEnded t :=
  h.of_executions (accept_frame ha).2.2.2.2.2.2.1

private theorem TasksEnded.settleOwner {s t : State} {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : TasksEnded s) (ho : s.settleOwner c inv task = .ok t) (hended : task.ended = true) : TasksEnded t := by
  rcases settleOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨_, e, _, -, he, -, rfl⟩
  · exact h.of_executions rfl
  · exact h.setTask (State.execution?_eq_some he).1 fun _ => hended

private theorem TasksEnded.cancelOwner {s t : State} {c : Call} (h : TasksEnded s) (ho : s.cancelOwner c = .ok t) :
    TasksEnded t := by
  rcases cancelOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨_, e, _, -, he, -, rfl⟩ <;> split
  · exact h.of_executions rfl
  · exact h
  · exact h.setTask (State.execution?_eq_some he).1 fun _ => rfl
  · exact h

private theorem TasksEnded.failCall {s t : State} {c : Call} {status : CallStatus} {cause : Cause}
    (h : TasksEnded s) (hf : s.failCall c status cause = .ok t) : TasksEnded t := by
  obtain ⟨_, _, -, ho, rfl⟩ := failCall_eq_ok.mp hf
  have h' : TasksEnded (s.setCall { c with status }) := h.of_executions rfl
  exact (h'.settleOwner ho rfl).fail

private theorem step_tasksEnded {s t : State} {op : Op} (h : TasksEnded s) (hs : step p s op = .ok t) :
    TasksEnded t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact h.of_executions rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact h.of_executions rfl
    · exact h.of_executions rfl
    · exact h.of_executions rfl
    · intro x hx hc
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx hc
      · rw [List.mem_singleton.mp hx] at hc
        cases hc
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.of_executions rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have h' : TasksEnded (s'.setCall { c with status := .returned }) := (h.accept hacc).of_executions rfl
    exact h'.settleOwner hso rfl
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact (h.accept hacc).of_executions rfl
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (h.accept hacc).of_executions rfl
  | ended id =>
    obtain ⟨-, -, c, -, -, -, hso⟩ := Step.ended_inv hs
    have h' : TasksEnded (s.setCall { c with status := .returned }) := h.of_executions rfl
    exact h'.settleOwner hso rfl
  | failed id =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.failed_inv hs
    exact h.failCall hf
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.timedOut_inv hs
    exact h.failCall hf
  | lost id =>
    obtain ⟨-, -, c, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.failCall hf
    · have h' : TasksEnded (s.setCall { c with status := .cancelled }) := h.of_executions rfl
      exact h'.cancelOwner ho
  | terminated id =>
    obtain ⟨-, -, c, -, -, ho⟩ := Step.terminated_inv hs
    have h' : TasksEnded (s.setCall { c with status := .cancelled }) := h.of_executions rfl
    exact h'.cancelOwner ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.of_executions rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    refine TasksEnded.fail ?_
    exact h.of_executions rfl
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, _, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    -- A pending task belongs to an open execution.
    refine h.setTask (State.execution?_eq_some he).1 fun hc => ?_
    have := h e (State.execution?_eq_some he).1 hc ts (List.mem_of_find?_eq_some hts)
    rw [hpend] at this
    cases this
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, _, _, _, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (h.setTask (State.execution?_eq_some he).1 fun _ => rfl).fail
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, hopen, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    have h' := h.setTask (ts := { ts with status := .active }) (State.execution?_eq_some he).1
      fun hc => by rw [hopen] at hc; cases hc
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact h'.of_executions rfl
    · exact h'.of_executions rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact h.of_executions rfl
    · exact h.of_executions rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    refine TasksEnded.fail ?_
    exact h.of_executions rfl
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact h.of_executions rfl
    · exact h.of_executions rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, -, -, -, hall, -, -, hcases⟩ := Step.closeExecution_inv hs
    -- The guard: every task ended.
    have h' : TasksEnded (s.setExecution { e with complete := true }) := by
      refine h.setExecution fun _ ts hts => ?_
      have := List.all_eq_true.mp hall ts hts
      simp only [State.taskEnded, Bool.and_eq_true] at this
      exact this.1.1
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h'.of_executions rfl
    · exact h'.of_executions rfl
    · exact h'.of_executions rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    have h' : TasksEnded (s.setRun { r with complete := true }) := h.of_executions rfl
    rcases hcases with ⟨-, _, -, hcases⟩ | ⟨_, e, _, -, he, -, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h'.of_executions rfl
    · have he' : e ∈ (s.setRun { r with complete := true }).executions := (State.execution?_eq_some he).1
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (h'.setTask he' fun _ => rfl).of_executions rfl
      · exact h'.setTask he' fun _ => rfl
      · exact h'.setTask he' fun _ => rfl
      · exact h'.setTask he' fun _ => rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.stop.of_executions rfl
    · exact h.of_executions rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact h.of_executions rfl
    · exact TasksEnded.endUnfinished.of_executions rfl

/-- In every reachable state, every task of a completed execution ended. -/
theorem Saturated.reachable_tasks_ended {s : State} (h : Reachable p s) :
    ∀ e ∈ s.executions, e.complete = true → ∀ ts ∈ e.tasks, ts.status.ended = true := by
  induction h with
  | empty => intro e he; simp at he
  | step op _ hs ih => exact step_tasksEnded ih hs

/-- Mostly Round 2: `Reachable.done_complete`, `Reachable.complete_run_settled`,
    `Reachable.delivered_of_validate`, `Settle.SettledInv.closed`, `Reachable.execution_outputs`; new:
    the tasks of a completed execution ended. -/
theorem saturated (valid : p.validate = .ok ()) (h : Reachable p T) (done : Done T) : Saturated p T := by
  obtain ⟨hruns, hexecs, hcalls⟩ := Reachable.done_complete h done
  have hsettled : ∀ r ∈ T.runs, ∀ w, p.workflow? r.workflow = some w → ∀ pl ∈ w.placements,
      (T.settled? r.path pl.name).isSome :=
    fun r hr => Reachable.complete_run_settled h r hr (hruns r hr)
  refine ⟨hruns, hcalls, fun e he => ⟨hexecs e he, Saturated.reachable_tasks_ended h e he (hexecs e he)⟩,
    hsettled, Reachable.delivered_of_validate valid h done, ?_,
    fun e he => Reachable.execution_outputs h e he (hexecs e he)⟩
  -- Each placement of a completed run settled, and a settled placement is closed (`Settle.Closed`).
  intro r hr w hw pl hpl hinv
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hsettled r hr w hw pl hpl)
  obtain ⟨hxm, hxr, hxp⟩ := State.settled?_eq_some hx
  obtain ⟨w', pl', hw', hpl', hclosed⟩ := (Settle.reachable h).2.2.2.closed x hxm
  have hww : T.workflow? p x.run = some w := by
    rw [hxr]
    simp [State.workflow?, h.wellKeyed.run?_of_mem hr, hw]
  have hw'' : w' = w := by
    rw [hww] at hw'
    exact (Option.some.inj hw').symm
  rw [hw''] at hpl' hclosed
  -- Placement names are unique, so the settled placement is `pl`.
  have hnames := ((Definition.validate_ok valid).workflows w (Definition.workflow?_eq_some hw).1).names
  have hpl'' : pl' = pl := by
    rw [hxp, Workflow.placement?_of_mem hnames hpl] at hpl'
    exact (Option.some.inj hpl').symm
  rw [hpl''] at hclosed
  unfold Settle.Closed at hclosed
  rw [hxr, hxp] at hclosed
  revert hclosed
  cases w.shape? p pl.name with
  | none => intro _; trivial
  | some sh =>
    cases sh with
    | none => exact fun hc => hc hinv
    | entry => exact fun hc => hc hinv
    | single j c => exact fun hc => hc.1
    | stream j c => exact fun hc => hc.2.2 hinv
    | merge cs => intro _; trivial

end SaturatedSection

end Suimon.Round3
