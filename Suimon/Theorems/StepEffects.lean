import Suimon.Theorems.StepInversion

/-! Effects of one accepted step on the whole state: the append-only parts grow, the workflow stays
    started, and what a stopping state can still do. -/

namespace Suimon

/-- From `s` to `t`, accepted results, deliveries, settlements and failures are only appended to,
    and invocations, calls, executions and task results keep their identities in order. --/
structure State.Grows (s t : State) : Prop where
  results : s.results <+: t.results
  deliveries : s.deliveries <+: t.deliveries
  settled : s.settled <+: t.settled
  failures : s.failures <+: t.failures
  invocations : s.invocations.map (·.id) <+: t.invocations.map (·.id)
  calls : s.calls.map (·.id) <+: t.calls.map (·.id)
  executions : s.executions.map (·.id) <+: t.executions.map (·.id)
  taskResults : s.taskResults.map (fun r => (r.execution, r.task, r.index)) <+:
    t.taskResults.map (fun r => (r.execution, r.task, r.index))

namespace State.Grows

theorem refl (s : State) : s.Grows s :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem trans {s t u : State} (h₁ : s.Grows t) (h₂ : t.Grows u) : s.Grows u :=
  ⟨h₁.results.trans h₂.results, h₁.deliveries.trans h₂.deliveries, h₁.settled.trans h₂.settled,
    h₁.failures.trans h₂.failures, h₁.invocations.trans h₂.invocations, h₁.calls.trans h₂.calls,
    h₁.executions.trans h₂.executions, h₁.taskResults.trans h₂.taskResults⟩

theorem mem_results {s t : State} (h : s.Grows t) {r : Result} (hr : r ∈ s.results) : r ∈ t.results :=
  h.results.subset hr
theorem mem_deliveries {s t : State} (h : s.Grows t) {d : Delivery} (hd : d ∈ s.deliveries) : d ∈ t.deliveries :=
  h.deliveries.subset hd
theorem mem_settled {s t : State} (h : s.Grows t) {x : Settled} (hx : x ∈ s.settled) : x ∈ t.settled :=
  h.settled.subset hx
theorem mem_failures {s t : State} (h : s.Grows t) {f : Failure} (hf : f ∈ s.failures) : f ∈ t.failures :=
  h.failures.subset hf

theorem invocation?_isSome {s t : State} (h : s.Grows t) {id : String} (hi : (s.invocation? id).isSome) :
    (t.invocation? id).isSome :=
  find?_key_isSome_of_prefix h.invocations hi
theorem call?_isSome {s t : State} (h : s.Grows t) {id : String} (hc : (s.call? id).isSome) : (t.call? id).isSome :=
  find?_key_isSome_of_prefix h.calls hc
theorem execution?_isSome {s t : State} (h : s.Grows t) {id : String} (he : (s.execution? id).isSome) :
    (t.execution? id).isSome :=
  find?_key_isSome_of_prefix h.executions he
theorem result?_eq_some {s t : State} (h : s.Grows t) {id : ResultId} {r : Result} (hr : s.result? id = some r) :
    t.result? id = some r := by
  obtain ⟨rest, hrest⟩ := h.results
  simp only [State.result?, ← hrest, List.find?_append]
  simp only [State.result?] at hr
  simp [hr]
theorem settled?_eq_some {s t : State} (h : s.Grows t) {path : Path} {name : String} {x : Settled}
    (hx : s.settled? path name = some x) : t.settled? path name = some x := by
  obtain ⟨rest, hrest⟩ := h.settled
  simp only [State.settled?, ← hrest, List.find?_append]
  simp only [State.settled?] at hx
  simp [hx]
theorem delivery?_eq_some {s t : State} (h : s.Grows t) {path : Path} {index : Nat} {source : ResultId}
    {d : Delivery} (hd : s.delivery? path index source = some d) : t.delivery? path index source = some d := by
  obtain ⟨rest, hrest⟩ := h.deliveries
  simp only [State.delivery?, ← hrest, List.find?_append]
  simp only [State.delivery?] at hd
  simp [hd]

end State.Grows

namespace State
variable {s t : State}

theorem grows_setRun {r : Run} : s.Grows (s.setRun r) := by constructor <;> simp
theorem grows_setInvocation {i : Invocation} : s.Grows (s.setInvocation i) := by constructor <;> simp
theorem grows_setCall {c : Call} : s.Grows (s.setCall c) := by constructor <;> simp
theorem grows_setExecution {e : Execution} : s.Grows (s.setExecution e) := by constructor <;> simp
theorem grows_setTask {e : Execution} {ts : TaskState} : s.Grows (s.setTask e ts) := by constructor <;> simp
theorem grows_setTaskResult {r : TaskResult} : s.Grows (s.setTaskResult r) := by constructor <;> simp
theorem grows_stop : s.Grows s.stop := by constructor <;> simp
theorem grows_fail {f : Failure} {policy : Policy} : s.Grows (s.fail f policy) := by constructor <;> simp

theorem accept_grows {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : s.Grows t := by
  rcases accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> constructor <;> simp

theorem settleOwner_grows {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : s.settleOwner c inv task = .ok t) : s.Grows t := by
  rcases settleOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · exact grows_setInvocation
  · exact grows_setTask

theorem cancelOwner_grows {c : Call} (h : s.cancelOwner c = .ok t) : s.Grows t := by
  rcases cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> split
  · exact grows_setInvocation
  · exact Grows.refl s
  · exact grows_setTask
  · exact Grows.refl s

theorem failCall_grows {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    s.Grows t := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  exact grows_setCall.trans ((settleOwner_grows hso).trans grows_fail)

/-- Settling or cancelling an owner changes only the status of one invocation or task. --/
structure OwnerUpdate (s t : State) : Prop where
  status : t.status = s.status
  started : t.started = s.started
  cancelled : t.cancelled = s.cancelled
  runs : t.runs = s.runs
  calls : t.calls = s.calls
  results : t.results = s.results
  taskResults : t.taskResults = s.taskResults
  deliveries : t.deliveries = s.deliveries
  settled : t.settled = s.settled
  failures : t.failures = s.failures
  invocations : t.invocations.map (·.id) = s.invocations.map (·.id)
  executions : t.executions.map (·.id) = s.executions.map (·.id)

theorem settleOwner_update {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : s.settleOwner c inv task = .ok t) : OwnerUpdate s t := by
  rcases settleOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> constructor <;> simp

theorem cancelOwner_update {c : Call} (h : s.cancelOwner c = .ok t) : OwnerUpdate s t := by
  rcases cancelOwner_eq_ok.mp h with ⟨-, _, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> split <;> constructor <;> simp

/-- Accepting a value appends one result or task result and changes nothing else. --/
theorem accept_frame {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) :
    t.status = s.status ∧ t.started = s.started ∧ t.cancelled = s.cancelled ∧ t.runs = s.runs ∧
      t.invocations = s.invocations ∧ t.calls = s.calls ∧ t.executions = s.executions ∧
      t.deliveries = s.deliveries ∧ t.settled = s.settled ∧ t.failures = s.failures := by
  rcases accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> simp

theorem failCall_started {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    t.started = s.started := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  simp [(settleOwner_update hso).started]

theorem failCall_runs {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    t.runs = s.runs := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  simp [(settleOwner_update hso).runs]

/-- A failure keeps the status or stops. --/
theorem failCall_status {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    t.status = s.status ∨ t.status = .stopping := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  cases c.policy <;> simp [(settleOwner_update hso).status]

/-- A stop by a failure leaves no call running or fetching. --/
theorem fail_quiet_of_running {f : Failure} {policy : Policy} (h : s.status = .running)
    (ht : (s.fail f policy).status = .stopping) :
    ∀ c ∈ (s.fail f policy).calls, c.status ≠ .running ∧ c.status ≠ .fetching := by
  cases policy
  · intro c hc
    exact stop_calls_quiet hc
  · simp [h] at ht

theorem failCall_quiet_of_running {c : Call} {status : CallStatus} {cause : Cause}
    (h : s.failCall c status cause = .ok t) (hs : s.status = .running) (ht : t.status = .stopping) :
    ∀ c ∈ t.calls, c.status ≠ .running ∧ c.status ≠ .fetching := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  exact fail_quiet_of_running (by simp [(settleOwner_update hso).status, hs]) ht

end State

open State in
/-- Accepted results, deliveries, settlements and failures are never withdrawn, and stored records
    keep their identities (§10.2, §11.4). --/
theorem step_grows {p : Program} {s t : State} {op : Op} (hs : step p s op = .ok t) : s.Grows t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    constructor <;> simp
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      constructor <;> simp
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact grows_setCall
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact (accept_grows hacc).trans (grows_setCall.trans (settleOwner_grows hso))
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact (accept_grows hacc).trans (grows_setCall.trans grows_setInvocation)
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (accept_grows hacc).trans grows_setCall
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact grows_setCall.trans (settleOwner_grows hso)
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact failCall_grows h
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact failCall_grows h
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact failCall_grows h
    · exact grows_setCall.trans (cancelOwner_grows h)
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact grows_setCall.trans (cancelOwner_grows h)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    constructor <;> simp
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Grows.trans (by constructor <;> simp) grows_fail
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact grows_setTask
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact grows_setTask.trans grows_fail
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> constructor <;> simp
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> constructor <;> simp
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact grows_setTaskResult.trans grows_fail
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> constructor <;> simp
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> constructor <;> simp
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> constructor <;> simp
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> constructor <;> simp
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> constructor <;> simp

open State in
/-- Runs are never removed or renamed once the workflow started; before the start there are none. --/
theorem step_runs_grow {p : Program} {s t : State} {op : Op} (hs : step p s op = .ok t)
    (h : s.runs = [] ∨ s.started = true) : s.runs.map (·.path) <+: t.runs.map (·.path) := by
  have keep : ∀ {u : State}, u.runs = s.runs → s.runs.map (·.path) <+: u.runs.map (·.path) := fun hu =>
    hu ▸ List.prefix_refl _
  have add : ∀ {u : State} (r : Run), u.runs = s.runs ++ [r] → s.runs.map (·.path) <+: u.runs.map (·.path) :=
    fun _ hu => by simp [hu]
  cases op with
  | start input =>
    obtain ⟨h1, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h with h | h
    · simp [h]
    · simp [h] at h1
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact keep rfl
    · exact keep rfl
    · exact add _ rfl
    · exact keep rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact keep rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact keep (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact keep (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact keep (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact keep (by rw [(settleOwner_update hso).runs, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact keep (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact keep (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact keep (failCall_runs h)
    · exact keep (by rw [(cancelOwner_update h).runs, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact keep (by rw [(cancelOwner_update h).runs, setCall_runs])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact keep rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact keep (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact keep rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact keep (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact keep rfl
    · exact add _ rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact keep (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact keep rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact keep rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · simp
    · exact keep rfl

open State in
/-- Every accepted step leaves the workflow started. --/
theorem step_started {p : Program} {s t : State} {op : Op} (hs : step p s op = .ok t) : t.started = true := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    rfl
  | invoke path name trigger =>
    obtain ⟨h1, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h1
  | fetch id =>
    obtain ⟨h1, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact h1
  | returned id value =>
    obtain ⟨h1, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    rw [(settleOwner_update hso).started, setCall_started, (accept_frame hacc).2.1, h1]
  | judged id arm =>
    obtain ⟨h1, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    rw [setInvocation_started, setCall_started, (accept_frame hacc).2.1, h1]
  | yielded id value =>
    obtain ⟨h1, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    rw [setCall_started, (accept_frame hacc).2.1, h1]
  | ended id =>
    obtain ⟨h1, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    rw [(settleOwner_update hso).started, setCall_started, h1]
  | failed id =>
    obtain ⟨h1, -, _, -, -, h⟩ := Step.failed_inv hs
    rw [failCall_started h, h1]
  | timedOut id element =>
    obtain ⟨h1, -, _, -, -, h⟩ := Step.timedOut_inv hs
    rw [failCall_started h, h1]
  | lost id =>
    obtain ⟨h1, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · rw [failCall_started h, h1]
    · rw [(cancelOwner_update h).started, setCall_started, h1]
  | terminated id =>
    obtain ⟨h1, -, _, -, -, h⟩ := Step.terminated_inv hs
    rw [(cancelOwner_update h).started, setCall_started, h1]
  | deliver path index source value =>
    obtain ⟨h1, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h1
  | transformFailed path index source =>
    obtain ⟨h1, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    simpa using h1
  | taskInput eid name value =>
    obtain ⟨h1, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    simpa using h1
  | taskInputFailed eid name =>
    obtain ⟨h1, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    simpa using h1
  | beginTask eid name =>
    obtain ⟨h1, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> simpa using h1
  | taskOutput eid name index value =>
    obtain ⟨h1, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> simpa using h1
  | taskOutputFailed eid name index =>
    obtain ⟨h1, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    simpa using h1
  | settle path name =>
    obtain ⟨h1, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h1
  | closeExecution eid =>
    obtain ⟨h1, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simpa using h1
  | closeRun path =>
    obtain ⟨h1, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simpa using h1
  | cancel =>
    obtain ⟨h1, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> simpa using h1
  | conclude =>
    obtain ⟨h1, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> simpa using h1

open State in
/-- From a running state, a step that stops leaves no call running or fetching (§11.3). --/
theorem step_stopping_quiet_of_running {p : Program} {s t : State} {op : Op} (hs : step p s op = .ok t)
    (running : s.status = .running) (stopping : t.status = .stopping) :
    ∀ c ∈ t.calls, c.status ≠ .running ∧ c.status ≠ .fetching := by
  have absurd : ∀ {P : Prop}, t.status = .running → P := fun h => by simp [h] at stopping
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact absurd running
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact absurd running
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact absurd running
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact absurd (by rw [(settleOwner_update hso).status, setCall_status, (accept_frame hacc).1, running])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact absurd (by rw [setInvocation_status, setCall_status, (accept_frame hacc).1, running])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact absurd (by rw [setCall_status, (accept_frame hacc).1, running])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact absurd (by rw [(settleOwner_update hso).status, setCall_status, running])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact failCall_quiet_of_running h running stopping
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact failCall_quiet_of_running h running stopping
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact failCall_quiet_of_running h running stopping
    · exact absurd (by rw [(cancelOwner_update h).status, setCall_status, running])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact absurd (by rw [(cancelOwner_update h).status, setCall_status, running])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact absurd running
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact fail_quiet_of_running running stopping
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact absurd running
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact fail_quiet_of_running running stopping
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact absurd running
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact absurd running
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact fail_quiet_of_running running stopping
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact absurd running
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact absurd running
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact absurd running
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨hs', rfl⟩⟩ := Step.cancel_inv hs
    · intro c hc
      exact stop_calls_quiet hc
    · simp [hs'] at running
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨hs', -, rfl⟩⟩ := Step.conclude_inv hs
    · simp only at stopping
      split at stopping
      · simp at stopping
      · split at stopping <;> simp at stopping
    · simp [hs'] at running

/-- A stopping or final state accepts only the end of a call, the caller's cancel, and the
    conclusion; the first case is a call that was still running or fetching (§11.3). --/
theorem step_of_status_ne_running {p : Program} {s t : State} {op : Op} (hs : step p s op = .ok t)
    (h : s.status ≠ .running) :
    s.status = .stopping ∧ s.started = true ∧
    ((∃ c ∈ s.calls, (c.status = .running ∨ c.status = .fetching) ∧ s.failCall c .lost .lost = .ok t) ∨
     (∃ c ∈ s.calls, c.status = .cancelling ∧ (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) ∨
     t = { s with cancelled := true } ∨
     (s.calls.all (·.status.ended) = true ∧ t = { s with status := if s.failures.isEmpty then .cancelled else .failed })) := by
  cases op with
  | start input => exact absurd (Step.start_inv hs).2.1 h
  | invoke path name trigger => exact absurd (Step.invoke_inv hs).2.1 h
  | fetch id => exact absurd (Step.fetch_inv hs).2.1 h
  | returned id value => exact absurd (Step.returned_inv hs).2.1 h
  | judged id arm => exact absurd (Step.judged_inv hs).2.1 h
  | yielded id value => exact absurd (Step.yielded_inv hs).2.1 h
  | ended id => exact absurd (Step.ended_inv hs).2.1 h
  | failed id => exact absurd (Step.failed_inv hs).2.1 h
  | timedOut id element => exact absurd (Step.timedOut_inv hs).2.1 h
  | lost id =>
    obtain ⟨h1, h2, c, hc, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := Step.lost_inv hs
    · exact ⟨h2.resolve_left h, h1, Or.inl ⟨c, (State.call?_eq_some hc).1, h3, h4⟩⟩
    · exact ⟨h2.resolve_left h, h1, Or.inr (Or.inl ⟨c, (State.call?_eq_some hc).1, h3, h4⟩)⟩
  | terminated id =>
    obtain ⟨h1, h2, c, hc, h3, h4⟩ := Step.terminated_inv hs
    exact ⟨h2.resolve_left h, h1, Or.inr (Or.inl ⟨c, (State.call?_eq_some hc).1, h3, h4⟩)⟩
  | deliver path index source value => exact absurd (Step.deliver_inv hs).2.1 h
  | transformFailed path index source => exact absurd (Step.transformFailed_inv hs).2.1 h
  | taskInput eid name value => exact absurd (Step.taskInput_inv hs).2.1 h
  | taskInputFailed eid name => exact absurd (Step.taskInputFailed_inv hs).2.1 h
  | beginTask eid name => exact absurd (Step.beginTask_inv hs).2.1 h
  | taskOutput eid name index value => exact absurd (Step.taskOutput_inv hs).2.1 h
  | taskOutputFailed eid name index => exact absurd (Step.taskOutputFailed_inv hs).2.1 h
  | settle path name => exact absurd (Step.settle_inv hs).2.1 h
  | closeExecution eid => exact absurd (Step.closeExecution_inv hs).2.1 h
  | closeRun path => exact absurd (Step.closeRun_inv hs).2.1 h
  | cancel =>
    obtain ⟨h1, ⟨h2, -⟩ | ⟨h2, rfl⟩⟩ := Step.cancel_inv hs
    · exact absurd h2 h
    · exact ⟨h2, h1, Or.inr (Or.inr (Or.inl rfl))⟩
  | conclude =>
    obtain ⟨h1, ⟨h2, -⟩ | ⟨h2, h3, rfl⟩⟩ := Step.conclude_inv hs
    · exact absurd h2 h
    · exact ⟨h2, h1, Or.inr (Or.inr (Or.inr ⟨h3, rfl⟩))⟩

end Suimon
