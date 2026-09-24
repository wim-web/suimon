import Suimon.Step
import Suimon.Theorems.StepEffects
import Suimon.Theorems.Keys

namespace Suimon

/-- States reachable from the empty state by accepted operations. --/
inductive Reachable (p : Definition) : State → Prop
  | empty : Reachable p {}
  | step {s t : State} (op : Op) : Reachable p s → step p s op = .ok t → Reachable p t

/-- Identities of stored records are unique. --/
structure State.WellKeyed (s : State) : Prop where
  results : (s.results.map (·.id)).Nodup
  invocations : (s.invocations.map (·.id)).Nodup
  calls : (s.calls.map (·.id)).Nodup
  runs : (s.runs.map (·.path)).Nodup
  executions : (s.executions.map (·.id)).Nodup
  deliveries : (s.deliveries.map fun d => (d.run, d.connection, d.source)).Nodup
  settled : (s.settled.map fun x => (x.run, x.placement)).Nodup
  taskResults : (s.taskResults.map fun r => (r.execution, r.task, r.index)).Nodup

namespace State.WellKeyed
variable {s : State}

theorem empty : ({} : State).WellKeyed :=
  ⟨List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil,
    List.nodup_nil, List.nodup_nil⟩

/-- Only the stored records matter. --/
theorem of_records {t : State} (h : s.WellKeyed) (hr : t.runs = s.runs) (hi : t.invocations = s.invocations)
    (hc : t.calls = s.calls) (he : t.executions = s.executions) (hres : t.results = s.results)
    (htr : t.taskResults = s.taskResults) (hd : t.deliveries = s.deliveries) (hs : t.settled = s.settled) :
    t.WellKeyed :=
  ⟨hres ▸ h.results, hi ▸ h.invocations, hc ▸ h.calls, hr ▸ h.runs, he ▸ h.executions, hd ▸ h.deliveries,
    hs ▸ h.settled, htr ▸ h.taskResults⟩

theorem setRun (h : s.WellKeyed) (r : Run) : (s.setRun r).WellKeyed :=
  { h with runs := by simpa using h.runs }
theorem setInvocation (h : s.WellKeyed) (i : Invocation) : (s.setInvocation i).WellKeyed :=
  { h with invocations := by simpa using h.invocations }
theorem setCall (h : s.WellKeyed) (c : Call) : (s.setCall c).WellKeyed :=
  { h with calls := by simpa using h.calls }
theorem setExecution (h : s.WellKeyed) (e : Execution) : (s.setExecution e).WellKeyed :=
  { h with executions := by simpa using h.executions }
theorem setTask (h : s.WellKeyed) (e : Execution) (ts : TaskState) : (s.setTask e ts).WellKeyed :=
  h.setExecution _
theorem setTaskResult (h : s.WellKeyed) (r : TaskResult) : (s.setTaskResult r).WellKeyed :=
  { h with taskResults := by simpa using h.taskResults }
theorem stop (h : s.WellKeyed) : s.stop.WellKeyed :=
  { h with calls := by simpa using h.calls, executions := by simpa using h.executions }
theorem endUnfinished (h : s.WellKeyed) : s.endUnfinished.WellKeyed :=
  { h with invocations := by simpa using h.invocations, executions := by simpa using h.executions }
theorem fail (h : s.WellKeyed) (f : Failure) (policy : Policy) : (s.fail f policy).WellKeyed := by
  have h' : ({ s with failures := s.failures ++ [f] } : State).WellKeyed := h.of_records rfl rfl rfl rfl rfl rfl rfl rfl
  cases policy
  · exact h'.stop
  · exact h'

theorem appendResult (h : s.WellKeyed) {r : Result} (hr : s.result? r.id = none) :
    ({ s with results := s.results ++ [r] } : State).WellKeyed :=
  { h with results := nodup_map_append_singleton h.results (State.result?_eq_none_iff.mp hr) }
theorem appendInvocation (h : s.WellKeyed) {i : Invocation} (hi : s.invocation? i.id = none) :
    ({ s with invocations := s.invocations ++ [i] } : State).WellKeyed :=
  { h with invocations := nodup_map_append_singleton h.invocations (State.invocation?_eq_none_iff.mp hi) }
theorem appendCall (h : s.WellKeyed) {c : Call} (hc : s.call? c.id = none) :
    ({ s with calls := s.calls ++ [c] } : State).WellKeyed :=
  { h with calls := nodup_map_append_singleton h.calls (State.call?_eq_none_iff.mp hc) }
theorem appendRun (h : s.WellKeyed) {r : Run} (hr : s.run? r.path = none) :
    ({ s with runs := s.runs ++ [r] } : State).WellKeyed :=
  { h with runs := nodup_map_append_singleton h.runs (State.run?_eq_none_iff.mp hr) }
theorem appendExecution (h : s.WellKeyed) {e : Execution} (he : s.execution? e.id = none) :
    ({ s with executions := s.executions ++ [e] } : State).WellKeyed :=
  { h with executions := nodup_map_append_singleton h.executions (State.execution?_eq_none_iff.mp he) }
theorem appendDelivery (h : s.WellKeyed) {d : Delivery} (hd : s.delivery? d.run d.connection d.source = none) :
    ({ s with deliveries := s.deliveries ++ [d] } : State).WellKeyed :=
  { h with deliveries := nodup_map_append_singleton h.deliveries (State.delivery?_eq_none_iff.mp hd) }
theorem appendSettled (h : s.WellKeyed) {x : Settled} (hx : s.settled? x.run x.placement = none) :
    ({ s with settled := s.settled ++ [x] } : State).WellKeyed :=
  { h with settled := nodup_map_append_singleton h.settled (State.settled?_eq_none_iff.mp hx) }
theorem appendTaskResult (h : s.WellKeyed) {r : TaskResult}
    (hr : (s.taskResults.any fun x => x.execution == r.execution && x.task == r.task && x.index == r.index) = false) :
    ({ s with taskResults := s.taskResults ++ [r] } : State).WellKeyed :=
  { h with taskResults := nodup_map_append_singleton h.taskResults (State.any_taskResult_key_eq_false_iff.mp hr) }

theorem accept (h : s.WellKeyed) {t : State} {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (ha : s.accept c index value arm = .ok t) : t.WellKeyed := by
  rcases State.accept_eq_ok.mp ha with ⟨-, _, -, hr, rfl⟩ | ⟨_, -, hr, rfl⟩
  · exact h.appendResult hr
  · exact h.appendTaskResult hr

theorem settleOwner (h : s.WellKeyed) {t : State} {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (ho : s.settleOwner c inv task = .ok t) : t.WellKeyed := by
  rcases State.settleOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · exact h.setInvocation _
  · exact h.setTask _ _

theorem cancelOwner (h : s.WellKeyed) {t : State} {c : Call} (ho : s.cancelOwner c = .ok t) : t.WellKeyed := by
  rcases State.cancelOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> split
  · exact h.setInvocation _
  · exact h
  · exact h.setTask _ _
  · exact h

theorem failCall (h : s.WellKeyed) {t : State} {c : Call} {status : CallStatus} {cause : Cause}
    (hf : s.failCall c status cause = .ok t) : t.WellKeyed := by
  obtain ⟨_, _, -, ho, rfl⟩ := State.failCall_eq_ok.mp hf
  exact ((h.setCall _).settleOwner ho).fail _ _

/-! With unique identities, the lookups find exactly the stored records. -/

theorem run?_of_mem (h : s.WellKeyed) {r : Run} (hr : r ∈ s.runs) : s.run? r.path = some r :=
  find?_eq_some_of_nodup h.runs hr fun _ => beq_iff_eq
theorem invocation?_of_mem (h : s.WellKeyed) {i : Invocation} (hi : i ∈ s.invocations) :
    s.invocation? i.id = some i :=
  find?_eq_some_of_nodup h.invocations hi fun _ => beq_iff_eq
theorem call?_of_mem (h : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) : s.call? c.id = some c :=
  find?_eq_some_of_nodup h.calls hc fun _ => beq_iff_eq
theorem execution?_of_mem (h : s.WellKeyed) {e : Execution} (he : e ∈ s.executions) : s.execution? e.id = some e :=
  find?_eq_some_of_nodup h.executions he fun _ => beq_iff_eq
theorem result?_of_mem (h : s.WellKeyed) {r : Result} (hr : r ∈ s.results) : s.result? r.id = some r :=
  find?_eq_some_of_nodup h.results hr fun _ => beq_iff_eq
theorem settled?_of_mem (h : s.WellKeyed) {x : Settled} (hx : x ∈ s.settled) :
    s.settled? x.run x.placement = some x :=
  find?_eq_some_of_nodup h.settled hx fun _ => by simp [Prod.ext_iff]
theorem delivery?_of_mem (h : s.WellKeyed) {d : Delivery} (hd : d ∈ s.deliveries) :
    s.delivery? d.run d.connection d.source = some d :=
  find?_eq_some_of_nodup h.deliveries hd fun _ => by simp [Prod.ext_iff, and_assoc]

theorem run_eq_of_path (h : s.WellKeyed) {r r' : Run} (hr : r ∈ s.runs) (hr' : r' ∈ s.runs)
    (hpath : r.path = r'.path) : r = r' := by
  have := h.run?_of_mem hr'
  rw [← hpath, h.run?_of_mem hr] at this
  exact Option.some.inj this
theorem invocation_eq_of_id (h : s.WellKeyed) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hi' : i' ∈ s.invocations) (hid : i.id = i'.id) : i = i' := by
  have := h.invocation?_of_mem hi'
  rw [← hid, h.invocation?_of_mem hi] at this
  exact Option.some.inj this
theorem call_eq_of_id (h : s.WellKeyed) {c c' : Call} (hc : c ∈ s.calls) (hc' : c' ∈ s.calls)
    (hid : c.id = c'.id) : c = c' := by
  have := h.call?_of_mem hc'
  rw [← hid, h.call?_of_mem hc] at this
  exact Option.some.inj this
theorem execution_eq_of_id (h : s.WellKeyed) {e e' : Execution} (he : e ∈ s.executions)
    (he' : e' ∈ s.executions) (hid : e.id = e'.id) : e = e' := by
  have := h.execution?_of_mem he'
  rw [← hid, h.execution?_of_mem he] at this
  exact Option.some.inj this
theorem result_eq_of_id (h : s.WellKeyed) {r r' : Result} (hr : r ∈ s.results) (hr' : r' ∈ s.results)
    (hid : r.id = r'.id) : r = r' := by
  have := h.result?_of_mem hr'
  rw [← hid, h.result?_of_mem hr] at this
  exact Option.some.inj this

end State.WellKeyed

open State in
theorem step_wellKeyed {p : Definition} {s t : State} {op : Op} (h : s.WellKeyed) (hs : step p s op = .ok t) :
    t.WellKeyed := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact { h with runs := by simp }
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, pl, input, id, -, -, -, -, -, -, -, hid, hcases⟩ := Step.invoke_inv hs
    have h' := h.appendInvocation (i := { id, run := path, placement := name, trigger, input }) hid
    rcases hcases with ⟨_, _, -, -, hc, rfl⟩ | ⟨_, _, -, hc, rfl⟩ | ⟨_, _, -, hr, rfl⟩ | ⟨_, -, he, rfl⟩
    · exact h'.appendCall hc
    · exact h'.appendCall hc
    · exact h'.appendRun hr
    · exact h'.appendExecution he
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.setCall _
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact ((h.accept hacc).setCall _).settleOwner hso
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact ((h.accept hacc).setCall _).setInvocation _
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (h.accept hacc).setCall _
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact (h.setCall _).settleOwner hso
  | failed id =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.failed_inv hs
    exact h.failCall hf
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.timedOut_inv hs
    exact h.failCall hf
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.failCall hf
    · exact (h.setCall _).cancelOwner ho
  | terminated id =>
    obtain ⟨-, -, _, -, -, ho⟩ := Step.terminated_inv hs
    exact (h.setCall _).cancelOwner ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, hdt, -, rfl⟩ := Step.deliver_inv hs
    exact h.appendDelivery (Step.deliveryTarget_eq_ok.mp hdt).2.2.2
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, hdt, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact (h.appendDelivery (Step.deliveryTarget_eq_ok.mp hdt).2.2.2).fail _ _
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.setTask _ _
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (h.setTask _ _).fail _ _
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    rcases hcases with ⟨_, _, -, -, hc, rfl⟩ | ⟨_, _, -, hr, rfl⟩
    · exact (h.setTask _ _).appendCall hc
    · exact (h.setTask _ _).appendRun hr
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, hres, rfl⟩ | ⟨-, rfl⟩
    · exact (h.setTaskResult _).appendResult hres
    · exact h.setTaskResult _
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (h.setTaskResult _).fail _ _
  | settle path name =>
    obtain ⟨-, -, _, _, pl, _, _, x, _, -, -, -, hpl, hfresh, -, -, hout, hcases⟩ := Step.settle_inv hs
    obtain ⟨-, hrun, hplace, -⟩ := State.settleOutcome_some hout
    have hx : s.settled? x.run x.placement = none := by
      rw [hrun, hplace, (Workflow.placement?_eq_some hpl).2]
      exact hfresh
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, hres, rfl⟩
    · exact h.appendSettled hx
    · exact (h.appendSettled hx).appendResult hres
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, hres, rfl⟩ | ⟨-, -, rfl⟩
    · exact (h.setExecution _).setInvocation _
    · exact ((h.setExecution _).setInvocation _).appendResult hres
    · exact (h.setExecution _).setInvocation _
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨-, _, -, hcases⟩ | ⟨_, _, _, -, -, -, hcases⟩
    · rcases hcases with ⟨-, _, -, hres, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ((h.setRun _).setInvocation _).appendResult hres
      all_goals exact (h.setRun _).setInvocation _
    · rcases hcases with ⟨-, _, -, hres, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ((h.setRun _).setTask _ _).appendTaskResult hres
      all_goals exact (h.setRun _).setTask _ _
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.stop.of_records rfl rfl rfl rfl rfl rfl rfl rfl
    · exact h.of_records rfl rfl rfl rfl rfl rfl rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact (h.setRun _).of_records rfl rfl rfl rfl rfl rfl rfl rfl
    · exact h.endUnfinished.of_records rfl rfl rfl rfl rfl rfl rfl rfl

theorem Reachable.wellKeyed {p : Definition} {s : State} (h : Reachable p s) : s.WellKeyed := by
  induction h with
  | empty => exact State.WellKeyed.empty
  | step op _ hs ih => exact step_wellKeyed ih hs

/-- Before the start, a reachable state is the empty state. --/
theorem Reachable.eq_empty_or_started {p : Definition} {s : State} (h : Reachable p s) : s = {} ∨ s.started = true := by
  cases h with
  | empty => exact Or.inl rfl
  | step op _ hs => exact Or.inr (step_started hs)

/-- Accepted results, deliveries, settlements and failure records are never withdrawn (§10.2, §11.4). --/
theorem step_monotone {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    (∀ r ∈ s.results, r ∈ t.results) ∧ (∀ d ∈ s.deliveries, d ∈ t.deliveries) ∧
    (∀ x ∈ s.settled, x ∈ t.settled) ∧ s.failures <+: t.failures := by
  have g := step_grows hs
  exact ⟨fun _ => g.mem_results, fun _ => g.mem_deliveries, fun _ => g.mem_settled, g.failures⟩

open State in
/-- A result a step adds names what produced it: the call that reported it, the execution or the
    sub-workflow invocation that closed, or the placement that aggregated; other steps add none. --/
theorem step_producer {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) {r : Result}
    (hr : r ∈ t.results) (hnew : r ∉ s.results) :
    match (generalizing := false) op with
    | .returned id _ | .judged id _ | .yielded id _ => r.producer = id
    | .taskOutput eid .. | .closeExecution eid => r.producer = eid
    | .closeRun path => (s.run? path).bind (·.owner) = some r.producer
    | .settle path name => r.producer = Key.aggregate path name
    | _ => False := by
  have keep : t.results = s.results → False := fun h => hnew (h ▸ hr)
  have added : ∀ {x : Result}, t.results = s.results ++ [x] → r = x := fun h => by
    rw [h, List.mem_append, List.mem_singleton] at hr
    exact hr.resolve_left hnew
  have accepted : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
      s.accept c index value arm = .ok s' → t.results = s'.results → r.producer = c.id := by
    intro c index value arm s' ha ht
    rcases accept_eq_ok.mp ha with ⟨-, i, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · rw [added ht]
    · exact (keep ht).elim
  have failed : ∀ {c : Call} {status : CallStatus} {cause : Cause}, s.failCall c status cause = .ok t → False := by
    intro c status cause h
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
    exact keep (by simp [(settleOwner_update hso).results])
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact keep rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact keep rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    show r.producer = id
    rw [accepted hacc (by rw [(settleOwner_update hso).results, setCall_results]), (call?_eq_some hc).2]
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    show r.producer = id
    rw [accepted hacc (by rw [setInvocation_results, setCall_results]), (call?_eq_some hc).2]
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    show r.producer = id
    rw [accepted hacc (by rw [setCall_results]), (call?_eq_some hc).2]
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact keep (by rw [(settleOwner_update hso).results, setCall_results])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact failed h
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact failed h
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact failed h
    · exact keep (by rw [(cancelOwner_update h).results, setCall_results])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact keep (by rw [(cancelOwner_update h).results, setCall_results])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact keep rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact keep (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact keep (by simp)
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact keep (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact keep (by simp)
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    show r.producer = eid
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · rw [added rfl]
    · exact (keep (by simp)).elim
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact keep (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, pl, _, _, _, _, -, -, -, hpl, -, -, -, hout, h⟩ := Step.settle_inv hs
    show r.producer = Key.aggregate path name
    rcases h with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact (keep rfl).elim
    · rw [added rfl, ((settleOutcome_some hout).2.2.2 res rfl).2.2.2.2.1, (Workflow.placement?_eq_some hpl).2]
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    show r.producer = eid
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact (keep (by simp)).elim
    · rw [added rfl]
    · exact (keep (by simp)).elim
  | closeRun path =>
    obtain ⟨-, -, run, _, _, _, owner, hrun, -, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    show (s.run? path).bind (·.owner) = some r.producer
    rw [hrun, Option.bind_some, howner]
    rcases h with ⟨-, i, hi, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [added rfl, (invocation?_eq_some hi).2]
      all_goals exact (keep (by simp)).elim
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact (keep (by simp)).elim
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact keep (by simp)
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact keep (by simp)

/-- A final state accepts no operation (§13.3). --/
theorem step_source_status {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    s.status = .running ∨ s.status = .stopping := by
  by_cases h : s.status = .running
  · exact Or.inl h
  · exact Or.inr (step_of_status_ne_running hs h).1

/-- The state an operation is accepted in has not concluded. --/
theorem step_source_nonterminal {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    s.status.terminal = false := by
  rcases step_source_status hs with h | h <;> simp [h, Status.terminal]

/-- While stopping, no call is running or fetching. --/
def State.Quiet (s : State) : Prop :=
  s.status = .stopping → ∀ c ∈ s.calls, c.status ≠ .running ∧ c.status ≠ .fetching

/-- Every step keeps a state quiet: a stop cancels all running and fetching calls in the same
    transition, and afterwards no call is started or fetched (§11.3). --/
theorem step_quiet {p : Definition} {s t : State} {op : Op} (quiet : s.Quiet) (hs : step p s op = .ok t) : t.Quiet := by
  intro stopping
  by_cases running : s.status = .running
  · exact step_stopping_quiet_of_running hs running stopping
  obtain ⟨hstop, -, hcases⟩ := step_of_status_ne_running hs running
  have quiet := quiet hstop
  rcases hcases with ⟨c, hc, hrun, -⟩ | ⟨c, -, -, ho⟩ | rfl | ⟨-, rfl⟩
  · rcases hrun with hrun | hrun
    · exact absurd hrun (quiet c hc).1
    · exact absurd hrun (quiet c hc).2
  · intro c' hc'
    rw [(State.cancelOwner_update ho).calls] at hc'
    rcases State.mem_setCall_calls hc' with rfl | hc'
    · simp
    · exact quiet c' hc'
  · exact quiet
  · exact quiet

theorem Reachable.quiet {p : Definition} {s : State} (h : Reachable p s) : s.Quiet := by
  induction h with
  | empty => intro h; cases h
  | step op _ hs ih => exact step_quiet ih hs

/-- After the stop, nothing new is invoked, called, fetched, accepted, delivered or settled, and no
    failure is added; only cancelled calls end and the final status is decided (§11.3). --/
theorem step_after_stop {p : Definition} {s t : State} {op : Op} (quiet : s.Quiet) (hs : step p s op = .ok t)
    (stopped : s.status ≠ .running) :
    t.results = s.results ∧ t.deliveries = s.deliveries ∧ t.taskResults = s.taskResults ∧
    t.settled = s.settled ∧ t.failures = s.failures ∧
    t.invocations.map (·.id) = s.invocations.map (·.id) ∧ t.calls.map (·.id) = s.calls.map (·.id) ∧
    t.runs.map (·.path) = s.runs.map (·.path) ∧ t.executions.map (·.id) = s.executions.map (·.id) ∧
    (∀ c ∈ t.calls, c.status ≠ .running ∧ c.status ≠ .fetching) := by
  obtain ⟨stopping, -, hcases⟩ := step_of_status_ne_running hs stopped
  have quiet := quiet stopping
  rcases hcases with ⟨c, hc, hrun, -⟩ | ⟨c, -, -, ho⟩ | rfl | ⟨-, rfl⟩
  · -- A running or fetching call contradicts the quiet stop.
    rcases hrun with hrun | hrun
    · exact absurd hrun (quiet c hc).1
    · exact absurd hrun (quiet c hc).2
  · have u := State.cancelOwner_update ho
    refine ⟨by simp [u.results], by simp [u.deliveries], by simp [u.taskResults], by simp [u.settled],
      by simp [u.failures], by simp [u.invocations], by simp [u.calls], by simp [u.runs], by simp [u.executions], ?_⟩
    intro c' hc'
    rw [u.calls] at hc'
    rcases State.mem_setCall_calls hc' with rfl | hc'
    · simp
    · exact quiet c' hc'
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, quiet⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, by simp, rfl, rfl, by simp, quiet⟩

/-- The status moves only forward: a stop is never undone, and a final status is kept. --/
theorem step_status {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    (s.status = .stopping → t.status ≠ .running) ∧ (s.started → t.started) := by
  refine ⟨fun stopping => ?_, fun _ => step_started hs⟩
  obtain ⟨-, -, hcases⟩ := step_of_status_ne_running hs (by simp [stopping])
  rcases hcases with ⟨c, -, -, hf⟩ | ⟨c, -, -, ho⟩ | rfl | ⟨-, rfl⟩
  · rcases State.failCall_status hf with h | h <;> simp [h, stopping]
  · simp [(State.cancelOwner_update ho).status, stopping]
  · simp [stopping]
  · simp only
    split <;> simp

end Suimon
