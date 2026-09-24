import Suimon.Theorems.Basic
import Suimon.Theorems.Identity

/-! Call safety (§4.1.1, §10.2, §11.3, §11.5, §11.6): a call that stopped never runs again, reports
    and fetches follow the call's status, and a call's own results are accepted only while it runs.
    Helpers live in `Suimon.Calls`. -/

namespace Suimon

namespace Calls
open State

/-! ### Stopped calls -/

/-- The call stored under `id` exists and is neither running nor fetching. --/
def StoppedAt (s : State) (id : String) : Prop :=
  ∃ c, s.call? id = some c ∧ c.status ≠ .running ∧ c.status ≠ .fetching

theorem call?_of_calls {s t : State} {id : String} (h : t.calls = s.calls) : t.call? id = s.call? id := by
  simp only [State.call?, h]

theorem call?_of_append {s t : State} {id : String} {c x : Call} (hc : s.call? id = some c)
    (h : t.calls = s.calls ++ [x]) : t.call? id = some c := by
  simp only [State.call?, h, List.find?_append] at hc ⊢
  simp [hc]

theorem StoppedAt.of_calls {s t : State} {id : String} (h : StoppedAt s id) (hc : t.calls = s.calls) :
    StoppedAt t id := by
  rw [StoppedAt, call?_of_calls hc]
  exact h

theorem StoppedAt.of_append {s t : State} {id : String} {x : Call} (h : StoppedAt s id)
    (hc : t.calls = s.calls ++ [x]) : StoppedAt t id := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c, call?_of_append h1 hc, h2⟩

/-- Storing a call keeps `id` stopped unless it stores a running or fetching call under `id`. --/
theorem StoppedAt.setCall {s : State} {id : String} {d : Call} (h : StoppedAt s id)
    (hd : d.id = id → d.status ≠ .running ∧ d.status ≠ .fetching) : StoppedAt (s.setCall d) id := by
  obtain ⟨c, hc, hstop⟩ := h
  rw [StoppedAt, call?_setCall, hc]
  split
  · rename_i hid
    exact ⟨d, rfl, hd hid⟩
  · exact ⟨c, rfl, hstop⟩

theorem StoppedAt.stop {s : State} {id : String} (h : StoppedAt s id) : StoppedAt s.stop id := by
  obtain ⟨c, hc, -⟩ := h
  exact ⟨stopCall c, by rw [call?_stop, hc]; rfl, stopCall_quiet c⟩

theorem StoppedAt.fail {s : State} {id : String} {f : Failure} {policy : Policy} (h : StoppedAt s id) :
    StoppedAt (s.fail f policy) id := by
  have h' : StoppedAt { s with failures := s.failures ++ [f] } id := h.of_calls rfl
  cases policy
  · exact h'.stop
  · exact h'

theorem StoppedAt.failCall {s t : State} {id : String} {c : Call} {status : CallStatus} {cause : Cause}
    (h : StoppedAt s id) (hst : status ≠ .running ∧ status ≠ .fetching)
    (hf : s.failCall c status cause = .ok t) : StoppedAt t id := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  exact ((h.setCall fun _ => hst).of_calls (settleOwner_update hso).calls).fail

theorem StoppedAt.cancelled {s t : State} {id : String} {c : Call} (h : StoppedAt s id)
    (ho : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) : StoppedAt t id :=
  (h.setCall fun _ => by simp).of_calls (cancelOwner_update ho).calls

/-! ### Identities of calls

A call's identity is `Key.invocation` of a function or branch invocation, or `Key.task`. An
execution's identity is the identity of its (concurrency) invocation, and a run's owner is an
invocation or an execution. Since invoke creates exactly one record per fresh invocation identity,
a call's identity is never an execution, a run owner, or an aggregate key. -/

/-- An identity made by `Key.invocation`. --/
def InvocationKey (id : String) : Prop := ∃ path name trigger, id = Key.invocation path name trigger

/-- An identity made by `Key.task`. --/
def TaskKey (id : String) : Prop := ∃ execution task, id = Key.task execution task

theorem not_taskKey_of_invocationKey {id : String} (hi : InvocationKey id) (ht : TaskKey id) : False := by
  obtain ⟨path, name, trigger, rfl⟩ := hi
  obtain ⟨a, b, h⟩ := ht
  exact Key.invocation_ne_task h

theorem not_invocationKey_aggregate {path : Path} {name : String} (h : InvocationKey (Key.aggregate path name)) :
    False := by
  obtain ⟨path', name', trigger, h⟩ := h
  exact Key.invocation_ne_aggregate h.symm

theorem not_taskKey_aggregate {path : Path} {name : String} (h : TaskKey (Key.aggregate path name)) : False := by
  obtain ⟨a, b, h⟩ := h
  exact Key.task_ne_aggregate h.symm

/-- How the identities of calls relate to the other records. --/
structure Keys (s : State) : Prop where
  invocations : ∀ id ∈ s.invocations.map (·.id), InvocationKey id
  executions : ∀ id ∈ s.executions.map (·.id), id ∈ s.invocations.map (·.id)
  calls : ∀ c ∈ s.calls, c.task = none → c.id ∈ s.invocations.map (·.id)
  tasks : ∀ c ∈ s.calls, c.task ≠ none → TaskKey c.id
  disjoint : ∀ c ∈ s.calls, c.id ∉ s.executions.map (·.id)
  owners : ∀ r ∈ s.runs, ∀ o, r.owner = some o → o ∈ s.invocations.map (·.id) ∧ ∀ c ∈ s.calls, c.id ≠ o

theorem Keys.empty : Keys {} where
  invocations := fun _ h => by simp at h
  executions := fun _ h => by simp at h
  calls := fun _ h => by simp at h
  tasks := fun _ h => by simp at h
  disjoint := fun _ h => by simp at h
  owners := fun _ h => by simp at h

/-- A fresh invocation identity is not yet a call, an execution or a run owner. --/
theorem Keys.fresh {s : State} {id : String} (h : Keys s) (hid : id ∉ s.invocations.map (·.id))
    (hkey : InvocationKey id) :
    (∀ c ∈ s.calls, c.id ≠ id) ∧ id ∉ s.executions.map (·.id) ∧
      ∀ r ∈ s.runs, ∀ o, r.owner = some o → o ≠ id := by
  refine ⟨fun c hc heq => ?_, fun hmem => hid (h.executions id hmem),
    fun r hr o ho heq => hid (heq ▸ (h.owners r hr o ho).1)⟩
  by_cases htask : c.task = none
  · exact hid (heq ▸ h.calls c hc htask)
  · exact not_taskKey_of_invocationKey hkey (heq ▸ h.tasks c hc htask)

theorem Keys.ne_aggregate {s : State} (h : Keys s) {c : Call} (hc : c ∈ s.calls) (path : Path) (name : String) :
    c.id ≠ Key.aggregate path name := by
  intro heq
  by_cases htask : c.task = none
  · exact not_invocationKey_aggregate (heq ▸ h.invocations _ (h.calls c hc htask))
  · exact not_taskKey_aggregate (heq ▸ h.tasks c hc htask)

theorem Keys.addInvocation {s : State} {i : Invocation} (h : Keys s) (hi : InvocationKey i.id) :
    Keys { s with invocations := s.invocations ++ [i] } where
  invocations := by
    intro id hid
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hid
    rcases hid with hid | rfl
    · exact h.invocations id hid
    · exact hi
  executions := fun id hid => by
    rw [List.map_append]
    exact List.mem_append_left _ (h.executions id hid)
  calls := fun c hc hnone => by
    rw [List.map_append]
    exact List.mem_append_left _ (h.calls c hc hnone)
  tasks := h.tasks
  disjoint := h.disjoint
  owners := fun r hr o ho => by
    refine ⟨?_, (h.owners r hr o ho).2⟩
    rw [List.map_append]
    exact List.mem_append_left _ (h.owners r hr o ho).1

theorem Keys.addCall {s : State} {c : Call} (h : Keys s)
    (hinv : c.task = none → c.id ∈ s.invocations.map (·.id)) (htask : c.task ≠ none → TaskKey c.id)
    (hexec : c.id ∉ s.executions.map (·.id)) (hown : ∀ r ∈ s.runs, ∀ o, r.owner = some o → c.id ≠ o) :
    Keys { s with calls := s.calls ++ [c] } where
  invocations := h.invocations
  executions := h.executions
  calls := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.calls x hx
    · rw [List.mem_singleton.mp hx]; exact hinv
  tasks := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.tasks x hx
    · rw [List.mem_singleton.mp hx]; exact htask
  disjoint := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.disjoint x hx
    · rw [List.mem_singleton.mp hx]; exact hexec
  owners := by
    intro r hr o ho
    refine ⟨(h.owners r hr o ho).1, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact (h.owners r hr o ho).2 x hx
    · rw [List.mem_singleton.mp hx]; exact hown r hr o ho

theorem Keys.addExecution {s : State} {e : Execution} (h : Keys s) (hinv : e.id ∈ s.invocations.map (·.id))
    (hcalls : ∀ c ∈ s.calls, c.id ≠ e.id) : Keys { s with executions := s.executions ++ [e] } where
  invocations := h.invocations
  executions := by
    intro id hid
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hid
    rcases hid with hid | rfl
    · exact h.executions id hid
    · exact hinv
  calls := h.calls
  tasks := h.tasks
  disjoint := by
    intro c hc hmem
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · exact h.disjoint c hc hmem
    · exact hcalls c hc hmem
  owners := h.owners

theorem Keys.addRun {s : State} {r : Run} (h : Keys s)
    (hown : ∀ o, r.owner = some o → o ∈ s.invocations.map (·.id) ∧ ∀ c ∈ s.calls, c.id ≠ o) :
    Keys { s with runs := s.runs ++ [r] } where
  invocations := h.invocations
  executions := h.executions
  calls := h.calls
  tasks := h.tasks
  disjoint := h.disjoint
  owners := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.owners x hx
    · rw [List.mem_singleton.mp hx]; exact hown

/-- A part of a step that keeps the identities of invocations and executions, the identity and task
    of each call, and the owner of each run. --/
structure Frame (s t : State) : Prop where
  invocations : t.invocations.map (·.id) = s.invocations.map (·.id)
  executions : t.executions.map (·.id) = s.executions.map (·.id)
  calls : ∀ c ∈ t.calls, ∃ c' ∈ s.calls, c'.id = c.id ∧ c'.task = c.task
  runs : ∀ r ∈ t.runs, ∃ r' ∈ s.runs, r'.owner = r.owner

namespace Frame

theorem trans {s t u : State} (h₁ : Frame s t) (h₂ : Frame t u) : Frame s u where
  invocations := h₂.invocations.trans h₁.invocations
  executions := h₂.executions.trans h₁.executions
  calls := fun c hc => by
    obtain ⟨c', hc', h1, h2⟩ := h₂.calls c hc
    obtain ⟨c'', hc'', h3, h4⟩ := h₁.calls c' hc'
    exact ⟨c'', hc'', h3.trans h1, h4.trans h2⟩
  runs := fun r hr => by
    obtain ⟨r', hr', h1⟩ := h₂.runs r hr
    obtain ⟨r'', hr'', h2⟩ := h₁.runs r' hr'
    exact ⟨r'', hr'', h2.trans h1⟩

theorem of_eq {s t : State} (hi : t.invocations = s.invocations) (he : t.executions = s.executions)
    (hc : t.calls = s.calls) (hr : t.runs = s.runs) : Frame s t where
  invocations := by rw [hi]
  executions := by rw [he]
  calls := fun c h => ⟨c, hc ▸ h, rfl, rfl⟩
  runs := fun r h => ⟨r, hr ▸ h, rfl⟩

theorem setCall {s : State} {c d : Call} (hc : c ∈ s.calls) (hid : c.id = d.id) (htask : c.task = d.task) :
    Frame s (s.setCall d) where
  invocations := rfl
  executions := rfl
  calls := fun x hx => by
    rcases mem_setCall_calls hx with rfl | hx
    · exact ⟨c, hc, hid, htask⟩
    · exact ⟨x, hx, rfl, rfl⟩
  runs := fun r hr => ⟨r, hr, rfl⟩

theorem setInvocation {s : State} {i : Invocation} : Frame s (s.setInvocation i) where
  invocations := setInvocation_invocations_map_id
  executions := rfl
  calls := fun c h => ⟨c, h, rfl, rfl⟩
  runs := fun r h => ⟨r, h, rfl⟩

theorem setExecution {s : State} {e : Execution} : Frame s (s.setExecution e) where
  invocations := rfl
  executions := setExecution_executions_map_id
  calls := fun c h => ⟨c, h, rfl, rfl⟩
  runs := fun r h => ⟨r, h, rfl⟩

theorem setTask {s : State} {e : Execution} {ts : TaskState} : Frame s (s.setTask e ts) := setExecution

theorem setRun {s : State} {r r' : Run} (hr : r ∈ s.runs) (howner : r.owner = r'.owner) :
    Frame s (s.setRun r') where
  invocations := rfl
  executions := rfl
  calls := fun c h => ⟨c, h, rfl, rfl⟩
  runs := fun x hx => by
    rcases mem_setRun_runs hx with rfl | hx
    · exact ⟨r, hr, howner⟩
    · exact ⟨x, hx, rfl⟩

theorem setTaskResult {s : State} {r : TaskResult} : Frame s (s.setTaskResult r) := of_eq rfl rfl rfl rfl

theorem stop {s : State} : Frame s s.stop where
  invocations := rfl
  executions := stop_executions_map_id
  calls := fun c hc => by
    obtain ⟨c', hc', rfl⟩ := mem_stop_calls.mp hc
    exact ⟨c', hc', stopCall_id.symm, stopCall_task.symm⟩
  runs := fun r h => ⟨r, h, rfl⟩

theorem endUnfinished {s : State} : Frame s s.endUnfinished where
  invocations := endUnfinished_invocations_map_id
  executions := endUnfinished_executions_map_id
  calls := fun c h => ⟨c, h, rfl, rfl⟩
  runs := fun r h => ⟨r, h, rfl⟩

theorem fail {s : State} {f : Failure} {policy : Policy} : Frame s (s.fail f policy) := by
  cases policy
  · rw [State.fail_stop]
    exact (of_eq (s := s) (t := { s with failures := s.failures ++ [f] }) rfl rfl rfl rfl).trans stop
  · exact of_eq rfl rfl rfl rfl

/-- A failure recorded after a frame step is still a frame step. --/
theorem andFail {s u : State} {f : Failure} {policy : Policy} (h : Frame s u) : Frame s (u.fail f policy) :=
  h.trans fail

theorem accept {s t : State} {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : Frame s t := by
  obtain ⟨-, -, -, hr, hi, hc, he, -⟩ := accept_frame h
  exact of_eq hi he hc hr

theorem ownerUpdate {s t : State} (h : OwnerUpdate s t) : Frame s t where
  invocations := h.invocations
  executions := h.executions
  calls := fun c hc => ⟨c, h.calls ▸ hc, rfl, rfl⟩
  runs := fun r hr => ⟨r, h.runs ▸ hr, rfl⟩

theorem failCall {s t : State} {c : Call} {status : CallStatus} {cause : Cause} (hc : c ∈ s.calls)
    (h : s.failCall c status cause = .ok t) : Frame s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp h
  exact ((setCall (d := { c with status }) hc rfl rfl).trans (ownerUpdate (settleOwner_update hso))).trans fail

end Frame

theorem Keys.frame {s t : State} (h : Keys s) (hf : Frame s t) : Keys t where
  invocations := by rw [hf.invocations]; exact h.invocations
  executions := by rw [hf.executions, hf.invocations]; exact h.executions
  calls := fun c hc hnone => by
    obtain ⟨c', hc', hid, htask⟩ := hf.calls c hc
    rw [hf.invocations, ← hid]
    exact h.calls c' hc' (htask.trans hnone)
  tasks := fun c hc hne => by
    obtain ⟨c', hc', hid, htask⟩ := hf.calls c hc
    rw [← hid]
    exact h.tasks c' hc' (by rwa [htask])
  disjoint := fun c hc => by
    obtain ⟨c', hc', hid, -⟩ := hf.calls c hc
    rw [hf.executions, ← hid]
    exact h.disjoint c' hc'
  owners := fun r hr o ho => by
    obtain ⟨r', hr', howner⟩ := hf.runs r hr
    obtain ⟨hinv, hcalls⟩ := h.owners r' hr' o (howner.trans ho)
    refine ⟨by rw [hf.invocations]; exact hinv, fun c hc => ?_⟩
    obtain ⟨c', hc', hid, -⟩ := hf.calls c hc
    rw [← hid]
    exact hcalls c' hc'

/-- Every step keeps the identities of calls apart from executions, run owners and aggregates. --/
theorem step_keys {p : Definition} {s t : State} {op : Op} (h : Keys s) (hs : step p s op = .ok t) : Keys t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact { h with owners := fun r hr o ho => by rw [List.mem_singleton.mp hr] at ho; cases ho }
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, pl, input, id, -, -, -, -, -, hkey, -, hfresh, hcases⟩ := Step.invoke_inv hs
    have key : InvocationKey id := ⟨path, name, trigger, hkey⟩
    obtain ⟨hcalls, hexec, hown⟩ := h.fresh (invocation?_eq_none_iff.mp hfresh) key
    have h' := h.addInvocation (i := { id, run := path, placement := name, trigger, input }) key
    have hmem : id ∈ (s.invocations ++ [({ id, run := path, placement := name, trigger, input } : Invocation)]).map
        (·.id) := by
      simp
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨judge, arms, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩ | ⟨cc, -, -, rfl⟩
    · exact h'.addCall (fun _ => hmem) (fun hne => absurd rfl hne) hexec (fun r hr o ho => (hown r hr o ho).symm)
    · exact h'.addCall (fun _ => hmem) (fun hne => absurd rfl hne) hexec (fun r hr o ho => (hown r hr o ho).symm)
    · exact h'.addRun fun o ho => by
        cases ho
        exact ⟨hmem, hcalls⟩
    · exact h'.addExecution hmem hcalls
  | fetch id =>
    obtain ⟨-, -, c, hc, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.frame (Frame.setCall (call?_eq_some hc).1 rfl rfl)
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact h.frame (((Frame.accept hacc).trans (Frame.setCall (d := { c with status := .returned }) hc' rfl rfl)).trans
      (Frame.ownerUpdate (settleOwner_update hso)))
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact h.frame (((Frame.accept hacc).trans (Frame.setCall (d := { c with status := .returned }) hc' rfl rfl)).trans
      Frame.setInvocation)
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (call?_eq_some hc).1
    exact h.frame ((Frame.accept hacc).trans
      (Frame.setCall (d := { c with status := .running, yields := c.yields + 1 }) hc' rfl rfl))
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    exact h.frame ((Frame.setCall (d := { c with status := .returned }) (call?_eq_some hc).1 rfl rfl).trans
      (Frame.ownerUpdate (settleOwner_update hso)))
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact h.frame (Frame.failCall (call?_eq_some hc).1 hf)
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    exact h.frame (Frame.failCall (call?_eq_some hc).1 hf)
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.frame (Frame.failCall (call?_eq_some hc).1 hf)
    · exact h.frame ((Frame.setCall (d := { c with status := .cancelled }) (call?_eq_some hc).1 rfl rfl).trans
        (Frame.ownerUpdate (cancelOwner_update ho)))
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact h.frame ((Frame.setCall (d := { c with status := .cancelled }) (call?_eq_some hc).1 rfl rfl).trans
      (Frame.ownerUpdate (cancelOwner_update ho)))
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.frame (Frame.of_eq rfl rfl rfl rfl)
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact h.frame (Frame.andFail (Frame.of_eq rfl rfl rfl rfl))
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.frame Frame.setTask
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact h.frame (Frame.setTask.trans Frame.fail)
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    have h' := h.frame (Frame.setTask (e := e) (ts := { ts with status := .active }))
    have heid : e.id ∈ s.executions.map (·.id) := List.mem_map.mpr ⟨e, (execution?_eq_some he).1, rfl⟩
    have key : TaskKey (taskId e.id name) := ⟨e.id, name, rfl⟩
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩
    · refine h'.addCall (fun hnone => absurd hnone (by simp)) (fun _ => key) ?_ ?_
      · rw [setTask_executions_map_id]
        intro hmem
        exact not_taskKey_of_invocationKey (h.invocations _ (h.executions _ hmem)) key
      · intro r hr o ho heq
        exact not_taskKey_of_invocationKey (h.invocations _ (h.owners r hr o ho).1) (heq ▸ key)
    · refine h'.addRun fun o ho => ?_
      cases ho
      exact ⟨h.executions _ heid, fun c hc heq => h.disjoint c hc (heq ▸ heid)⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact h.frame (Frame.of_eq rfl rfl rfl rfl)
    · exact h.frame Frame.setTaskResult
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact h.frame (Frame.setTaskResult.trans Frame.fail)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h.frame (Frame.of_eq rfl rfl rfl rfl)
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h.frame (Frame.setExecution.trans Frame.setInvocation)
    · exact h.frame ((Frame.setExecution.trans Frame.setInvocation).trans (Frame.of_eq rfl rfl rfl rfl))
    · exact h.frame (Frame.setExecution.trans Frame.setInvocation)
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    have hf : Frame s (s.setRun { r with complete := true }) := Frame.setRun (run?_eq_some hr).1 rfl
    rcases hcases with ⟨-, _, -, hcases⟩ | ⟨_, _, _, -, -, -, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact h.frame ((hf.trans Frame.setInvocation).trans (Frame.of_eq rfl rfl rfl rfl))
      all_goals exact h.frame (hf.trans Frame.setInvocation)
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact h.frame ((hf.trans Frame.setTask).trans (Frame.of_eq rfl rfl rfl rfl))
      all_goals exact h.frame (hf.trans Frame.setTask)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.frame (Frame.stop.trans (Frame.of_eq rfl rfl rfl rfl))
    · exact h.frame (Frame.of_eq rfl rfl rfl rfl)
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have hf : Frame s (s.setRun { r with complete := true }) := Frame.setRun (run?_eq_some hr).1 rfl
      exact h.frame (hf.trans (Frame.of_eq rfl rfl rfl rfl))
    · exact h.frame (Frame.endUnfinished.trans (Frame.of_eq rfl rfl rfl rfl))

theorem reachable_keys {p : Definition} {s : State} (h : Reachable p s) : Keys s := by
  induction h with
  | empty => exact Keys.empty
  | step op _ hs ih => exact step_keys ih hs

end Calls

open State in
/-- Once a call has stopped running, it never runs again (§11.3, §11.5, §11.6). --/
theorem step_call_stays_stopped {p : Definition} {s t : State} {op : Op} {id : String} {c : Call}
    (hk : s.WellKeyed) (hs : step p s op = .ok t) (hc : s.call? id = some c)
    (stopped : c.status ≠ .running ∧ c.status ≠ .fetching) :
    ∀ c', t.call? id = some c' → c'.status ≠ .running ∧ c'.status ≠ .fetching := by
  suffices h : Calls.StoppedAt t id by
    intro c' hc'
    obtain ⟨c'', hc'', hstop⟩ := h
    rw [hc'] at hc''
    cases hc''
    exact hstop
  have h0 : Calls.StoppedAt s id := ⟨c, hc, stopped⟩
  -- Only fetch and yielded store a running or fetching call, and each needs the call it updates to
  -- be running or fetching; with unique identities, the call under `id` is `c`, which is not.
  have other : ∀ {id' : String} {c0 : Call}, s.call? id' = some c0 →
      (c0.status = .running ∨ c0.status = .fetching) → c0.id ≠ id := by
    intro id' c0 hc0 hrun hid
    have heq : c0 = c :=
      hk.call_eq_of_id (call?_eq_some hc0).1 (call?_eq_some hc).1 (hid.trans (call?_eq_some hc).2.symm)
    subst heq
    rcases hrun with h | h
    · exact stopped.1 h
    · exact stopped.2 h
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact h0.of_calls rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact h0.of_append rfl
    · exact h0.of_append rfl
    · exact h0.of_calls rfl
    · exact h0.of_calls rfl
  | fetch id' =>
    obtain ⟨-, -, c0, hc0, -, hrun, rfl⟩ := Step.fetch_inv hs
    exact h0.setCall fun hid => (other hc0 (Or.inl hrun) hid).elim
  | returned id' value =>
    obtain ⟨-, -, c0, _, s', hc0, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact ((h0.of_calls (accept_frame hacc).2.2.2.2.2.1).setCall fun _ => by simp).of_calls
      (settleOwner_update hso).calls
  | judged id' arm =>
    obtain ⟨-, -, c0, _, _, _, _, _, s', hc0, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact ((h0.of_calls (accept_frame hacc).2.2.2.2.2.1).setCall fun _ => by simp).of_calls rfl
  | yielded id' value =>
    obtain ⟨-, -, c0, s', hc0, -, hf, hacc, rfl⟩ := Step.yielded_inv hs
    exact (h0.of_calls (accept_frame hacc).2.2.2.2.2.1).setCall fun hid => (other hc0 (Or.inr hf) hid).elim
  | ended id' =>
    obtain ⟨-, -, c0, hc0, -, -, hso⟩ := Step.ended_inv hs
    exact (h0.setCall fun _ => by simp).of_calls (settleOwner_update hso).calls
  | failed id' =>
    obtain ⟨-, -, c0, -, -, hf⟩ := Step.failed_inv hs
    exact h0.failCall (by simp) hf
  | timedOut id' element =>
    obtain ⟨-, -, c0, -, -, hf⟩ := Step.timedOut_inv hs
    exact h0.failCall (by simp) hf
  | lost id' =>
    obtain ⟨-, -, c0, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h0.failCall (by simp) hf
    · exact h0.cancelled ho
  | terminated id' =>
    obtain ⟨-, -, c0, -, -, ho⟩ := Step.terminated_inv hs
    exact h0.cancelled ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h0.of_calls rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Calls.StoppedAt.fail (h0.of_calls rfl)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h0.of_calls rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact Calls.StoppedAt.fail (h0.of_calls rfl)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact h0.of_append rfl
    · exact h0.of_calls rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h0.of_calls rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Calls.StoppedAt.fail (h0.of_calls rfl)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h0.of_calls rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact h0.of_calls rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h0.of_calls rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h0.stop.of_calls rfl
    · exact h0.of_calls rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact h0.of_calls rfl

/-- A value, an element or the end is accepted from a call only while it runs; after a failure, a
    timeout, a loss or a cancellation nothing more is accepted from it (§10.2, §11.5, §11.6). --/
theorem step_report_requires_running {p : Definition} {s t : State} {op : Op} {id : String}
    (hs : step p s op = .ok t)
    (hop : (∃ v, op = .returned id v) ∨ (∃ v, op = .yielded id v) ∨ (∃ a, op = .judged id a) ∨ op = .ended id) :
    ∃ c, s.call? id = some c ∧ (c.status = .running ∨ c.status = .fetching) := by
  rcases hop with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨a, rfl⟩ | rfl
  · obtain ⟨-, -, c, _, _, hc, -, hrun, -⟩ := Step.returned_inv hs
    exact ⟨c, hc, Or.inl hrun⟩
  · obtain ⟨-, -, c, _, hc, -, hf, -⟩ := Step.yielded_inv hs
    exact ⟨c, hc, Or.inr hf⟩
  · obtain ⟨-, -, c, _, _, _, _, _, _, hc, hrun, -⟩ := Step.judged_inv hs
    exact ⟨c, hc, Or.inl hrun⟩
  · obtain ⟨-, -, c, hc, -, hf, -⟩ := Step.ended_inv hs
    exact ⟨c, hc, Or.inr hf⟩

/-- A generator is asked for its next element only when no request is outstanding, and answers
    only an outstanding request (§4.1.1). --/
theorem step_fetch_sequential {p : Definition} {s t : State} {id : String} :
    (step p s (.fetch id) = .ok t → ∃ c, s.call? id = some c ∧ c.stream = true ∧ c.status = .running) ∧
    (∀ v, step p s (.yielded id v) = .ok t → ∃ c, s.call? id = some c ∧ c.stream = true ∧ c.status = .fetching) ∧
    (step p s (.ended id) = .ok t → ∃ c, s.call? id = some c ∧ c.stream = true ∧ c.status = .fetching) := by
  refine ⟨fun hs => ?_, fun v hs => ?_, fun hs => ?_⟩
  · obtain ⟨-, -, c, hc, hstream, hrun, -⟩ := Step.fetch_inv hs
    exact ⟨c, hc, hstream, hrun⟩
  · obtain ⟨-, -, c, _, hc, hstream, hf, -⟩ := Step.yielded_inv hs
    exact ⟨c, hc, hstream, hf⟩
  · obtain ⟨-, -, c, hc, hstream, hf, -⟩ := Step.ended_inv hs
    exact ⟨c, hc, hstream, hf⟩

open State in
/-- A call's own results are accepted only while that call runs (§10.2). --/
theorem Reachable.call_results {p : Definition} {s t : State} {op : Op} (h : Reachable p s)
    (hs : Suimon.step p s op = .ok t) :
    ∀ r ∈ t.results, r ∉ s.results → ∀ c ∈ s.calls, r.producer = c.id → c.status = .running ∨ c.status = .fetching := by
  intro r hr hnew c hc hprod
  have keys := Calls.reachable_keys h
  have hp := step_producer hs hr hnew
  -- A report names the stored call `c`, since call identities are unique.
  have same : ∀ {id : String} {c0 : Call}, s.call? id = some c0 → r.producer = id → c0 = c := by
    intro id c0 hc0 hid
    have := h.wellKeyed.call?_of_mem hc
    rw [← hprod, hid, hc0] at this
    exact Option.some.inj this
  cases op
  case returned id value =>
    obtain ⟨-, -, c0, _, _, hc0, -, hrun, -⟩ := Step.returned_inv hs
    exact Or.inl (same hc0 hp ▸ hrun)
  case judged id arm =>
    obtain ⟨-, -, c0, _, _, _, _, _, _, hc0, hrun, -⟩ := Step.judged_inv hs
    exact Or.inl (same hc0 hp ▸ hrun)
  case yielded id value =>
    obtain ⟨-, -, c0, _, hc0, -, hf, -⟩ := Step.yielded_inv hs
    exact Or.inr (same hc0 hp ▸ hf)
  -- An execution, the owner of a run, or an aggregate is never a call.
  case taskOutput eid name index value =>
    obtain ⟨-, -, e, _, _, _, he, -⟩ := Step.taskOutput_inv hs
    exact absurd (List.mem_map.mpr ⟨e, (execution?_eq_some he).1,
      (execution?_eq_some he).2.trans ((hp : r.producer = eid).symm.trans hprod)⟩) (keys.disjoint c hc)
  case closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, -⟩ := Step.closeExecution_inv hs
    exact absurd (List.mem_map.mpr ⟨e, (execution?_eq_some he).1,
      (execution?_eq_some he).2.trans ((hp : r.producer = eid).symm.trans hprod)⟩) (keys.disjoint c hc)
  case closeRun path =>
    obtain ⟨run, hrun, howner⟩ := Option.bind_eq_some_iff.mp (hp : (s.run? path).bind (·.owner) = some r.producer)
    exact absurd hprod ((keys.owners run (run?_eq_some hrun).1 _ howner).2 c hc).symm
  case settle path name =>
    exact absurd (hprod.symm.trans (hp : r.producer = Key.aggregate path name)) (keys.ne_aggregate hc path name)
  all_goals exact False.elim hp

/-- An invocation is not ended while any of its calls still runs, including a Stream generator that
    has not finished and a cancelled call that has not terminated (§4.1.1, §8.2). --/
theorem State.invocationEnded_calls {s : State} {i : Invocation} (h : s.invocationEnded i = true) :
    ∀ c ∈ s.calls, c.owner = i.id → c.task = none → c.status.ended = true := by
  intro c hc howner htask
  unfold State.invocationEnded at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.2 c (List.mem_filter.mpr ⟨hc, by simp [howner, htask]⟩)

end Suimon
