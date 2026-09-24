import Suimon.Theorems.SettleInv

/-! What every step keeps: the static part of each stored record (its key), and the workflow of
    each run. -/

namespace Suimon.Settle

open State

/-- The parts of a call that never change. --/
def callKey (c : Call) : String × String × Option String × Bool := (c.id, c.owner, c.task, c.stream)
/-- The parts of an invocation that never change. --/
def invKey (i : Invocation) : String × Path × String × Option ResultId := (i.id, i.run, i.placement, i.trigger)
/-- The parts of an execution that never change. --/
def execKey (e : Execution) : String × Path × String × List String := (e.id, e.run, e.placement, e.tasks.map (·.name))
/-- The parts of a run that never change. --/
def runKey (r : Run) : Path × String × Option String × Option String := (r.path, r.workflow, r.owner, r.task)
/-- The parts of a task result that never change. --/
def trKey (r : TaskResult) : String × String × Nat := (r.execution, r.task, r.index)

@[simp] theorem callKey_eq {c c' : Call} :
    callKey c = callKey c' ↔ c.id = c'.id ∧ c.owner = c'.owner ∧ c.task = c'.task ∧ c.stream = c'.stream := by
  simp [callKey]
@[simp] theorem invKey_eq {i i' : Invocation} :
    invKey i = invKey i' ↔ i.id = i'.id ∧ i.run = i'.run ∧ i.placement = i'.placement ∧ i.trigger = i'.trigger := by
  simp [invKey]
@[simp] theorem execKey_eq {e e' : Execution} :
    execKey e = execKey e' ↔ e.id = e'.id ∧ e.run = e'.run ∧ e.placement = e'.placement ∧
      e.tasks.map (·.name) = e'.tasks.map (·.name) := by
  simp [execKey]
@[simp] theorem runKey_eq {r r' : Run} :
    runKey r = runKey r' ↔ r.path = r'.path ∧ r.workflow = r'.workflow ∧ r.owner = r'.owner ∧ r.task = r'.task := by
  simp [runKey]
@[simp] theorem trKey_eq {r r' : TaskResult} :
    trKey r = trKey r' ↔ r.execution = r'.execution ∧ r.task = r'.task ∧ r.index = r'.index := by
  simp [trKey]

/-! ### Replacing a record by one with the same key -/

section Replace
variable {α κ β : Type} [BEq β] [LawfulBEq β]

/-- Replacing the members with one identity by a record with the same key keeps the keys. --/
theorem map_key_replace {l : List α} {f : α → β} {k : α → κ} {y : α}
    (h : ∀ x ∈ l, f x = f y → k x = k y) : (l.map fun x => if f x == f y then y else x).map k = l.map k := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  by_cases hxy : f x = f y
  · simp [hxy, h x hx hxy]
  · simp [hxy]

end Replace

/-- With distinct keys, members with the same key are equal. --/
theorem eq_of_nodup_map {α κ : Type} {l : List α} {f : α → κ} (hn : (l.map f).Nodup) {x y : α} (hx : x ∈ l)
    (hy : y ∈ l) (h : f x = f y) : x = y := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨y, hy', h.symm⟩) hn.1
    · exact absurd (List.mem_map.mpr ⟨x, hx', h⟩) hn.1
    · exact ih hn.2 hx' hy'

section Keys
variable {s : State}

theorem setCall_keys (hn : (s.calls.map (·.id)).Nodup) {c c' : Call} (hc : c ∈ s.calls)
    (hk : callKey c' = callKey c) : (s.setCall c').calls.map callKey = s.calls.map callKey :=
  map_key_replace (f := fun x : Call => x.id) fun x hx hid => by
    have hid' : x.id = c.id := hid.trans (callKey_eq.mp hk).1
    rw [eq_of_nodup_map hn hx hc hid', hk]

theorem setInvocation_keys (hn : (s.invocations.map (·.id)).Nodup) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hk : invKey i' = invKey i) : (s.setInvocation i').invocations.map invKey = s.invocations.map invKey :=
  map_key_replace (f := fun x : Invocation => x.id) fun x hx hid => by
    have hid' : x.id = i.id := hid.trans (invKey_eq.mp hk).1
    rw [eq_of_nodup_map hn hx hi hid', hk]

theorem setExecution_keys (hn : (s.executions.map (·.id)).Nodup) {e e' : Execution} (he : e ∈ s.executions)
    (hk : execKey e' = execKey e) : (s.setExecution e').executions.map execKey = s.executions.map execKey :=
  map_key_replace (f := fun x : Execution => x.id) fun x hx hid => by
    have hid' : x.id = e.id := hid.trans (execKey_eq.mp hk).1
    rw [eq_of_nodup_map hn hx he hid', hk]

theorem withTask_names {e : Execution} {ts : TaskState} :
    (withTask e ts).tasks.map (·.name) = e.tasks.map (·.name) :=
  map_key_replace (f := fun x : TaskState => x.name) fun _ _ h => h

theorem execKey_withTask {e : Execution} {ts : TaskState} : execKey (withTask e ts) = execKey e := by
  simp [withTask_names]

theorem setRun_keys (hn : (s.runs.map (·.path)).Nodup) {r r' : Run} (hr : r ∈ s.runs) (hk : runKey r' = runKey r) :
    (s.setRun r').runs.map runKey = s.runs.map runKey :=
  map_key_replace (f := fun x : Run => x.path) fun x hx hp => by
    have hp' : x.path = r.path := hp.trans (runKey_eq.mp hk).1
    rw [eq_of_nodup_map hn hx hr hp', hk]

theorem setTaskResult_keys {r : TaskResult} :
    (s.setTaskResult r).taskResults.map trKey = s.taskResults.map trKey := by
  rw [setTaskResult_taskResults, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp [trKey, h1, h2, h3]
  · rfl

theorem stop_call_keys : s.stop.calls.map callKey = s.calls.map callKey := by
  simp only [stop_calls, List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, callKey, stopCall]
  split <;> rfl

theorem stopExecution_names {e : Execution} : (stopExecution e).tasks.map (·.name) = e.tasks.map (·.name) := by
  simp only [stopExecution, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp]
  split <;> rfl

theorem stop_exec_keys : s.stop.executions.map execKey = s.executions.map execKey := by
  simp only [stop_executions, List.map_map]
  apply List.map_congr_left
  intro e _
  simp [execKey, stopExecution_names]

end Keys

/-- Members of lists with the same keys correspond. --/
theorem exists_of_map_eq {α κ : Type} {l l' : List α} {k : α → κ} (h : l'.map k = l.map k) {x : α} (hx : x ∈ l) :
    ∃ y ∈ l', k y = k x := by
  have : k x ∈ l'.map k := h ▸ List.mem_map_of_mem hx
  obtain ⟨y, hy, hky⟩ := List.mem_map.mp this
  exact ⟨y, hy, hky⟩

/-! ### Workflows of runs -/

/-- Every run keeps its workflow. --/
def KeepsWorkflows (p : Definition) (s t : State) : Prop :=
  ∀ path w, s.workflow? p path = some w → t.workflow? p path = some w

namespace KeepsWorkflows
variable {p : Definition} {s t u : State}

theorem refl : KeepsWorkflows p s s := fun _ _ h => h

theorem trans (h₁ : KeepsWorkflows p s t) (h₂ : KeepsWorkflows p t u) : KeepsWorkflows p s u :=
  fun path w h => h₂ path w (h₁ path w h)

theorem of_runs (h : t.runs = s.runs) : KeepsWorkflows p s t := fun path w hw => by
  simpa [State.workflow?, State.run?, h] using hw

theorem of_append {l : List Run} (h : t.runs = s.runs ++ l) : KeepsWorkflows p s t := fun path w hw => by
  simp only [State.workflow?, option_bind_eq_some] at hw ⊢
  obtain ⟨r, hr, hw⟩ := hw
  refine ⟨r, ?_, hw⟩
  unfold State.run? at hr ⊢
  rw [h, List.find?_append, hr]
  rfl

theorem setRun {r r' : Run} (hr : s.run? r'.path = some r) (hw : r'.workflow = r.workflow) :
    KeepsWorkflows p s (s.setRun r') := fun path w h => by
  simp only [State.workflow?, option_bind_eq_some] at h ⊢
  obtain ⟨x, hx, h⟩ := h
  rw [run?_setRun]
  by_cases hp : r'.path = path
  · subst hp
    rw [hr] at hx
    cases hx
    exact ⟨r', by simp [hr], hw ▸ h⟩
  · exact ⟨x, by simp [hp, hx], h⟩

theorem placementAt (h : KeepsWorkflows p s t) {path : Path} {name : String} {pl : Placement}
    (hpl : Settle.placementAt p s path name = some pl) : Settle.placementAt p t path name = some pl := by
  unfold Settle.placementAt at hpl ⊢
  cases hw : s.workflow? p path with
  | none => simp [hw] at hpl
  | some w => rw [h path w hw]; simpa [hw] using hpl

theorem placementOf (h : KeepsWorkflows p s t) {path : Path} {name : String} {pl : Placement}
    (hpl : s.placementOf p path name = .ok pl) : t.placementOf p path name = .ok pl := by
  rw [placementOf_eq_ok] at hpl ⊢
  obtain ⟨w, hw, hpl⟩ := hpl
  exact ⟨w, h path w hw, hpl⟩

theorem concurrencyOf (h : KeepsWorkflows p s t) {e e' : Execution} (hrun : e'.run = e.run)
    (hplace : e'.placement = e.placement) {cc : Concurrency} (hc : s.concurrencyOf p e = .ok cc) :
    t.concurrencyOf p e' = .ok cc := by
  rw [concurrencyOf_eq_ok] at hc ⊢
  obtain ⟨pl, hpl, hc⟩ := hc
  exact ⟨pl, by rw [hrun, hplace]; exact h.placementOf hpl, hc⟩

theorem taskSpec (h : KeepsWorkflows p s t) {e e' : Execution} (hrun : e'.run = e.run)
    (hplace : e'.placement = e.placement) {name : String} {spec : TaskSpec} (hs : s.taskSpec p e name = .ok spec) :
    t.taskSpec p e' name = .ok spec := by
  rw [taskSpec_eq_ok] at hs ⊢
  obtain ⟨cc, hc, hs⟩ := hs
  exact ⟨cc, h.concurrencyOf hrun hplace hc, hs⟩

end KeepsWorkflows

theorem placementAt_eq {p : Definition} {s : State} {path : Path} {name : String} {w : Workflow}
    (hw : s.workflow? p path = some w) : placementAt p s path name = w.placement? name := by
  simp [placementAt, hw]

theorem concurrencyOf_det {p : Definition} {s : State} {e : Execution} {cc cc' : Concurrency}
    (h : s.concurrencyOf p e = .ok cc) (h' : s.concurrencyOf p e = .ok cc') : cc = cc' := by
  rw [h] at h'
  exact Except.ok.inj h'

theorem taskSpec_det {p : Definition} {s : State} {e : Execution} {name : String} {spec spec' : TaskSpec}
    (h : s.taskSpec p e name = .ok spec) (h' : s.taskSpec p e name = .ok spec') : spec = spec' := by
  rw [h] at h'
  exact Except.ok.inj h'


/-! ### Steps that only update records -/

/-- A step that only updates stored records keeps their keys and the workflows of the runs. --/
structure SameKeys (p : Definition) (s t : State) : Prop where
  workflows : KeepsWorkflows p s t
  calls : t.calls.map callKey = s.calls.map callKey
  invocations : t.invocations.map invKey = s.invocations.map invKey
  executions : t.executions.map execKey = s.executions.map execKey
  runs : t.runs.map runKey = s.runs.map runKey

namespace SameKeys
variable {p : Definition} {s t u : State}

theorem refl : SameKeys p s s := ⟨KeepsWorkflows.refl, rfl, rfl, rfl, rfl⟩

theorem trans (h₁ : SameKeys p s t) (h₂ : SameKeys p t u) : SameKeys p s u :=
  ⟨h₁.workflows.trans h₂.workflows, h₂.calls.trans h₁.calls, h₂.invocations.trans h₁.invocations,
    h₂.executions.trans h₁.executions, h₂.runs.trans h₁.runs⟩

theorem of_records (hr : t.runs = s.runs) (hi : t.invocations = s.invocations) (hc : t.calls = s.calls)
    (he : t.executions = s.executions) : SameKeys p s t :=
  ⟨KeepsWorkflows.of_runs hr, by rw [hc], by rw [hi], by rw [he], by rw [hr]⟩

theorem setCall (hn : (s.calls.map (·.id)).Nodup) {c c' : Call} (hc : c ∈ s.calls) (hk : callKey c' = callKey c) :
    SameKeys p s (s.setCall c') :=
  ⟨KeepsWorkflows.of_runs rfl, setCall_keys hn hc hk, rfl, rfl, rfl⟩

theorem setInvocation (hn : (s.invocations.map (·.id)).Nodup) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hk : invKey i' = invKey i) : SameKeys p s (s.setInvocation i') :=
  ⟨KeepsWorkflows.of_runs rfl, rfl, setInvocation_keys hn hi hk, rfl, rfl⟩

theorem setExecution (hn : (s.executions.map (·.id)).Nodup) {e e' : Execution} (he : e ∈ s.executions)
    (hk : execKey e' = execKey e) : SameKeys p s (s.setExecution e') :=
  ⟨KeepsWorkflows.of_runs rfl, rfl, rfl, setExecution_keys hn he hk, rfl⟩

theorem setTask (hn : (s.executions.map (·.id)).Nodup) {e : Execution} {ts : TaskState} (he : e ∈ s.executions) :
    SameKeys p s (s.setTask e ts) :=
  setExecution hn he execKey_withTask

theorem setRun (hn : (s.runs.map (·.path)).Nodup) {r r' : Run} (hr : s.run? r'.path = some r)
    (hk : runKey r' = runKey r) : SameKeys p s (s.setRun r') :=
  ⟨KeepsWorkflows.setRun hr (runKey_eq.mp hk).2.1, rfl, rfl, rfl, setRun_keys hn (run?_eq_some hr).1 hk⟩

theorem setTaskResult {r : TaskResult} : SameKeys p s (s.setTaskResult r) := of_records rfl rfl rfl rfl

theorem stop : SameKeys p s s.stop :=
  ⟨KeepsWorkflows.of_runs rfl, stop_call_keys, rfl, stop_exec_keys, rfl⟩

theorem fail {f : Failure} {policy : Policy} : SameKeys p s (s.fail f policy) := by
  cases policy
  · show SameKeys p s ({ s with failures := s.failures ++ [f] }.stop)
    exact (of_records (s := s) (t := { s with failures := s.failures ++ [f] }) rfl rfl rfl rfl).trans stop
  · exact of_records rfl rfl rfl rfl

theorem settleOwner (hi : (s.invocations.map (·.id)).Nodup) (he : (s.executions.map (·.id)).Nodup) {c : Call}
    {inv : InvocationStatus} {task : TaskStatus} (h : s.settleOwner c inv task = .ok t) : SameKeys p s t := by
  rcases settleOwner_eq_ok.mp h with ⟨-, i, hio, rfl⟩ | ⟨_, e, _, -, heo, -, rfl⟩
  · exact setInvocation hi (invocation?_eq_some hio).1 rfl
  · exact setTask he (execution?_eq_some heo).1

theorem cancelOwner (hi : (s.invocations.map (·.id)).Nodup) (he : (s.executions.map (·.id)).Nodup) {c : Call}
    (h : s.cancelOwner c = .ok t) : SameKeys p s t := by
  rcases cancelOwner_eq_ok.mp h with ⟨-, i, hio, rfl⟩ | ⟨_, e, _, -, heo, -, rfl⟩ <;> split
  · exact setInvocation hi (invocation?_eq_some hio).1 rfl
  · exact refl
  · exact setTask he (execution?_eq_some heo).1
  · exact refl

theorem accept {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (h : s.accept c index value arm = .ok t) : SameKeys p s t := by
  obtain ⟨-, -, -, hr, hi, hc, he, -⟩ := accept_frame h
  exact of_records hr hi hc he

theorem failCall (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) {status : CallStatus} {cause : Cause}
    (h : s.failCall c status cause = .ok t) : SameKeys p s t := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  exact ((setCall (c' := { c with status }) wk.calls hc rfl).trans
    (settleOwner wk.invocations wk.executions hso)).trans fail

end SameKeys

theorem workflow?_of_run {p : Definition} {s : State} {path : Path} {r : Run} {w : Workflow}
    (hr : s.run? path = some r) (hw : p.workflow? r.workflow = some w) : s.workflow? p path = some w := by
  simp [State.workflow?, hr, hw]

namespace SameKeys
variable {p : Definition} {s t : State}

theorem call_ids (h : SameKeys p s t) : t.calls.map (·.id) = s.calls.map (·.id) := by
  have := congrArg (List.map (·.1)) h.calls
  simpa [List.map_map, Function.comp_def, callKey] using this

theorem invocation_ids (h : SameKeys p s t) : t.invocations.map (·.id) = s.invocations.map (·.id) := by
  have := congrArg (List.map (·.1)) h.invocations
  simpa [List.map_map, Function.comp_def, invKey] using this

theorem execution_ids (h : SameKeys p s t) : t.executions.map (·.id) = s.executions.map (·.id) := by
  have := congrArg (List.map (·.1)) h.executions
  simpa [List.map_map, Function.comp_def, execKey] using this

theorem run_paths (h : SameKeys p s t) : t.runs.map (·.path) = s.runs.map (·.path) := by
  have := congrArg (List.map (·.1)) h.runs
  simpa [List.map_map, Function.comp_def, runKey] using this

end SameKeys

namespace SameKeys
variable {p : Definition} {s t : State}

theorem calls_nodup (h : SameKeys p s t) (hn : (s.calls.map (·.id)).Nodup) : (t.calls.map (·.id)).Nodup := by
  rw [h.call_ids]; exact hn
theorem invocations_nodup (h : SameKeys p s t) (hn : (s.invocations.map (·.id)).Nodup) :
    (t.invocations.map (·.id)).Nodup := by
  rw [h.invocation_ids]; exact hn
theorem executions_nodup (h : SameKeys p s t) (hn : (s.executions.map (·.id)).Nodup) :
    (t.executions.map (·.id)).Nodup := by
  rw [h.execution_ids]; exact hn
end SameKeys

end Suimon.Settle
