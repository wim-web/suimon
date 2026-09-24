import Suimon.Theorems.Values.Typing

/-! # Typed values: the invariant

Every record of a state holds values of the types that its place declares. A run and an invocation
take an input of the declared input type, a call one of its function's or judge's input type, an
execution one of its concurrency's input type, and a task ready to begin one of its body's input type.
A result has the result type of its placement; a task result has the element type of its body and,
after the output transform, the concurrency's element type; a delivered value has the input type of
its connection's target.

The typings read a state only through the workflow of each run path and the place of each execution
(`Keeps`), which no step changes. This file holds the invariant and how the elementary updates of
`Suimon/Step.lean` keep it. -/

namespace Suimon.Values
open Round3 State

/-- A run takes an input that fits its workflow's input (§3.1, §4.5). -/
def RunTyped (τ : ValueTyping) (p : Definition) (r : Run) : Prop :=
  ∃ w, p.workflow? r.workflow = some w ∧ τ.Fits r.input (w.input.map (·.valueType))

/-- An invocation takes an input that fits what its placement takes (§3.2, §4.2). -/
def InvocationTyped (τ : ValueTyping) (p : Definition) (s : State) (i : Invocation) : Prop :=
  ∃ w pl input, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧
    p.inputType pl.control = some input ∧ τ.Fits i.input input

/-- A call takes an input that fits the input of the function or judge it calls (§4.1, §7.1). -/
def CallTyped (τ : ValueTyping) (p : Definition) (c : Call) : Prop :=
  match c.target with
  | .function f => ∃ decl, p.function? f = some decl ∧ τ.Fits c.input decl.input
  | .judge j => ∃ decl, p.judge? j = some decl ∧ τ.Fits c.input (some decl.input)

/-- An execution takes an input that fits its concurrency's input, and a task ready to begin holds an
    input that fits its body's input (§8.1). -/
def ExecutionTyped (τ : ValueTyping) (p : Definition) (s : State) (e : Execution) : Prop :=
  ∃ c, s.concurrencyOf p e = .ok c ∧ τ.Fits e.input c.input ∧
    ∀ tk ∈ e.tasks, tk.status = .ready → ∀ spec, c.tasks.find? (·.name == tk.name) = some spec →
      ∃ input, p.bodyInput spec.body = some input ∧ τ.Fits tk.input input

/-- A result has the result type of the placement that produced it (§4.1, §5.2, §8.3, §9). -/
def ResultTyped (τ : ValueTyping) (p : Definition) (s : State) (r : Result) : Prop :=
  ∃ w pl T, s.workflow? p r.run = some w ∧ w.placement? r.placement = some pl ∧
    p.resultType pl.control = some T ∧ τ.HasType r.value T

/-- A result of a task has the element type of the task's body, and its output after the output
    transform has the concurrency's element type (§8.1, §8.3). -/
def TaskResultTyped (τ : ValueTyping) (p : Definition) (s : State) (x : TaskResult) : Prop :=
  ∃ e ∈ s.executions, e.id = x.execution ∧ ∃ c spec T, s.concurrencyOf p e = .ok c ∧
    c.tasks.find? (·.name == x.task) = some spec ∧ p.bodyElement p.depth spec.body = some T ∧
    τ.HasType x.value T ∧ ∀ v, x.output = .value v → τ.HasType v c.element

/-- A delivery fits the input of its connection's target (§3.2, §4.2). -/
def DeliveryTyped (τ : ValueTyping) (p : Definition) (s : State) (d : Delivery) : Prop :=
  ∃ w c pl input, s.workflow? p d.run = some w ∧ w.connections[d.connection]? = some c ∧
    w.placement? c.target = some pl ∧ p.inputType pl.control = some input ∧ τ.DeliveredFits d.outcome input

/-- Every value a state holds has the type that its place declares. -/
structure Typed (τ : ValueTyping) (p : Definition) (s : State) : Prop where
  runs : ∀ r ∈ s.runs, RunTyped τ p r
  invocations : ∀ i ∈ s.invocations, InvocationTyped τ p s i
  calls : ∀ c ∈ s.calls, CallTyped τ p c
  executions : ∀ e ∈ s.executions, ExecutionTyped τ p s e
  results : ∀ r ∈ s.results, ResultTyped τ p s r
  taskResults : ∀ x ∈ s.taskResults, TaskResultTyped τ p s x
  deliveries : ∀ d ∈ s.deliveries, DeliveryTyped τ p s d

/-- What the typings read from a state is kept from `s` to `t`: the workflow of each run path, and the
    run and placement of each execution. -/
structure Keeps (p : Definition) (s t : State) : Prop where
  workflow : ∀ {path : Path} {w : Workflow}, s.workflow? p path = some w → t.workflow? p path = some w
  execution : ∀ e ∈ s.executions, ∃ e' ∈ t.executions, e'.id = e.id ∧ e'.run = e.run ∧ e'.placement = e.placement

section Transfer
variable {τ : ValueTyping} {p : Definition} {s t : State}

theorem Keeps.concurrencyOf (K : Keeps p s t) {e e' : Execution} (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) {c : Concurrency} (h : s.concurrencyOf p e = .ok c) :
    t.concurrencyOf p e' = .ok c := by
  obtain ⟨w, pl, hw, hpl', hc⟩ := Delivery.concurrencyOf_iff.mp h
  exact Delivery.concurrencyOf_iff.mpr ⟨w, pl, hrun ▸ K.workflow hw, hpl ▸ hpl', hc⟩

theorem Keeps.trans {u : State} (K₁ : Keeps p s u) (K₂ : Keeps p u t) : Keeps p s t where
  workflow h := K₂.workflow (K₁.workflow h)
  execution e he := by
    obtain ⟨e₁, he₁, a1, a2, a3⟩ := K₁.execution e he
    obtain ⟨e₂, he₂, b1, b2, b3⟩ := K₂.execution e₁ he₁
    exact ⟨e₂, he₂, b1.trans a1, b2.trans a2, b3.trans a3⟩

/-- A state that keeps its runs and executions keeps what the typings read. -/
theorem Keeps.of_eq (hr : t.runs = s.runs) (he : t.executions = s.executions) : Keeps p s t where
  workflow h := by
    unfold State.workflow? State.run? at h ⊢
    rw [hr]
    exact h
  execution e h := ⟨e, he ▸ h, rfl, rfl, rfl⟩

theorem CallTyped.congr {c c' : Call} (h : CallTyped τ p c) (ht : c.target = c'.target) (hi : c.input = c'.input) :
    CallTyped τ p c' := by
  unfold CallTyped at h ⊢
  rw [← ht, ← hi]
  exact h

theorem RunTyped.congr {r r' : Run} (h : RunTyped τ p r) (hw : r.workflow = r'.workflow) (hi : r.input = r'.input) :
    RunTyped τ p r' := by
  obtain ⟨w, hw', hf⟩ := h
  exact ⟨w, hw ▸ hw', hi ▸ hf⟩

theorem InvocationTyped.keep {i i' : Invocation} (h : InvocationTyped τ p s i) (K : Keeps p s t)
    (hrun : i.run = i'.run) (hpl : i.placement = i'.placement) (hin : i.input = i'.input) :
    InvocationTyped τ p t i' := by
  obtain ⟨w, pl, input, hw, hpl', hinput, hfits⟩ := h
  exact ⟨w, pl, input, hrun ▸ K.workflow hw, hpl ▸ hpl', hinput, hin ▸ hfits⟩

theorem ResultTyped.keep {r : Result} (h : ResultTyped τ p s r) (K : Keeps p s t) : ResultTyped τ p t r := by
  obtain ⟨w, pl, T, hw, hpl, hT, hv⟩ := h
  exact ⟨w, pl, T, K.workflow hw, hpl, hT, hv⟩

theorem DeliveryTyped.keep {d : Delivery} (h : DeliveryTyped τ p s d) (K : Keeps p s t) : DeliveryTyped τ p t d := by
  obtain ⟨w, c, pl, input, hw, hc, hpl, hinput, hfits⟩ := h
  exact ⟨w, c, pl, input, K.workflow hw, hc, hpl, hinput, hfits⟩

theorem TaskResultTyped.keep {x x' : TaskResult} (h : TaskResultTyped τ p s x) (K : Keeps p s t)
    (hexec : x.execution = x'.execution) (htask : x.task = x'.task) (hval : x.value = x'.value)
    (hout : ∀ v, x'.output = .value v → x.output = .value v) : TaskResultTyped τ p t x' := by
  obtain ⟨e, he, heid, c, spec, T, hc, hspec, hT, hv, ho⟩ := h
  obtain ⟨e', he', hid, hrun, hpl⟩ := K.execution e he
  exact ⟨e', he', hid.trans (heid.trans hexec), c, spec, T, K.concurrencyOf hrun hpl hc, htask ▸ hspec, hT,
    hval ▸ hv, fun v hv' => ho v (hout v hv')⟩

theorem ExecutionTyped.keep {e e' : Execution} (h : ExecutionTyped τ p s e) (K : Keeps p s t)
    (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (hin : e.input = e'.input)
    (htasks : ∀ tk ∈ e'.tasks, tk.status = .ready →
      ∃ tk₀ ∈ e.tasks, tk₀.name = tk.name ∧ tk₀.input = tk.input ∧ tk₀.status = .ready) :
    ExecutionTyped τ p t e' := by
  obtain ⟨c, hc, hfits, hready⟩ := h
  refine ⟨c, K.concurrencyOf hrun hpl hc, hin ▸ hfits, fun tk htk hst spec hspec => ?_⟩
  obtain ⟨tk₀, htk₀, hname, hinput, hst₀⟩ := htasks tk htk hst
  obtain ⟨input, hb, hf⟩ := hready tk₀ htk₀ hst₀ spec (hname ▸ hspec)
  exact ⟨input, hb, hinput ▸ hf⟩

/-- The invariant carries over to a state that keeps what the typings read, when every record of the
    new state is typed or is a record from before with the same values. -/
theorem Typed.of_frame (h : Typed τ p s) (K : Keeps p s t)
    (runs : ∀ r ∈ t.runs, RunTyped τ p r)
    (calls : ∀ c ∈ t.calls, CallTyped τ p c)
    (invocations : ∀ i ∈ t.invocations,
      (∃ i₀ ∈ s.invocations, i₀.run = i.run ∧ i₀.placement = i.placement ∧ i₀.input = i.input) ∨
        InvocationTyped τ p t i)
    (executions : ∀ e ∈ t.executions,
      (∃ e₀ ∈ s.executions, e.run = e₀.run ∧ e.placement = e₀.placement ∧ e₀.input = e.input ∧
        ∀ tk ∈ e.tasks, tk.status = .ready →
          ∃ tk₀ ∈ e₀.tasks, tk₀.name = tk.name ∧ tk₀.input = tk.input ∧ tk₀.status = .ready) ∨
        ExecutionTyped τ p t e)
    (results : ∀ r ∈ t.results, r ∈ s.results ∨ ResultTyped τ p t r)
    (taskResults : ∀ x ∈ t.taskResults,
      (∃ x₀ ∈ s.taskResults, x₀.execution = x.execution ∧ x₀.task = x.task ∧ x₀.value = x.value ∧
        ∀ v, x.output = .value v → x₀.output = .value v) ∨ TaskResultTyped τ p t x)
    (deliveries : ∀ d ∈ t.deliveries, d ∈ s.deliveries ∨ DeliveryTyped τ p t d) :
    Typed τ p t where
  runs := runs
  calls := calls
  invocations i hi := by
    rcases invocations i hi with ⟨i₀, hi₀, a1, a2, a3⟩ | h'
    · exact (h.invocations i₀ hi₀).keep K a1 a2 a3
    · exact h'
  executions e he := by
    rcases executions e he with ⟨e₀, he₀, a1, a2, a3, a4⟩ | h'
    · exact (h.executions e₀ he₀).keep K a1 a2 a3 a4
    · exact h'
  results r hr := by
    rcases results r hr with hr | h'
    · exact (h.results r hr).keep K
    · exact h'
  taskResults x hx := by
    rcases taskResults x hx with ⟨x₀, hx₀, a1, a2, a3, a4⟩ | h'
    · exact (h.taskResults x₀ hx₀).keep K a1 a2 a3 a4
    · exact h'
  deliveries d hd := by
    rcases deliveries d hd with hd | h'
    · exact (h.deliveries d hd).keep K
    · exact h'

end Transfer

/-! ## Elementary updates -/

section Updates
variable {τ : ValueTyping} {p : Definition} {s : State}

/-- The frame of a list that an update leaves as it is. -/
theorem same_invocations {t : State} (h : t.invocations = s.invocations) : ∀ i ∈ t.invocations,
    (∃ i₀ ∈ s.invocations, i₀.run = i.run ∧ i₀.placement = i.placement ∧ i₀.input = i.input) ∨
      InvocationTyped τ p t i :=
  fun i hi => Or.inl ⟨i, h ▸ hi, rfl, rfl, rfl⟩

theorem same_executions {t : State} (h : t.executions = s.executions) : ∀ e ∈ t.executions,
    (∃ e₀ ∈ s.executions, e.run = e₀.run ∧ e.placement = e₀.placement ∧ e₀.input = e.input ∧
      ∀ tk ∈ e.tasks, tk.status = .ready →
        ∃ tk₀ ∈ e₀.tasks, tk₀.name = tk.name ∧ tk₀.input = tk.input ∧ tk₀.status = .ready) ∨
      ExecutionTyped τ p t e :=
  fun e he => Or.inl ⟨e, h ▸ he, rfl, rfl, rfl, fun tk htk hst => ⟨tk, htk, rfl, rfl, hst⟩⟩

theorem same_taskResults {t : State} (h : t.taskResults = s.taskResults) : ∀ x ∈ t.taskResults,
    (∃ x₀ ∈ s.taskResults, x₀.execution = x.execution ∧ x₀.task = x.task ∧ x₀.value = x.value ∧
      ∀ v, x.output = .value v → x₀.output = .value v) ∨ TaskResultTyped τ p t x :=
  fun x hx => Or.inl ⟨x, h ▸ hx, rfl, rfl, rfl, fun _ h => h⟩

theorem Typed.setCall (h : Typed τ p s) {c c' : Call} (hc : c ∈ s.calls) (ht : c.target = c'.target)
    (hi : c.input = c'.input) : Typed τ p (s.setCall c') where
  runs := h.runs
  invocations := h.invocations
  calls x hx := by
    rcases mem_setCall_calls hx with rfl | hx
    · exact (h.calls c hc).congr ht hi
    · exact h.calls x hx
  executions := h.executions
  results := h.results
  taskResults := h.taskResults
  deliveries := h.deliveries

theorem Typed.setInvocation (h : Typed τ p s) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hrun : i.run = i'.run) (hpl : i.placement = i'.placement) (hin : i.input = i'.input) :
    Typed τ p (s.setInvocation i') where
  runs := h.runs
  invocations x hx := by
    rcases mem_setInvocation_invocations hx with rfl | hx
    · exact (h.invocations i hi).keep (Keeps.of_eq rfl rfl) hrun hpl hin
    · exact h.invocations x hx
  calls := h.calls
  executions := h.executions
  results := h.results
  taskResults := h.taskResults
  deliveries := h.deliveries

theorem Typed.setTaskResult (h : Typed τ p s) {r r' : TaskResult} (hr : r ∈ s.taskResults)
    (hexec : r.execution = r'.execution) (htask : r.task = r'.task) (hval : r.value = r'.value)
    (hout : ∀ v, r'.output = .value v → ∀ e ∈ s.executions, e.id = r.execution →
      ∀ c, s.concurrencyOf p e = .ok c → τ.HasType v c.element) :
    Typed τ p (s.setTaskResult r') where
  runs := h.runs
  invocations := h.invocations
  calls := h.calls
  executions := h.executions
  results := h.results
  taskResults x hx := by
    rcases mem_setTaskResult_taskResults hx with rfl | hx
    · obtain ⟨e, he, heid, c, spec, T, hc, hspec, hT, hv, -⟩ := h.taskResults r hr
      exact ⟨e, he, heid.trans hexec, c, spec, T, hc, htask ▸ hspec, hT, hval ▸ hv,
        fun v hv' => hout v hv' e he heid c hc⟩
    · exact h.taskResults x hx
  deliveries := h.deliveries

theorem Typed.appendResult (h : Typed τ p s) {r : Result} (hr : ResultTyped τ p s r) :
    Typed τ p { s with results := s.results ++ [r] } where
  runs := h.runs
  invocations := h.invocations
  calls := h.calls
  executions := h.executions
  results x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.results x hx
    · rw [List.mem_singleton.mp hx]
      exact hr
  taskResults := h.taskResults
  deliveries := h.deliveries

theorem Typed.appendTaskResult (h : Typed τ p s) {x : TaskResult} (hx : TaskResultTyped τ p s x) :
    Typed τ p { s with taskResults := s.taskResults ++ [x] } where
  runs := h.runs
  invocations := h.invocations
  calls := h.calls
  executions := h.executions
  results := h.results
  taskResults y hy := by
    rcases List.mem_append.mp hy with hy | hy
    · exact h.taskResults y hy
    · rw [List.mem_singleton.mp hy]
      exact hx
  deliveries := h.deliveries

theorem Typed.appendDelivery (h : Typed τ p s) {d : Delivery} (hd : DeliveryTyped τ p s d) :
    Typed τ p { s with deliveries := s.deliveries ++ [d] } where
  runs := h.runs
  invocations := h.invocations
  calls := h.calls
  executions := h.executions
  results := h.results
  taskResults := h.taskResults
  deliveries x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.deliveries x hx
    · rw [List.mem_singleton.mp hx]
      exact hd

/-- Recording a failure adds no value, and a stop only cancels calls and leaves waiting tasks unstarted. -/
theorem stopCall_target (c : Call) : (stopCall c).target = c.target := by unfold stopCall; split <;> rfl
theorem stopCall_input (c : Call) : (stopCall c).input = c.input := by unfold stopCall; split <;> rfl

theorem Keeps.stop : Keeps p s s.stop where
  workflow h := h
  execution e he := ⟨stopExecution e, mem_stop_executions.mpr ⟨e, he, rfl⟩, rfl, rfl, rfl⟩

theorem Typed.stop (h : Typed τ p s) : Typed τ p s.stop := by
  refine h.of_frame Keeps.stop h.runs (fun c hc => ?_) (same_invocations rfl) (fun e he => ?_)
    (fun r hr => Or.inl hr) (same_taskResults rfl) (fun d hd => Or.inl hd)
  · obtain ⟨c₀, hc₀, rfl⟩ := mem_stop_calls.mp hc
    exact (h.calls c₀ hc₀).congr (stopCall_target c₀).symm (stopCall_input c₀).symm
  · obtain ⟨e₀, he₀, rfl⟩ := mem_stop_executions.mp he
    refine Or.inl ⟨e₀, he₀, rfl, rfl, rfl, fun tk htk hst => ?_⟩
    obtain ⟨tk₀, htk₀, rfl⟩ := List.mem_map.mp htk
    by_cases hw : (tk₀.status == .pending || tk₀.status == .ready) = true
    · simp [hw] at hst
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hst ⊢
      exact ⟨tk₀, htk₀, rfl, rfl, hst⟩

theorem Typed.fail (h : Typed τ p s) (f : Failure) (policy : Policy) : Typed τ p (s.fail f policy) := by
  have h' : Typed τ p { s with failures := s.failures ++ [f] } :=
    ⟨h.runs, h.invocations, h.calls, h.executions, h.results, h.taskResults, h.deliveries⟩
  cases policy
  · exact h'.stop
  · exact h'

theorem Keeps.endUnfinished : Keeps p s s.endUnfinished where
  workflow h := h
  execution e he := ⟨endExecution e, mem_endUnfinished_executions.mpr ⟨e, he, rfl⟩, rfl, rfl, rfl⟩

theorem Typed.endUnfinished (h : Typed τ p s) : Typed τ p s.endUnfinished := by
  refine h.of_frame Keeps.endUnfinished h.runs h.calls (fun i hi => ?_) (fun e he => ?_)
    (fun r hr => Or.inl hr) (same_taskResults rfl) (fun d hd => Or.inl hd)
  · obtain ⟨i₀, hi₀, rfl⟩ := mem_endUnfinished_invocations.mp hi
    exact Or.inl ⟨i₀, hi₀, by simp, by simp, by simp⟩
  · obtain ⟨e₀, he₀, rfl⟩ := mem_endUnfinished_executions.mp he
    refine Or.inl ⟨e₀, he₀, rfl, rfl, rfl, fun tk htk hst => ?_⟩
    rw [endExecution_tasks] at htk
    obtain ⟨tk₀, -, rfl⟩ := List.mem_map.mp htk
    rw [endTask_status] at hst
    split at hst
    · cases hst
    · split at hst
      · cases hst
      · rename_i h1 h2
        exact absurd (Or.inr hst) h2

/-- Updating a run keeps what the typings read when it keeps the run's path and workflow. -/
theorem Keeps.setRun (wk : s.WellKeyed) {r r' : Run} (hr : r ∈ s.runs) (hpath : r'.path = r.path)
    (hwf : r'.workflow = r.workflow) : Keeps p s (s.setRun r') where
  workflow {path w} h := by
    obtain ⟨x, hx, hw⟩ := Delivery.workflow?_iff.mp h
    refine Delivery.workflow?_iff.mpr ?_
    rw [run?_setRun]
    by_cases hp : r'.path = path
    · have hrx : s.run? path = some r := by rw [← hp, hpath]; exact wk.run?_of_mem hr
      rw [hx] at hrx
      cases hrx
      exact ⟨r', by simp [hp, hx], hwf ▸ hw⟩
    · exact ⟨x, by simp [hp, hx], hw⟩
  execution e he := ⟨e, he, rfl, rfl, rfl⟩

theorem Typed.setRun (h : Typed τ p s) (wk : s.WellKeyed) {r r' : Run} (hr : r ∈ s.runs)
    (hpath : r'.path = r.path) (hwf : r.workflow = r'.workflow) (hin : r.input = r'.input) :
    Typed τ p (s.setRun r') := by
  refine h.of_frame (Keeps.setRun wk hr hpath hwf.symm) (fun x hx => ?_) h.calls (same_invocations rfl)
    (same_executions rfl) (fun r hr => Or.inl hr) (same_taskResults rfl) (fun d hd => Or.inl hd)
  rcases mem_setRun_runs hx with rfl | hx
  · exact (h.runs r hr).congr hwf hin
  · exact h.runs x hx

/-- Updating an execution keeps what the typings read when it keeps the execution's place. -/
theorem Keeps.setExecution (wk : s.WellKeyed) {e e' : Execution} (he : e ∈ s.executions) (hid : e'.id = e.id)
    (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) : Keeps p s (s.setExecution e') where
  workflow h := h
  execution x hx := by
    refine ⟨if x.id == e'.id then e' else x, List.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    by_cases hxe : x.id = e'.id
    · have : x = e := wk.execution_eq_of_id hx he (hxe.trans hid)
      subst this
      have hb : (x.id == e'.id) = true := beq_iff_eq.mpr hxe
      simp only [hb, ↓reduceIte]
      exact ⟨hid, hrun, hpl⟩
    · have hb : (x.id == e'.id) = false := beq_eq_false_iff_ne.mpr hxe
      simp only [hb, Bool.false_eq_true, ↓reduceIte, and_self]

theorem Typed.setExecution (h : Typed τ p s) (wk : s.WellKeyed) {e e' : Execution} (he : e ∈ s.executions)
    (hid : e'.id = e.id) (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (hin : e.input = e'.input)
    (htasks : e'.tasks = e.tasks) : Typed τ p (s.setExecution e') := by
  refine h.of_frame (Keeps.setExecution wk he hid hrun hpl) h.runs h.calls (same_invocations rfl)
    (fun x hx => ?_) (fun r hr => Or.inl hr) (same_taskResults rfl) (fun d hd => Or.inl hd)
  rcases mem_setExecution_executions hx with rfl | hx
  · exact Or.inl ⟨e, he, hrun, hpl, hin, fun tk htk hst => ⟨tk, htasks ▸ htk, rfl, rfl, hst⟩⟩
  · exact Or.inl ⟨x, hx, rfl, rfl, rfl, fun tk htk hst => ⟨tk, htk, rfl, rfl, hst⟩⟩

/-- Updating a task keeps the invariant when a task that becomes ready holds an input of its body's
    input type. -/
theorem Typed.setTask (h : Typed τ p s) (wk : s.WellKeyed) {e : Execution} (he : e ∈ s.executions)
    {ts : TaskState}
    (hready : ts.status = .ready → ∀ c spec, s.concurrencyOf p e = .ok c →
      c.tasks.find? (·.name == ts.name) = some spec →
      ∃ input, p.bodyInput spec.body = some input ∧ τ.Fits ts.input input) :
    Typed τ p (s.setTask e ts) := by
  refine h.of_frame (Keeps.setExecution wk he rfl rfl rfl) h.runs h.calls (same_invocations rfl)
    (fun x hx => ?_) (fun r hr => Or.inl hr) (same_taskResults rfl) (fun d hd => Or.inl hd)
  rcases mem_setTask_executions hx with rfl | hx
  · obtain ⟨c, hc, hfits, htasks⟩ := h.executions e he
    refine Or.inr ⟨c, hc, hfits, fun tk htk hst spec hspec => ?_⟩
    rcases mem_map_replace htk with rfl | htk
    · exact hready hst c spec hc hspec
    · exact htasks tk htk hst spec hspec
  · exact Or.inl ⟨x, hx, rfl, rfl, rfl, fun tk htk hst => ⟨tk, htk, rfl, rfl, hst⟩⟩

theorem Keeps.appendRun {r : Run} : Keeps p s { s with runs := s.runs ++ [r] } where
  workflow {path w} h := by
    obtain ⟨x, hx, hw⟩ := Delivery.workflow?_iff.mp h
    refine Delivery.workflow?_iff.mpr ⟨x, ?_, hw⟩
    unfold State.run? at hx ⊢
    simp [List.find?_append, hx]
  execution e he := ⟨e, he, rfl, rfl, rfl⟩

theorem Typed.appendRun (h : Typed τ p s) {r : Run} (hr : RunTyped τ p r) :
    Typed τ p { s with runs := s.runs ++ [r] } := by
  refine h.of_frame Keeps.appendRun (fun x hx => ?_) h.calls (same_invocations rfl) (same_executions rfl)
    (fun r hr => Or.inl hr) (same_taskResults rfl) (fun d hd => Or.inl hd)
  rcases List.mem_append.mp hx with hx | hx
  · exact h.runs x hx
  · rw [List.mem_singleton.mp hx]
    exact hr

theorem Typed.appendCall (h : Typed τ p s) {c : Call} (hc : CallTyped τ p c) :
    Typed τ p { s with calls := s.calls ++ [c] } where
  runs := h.runs
  invocations := h.invocations
  calls x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.calls x hx
    · rw [List.mem_singleton.mp hx]
      exact hc
  executions := h.executions
  results := h.results
  taskResults := h.taskResults
  deliveries := h.deliveries

theorem Typed.appendInvocation (h : Typed τ p s) {i : Invocation} (hi : InvocationTyped τ p s i) :
    Typed τ p { s with invocations := s.invocations ++ [i] } where
  runs := h.runs
  invocations x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.invocations x hx
    · rw [List.mem_singleton.mp hx]
      exact hi
  calls := h.calls
  executions := h.executions
  results := h.results
  taskResults := h.taskResults
  deliveries := h.deliveries

theorem Keeps.appendExecution {e : Execution} : Keeps p s { s with executions := s.executions ++ [e] } where
  workflow h := h
  execution x hx := ⟨x, List.mem_append_left _ hx, rfl, rfl, rfl⟩

theorem Typed.appendExecution (h : Typed τ p s) {e : Execution} (he : ExecutionTyped τ p s e) :
    Typed τ p { s with executions := s.executions ++ [e] } := by
  refine h.of_frame Keeps.appendExecution h.runs h.calls (same_invocations rfl) (fun x hx => ?_)
    (fun r hr => Or.inl hr) (same_taskResults rfl) (fun d hd => Or.inl hd)
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl ⟨x, hx, rfl, rfl, rfl, fun tk htk hst => ⟨tk, htk, rfl, rfl, hst⟩⟩
  · rw [List.mem_singleton.mp hx]
    exact Or.inr (he.keep Keeps.appendExecution rfl rfl rfl fun tk htk hst => ⟨tk, htk, rfl, rfl, hst⟩)

end Updates

end Suimon.Values
