import Suimon.Step

/-! Reusable lemmas about the building blocks of the operational rules in `Suimon/Step.lean`: the
    `Except` combinators, lookups by key, and the state updates `setRun`, `setInvocation`, `setCall`,
    `setExecution`, `setTask`, `setTaskResult`, `stop`, `endUnfinished` and `fail`. -/

namespace Suimon

section Monads
variable {ε α β : Type}

@[simp] theorem bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

@[simp] theorem pure_eq_ok {a b : α} : (pure a : Except ε α) = .ok b ↔ b = a := by
  simp [pure, Except.pure, eq_comm]

@[simp] theorem map_eq_ok {x : Except ε α} {f : α → β} {b : β} :
    (f <$> x) = .ok b ↔ ∃ a, x = .ok a ∧ b = f a := by
  cases x <;> simp [Functor.map, Except.map, eq_comm]

@[simp] theorem throw_eq_ok {e : ε} {b : α} : (throw e : Except ε α) = .ok b ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw]

@[simp] theorem require_eq_ok {c : Bool} {code : String} {u : Unit} : require c code = .ok u ↔ c = true := by
  cases c <;> simp [require]

@[simp] theorem need_eq_ok {o : Option α} {code : String} {v : α} : need o code = .ok v ↔ o = some v := by
  cases o with
  | none => simp [need]
  | some a => simp only [need, pure_eq_ok, Option.some.injEq]; exact eq_comm

@[simp] theorem exists_unit_iff {P : Unit → Prop} : (∃ u, P u) ↔ P () :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

theorem option_bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp [bind, Option.bind]

theorem option_guard_eq_some {c : Prop} [Decidable c] {u : Unit} : (guard c : Option Unit) = some u ↔ c := by
  by_cases hc : c <;> simp [hc, guard, failure, pure]

end Monads

section Lists
variable {α β κ : Type}

theorem find?_key_eq_none_iff [BEq κ] [LawfulBEq κ] {l : List α} {f : α → κ} {k : κ} :
    l.find? (fun x => f x == k) = none ↔ k ∉ l.map f := by
  simp [List.find?_eq_none]

theorem find?_key_eq_some [BEq κ] [LawfulBEq κ] {l : List α} {f : α → κ} {k : κ} {x : α}
    (h : l.find? (fun x => f x == k) = some x) : x ∈ l ∧ f x = k :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- With unique keys, the lookup by the key of a member finds that member. --/
theorem find?_key_of_mem [BEq κ] [LawfulBEq κ] {l : List α} {f : α → κ} {x : α} (hl : (l.map f).Nodup)
    (hx : x ∈ l) : l.find? (fun y => f y == f x) = some x := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hl
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : f y ≠ f x := fun h => hl.1 x hx h.symm
      simp [hne, ih hl.2 hx]

/-- With unique keys, a lookup whose predicate selects exactly the key of a member finds that member. --/
theorem find?_eq_some_of_nodup {l : List α} {f : α → κ} {P : α → Bool} {x : α} (hl : (l.map f).Nodup)
    (hx : x ∈ l) (hP : ∀ y, P y = true ↔ f y = f x) : l.find? P = some x := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hl
    rcases List.mem_cons.mp hx with rfl | hx
    · have hPx : P x = true := (hP x).mpr rfl
      simp [hPx]
    · have hne : P y = false := by
        rw [Bool.eq_false_iff]
        intro h
        exact hl.1 x hx ((hP y).mp h).symm
      simp [hne, ih hl.2 hx]

/-- A key found in a list is found in any list whose keys extend it. --/
theorem find?_key_isSome_of_prefix [BEq κ] [LawfulBEq κ] {l l' : List α} {f : α → κ} {k : κ}
    (hp : l.map f <+: l'.map f) (h : (l.find? fun x => f x == k).isSome) : (l'.find? fun x => f x == k).isSome := by
  have hk : k ∈ l.map f := by
    cases hfind : l.find? (fun x => f x == k) with
    | none => simp [hfind] at h
    | some x =>
      obtain ⟨hx, hfx⟩ := find?_key_eq_some hfind
      exact List.mem_map.mpr ⟨x, hx, hfx⟩
  have hk' : k ∈ l'.map f := hp.subset hk
  cases hfind : l'.find? (fun x => f x == k) with
  | none => exact absurd hk' (find?_key_eq_none_iff.mp hfind)
  | some _ => rfl

theorem nodup_map_append_singleton {l : List α} {f : α → κ} {x : α} (hl : (l.map f).Nodup)
    (hx : f x ∉ l.map f) : ((l ++ [x]).map f).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hl, by simp, ?_⟩
  intro a ha b hb
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  exact fun h => hx (h ▸ ha)

/-- Replacing elements by one with the same key keeps the keys. --/
theorem map_replace_map {l : List α} {p : α → Bool} {y : α} {f : α → β}
    (h : ∀ x, p x = true → f y = f x) : (l.map fun x => if p x then y else x).map f = l.map f := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  by_cases hx : p x = true
  · simp [hx, h x hx]
  · simp [hx]

theorem mem_map_replace {l : List α} {p : α → Bool} {y z : α} (h : z ∈ l.map fun x => if p x then y else x) :
    z = y ∨ z ∈ l := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  by_cases hp : p x = true
  · simp [hp]
  · simp [hp, hx]

/-- A lookup by key after replacing the element with the key of `y`. --/
theorem find?_map_replace_key [BEq κ] [LawfulBEq κ] [DecidableEq κ] {l : List α} {f : α → κ} {y : α} {k : κ} :
    (l.map fun x => if f x == f y then y else x).find? (fun x => f x == k) =
      if f y = k then (l.find? fun x => f x == k).map fun _ => y else l.find? fun x => f x == k := by
  rw [List.find?_map]
  have hp : ((fun x => f x == k) ∘ fun x => if f x == f y then y else x) = fun x => f x == k := by
    funext x
    by_cases hx : f x = f y
    · simp [hx]
    · simp [hx]
  rw [hp]
  cases hfind : l.find? (fun x => f x == k) with
  | none => simp
  | some x =>
    have hx : f x = k := by simpa using List.find?_some hfind
    by_cases hy : f y = k
    · simp [hy, hx]
    · have : f x ≠ f y := fun h => hy (h ▸ hx)
      simp [hy, this]

end Lists

theorem Workflow.placement?_eq_some {w : Workflow} {name : String} {pl : Placement}
    (h : w.placement? name = some pl) : pl ∈ w.placements ∧ pl.name = name :=
  find?_key_eq_some h

theorem Definition.workflow?_eq_some {p : Definition} {id : String} {w : Workflow} (h : p.workflow? id = some w) :
    w ∈ p.workflows ∧ w.id = id :=
  find?_key_eq_some h

namespace State
variable {s : State}

/-! ### Freshness and lookups -/

theorem run?_eq_none_iff {path : Path} : s.run? path = none ↔ path ∉ s.runs.map (·.path) :=
  find?_key_eq_none_iff
theorem invocation?_eq_none_iff {id : String} : s.invocation? id = none ↔ id ∉ s.invocations.map (·.id) :=
  find?_key_eq_none_iff
theorem call?_eq_none_iff {id : String} : s.call? id = none ↔ id ∉ s.calls.map (·.id) :=
  find?_key_eq_none_iff
theorem execution?_eq_none_iff {id : String} : s.execution? id = none ↔ id ∉ s.executions.map (·.id) :=
  find?_key_eq_none_iff
theorem result?_eq_none_iff {id : ResultId} : s.result? id = none ↔ id ∉ s.results.map (·.id) :=
  find?_key_eq_none_iff

theorem settled?_eq_none_iff {path : Path} {name : String} :
    s.settled? path name = none ↔ (path, name) ∉ s.settled.map fun x => (x.run, x.placement) := by
  simp [settled?, List.find?_eq_none]

theorem delivery?_eq_none_iff {path : Path} {index : Nat} {source : ResultId} :
    s.delivery? path index source = none ↔
      (path, index, source) ∉ s.deliveries.map fun d => (d.run, d.connection, d.source) := by
  simp [delivery?, List.find?_eq_none, and_assoc]

theorem any_taskResult_key_eq_false_iff {l : List TaskResult} {execution task : String} {index : Nat} :
    (l.any fun x => x.execution == execution && x.task == task && x.index == index) = false ↔
      (execution, task, index) ∉ l.map fun x => (x.execution, x.task, x.index) := by
  simp [and_assoc]

theorem run?_eq_some {path : Path} {r : Run} (h : s.run? path = some r) : r ∈ s.runs ∧ r.path = path :=
  find?_key_eq_some h
theorem invocation?_eq_some {id : String} {i : Invocation} (h : s.invocation? id = some i) :
    i ∈ s.invocations ∧ i.id = id :=
  find?_key_eq_some h
theorem call?_eq_some {id : String} {c : Call} (h : s.call? id = some c) : c ∈ s.calls ∧ c.id = id :=
  find?_key_eq_some h
theorem execution?_eq_some {id : String} {e : Execution} (h : s.execution? id = some e) :
    e ∈ s.executions ∧ e.id = id :=
  find?_key_eq_some h
theorem result?_eq_some {id : ResultId} {r : Result} (h : s.result? id = some r) : r ∈ s.results ∧ r.id = id :=
  find?_key_eq_some h

theorem settled?_eq_some {path : Path} {name : String} {x : Settled} (h : s.settled? path name = some x) :
    x ∈ s.settled ∧ x.run = path ∧ x.placement = name := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  simpa using List.find?_some h

theorem delivery?_eq_some {path : Path} {index : Nat} {source : ResultId} {d : Delivery}
    (h : s.delivery? path index source = some d) :
    d ∈ s.deliveries ∧ d.run = path ∧ d.connection = index ∧ d.source = source := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  simpa [and_assoc] using List.find?_some h

/-! ### `setRun` -/

section setRun
variable {r : Run}
@[simp] theorem setRun_status : (s.setRun r).status = s.status := rfl
@[simp] theorem setRun_started : (s.setRun r).started = s.started := rfl
@[simp] theorem setRun_cancelled : (s.setRun r).cancelled = s.cancelled := rfl
@[simp] theorem setRun_invocations : (s.setRun r).invocations = s.invocations := rfl
@[simp] theorem setRun_calls : (s.setRun r).calls = s.calls := rfl
@[simp] theorem setRun_executions : (s.setRun r).executions = s.executions := rfl
@[simp] theorem setRun_results : (s.setRun r).results = s.results := rfl
@[simp] theorem setRun_taskResults : (s.setRun r).taskResults = s.taskResults := rfl
@[simp] theorem setRun_deliveries : (s.setRun r).deliveries = s.deliveries := rfl
@[simp] theorem setRun_settled : (s.setRun r).settled = s.settled := rfl
@[simp] theorem setRun_failures : (s.setRun r).failures = s.failures := rfl
theorem setRun_runs : (s.setRun r).runs = s.runs.map fun x => if x.path == r.path then r else x := rfl
@[simp] theorem setRun_runs_map_path : (s.setRun r).runs.map (·.path) = s.runs.map (·.path) := by
  apply map_replace_map
  intro _ h
  exact (beq_iff_eq.mp h).symm
@[simp] theorem setRun_runs_length : (s.setRun r).runs.length = s.runs.length := List.length_map ..
theorem mem_setRun_runs {x : Run} (h : x ∈ (s.setRun r).runs) : x = r ∨ x ∈ s.runs := mem_map_replace h
theorem run?_setRun {path : Path} :
    (s.setRun r).run? path = if r.path = path then (s.run? path).map fun _ => r else s.run? path :=
  find?_map_replace_key
end setRun

/-! ### `setInvocation` -/

section setInvocation
variable {i : Invocation}
@[simp] theorem setInvocation_status : (s.setInvocation i).status = s.status := rfl
@[simp] theorem setInvocation_started : (s.setInvocation i).started = s.started := rfl
@[simp] theorem setInvocation_cancelled : (s.setInvocation i).cancelled = s.cancelled := rfl
@[simp] theorem setInvocation_runs : (s.setInvocation i).runs = s.runs := rfl
@[simp] theorem setInvocation_calls : (s.setInvocation i).calls = s.calls := rfl
@[simp] theorem setInvocation_executions : (s.setInvocation i).executions = s.executions := rfl
@[simp] theorem setInvocation_results : (s.setInvocation i).results = s.results := rfl
@[simp] theorem setInvocation_taskResults : (s.setInvocation i).taskResults = s.taskResults := rfl
@[simp] theorem setInvocation_deliveries : (s.setInvocation i).deliveries = s.deliveries := rfl
@[simp] theorem setInvocation_settled : (s.setInvocation i).settled = s.settled := rfl
@[simp] theorem setInvocation_failures : (s.setInvocation i).failures = s.failures := rfl
theorem setInvocation_invocations :
    (s.setInvocation i).invocations = s.invocations.map fun x => if x.id == i.id then i else x := rfl
@[simp] theorem setInvocation_invocations_map_id :
    (s.setInvocation i).invocations.map (·.id) = s.invocations.map (·.id) := by
  apply map_replace_map
  intro _ h
  exact (beq_iff_eq.mp h).symm
@[simp] theorem setInvocation_invocations_length :
    (s.setInvocation i).invocations.length = s.invocations.length := List.length_map ..
theorem mem_setInvocation_invocations {x : Invocation} (h : x ∈ (s.setInvocation i).invocations) :
    x = i ∨ x ∈ s.invocations := mem_map_replace h
theorem invocation?_setInvocation {id : String} :
    (s.setInvocation i).invocation? id = if i.id = id then (s.invocation? id).map fun _ => i else s.invocation? id :=
  find?_map_replace_key
end setInvocation

/-! ### `setCall` -/

section setCall
variable {c : Call}
@[simp] theorem setCall_status : (s.setCall c).status = s.status := rfl
@[simp] theorem setCall_started : (s.setCall c).started = s.started := rfl
@[simp] theorem setCall_cancelled : (s.setCall c).cancelled = s.cancelled := rfl
@[simp] theorem setCall_runs : (s.setCall c).runs = s.runs := rfl
@[simp] theorem setCall_invocations : (s.setCall c).invocations = s.invocations := rfl
@[simp] theorem setCall_executions : (s.setCall c).executions = s.executions := rfl
@[simp] theorem setCall_results : (s.setCall c).results = s.results := rfl
@[simp] theorem setCall_taskResults : (s.setCall c).taskResults = s.taskResults := rfl
@[simp] theorem setCall_deliveries : (s.setCall c).deliveries = s.deliveries := rfl
@[simp] theorem setCall_settled : (s.setCall c).settled = s.settled := rfl
@[simp] theorem setCall_failures : (s.setCall c).failures = s.failures := rfl
theorem setCall_calls : (s.setCall c).calls = s.calls.map fun x => if x.id == c.id then c else x := rfl
@[simp] theorem setCall_calls_map_id : (s.setCall c).calls.map (·.id) = s.calls.map (·.id) := by
  apply map_replace_map
  intro _ h
  exact (beq_iff_eq.mp h).symm
@[simp] theorem setCall_calls_length : (s.setCall c).calls.length = s.calls.length := List.length_map ..
theorem mem_setCall_calls {x : Call} (h : x ∈ (s.setCall c).calls) : x = c ∨ x ∈ s.calls := mem_map_replace h
theorem call?_setCall {id : String} :
    (s.setCall c).call? id = if c.id = id then (s.call? id).map fun _ => c else s.call? id :=
  find?_map_replace_key
end setCall

/-! ### `setExecution` and `setTask` -/

section setExecution
variable {e : Execution}
@[simp] theorem setExecution_status : (s.setExecution e).status = s.status := rfl
@[simp] theorem setExecution_started : (s.setExecution e).started = s.started := rfl
@[simp] theorem setExecution_cancelled : (s.setExecution e).cancelled = s.cancelled := rfl
@[simp] theorem setExecution_runs : (s.setExecution e).runs = s.runs := rfl
@[simp] theorem setExecution_invocations : (s.setExecution e).invocations = s.invocations := rfl
@[simp] theorem setExecution_calls : (s.setExecution e).calls = s.calls := rfl
@[simp] theorem setExecution_results : (s.setExecution e).results = s.results := rfl
@[simp] theorem setExecution_taskResults : (s.setExecution e).taskResults = s.taskResults := rfl
@[simp] theorem setExecution_deliveries : (s.setExecution e).deliveries = s.deliveries := rfl
@[simp] theorem setExecution_settled : (s.setExecution e).settled = s.settled := rfl
@[simp] theorem setExecution_failures : (s.setExecution e).failures = s.failures := rfl
theorem setExecution_executions :
    (s.setExecution e).executions = s.executions.map fun x => if x.id == e.id then e else x := rfl
@[simp] theorem setExecution_executions_map_id :
    (s.setExecution e).executions.map (·.id) = s.executions.map (·.id) := by
  apply map_replace_map
  intro _ h
  exact (beq_iff_eq.mp h).symm
@[simp] theorem setExecution_executions_length :
    (s.setExecution e).executions.length = s.executions.length := List.length_map ..
theorem mem_setExecution_executions {x : Execution} (h : x ∈ (s.setExecution e).executions) :
    x = e ∨ x ∈ s.executions := mem_map_replace h
theorem execution?_setExecution {id : String} :
    (s.setExecution e).execution? id = if e.id = id then (s.execution? id).map fun _ => e else s.execution? id :=
  find?_map_replace_key
end setExecution

section setTask
variable {e : Execution} {t : TaskState}
/-- The execution `setTask e t` stores. --/
def withTask (e : Execution) (t : TaskState) : Execution :=
  { e with tasks := e.tasks.map fun x => if x.name == t.name then t else x }
theorem setTask_eq : s.setTask e t = s.setExecution (withTask e t) := rfl
@[simp] theorem withTask_id : (withTask e t).id = e.id := rfl
@[simp] theorem withTask_run : (withTask e t).run = e.run := rfl
@[simp] theorem withTask_placement : (withTask e t).placement = e.placement := rfl
@[simp] theorem withTask_input : (withTask e t).input = e.input := rfl
@[simp] theorem withTask_complete : (withTask e t).complete = e.complete := rfl
theorem withTask_tasks : (withTask e t).tasks = e.tasks.map fun x => if x.name == t.name then t else x := rfl
@[simp] theorem setTask_status : (s.setTask e t).status = s.status := rfl
@[simp] theorem setTask_started : (s.setTask e t).started = s.started := rfl
@[simp] theorem setTask_cancelled : (s.setTask e t).cancelled = s.cancelled := rfl
@[simp] theorem setTask_runs : (s.setTask e t).runs = s.runs := rfl
@[simp] theorem setTask_invocations : (s.setTask e t).invocations = s.invocations := rfl
@[simp] theorem setTask_calls : (s.setTask e t).calls = s.calls := rfl
@[simp] theorem setTask_results : (s.setTask e t).results = s.results := rfl
@[simp] theorem setTask_taskResults : (s.setTask e t).taskResults = s.taskResults := rfl
@[simp] theorem setTask_deliveries : (s.setTask e t).deliveries = s.deliveries := rfl
@[simp] theorem setTask_settled : (s.setTask e t).settled = s.settled := rfl
@[simp] theorem setTask_failures : (s.setTask e t).failures = s.failures := rfl
@[simp] theorem setTask_executions_map_id : (s.setTask e t).executions.map (·.id) = s.executions.map (·.id) :=
  setExecution_executions_map_id
@[simp] theorem setTask_executions_length : (s.setTask e t).executions.length = s.executions.length :=
  setExecution_executions_length
theorem mem_setTask_executions {x : Execution} (h : x ∈ (s.setTask e t).executions) :
    x = withTask e t ∨ x ∈ s.executions := mem_setExecution_executions h
theorem execution?_setTask {id : String} :
    (s.setTask e t).execution? id = if e.id = id then (s.execution? id).map fun _ => withTask e t else s.execution? id :=
  execution?_setExecution
end setTask

/-! ### `setTaskResult` -/

section setTaskResult
variable {r : TaskResult}
@[simp] theorem setTaskResult_status : (s.setTaskResult r).status = s.status := rfl
@[simp] theorem setTaskResult_started : (s.setTaskResult r).started = s.started := rfl
@[simp] theorem setTaskResult_cancelled : (s.setTaskResult r).cancelled = s.cancelled := rfl
@[simp] theorem setTaskResult_runs : (s.setTaskResult r).runs = s.runs := rfl
@[simp] theorem setTaskResult_invocations : (s.setTaskResult r).invocations = s.invocations := rfl
@[simp] theorem setTaskResult_calls : (s.setTaskResult r).calls = s.calls := rfl
@[simp] theorem setTaskResult_executions : (s.setTaskResult r).executions = s.executions := rfl
@[simp] theorem setTaskResult_results : (s.setTaskResult r).results = s.results := rfl
@[simp] theorem setTaskResult_deliveries : (s.setTaskResult r).deliveries = s.deliveries := rfl
@[simp] theorem setTaskResult_settled : (s.setTaskResult r).settled = s.settled := rfl
@[simp] theorem setTaskResult_failures : (s.setTaskResult r).failures = s.failures := rfl
theorem setTaskResult_taskResults :
    (s.setTaskResult r).taskResults = s.taskResults.map fun x =>
      if x.execution == r.execution && x.task == r.task && x.index == r.index then r else x := rfl
@[simp] theorem setTaskResult_taskResults_map_key :
    (s.setTaskResult r).taskResults.map (fun x => (x.execution, x.task, x.index)) =
      s.taskResults.map (fun x => (x.execution, x.task, x.index)) :=
  map_replace_map fun _ h => by simp only [Bool.and_eq_true, beq_iff_eq] at h; simp [h]
@[simp] theorem setTaskResult_taskResults_length :
    (s.setTaskResult r).taskResults.length = s.taskResults.length := List.length_map ..
theorem mem_setTaskResult_taskResults {x : TaskResult} (h : x ∈ (s.setTaskResult r).taskResults) :
    x = r ∨ x ∈ s.taskResults := mem_map_replace h
end setTaskResult

/-! ### `stop` -/

section stop
@[simp] theorem stop_status : s.stop.status = .stopping := rfl
@[simp] theorem stop_started : s.stop.started = s.started := rfl
@[simp] theorem stop_cancelled : s.stop.cancelled = s.cancelled := rfl
@[simp] theorem stop_runs : s.stop.runs = s.runs := rfl
@[simp] theorem stop_invocations : s.stop.invocations = s.invocations := rfl
@[simp] theorem stop_results : s.stop.results = s.results := rfl
@[simp] theorem stop_taskResults : s.stop.taskResults = s.taskResults := rfl
@[simp] theorem stop_deliveries : s.stop.deliveries = s.deliveries := rfl
@[simp] theorem stop_settled : s.stop.settled = s.settled := rfl
@[simp] theorem stop_failures : s.stop.failures = s.failures := rfl

/-- The call `stop` leaves in place of `c`. --/
def stopCall (c : Call) : Call :=
  if c.status == .running || c.status == .fetching then { c with status := .cancelling } else c

/-- The execution `stop` leaves in place of `e`. --/
def stopExecution (e : Execution) : Execution :=
  { e with tasks := e.tasks.map fun t =>
      if t.status == .pending || t.status == .ready then { t with status := .notStarted } else t }

theorem stop_calls : s.stop.calls = s.calls.map stopCall := rfl
theorem stop_executions : s.stop.executions = s.executions.map stopExecution := rfl

@[simp] theorem stopCall_id {c : Call} : (stopCall c).id = c.id := by
  unfold stopCall; split <;> rfl
@[simp] theorem stopCall_owner {c : Call} : (stopCall c).owner = c.owner := by
  unfold stopCall; split <;> rfl
@[simp] theorem stopCall_task {c : Call} : (stopCall c).task = c.task := by
  unfold stopCall; split <;> rfl

theorem stopCall_status {c : Call} :
    (stopCall c).status = if c.status = .running ∨ c.status = .fetching then .cancelling else c.status := by
  unfold stopCall
  by_cases h : c.status = .running ∨ c.status = .fetching
  · simp [h]
  · have h' : (c.status == .running || c.status == .fetching) = false := by simpa using h
    simp [h', h]

/-- After the stop no call is running or fetching. --/
theorem stopCall_quiet (c : Call) : (stopCall c).status ≠ .running ∧ (stopCall c).status ≠ .fetching := by
  rw [stopCall_status]
  by_cases h : c.status = .running ∨ c.status = .fetching
  · simp [h]
  · simp only [h, ite_false]
    exact not_or.mp h

@[simp] theorem stopExecution_id {e : Execution} : (stopExecution e).id = e.id := rfl
@[simp] theorem stopExecution_run {e : Execution} : (stopExecution e).run = e.run := rfl
@[simp] theorem stopExecution_placement {e : Execution} : (stopExecution e).placement = e.placement := rfl
@[simp] theorem stopExecution_complete {e : Execution} : (stopExecution e).complete = e.complete := rfl

@[simp] theorem stop_calls_map_id : s.stop.calls.map (·.id) = s.calls.map (·.id) := by
  simp [stop_calls, Function.comp_def]
@[simp] theorem stop_calls_length : s.stop.calls.length = s.calls.length := List.length_map ..
@[simp] theorem stop_executions_map_id : s.stop.executions.map (·.id) = s.executions.map (·.id) := by
  simp [stop_executions, Function.comp_def]
@[simp] theorem stop_executions_length : s.stop.executions.length = s.executions.length := List.length_map ..

theorem mem_stop_calls {c : Call} : c ∈ s.stop.calls ↔ ∃ c' ∈ s.calls, stopCall c' = c := List.mem_map
theorem mem_stop_executions {e : Execution} : e ∈ s.stop.executions ↔ ∃ e' ∈ s.executions, stopExecution e' = e :=
  List.mem_map

theorem stop_calls_quiet {c : Call} (h : c ∈ s.stop.calls) : c.status ≠ .running ∧ c.status ≠ .fetching := by
  obtain ⟨c', _, rfl⟩ := mem_stop_calls.mp h
  exact stopCall_quiet c'

theorem call?_stop {id : String} : s.stop.call? id = (s.call? id).map stopCall := by
  simp only [call?, stop_calls, List.find?_map]
  have : ((fun x : Call => x.id == id) ∘ stopCall) = fun x => x.id == id := by funext c; simp
  rw [this]

theorem execution?_stop {id : String} : s.stop.execution? id = (s.execution? id).map stopExecution := by
  simp only [execution?, stop_executions, List.find?_map]
  rfl
end stop

/-! ### `endUnfinished` -/

section endUnfinished
@[simp] theorem endUnfinished_status : s.endUnfinished.status = s.status := rfl
@[simp] theorem endUnfinished_started : s.endUnfinished.started = s.started := rfl
@[simp] theorem endUnfinished_cancelled : s.endUnfinished.cancelled = s.cancelled := rfl
@[simp] theorem endUnfinished_runs : s.endUnfinished.runs = s.runs := rfl
@[simp] theorem endUnfinished_calls : s.endUnfinished.calls = s.calls := rfl
@[simp] theorem endUnfinished_results : s.endUnfinished.results = s.results := rfl
@[simp] theorem endUnfinished_taskResults : s.endUnfinished.taskResults = s.taskResults := rfl
@[simp] theorem endUnfinished_deliveries : s.endUnfinished.deliveries = s.deliveries := rfl
@[simp] theorem endUnfinished_settled : s.endUnfinished.settled = s.settled := rfl
@[simp] theorem endUnfinished_failures : s.endUnfinished.failures = s.failures := rfl

/-- The execution `endUnfinished` leaves in place of `e`. --/
def endExecution (e : Execution) : Execution := { e with tasks := e.tasks.map endTask }

theorem endUnfinished_invocations : s.endUnfinished.invocations = s.invocations.map endInvocation := rfl
theorem endUnfinished_executions : s.endUnfinished.executions = s.executions.map endExecution := rfl

section
variable {i : Invocation}
@[simp] theorem endInvocation_id : (endInvocation i).id = i.id := by unfold endInvocation; split <;> rfl
@[simp] theorem endInvocation_run : (endInvocation i).run = i.run := by unfold endInvocation; split <;> rfl
@[simp] theorem endInvocation_placement : (endInvocation i).placement = i.placement := by
  unfold endInvocation; split <;> rfl
@[simp] theorem endInvocation_trigger : (endInvocation i).trigger = i.trigger := by
  unfold endInvocation; split <;> rfl
@[simp] theorem endInvocation_input : (endInvocation i).input = i.input := by unfold endInvocation; split <;> rfl
@[simp] theorem endInvocation_arm : (endInvocation i).arm = i.arm := by unfold endInvocation; split <;> rfl

theorem endInvocation_status :
    (endInvocation i).status = if i.status = .active then .cancelled else i.status := by
  unfold endInvocation
  by_cases h : i.status = .active <;> simp [h]

theorem endInvocation_of_ne (h : i.status ≠ .active) : endInvocation i = i := by simp [endInvocation, h]

/-- No invocation is active after the conclusion. --/
theorem endInvocation_status_ne : (endInvocation i).status ≠ .active := by
  rw [endInvocation_status]
  split <;> simp_all
end

section
variable {t : TaskState}
@[simp] theorem endTask_name : (endTask t).name = t.name := by unfold endTask; split <;> (try split) <;> rfl
@[simp] theorem endTask_input : (endTask t).input = t.input := by unfold endTask; split <;> (try split) <;> rfl

theorem endTask_status : (endTask t).status =
    if t.status = .active then .cancelled
    else if t.status = .pending ∨ t.status = .ready then .notStarted else t.status := by
  unfold endTask
  by_cases h : t.status = .active
  · simp [h]
  · by_cases h' : t.status = .pending ∨ t.status = .ready
    · rcases h' with h' | h' <;> simp [h']
    · have h'' : (t.status == .pending || t.status == .ready) = false := by simpa using h'
      simp [h, h'', h']

theorem endTask_of_ended (h : t.status.ended = true) : endTask t = t := by
  cases t with
  | mk name input status => cases status <;> simp_all [endTask, TaskStatus.ended]

theorem endTask_status_ne_active : (endTask t).status ≠ .active := by
  rw [endTask_status]
  split
  · simp
  · split
    · simp
    · assumption

/-- Every task has ended after the conclusion. --/
theorem endTask_ended : (endTask t).status.ended = true := by
  rw [endTask_status]
  split
  · rfl
  · split
    · rfl
    · rename_i h h'
      cases hs : t.status <;> simp_all [TaskStatus.ended]
end

section
variable {e : Execution}
@[simp] theorem endExecution_id : (endExecution e).id = e.id := rfl
@[simp] theorem endExecution_run : (endExecution e).run = e.run := rfl
@[simp] theorem endExecution_placement : (endExecution e).placement = e.placement := rfl
@[simp] theorem endExecution_input : (endExecution e).input = e.input := rfl
@[simp] theorem endExecution_complete : (endExecution e).complete = e.complete := rfl
theorem endExecution_tasks : (endExecution e).tasks = e.tasks.map endTask := rfl
end

@[simp] theorem endUnfinished_invocations_map_id :
    s.endUnfinished.invocations.map (·.id) = s.invocations.map (·.id) := by
  simp [endUnfinished_invocations, Function.comp_def]
@[simp] theorem endUnfinished_invocations_length : s.endUnfinished.invocations.length = s.invocations.length :=
  List.length_map ..
@[simp] theorem endUnfinished_executions_map_id :
    s.endUnfinished.executions.map (·.id) = s.executions.map (·.id) := by
  simp [endUnfinished_executions, Function.comp_def]
@[simp] theorem endUnfinished_executions_length : s.endUnfinished.executions.length = s.executions.length :=
  List.length_map ..

theorem mem_endUnfinished_invocations {i : Invocation} :
    i ∈ s.endUnfinished.invocations ↔ ∃ i' ∈ s.invocations, endInvocation i' = i := List.mem_map
theorem mem_endUnfinished_executions {e : Execution} :
    e ∈ s.endUnfinished.executions ↔ ∃ e' ∈ s.executions, endExecution e' = e := List.mem_map

theorem invocation?_endUnfinished {id : String} :
    s.endUnfinished.invocation? id = (s.invocation? id).map endInvocation := by
  simp only [invocation?, endUnfinished_invocations, List.find?_map]
  have : ((fun x : Invocation => x.id == id) ∘ endInvocation) = fun x => x.id == id := by funext i; simp
  rw [this]

theorem execution?_endUnfinished {id : String} :
    s.endUnfinished.execution? id = (s.execution? id).map endExecution := by
  simp only [execution?, endUnfinished_executions, List.find?_map]
  rfl

/-- When every call has ended, as the conclusion after a stop requires, none is running or fetching. --/
theorem calls_quiet_of_ended (h : s.calls.all (·.status.ended) = true) :
    ∀ c ∈ s.calls, c.status ≠ .running ∧ c.status ≠ .fetching := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  cases hst : c.status <;> simp_all [CallStatus.ended]

theorem run?_endUnfinished {path : Path} : s.endUnfinished.run? path = s.run? path := rfl
theorem call?_endUnfinished {id : String} : s.endUnfinished.call? id = s.call? id := rfl
theorem result?_endUnfinished {id : ResultId} : s.endUnfinished.result? id = s.result? id := rfl
theorem settled?_endUnfinished {path : Path} {name : String} :
    s.endUnfinished.settled? path name = s.settled? path name := rfl
end endUnfinished

/-! ### `fail` -/

section fail
variable {f : Failure} {policy : Policy}
@[simp] theorem fail_stop : s.fail f .stop = { s with failures := s.failures ++ [f] }.stop := rfl
@[simp] theorem fail_continue : s.fail f .continue = { s with failures := s.failures ++ [f] } := rfl
@[simp] theorem fail_started : (s.fail f policy).started = s.started := by cases policy <;> rfl
@[simp] theorem fail_cancelled : (s.fail f policy).cancelled = s.cancelled := by cases policy <;> rfl
@[simp] theorem fail_runs : (s.fail f policy).runs = s.runs := by cases policy <;> rfl
@[simp] theorem fail_invocations : (s.fail f policy).invocations = s.invocations := by cases policy <;> rfl
@[simp] theorem fail_results : (s.fail f policy).results = s.results := by cases policy <;> rfl
@[simp] theorem fail_taskResults : (s.fail f policy).taskResults = s.taskResults := by cases policy <;> rfl
@[simp] theorem fail_deliveries : (s.fail f policy).deliveries = s.deliveries := by cases policy <;> rfl
@[simp] theorem fail_settled : (s.fail f policy).settled = s.settled := by cases policy <;> rfl
@[simp] theorem fail_failures : (s.fail f policy).failures = s.failures ++ [f] := by cases policy <;> rfl
@[simp] theorem fail_calls_map_id : (s.fail f policy).calls.map (·.id) = s.calls.map (·.id) := by
  cases policy <;> simp
@[simp] theorem fail_executions_map_id : (s.fail f policy).executions.map (·.id) = s.executions.map (·.id) := by
  cases policy <;> simp
theorem fail_status : (s.fail f policy).status = if policy = .stop then .stopping else s.status := by
  cases policy <;> rfl
theorem fail_status_of_running (h : s.status = .running) :
    (s.fail f policy).status = .running ∨ (s.fail f policy).status = .stopping := by
  cases policy <;> simp [h]
end fail

end State

end Suimon
