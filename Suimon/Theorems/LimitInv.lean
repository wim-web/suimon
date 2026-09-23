import Suimon.Theorems.Basic

/-! Invariants of the tasks of concurrency executions (§8.1, §8.2, §8.4), proven for every
    reachable state of every program: a task call or a task run belongs to a task of an existing
    execution that left pending/ready, a running or fetching call belongs to an active task, a task
    never has both a call and a run, and a task result belongs to a task of its execution. They are
    the base of the concurrency-limit proof in `Suimon.Theorems.LimitCount`. -/

namespace Suimon
namespace Limit
open State

/-! ### Lists and records -/

/-- With distinct keys, members with the same key are equal. --/
theorem eq_of_key {α κ : Type} {f : α → κ} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: l, hl, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hl
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'
      exact absurd hab.symm (hl.1 b hb')
    · subst hb'
      exact absurd hab (hl.1 a ha')
    · exact eq_of_key hl.2 ha' hb' hab

theorem mem_setCall_iff {s : State} {c x : Call} (hx : x ∈ (s.setCall c).calls) :
    x = c ∨ (x ∈ s.calls ∧ x.id ≠ c.id) := by
  rw [setCall_calls, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_cases h : y.id = c.id
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h, hy])

theorem mem_setCall_self {s : State} {c y : Call} (hy : y ∈ s.calls) (hid : y.id = c.id) :
    c ∈ (s.setCall c).calls := by
  rw [setCall_calls, List.mem_map]
  exact ⟨y, hy, by simp [hid]⟩

theorem mem_setExecution_iff {s : State} {e x : Execution} (hx : x ∈ (s.setExecution e).executions) :
    x = e ∨ (x ∈ s.executions ∧ x.id ≠ e.id) := by
  rw [setExecution_executions, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_cases h : y.id = e.id
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h, hy])

theorem mem_setExecution_self {s : State} {e y : Execution} (hy : y ∈ s.executions) (hid : y.id = e.id) :
    e ∈ (s.setExecution e).executions := by
  rw [setExecution_executions, List.mem_map]
  exact ⟨y, hy, by simp [hid]⟩

theorem mem_setExecution_of_ne {s : State} {e y : Execution} (hy : y ∈ s.executions) (hid : y.id ≠ e.id) :
    y ∈ (s.setExecution e).executions := by
  rw [setExecution_executions, List.mem_map]
  exact ⟨y, hy, by simp [hid]⟩

/-- A run found by its path is still found after appending a run. --/
theorem run?_append {s : State} {x r : Run} {path : Path} (hr : s.run? path = some r) :
    ({ s with runs := s.runs ++ [x] } : State).run? path = some r := by
  simp only [State.run?, List.find?_append] at hr ⊢
  rw [hr, Option.some_or]

/-- The task `setTask e t` stores in place of `x`. --/
def replaceTask (t x : TaskState) : TaskState := if x.name == t.name then t else x

theorem withTask_tasks' {e : Execution} {t : TaskState} : (withTask e t).tasks = e.tasks.map (replaceTask t) := rfl

@[simp] theorem replaceTask_name {t x : TaskState} : (replaceTask t x).name = x.name := by
  unfold replaceTask
  split <;> simp_all

theorem replaceTask_of_name {t x : TaskState} (h : x.name = t.name) : replaceTask t x = t := by
  simp [replaceTask, h]

theorem replaceTask_of_ne {t x : TaskState} (h : x.name ≠ t.name) : replaceTask t x = x := by
  simp [replaceTask, h]

/-- A task status after pending and ready: the task began, or it ended without beginning. --/
def Begun (st : TaskStatus) : Prop := st ≠ .pending ∧ st ≠ .ready

/-- The task `stop` leaves in place of `t`. --/
def stopTask (t : TaskState) : TaskState :=
  if t.status == .pending || t.status == .ready then { t with status := .notStarted } else t

theorem stopExecution_tasks {e : Execution} : (stopExecution e).tasks = e.tasks.map stopTask := rfl

@[simp] theorem stopTask_name {t : TaskState} : (stopTask t).name = t.name := by
  unfold stopTask
  split <;> rfl

theorem stopTask_of_begun {t : TaskState} (h : Begun t.status) : stopTask t = t := by
  obtain ⟨h1, h2⟩ := h
  simp [stopTask, h1, h2]

theorem stopTask_active {t : TaskState} (h : (stopTask t).status = .active) : t.status = .active := by
  unfold stopTask at h
  split at h
  · simp at h
  · exact h

/-! ### Tasks of executions -/

/-- Execution `id` exists and has a task named `name` whose status satisfies `P`. --/
def TaskHas (P : TaskStatus → Prop) (s : State) (id name : String) : Prop :=
  ∃ e ∈ s.executions, e.id = id ∧ ∃ x ∈ e.tasks, x.name = name ∧ P x.status

namespace TaskHas
variable {P : TaskStatus → Prop} {s t : State} {id name : String}

theorem mono {Q : TaskStatus → Prop} (h : TaskHas P s id name) (hPQ : ∀ st, P st → Q st) :
    TaskHas Q s id name := by
  obtain ⟨e, he, hid, x, hx, hn, hp⟩ := h
  exact ⟨e, he, hid, x, hx, hn, hPQ _ hp⟩

theorem append {x : Execution} (he : t.executions = s.executions ++ [x]) (h : TaskHas P s id name) :
    TaskHas P t id name := by
  obtain ⟨e, he', hid, y, hy, hn, hp⟩ := h
  exact ⟨e, by rw [he]; exact List.mem_append_left _ he', hid, y, hy, hn, hp⟩

theorem setExecution {e e' : Execution} (hids : (s.executions.map (·.id)).Nodup) (he : e ∈ s.executions)
    (hid : e'.id = e.id) (htasks : e'.tasks = e.tasks) (h : TaskHas P s id name) :
    TaskHas P (s.setExecution e') id name := by
  obtain ⟨e2, he2, rfl, y, hy, hn, hp⟩ := h
  by_cases h2 : e2.id = e'.id
  · have : e2 = e := eq_of_key hids he2 he (h2.trans hid)
    subst this
    exact ⟨e', mem_setExecution_self he2 h2, h2.symm, y, by rw [htasks]; exact hy, hn, hp⟩
  · exact ⟨e2, mem_setExecution_of_ne he2 h2, rfl, y, hy, hn, hp⟩

/-- Storing a task keeps every known task, and the stored task where it replaces one. --/
theorem setTask {e : Execution} {ts : TaskState} (hids : (s.executions.map (·.id)).Nodup)
    (he : e ∈ s.executions) (h : TaskHas P s id name) (hP : e.id = id → ts.name = name → P ts.status) :
    TaskHas P (s.setTask e ts) id name := by
  obtain ⟨e2, he2, rfl, y, hy, rfl, hp⟩ := h
  rw [setTask_eq]
  by_cases h2 : e2.id = e.id
  · have : e2 = e := eq_of_key hids he2 he h2
    subst this
    refine ⟨withTask e2 ts, mem_setExecution_self he2 rfl, rfl, replaceTask ts y, ?_, by simp, ?_⟩
    · rw [withTask_tasks']
      exact List.mem_map_of_mem hy
    · by_cases hn : y.name = ts.name
      · rw [replaceTask_of_name hn]
        exact hP rfl hn.symm
      · rw [replaceTask_of_ne hn]
        exact hp
  · exact ⟨e2, mem_setExecution_of_ne he2 h2, rfl, y, hy, rfl, hp⟩

/-- The stored task itself. --/
theorem setTask_self {e : Execution} {ts ts' : TaskState} (he : e ∈ s.executions) (hts : ts ∈ e.tasks)
    (hn : ts.name = name) (hname : ts'.name = ts.name) (hP : P ts'.status) :
    TaskHas P (s.setTask e ts') e.id name := by
  rw [setTask_eq]
  refine ⟨withTask e ts', mem_setExecution_self he rfl, rfl, ts', ?_, hname.trans hn, hP⟩
  rw [withTask_tasks']
  exact List.mem_map.mpr ⟨ts, hts, replaceTask_of_name hname.symm⟩

theorem stop (hP : ∀ x : TaskState, P x.status → P (stopTask x).status) (h : TaskHas P s id name) :
    TaskHas P s.stop id name := by
  obtain ⟨e, he, hid, x, hx, hn, hp⟩ := h
  refine ⟨stopExecution e, mem_stop_executions.mpr ⟨e, he, rfl⟩, hid, stopTask x, ?_, ?_, hP x hp⟩
  · rw [stopExecution_tasks]
    exact List.mem_map_of_mem hx
  · rw [stopTask_name, hn]

end TaskHas

theorem begun_stopTask (x : TaskState) (h : Begun x.status) : Begun (stopTask x).status := by
  rw [stopTask_of_begun h]
  exact h

theorem active_stopTask (x : TaskState) (h : x.status = .active) : (stopTask x).status = .active := by
  rw [stopTask_of_begun (by rw [h]; simp [Begun])]
  exact h

/-! ### The invariant -/

/-- What every reachable state satisfies about task calls, task runs and task results. The
    identities of executions and calls are distinct, same-named tasks of an execution are equal
    (they start equal and `setTask` replaces them together), and a task call is stored under
    `Key.task` of its execution and task. --/
structure Inv (s : State) : Prop where
  execIds : (s.executions.map (·.id)).Nodup
  callIds : (s.calls.map (·.id)).Nodup
  coherent : ∀ e ∈ s.executions, ∀ x ∈ e.tasks, ∀ y ∈ e.tasks, x.name = y.name → x = y
  keys : ∀ c ∈ s.calls, ∀ name, c.task = some name → c.id = Key.task c.owner name
  calls : ∀ c ∈ s.calls, ∀ name, c.task = some name → TaskHas Begun s c.owner name
  runs : ∀ r ∈ s.runs, ∀ o name, r.owner = some o → r.task = some name → TaskHas Begun s o name
  apart : ∀ c ∈ s.calls, ∀ r ∈ s.runs, ∀ name, c.task = some name → r.task = some name →
    r.owner ≠ some c.owner
  active : ∀ c ∈ s.calls, (c.status = .running ∨ c.status = .fetching) → ∀ name, c.task = some name →
    TaskHas (· = .active) s c.owner name
  results : ∀ r ∈ s.taskResults, TaskHas (fun _ => True) s r.execution r.task
  execRuns : ∀ e ∈ s.executions, (s.run? e.run).isSome

namespace Inv
variable {s t : State}

theorem empty : Inv {} :=
  ⟨List.nodup_nil, List.nodup_nil, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-! #### Consequences -/

theorem execution_eq (h : Inv s) {e e' : Execution} (he : e ∈ s.executions) (he' : e' ∈ s.executions)
    (hid : e.id = e'.id) : e = e' :=
  eq_of_key h.execIds he he' hid

/-- Two calls of the same task are the same call. --/
theorem task_call_eq (h : Inv s) {c c' : Call} {name : String} (hc : c ∈ s.calls) (hc' : c' ∈ s.calls)
    (ht : c.task = some name) (ht' : c'.task = some name) (howner : c.owner = c'.owner) : c = c' :=
  eq_of_key h.callIds hc hc' (by rw [h.keys c hc name ht, h.keys c' hc' name ht', howner])

/-- What is known about the task named like `x` in the execution of `e` holds for `x`. --/
theorem status_of (h : Inv s) {P : TaskStatus → Prop} {e : Execution} {x : TaskState}
    (he : e ∈ s.executions) (hx : x ∈ e.tasks) (hh : TaskHas P s e.id x.name) : P x.status := by
  obtain ⟨e2, he2, hid, y, hy, hn, hp⟩ := hh
  have := h.execution_eq he2 he hid
  subst this
  rw [← h.coherent e2 he2 y hy x hx hn]
  exact hp

/-- A task that has not begun has no call. --/
theorem no_call (h : Inv s) {e : Execution} {x : TaskState} (he : e ∈ s.executions) (hx : x ∈ e.tasks)
    (hb : ¬Begun x.status) : ∀ c ∈ s.calls, c.task = some x.name → c.owner ≠ e.id := by
  intro c hc ht hown
  have := h.calls c hc x.name ht
  rw [hown] at this
  exact hb (h.status_of he hx this)

/-- A task that has not begun has no run. --/
theorem no_run (h : Inv s) {e : Execution} {x : TaskState} (he : e ∈ s.executions) (hx : x ∈ e.tasks)
    (hb : ¬Begun x.status) : ∀ r ∈ s.runs, r.task = some x.name → r.owner ≠ some e.id := by
  intro r hr ht hown
  exact hb (h.status_of he hx (h.runs r hr e.id x.name hown ht))

/-! #### Primitive updates -/

/-- The invariant reads only the executions, calls, runs and task results. --/
theorem of_eq (h : Inv s) (hc : t.calls = s.calls) (he : t.executions = s.executions) (hr : t.runs = s.runs)
    (htr : t.taskResults = s.taskResults) : Inv t := by
  cases s
  cases t
  simp only at hc he hr htr
  subst hc he hr htr
  exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10⟩

theorem setCall (h : Inv s) {c c' : Call} (hc : c ∈ s.calls) (hid : c'.id = c.id) (howner : c'.owner = c.owner)
    (htask : c'.task = c.task)
    (hrun : c'.status = .running ∨ c'.status = .fetching → c.status = .running ∨ c.status = .fetching) :
    Inv (s.setCall c') where
  execIds := h.execIds
  callIds := by rw [setCall_calls_map_id]; exact h.callIds
  coherent := h.coherent
  keys := by
    intro x hx name hn
    rcases mem_setCall_calls hx with rfl | hx
    · rw [hid, howner]
      exact h.keys c hc name (htask.symm.trans hn)
    · exact h.keys x hx name hn
  calls := by
    intro x hx name hn
    rcases mem_setCall_calls hx with rfl | hx
    · rw [howner]
      exact h.calls c hc name (htask.symm.trans hn)
    · exact h.calls x hx name hn
  runs := h.runs
  apart := by
    intro x hx r hr name h1 h2
    rcases mem_setCall_calls hx with rfl | hx
    · rw [howner]
      exact h.apart c hc r hr name (htask.symm.trans h1) h2
    · exact h.apart x hx r hr name h1 h2
  active := by
    intro x hx hst name hn
    rcases mem_setCall_calls hx with rfl | hx
    · rw [howner]
      exact h.active c hc (hrun hst) name (htask.symm.trans hn)
    · exact h.active x hx hst name hn
  results := h.results
  execRuns := h.execRuns

/-- Storing a task needs, for a status before beginning, that its task has no call or run, and for
    a status other than active, that its task has no running call. --/
theorem setTask (h : Inv s) {e : Execution} {ts : TaskState} (he : e ∈ s.executions)
    (hcalls : ¬Begun ts.status → ∀ c ∈ s.calls, c.task = some ts.name → c.owner ≠ e.id)
    (hruns : ¬Begun ts.status → ∀ r ∈ s.runs, r.task = some ts.name → r.owner ≠ some e.id)
    (hactive : ts.status ≠ .active → ∀ c ∈ s.calls, (c.status = .running ∨ c.status = .fetching) →
      c.task = some ts.name → c.owner ≠ e.id) :
    Inv (s.setTask e ts) where
  execIds := by rw [setTask_executions_map_id]; exact h.execIds
  callIds := h.callIds
  coherent := by
    intro e' he' x hx y hy hxy
    rw [setTask_eq] at he'
    rcases mem_setExecution_iff he' with rfl | ⟨he', -⟩
    · rw [withTask_tasks', List.mem_map] at hx hy
      obtain ⟨x0, hx0, rfl⟩ := hx
      obtain ⟨y0, hy0, rfl⟩ := hy
      simp only [replaceTask_name] at hxy
      rw [h.coherent e he x0 hx0 y0 hy0 hxy]
    · exact h.coherent e' he' x hx y hy hxy
  keys := h.keys
  calls := fun c hc name hn => (h.calls c hc name hn).setTask h.execIds he fun hid hname =>
    Classical.byContradiction fun hb => hcalls hb c hc (by rw [hname]; exact hn) hid.symm
  runs := fun r hr o name ho hn => (h.runs r hr o name ho hn).setTask h.execIds he fun hid hname =>
    Classical.byContradiction fun hb => hruns hb r hr (by rw [hname]; exact hn) (by rw [hid]; exact ho)
  apart := h.apart
  active := fun c hc hst name hn => (h.active c hc hst name hn).setTask h.execIds he fun hid hname =>
    Classical.byContradiction fun hb => hactive hb c hc hst (by rw [hname]; exact hn) hid.symm
  results := fun r hr => (h.results r hr).setTask h.execIds he fun _ _ => trivial
  execRuns := by
    intro e' he'
    rw [setTask_eq] at he'
    rcases mem_setExecution_iff he' with rfl | ⟨he', -⟩
    · exact h.execRuns e he
    · exact h.execRuns e' he'

theorem stop (h : Inv s) : Inv s.stop where
  execIds := by rw [stop_executions_map_id]; exact h.execIds
  callIds := by rw [stop_calls_map_id]; exact h.callIds
  coherent := by
    intro e' he' x hx y hy hxy
    obtain ⟨e, he, rfl⟩ := mem_stop_executions.mp he'
    rw [stopExecution_tasks, List.mem_map] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨y0, hy0, rfl⟩ := hy
    simp only [stopTask_name] at hxy
    rw [h.coherent e he x0 hx0 y0 hy0 hxy]
  keys := by
    intro c hc name hn
    obtain ⟨c0, hc0, rfl⟩ := mem_stop_calls.mp hc
    simp only [stopCall_id, stopCall_owner, stopCall_task] at hn ⊢
    exact h.keys c0 hc0 name hn
  calls := by
    intro c hc name hn
    obtain ⟨c0, hc0, rfl⟩ := mem_stop_calls.mp hc
    simp only [stopCall_owner, stopCall_task] at hn ⊢
    exact (h.calls c0 hc0 name hn).stop begun_stopTask
  runs := fun r hr o name ho hn => (h.runs r hr o name ho hn).stop begun_stopTask
  apart := by
    intro c hc r hr name h1 h2
    obtain ⟨c0, hc0, rfl⟩ := mem_stop_calls.mp hc
    simp only [stopCall_owner, stopCall_task] at h1 ⊢
    exact h.apart c0 hc0 r hr name h1 h2
  active := by
    intro c hc hst
    have := stop_calls_quiet hc
    rcases hst with hst | hst
    · exact absurd hst this.1
    · exact absurd hst this.2
  results := fun r hr => (h.results r hr).stop fun _ _ => trivial
  execRuns := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := mem_stop_executions.mp he'
    exact h.execRuns e he

theorem fail (h : Inv s) {f : Failure} {policy : Policy} : Inv (s.fail f policy) := by
  have h' : Inv { s with failures := s.failures ++ [f] } := h.of_eq rfl rfl rfl rfl
  cases policy
  · exact h'.stop
  · exact h'

theorem appendCall (h : Inv s) {x : Call} (hc : t.calls = s.calls ++ [x]) (he : t.executions = s.executions)
    (hr : t.runs = s.runs) (htr : t.taskResults = s.taskResults) (hfresh : x.id ∉ s.calls.map (·.id))
    (hkey : ∀ name, x.task = some name → x.id = Key.task x.owner name)
    (hbegun : ∀ name, x.task = some name → TaskHas Begun s x.owner name)
    (hapart : ∀ name, x.task = some name → ∀ r ∈ s.runs, r.task = some name → r.owner ≠ some x.owner)
    (hactive : x.status = .running ∨ x.status = .fetching → ∀ name, x.task = some name →
      TaskHas (· = .active) s x.owner name) :
    Inv t := by
  refine Inv.of_eq (s := { s with calls := s.calls ++ [x] }) ?_ hc he hr htr
  exact {
    execIds := h.execIds
    callIds := nodup_map_append_singleton h.callIds hfresh
    coherent := h.coherent
    keys := by
      intro c hc name hn
      rcases List.mem_append.mp hc with hc | hc
      · exact h.keys c hc name hn
      · obtain rfl := List.mem_singleton.mp hc
        exact hkey name hn
    calls := by
      intro c hc name hn
      rcases List.mem_append.mp hc with hc | hc
      · exact h.calls c hc name hn
      · obtain rfl := List.mem_singleton.mp hc
        exact hbegun name hn
    runs := h.runs
    apart := by
      intro c hc r hr name h1 h2
      rcases List.mem_append.mp hc with hc | hc
      · exact h.apart c hc r hr name h1 h2
      · obtain rfl := List.mem_singleton.mp hc
        exact hapart name h1 r hr h2
    active := by
      intro c hc hst name hn
      rcases List.mem_append.mp hc with hc | hc
      · exact h.active c hc hst name hn
      · obtain rfl := List.mem_singleton.mp hc
        exact hactive hst name hn
    results := h.results
    execRuns := h.execRuns }

theorem appendRun (h : Inv s) {x : Run} (hc : t.calls = s.calls) (he : t.executions = s.executions)
    (hr : t.runs = s.runs ++ [x]) (htr : t.taskResults = s.taskResults)
    (hruns : ∀ o name, x.owner = some o → x.task = some name → TaskHas Begun s o name)
    (hapart : ∀ name, x.task = some name → ∀ c ∈ s.calls, c.task = some name → x.owner ≠ some c.owner) :
    Inv t := by
  refine Inv.of_eq (s := { s with runs := s.runs ++ [x] }) ?_ hc he hr htr
  exact {
    execIds := h.execIds
    callIds := h.callIds
    coherent := h.coherent
    keys := h.keys
    calls := h.calls
    runs := by
      intro r hr o name ho hn
      rcases List.mem_append.mp hr with hr | hr
      · exact h.runs r hr o name ho hn
      · obtain rfl := List.mem_singleton.mp hr
        exact hruns o name ho hn
    apart := by
      intro c hc r hr name h1 h2
      rcases List.mem_append.mp hr with hr | hr
      · exact h.apart c hc r hr name h1 h2
      · obtain rfl := List.mem_singleton.mp hr
        exact hapart name h2 c hc h1
    active := h.active
    results := h.results
    execRuns := by
      intro e he
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (h.execRuns e he)
      rw [run?_append hr]
      rfl }

theorem appendExecution (h : Inv s) {x : Execution} (hc : t.calls = s.calls)
    (he : t.executions = s.executions ++ [x]) (hr : t.runs = s.runs) (htr : t.taskResults = s.taskResults)
    (hfresh : x.id ∉ s.executions.map (·.id)) (hcoh : ∀ a ∈ x.tasks, ∀ b ∈ x.tasks, a.name = b.name → a = b)
    (hrun : (s.run? x.run).isSome) : Inv t := by
  have hs : ({ s with executions := s.executions ++ [x] } : State).executions = s.executions ++ [x] := rfl
  refine Inv.of_eq (s := { s with executions := s.executions ++ [x] }) ?_ hc he hr htr
  exact {
    execIds := nodup_map_append_singleton h.execIds hfresh
    callIds := h.callIds
    coherent := by
      intro e he a ha b hb hab
      rcases List.mem_append.mp he with he | he
      · exact h.coherent e he a ha b hb hab
      · obtain rfl := List.mem_singleton.mp he
        exact hcoh a ha b hb hab
    keys := h.keys
    calls := fun c hc name hn => (h.calls c hc name hn).append hs
    runs := fun r hr o name ho hn => (h.runs r hr o name ho hn).append hs
    apart := h.apart
    active := fun c hc hst name hn => (h.active c hc hst name hn).append hs
    results := fun r hr => (h.results r hr).append hs
    execRuns := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact h.execRuns e he
      · obtain rfl := List.mem_singleton.mp he
        exact hrun }

theorem setExecution (h : Inv s) {e e' : Execution} (he : e ∈ s.executions) (hid : e'.id = e.id)
    (htasks : e'.tasks = e.tasks) (hrun : e'.run = e.run) : Inv (s.setExecution e') where
  execIds := by rw [setExecution_executions_map_id]; exact h.execIds
  callIds := h.callIds
  coherent := by
    intro e2 he2 x hx y hy hxy
    rcases mem_setExecution_iff he2 with rfl | ⟨he2, -⟩
    · rw [htasks] at hx hy
      exact h.coherent e he x hx y hy hxy
    · exact h.coherent e2 he2 x hx y hy hxy
  keys := h.keys
  calls := fun c hc name hn => (h.calls c hc name hn).setExecution h.execIds he hid htasks
  runs := fun r hr o name ho hn => (h.runs r hr o name ho hn).setExecution h.execIds he hid htasks
  apart := h.apart
  active := fun c hc hst name hn => (h.active c hc hst name hn).setExecution h.execIds he hid htasks
  results := fun r hr => (h.results r hr).setExecution h.execIds he hid htasks
  execRuns := by
    intro e2 he2
    rcases mem_setExecution_iff he2 with rfl | ⟨he2, -⟩
    · rw [hrun]
      exact h.execRuns e he
    · exact h.execRuns e2 he2

theorem setRun (h : Inv s) {r r' : Run} (hr : r ∈ s.runs) (howner : r'.owner = r.owner) (htask : r'.task = r.task) :
    Inv (s.setRun r') where
  execIds := h.execIds
  callIds := h.callIds
  coherent := h.coherent
  keys := h.keys
  calls := h.calls
  runs := by
    intro x hx o name ho hn
    rcases mem_setRun_runs hx with rfl | hx
    · exact h.runs r hr o name (howner.symm.trans ho) (htask.symm.trans hn)
    · exact h.runs x hx o name ho hn
  apart := by
    intro c hc x hx name h1 h2
    rcases mem_setRun_runs hx with rfl | hx
    · rw [howner]
      exact h.apart c hc r hr name h1 (htask.symm.trans h2)
    · exact h.apart c hc x hx name h1 h2
  active := h.active
  results := h.results
  execRuns := by
    intro e he
    rw [run?_setRun]
    split
    · simpa using h.execRuns e he
    · exact h.execRuns e he

theorem setTaskResult (h : Inv s) {r : TaskResult} : Inv (s.setTaskResult r) where
  execIds := h.execIds
  callIds := h.callIds
  coherent := h.coherent
  keys := h.keys
  calls := h.calls
  runs := h.runs
  apart := h.apart
  active := h.active
  results := by
    intro x hx
    rw [setTaskResult_taskResults, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    split
    · rename_i hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨h1, h2⟩, -⟩ := hm
      rw [← h1, ← h2]
      exact h.results y hy
    · exact h.results y hy
  execRuns := h.execRuns

theorem appendTaskResult (h : Inv s) {r : TaskResult} (hc : t.calls = s.calls) (he : t.executions = s.executions)
    (hr : t.runs = s.runs) (htr : t.taskResults = s.taskResults ++ [r])
    (hres : TaskHas (fun _ => True) s r.execution r.task) : Inv t := by
  refine Inv.of_eq (s := { s with taskResults := s.taskResults ++ [r] }) ?_ hc he hr htr
  exact {
    execIds := h.execIds
    callIds := h.callIds
    coherent := h.coherent
    keys := h.keys
    calls := h.calls
    runs := h.runs
    apart := h.apart
    active := h.active
    results := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h.results x hx
      · obtain rfl := List.mem_singleton.mp hx
        exact hres
    execRuns := h.execRuns }

/-! #### Composite updates -/

theorem accept (h : Inv s) {c : Call} {index : Nat} {value : Value} {arm : Option String} (hc : c ∈ s.calls)
    (ha : s.accept c index value arm = .ok t) : Inv t := by
  rcases accept_eq_ok.mp ha with ⟨-, _, -, -, rfl⟩ | ⟨name, hname, -, rfl⟩
  · exact h.of_eq rfl rfl rfl rfl
  · exact h.appendTaskResult rfl rfl rfl rfl ((h.calls c hc name hname).mono fun _ _ => trivial)

/-- Once `c'` replaces the task call `c`, it is the only call of that task. --/
theorem quiet_of_setCall {c c' : Call} (h : Inv (s.setCall c')) (hc : c ∈ s.calls) (hid : c'.id = c.id)
    (howner : c'.owner = c.owner) (htask : c'.task = c.task)
    (hq : c'.status ≠ .running ∧ c'.status ≠ .fetching) :
    ∀ name, c.task = some name → ∀ c2 ∈ (s.setCall c').calls, c2.task = some name → c2.owner = c.owner →
      c2.status ≠ .running ∧ c2.status ≠ .fetching := by
  intro name hname c2 hc2 ht2 ho2
  rw [h.task_call_eq hc2 (mem_setCall_self hc hid.symm) ht2 (htask.trans hname) (ho2.trans howner.symm)]
  exact hq

theorem settleOwner (h : Inv s) {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (hquiet : ∀ name, c.task = some name → ∀ c2 ∈ s.calls, c2.task = some name → c2.owner = c.owner →
      c2.status ≠ .running ∧ c2.status ≠ .fetching)
    (hbegun : Begun task) (ho : s.settleOwner c inv task = .ok t) : Inv t := by
  rcases settleOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨name, e, ts, hname, he, hts, rfl⟩
  · exact h.of_eq rfl rfl rfl rfl
  · have he' := execution?_eq_some he
    have hts' := find?_key_eq_some hts
    refine h.setTask he'.1 (fun hb => absurd hbegun hb) (fun hb => absurd hbegun hb) ?_
    intro _ c2 hc2 hst ht2 ho2
    have := hquiet name hname c2 hc2 (by rw [ht2]; simp [hts'.2]) (ho2.trans he'.2)
    rcases hst with hst | hst
    · exact this.1 hst
    · exact this.2 hst

theorem cancelOwner (h : Inv s) {c : Call}
    (hquiet : ∀ name, c.task = some name → ∀ c2 ∈ s.calls, c2.task = some name → c2.owner = c.owner →
      c2.status ≠ .running ∧ c2.status ≠ .fetching)
    (ho : s.cancelOwner c = .ok t) : Inv t := by
  rcases cancelOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨name, e, ts, hname, he, hts, rfl⟩
  · split
    · exact h.of_eq rfl rfl rfl rfl
    · exact h
  · split
    · have he' := execution?_eq_some he
      have hts' := find?_key_eq_some hts
      refine h.setTask he'.1 (fun hb => absurd (by simp [Begun]) hb) (fun hb => absurd (by simp [Begun]) hb) ?_
      intro _ c2 hc2 hst ht2 ho2
      have := hquiet name hname c2 hc2 (by rw [ht2]; simp [hts'.2]) (ho2.trans he'.2)
      rcases hst with hst | hst
      · exact this.1 hst
      · exact this.2 hst
    · exact h

theorem failCall (h : Inv s) {c : Call} {status : CallStatus} {cause : Cause} (hc : c ∈ s.calls)
    (hst : status ≠ .running ∧ status ≠ .fetching) (hf : s.failCall c status cause = .ok t) : Inv t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  have h1 := h.setCall (c' := { c with status }) hc rfl rfl rfl fun hr => by
    rcases hr with hr | hr
    · exact absurd hr hst.1
    · exact absurd hr hst.2
  exact (h1.settleOwner (h1.quiet_of_setCall hc rfl rfl rfl hst) (by simp [Begun]) hso).fail

end Inv

/-! ### Every step keeps the invariant -/

theorem step_inv {p : Program} {s t : State} {op : Op} (h : Inv s) (h0 : s = {} ∨ s.started = true)
    (hs : step p s op = .ok t) : Inv t := by
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h0 with rfl | h0
    · exact ⟨List.nodup_nil, List.nodup_nil, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp⟩
    · simp [h0] at hst
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨f, decl, -, -, hc, rfl⟩ | ⟨judge, arms, -, hc, rfl⟩ | ⟨wf, out, -, -, rfl⟩ |
      ⟨c, -, he, rfl⟩
    · exact h.appendCall rfl rfl rfl rfl (call?_eq_none_iff.mp hc) (by simp) (by simp) (by simp) (by simp)
    · exact h.appendCall rfl rfl rfl rfl (call?_eq_none_iff.mp hc) (by simp) (by simp) (by simp) (by simp)
    · exact h.appendRun rfl rfl rfl rfl (by simp) (by simp)
    · refine h.appendExecution rfl rfl rfl rfl (execution?_eq_none_iff.mp he) ?_ (by simp [hr])
      intro a ha b hb hab
      simp only [List.mem_map] at ha hb
      obtain ⟨a0, -, rfl⟩ := ha
      obtain ⟨b0, -, rfl⟩ := hb
      simp only at hab ⊢
      rw [hab]
  | fetch id =>
    obtain ⟨-, -, c, hc, -, hst, rfl⟩ := Step.fetch_inv hs
    exact h.setCall (call?_eq_some hc).1 rfl rfl rfl fun _ => Or.inl hst
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have hcs := (call?_eq_some hc).1
    have hcs' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact hcs
    have h1 := (h.accept hcs hacc).setCall (c' := { c with status := .returned }) hcs' rfl rfl rfl (by simp)
    exact h1.settleOwner (h1.quiet_of_setCall hcs' rfl rfl rfl (by simp)) (by simp [Begun]) hso
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hcs := (call?_eq_some hc).1
    have hcs' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact hcs
    exact ((h.accept hcs hacc).setCall (c' := { c with status := .returned }) hcs' rfl rfl rfl (by simp)).of_eq
      rfl rfl rfl rfl
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, hst, hacc, rfl⟩ := Step.yielded_inv hs
    have hcs := (call?_eq_some hc).1
    have hcs' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact hcs
    exact (h.accept hcs hacc).setCall hcs' rfl rfl rfl fun _ => Or.inr hst
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    have hcs := (call?_eq_some hc).1
    have h1 := h.setCall (c' := { c with status := .returned }) hcs rfl rfl rfl (by simp)
    exact h1.settleOwner (h1.quiet_of_setCall hcs rfl rfl rfl (by simp)) (by simp [Begun]) hso
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact h.failCall (call?_eq_some hc).1 (by simp) hf
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    exact h.failCall (call?_eq_some hc).1 (by simp) hf
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact h.failCall (call?_eq_some hc).1 (by simp) hf
    · have hcs := (call?_eq_some hc).1
      have h1 := h.setCall (c' := { c with status := .cancelled }) hcs rfl rfl rfl (by simp)
      exact h1.cancelOwner (h1.quiet_of_setCall hcs rfl rfl rfl (by simp)) ho
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    have hcs := (call?_eq_some hc).1
    have h1 := h.setCall (c' := { c with status := .cancelled }) hcs rfl rfl rfl (by simp)
    exact h1.cancelOwner (h1.quiet_of_setCall hcs rfl rfl rfl (by simp)) ho
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact h.of_eq rfl rfl rfl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    refine Inv.fail ?_
    exact h.of_eq rfl rfl rfl rfl
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    have he' := (execution?_eq_some he).1
    have hts' := (find?_key_eq_some hts).1
    have hnb : ¬Begun ts.status := by simp [Begun, hpend]
    exact h.setTask he' (fun _ => h.no_call (x := ts) he' hts' hnb) (fun _ => h.no_run (x := ts) he' hts' hnb)
      fun _ c hc _ => h.no_call (x := ts) he' hts' hnb c hc
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, hts, hpend, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    have he' := (execution?_eq_some he).1
    have hts' := (find?_key_eq_some hts).1
    have hnb : ¬Begun ts.status := by simp [Begun, hpend]
    exact (h.setTask (ts := { ts with status := .failed }) he' (fun hb => absurd (by simp [Begun]) hb)
      (fun hb => absurd (by simp [Begun]) hb) fun _ c hc _ => h.no_call (x := ts) he' hts' hnb c hc).fail
  | beginTask eid name =>
    obtain ⟨-, -, e, c, ts, spec, he, -, -, hts, hready, -, -, hcases⟩ := Step.beginTask_inv hs
    have he' := (execution?_eq_some he).1
    obtain ⟨hts', hname⟩ := find?_key_eq_some hts
    have hnb : ¬Begun ts.status := by simp [Begun, hready]
    have h1 := h.setTask (ts := { ts with status := .active }) he' (fun hb => absurd (by simp [Begun]) hb)
      (fun hb => absurd (by simp [Begun]) hb) fun hna => absurd rfl hna
    have hact : ∀ {P : TaskStatus → Prop}, P .active →
        TaskHas P (s.setTask e { ts with status := .active }) e.id name := fun hP =>
      TaskHas.setTask_self he' hts' hname rfl hP
    rcases hcases with ⟨f, decl, -, -, hcall, rfl⟩ | ⟨wf, out, -, -, rfl⟩
    · refine h1.appendCall rfl rfl rfl rfl (call?_eq_none_iff.mp hcall) ?_ ?_ ?_ ?_
      · intro n hn
        cases hn
        rfl
      · intro n hn
        cases hn
        exact hact (by simp [Begun])
      · intro n hn r hr hrt
        cases hn
        exact h.no_run he' hts' hnb r hr (by rw [hname]; exact hrt)
      · intro _ n hn
        cases hn
        exact hact rfl
    · refine h1.appendRun rfl rfl rfl rfl ?_ ?_
      · intro o n ho hn
        cases ho
        cases hn
        exact hact (by simp [Begun])
      · intro n hn c' hc' hct hown
        cases hn
        exact h.no_call he' hts' hnb c' hc' (by rw [hname]; exact hct) (Option.some.inj hown).symm
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact h.setTaskResult.of_eq rfl rfl rfl rfl
    · exact h.setTaskResult
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact h.setTaskResult.fail
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact h.of_eq rfl rfl rfl rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    have h1 := h.setExecution (e' := { e with complete := true }) (execution?_eq_some he).1 rfl rfl rfl
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact h1.of_eq rfl rfl rfl rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, -, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    have hrs := (run?_eq_some hr).1
    have h1 := h.setRun (r' := { r with complete := true }) hrs rfl rfl
    rcases hcases with ⟨-, _, -, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h1.of_eq rfl rfl rfl rfl
    · have he' := execution?_eq_some he
      obtain ⟨hts', hname⟩ := find?_key_eq_some hts
      -- A task with a run has no call, so its status may change.
      have hq : ∀ st : TaskStatus, st ≠ .active → ∀ c ∈ (s.setRun { r with complete := true }).calls,
          (c.status = .running ∨ c.status = .fetching) → c.task = some ({ ts with status := st } : TaskState).name →
          c.owner ≠ e.id := by
        intro st _ c hc _ hct hown
        exact h.apart c hc r hrs name (by rw [hct]; simp [hname]) htask (by rw [howner, hown, he'.2])
      have step : ∀ st : TaskStatus, Begun st → st ≠ .active →
          Inv ((s.setRun { r with complete := true }).setTask e { ts with status := st }) := fun st hb hna =>
        h1.setTask he'.1 (fun hnb => absurd hb hnb) (fun hnb => absurd hb hnb) fun _ => hq st hna
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine (step .succeeded (by simp [Begun]) (by simp)).appendTaskResult rfl rfl rfl rfl ?_
        exact TaskHas.setTask_self (P := fun _ => True) (s := s.setRun { r with complete := true }) he'.1 hts'
          hname rfl trivial
      · exact step .skipped (by simp [Begun]) (by simp)
      · exact step .failed (by simp [Begun]) (by simp)
      · exact step .upstreamFailed (by simp [Begun]) (by simp)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact h.stop.of_eq rfl rfl rfl rfl
    · exact h.of_eq rfl rfl rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact (h.setRun (r' := { r with complete := true }) (run?_eq_some hr).1 rfl rfl).of_eq rfl rfl rfl rfl
    · exact h.of_eq rfl rfl rfl rfl

theorem reachable_inv {p : Program} {s : State} (h : Reachable p s) : Inv s := by
  induction h with
  | empty => exact Inv.empty
  | step op hr hs ih => exact step_inv ih hr.eq_empty_or_started hs

end Limit
end Suimon
