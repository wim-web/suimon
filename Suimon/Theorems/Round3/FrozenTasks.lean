import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## Helpers for [15] Round3/Frozen.lean — task E3: tasks and executions

Two invariants of reachable states describe finished tasks: a complete execution has ended all its
tasks (`DoneTasks`), and a task whose run is open is active (`RunTasks`). With them, a step keeps
every ended task and every complete execution unchanged (`step_good`). The step lemma is assembled
from the state updates the rules use, each described by `Good`. -/

namespace FrozenAux

/-- A complete execution has ended all its tasks: `closeExecution` checks it, and ended tasks stay. -/
def DoneTasks (s : State) : Prop :=
  ∀ e ∈ s.executions, e.complete = true → ∀ tk ∈ e.tasks, tk.status.ended = true

/-- A task whose run is open is active: only `closeRun` of that run ends the task. -/
def RunTasks (s : State) : Prop :=
  ∀ r ∈ s.runs, r.complete = false → ∀ name, r.task = some name → ∀ e ∈ s.executions, r.owner = some e.id →
    ∀ tk ∈ e.tasks, tk.name = name → tk.status = .active

/-- What an update does to executions: ended tasks and complete executions whose tasks ended stay,
    and both invariants are kept. -/
structure Good (s t : State) : Prop where
  tasks : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status.ended = true →
    ∃ e' ∈ t.executions, e'.id = e.id ∧ tk ∈ e'.tasks
  done : ∀ e ∈ s.executions, e.complete = true → (∀ tk ∈ e.tasks, tk.status.ended = true) → e ∈ t.executions
  doneTasks : DoneTasks s → DoneTasks t
  runTasks : RunTasks s → RunTasks t

theorem begun_of_ended {st : TaskStatus} (h : st.ended = true) : Limit.Begun st := by
  cases st <;> simp_all [TaskStatus.ended, Limit.Begun]

theorem stopTask_of_ended {tk : TaskState} (h : tk.status.ended = true) : Limit.stopTask tk = tk :=
  Limit.stopTask_of_begun (begun_of_ended h)

/-- The stop leaves an execution whose tasks ended as it is. -/
theorem stopExecution_of_ended {e : Execution} (h : ∀ tk ∈ e.tasks, tk.status.ended = true) :
    stopExecution e = e := by
  have htasks : e.tasks.map Limit.stopTask = e.tasks := by
    have : e.tasks.map Limit.stopTask = e.tasks.map id :=
      List.map_congr_left fun tk htk => stopTask_of_ended (h tk htk)
    rw [this, List.map_id]
  have : (stopExecution e).tasks = e.tasks := by rw [Limit.stopExecution_tasks, htasks]
  cases e
  simp only [stopExecution] at this ⊢
  rw [this]

theorem mem_setTask_of_ne {s : State} {e x : Execution} {ts : TaskState} (hx : x ∈ s.executions) (hid : x.id ≠ e.id) :
    x ∈ (s.setTask e ts).executions :=
  Limit.mem_setExecution_of_ne hx (by simpa using hid)

theorem eq_of_mem_setTask {s : State} {e x : Execution} {ts : TaskState} (hx : x ∈ (s.setTask e ts).executions)
    (hid : x.id = e.id) : x = withTask e ts := by
  rcases Limit.mem_setExecution_iff hx with h | ⟨-, hne⟩
  · exact h
  · exact absurd hid (by simpa using hne)

namespace Good
variable {s t u : State}

theorem trans (h₁ : Good s u) (h₂ : Good u t) : Good s t where
  tasks e he tk htk hend := by
    obtain ⟨e', he', hid, htk'⟩ := h₁.tasks e he tk htk hend
    obtain ⟨e'', he'', hid', htk''⟩ := h₂.tasks e' he' tk htk' hend
    exact ⟨e'', he'', hid'.trans hid, htk''⟩
  done e he hc hall := h₂.done e (h₁.done e he hc hall) hc hall
  doneTasks h := h₂.doneTasks (h₁.doneTasks h)
  runTasks h := h₂.runTasks (h₁.runTasks h)

/-- Updates that keep runs and executions. -/
theorem of_eq (hr : t.runs = s.runs) (he : t.executions = s.executions) : Good s t where
  tasks e he' tk htk _ := ⟨e, by rw [he]; exact he', rfl, htk⟩
  done e he' _ _ := by rw [he]; exact he'
  doneTasks h := by
    intro e he' hc tk htk
    rw [he] at he'
    exact h e he' hc tk htk
  runTasks h := by
    intro r hr' hc name hn e he' ho tk htk hname
    rw [hr] at hr'
    rw [he] at he'
    exact h r hr' hc name hn e he' ho tk htk hname

theorem stop : Good s s.stop where
  tasks e he tk htk hend := ⟨stopExecution e, State.mem_stop_executions.mpr ⟨e, he, rfl⟩, rfl, by
    rw [Limit.stopExecution_tasks]
    exact List.mem_map.mpr ⟨tk, htk, stopTask_of_ended hend⟩⟩
  done e he _ hall := State.mem_stop_executions.mpr ⟨e, he, stopExecution_of_ended hall⟩
  doneTasks h := by
    intro e he hc tk htk
    obtain ⟨e₀, he₀, rfl⟩ := State.mem_stop_executions.mp he
    rw [Limit.stopExecution_tasks, List.mem_map] at htk
    obtain ⟨tk₀, htk₀, rfl⟩ := htk
    have hend := h e₀ he₀ (by simpa using hc) tk₀ htk₀
    rw [stopTask_of_ended hend]
    exact hend
  runTasks h := by
    intro r hr hc name hn e he ho tk htk hname
    obtain ⟨e₀, he₀, rfl⟩ := State.mem_stop_executions.mp he
    rw [Limit.stopExecution_tasks, List.mem_map] at htk
    obtain ⟨tk₀, htk₀, rfl⟩ := htk
    have := h r (by simpa using hr) hc name hn e₀ he₀ (by simpa using ho) tk₀ htk₀ (by simpa using hname)
    exact Limit.active_stopTask tk₀ this

theorem fail {f : Failure} {policy : Policy} : Good s (s.fail f policy) := by
  cases policy
  · show Good s ({ s with failures := s.failures ++ [f] } : State).stop
    exact Good.trans (u := { s with failures := s.failures ++ [f] }) (of_eq rfl rfl) stop
  · exact of_eq rfl rfl

theorem then_fail {f : Failure} {policy : Policy} (h : Good s u) : Good s (u.fail f policy) := h.trans fail

/-- An update after one that keeps runs and executions. -/
theorem pre (h : Good u t) (hr : u.runs = s.runs) (he : u.executions = s.executions) : Good s t :=
  (of_eq hr he).trans h

/-- A task changes from a status that has not ended: every task of that name has that status (the
    tasks of an execution are coherent), and the task has no open run unless it becomes active. -/
theorem setTask {e : Execution} {ts ts' : TaskState} (he : e ∈ s.executions)
    (ids : (s.executions.map (·.id)).Nodup) (hts : ts ∈ e.tasks) (hname : ts'.name = ts.name)
    (hsame : ∀ x ∈ e.tasks, x.name = ts.name → x = ts) (hne : ts.status.ended = false)
    (hdone : e.complete = true → ts'.status.ended = true)
    (hrun : ts'.status = .active ∨ ∀ R ∈ s.runs, R.complete = false → R.owner = some e.id → R.task ≠ some ts.name) :
    Good s (s.setTask e ts') where
  tasks x hx tk htk hend := by
    by_cases hid : x.id = e.id
    · obtain rfl : x = e := Limit.eq_of_key ids hx he hid
      refine ⟨withTask x ts', Delivery.mem_setTask_self hx, rfl, ?_⟩
      rw [Limit.withTask_tasks']
      refine List.mem_map.mpr ⟨tk, htk, Limit.replaceTask_of_ne fun h => ?_⟩
      rw [hsame tk htk (h.trans hname), hne] at hend
      cases hend
    · exact ⟨x, mem_setTask_of_ne hx hid, rfl, htk⟩
  done x hx _ hall := by
    by_cases hid : x.id = e.id
    · obtain rfl : x = e := Limit.eq_of_key ids hx he hid
      rw [hall ts hts] at hne
      cases hne
    · exact mem_setTask_of_ne hx hid
  doneTasks h := by
    intro x hx hc tk htk
    rcases State.mem_setTask_executions hx with rfl | hx
    · simp only [withTask_complete] at hc
      rw [Limit.withTask_tasks', List.mem_map] at htk
      obtain ⟨y, hy, rfl⟩ := htk
      by_cases hy' : y.name = ts'.name
      · rw [Limit.replaceTask_of_name hy']
        exact hdone hc
      · rw [Limit.replaceTask_of_ne hy']
        exact h e he hc y hy
    · exact h x hx hc tk htk
  runTasks h := by
    intro r hr hc name hn x hx ho tk htk hname'
    rcases State.mem_setTask_executions hx with rfl | hx
    · rw [Limit.withTask_tasks', List.mem_map] at htk
      obtain ⟨y, hy, rfl⟩ := htk
      by_cases hy' : y.name = ts'.name
      · rw [Limit.replaceTask_of_name hy'] at hname' ⊢
        rcases hrun with hact | hrun
        · exact hact
        · exact absurd (by rw [hn, ← hname', hname]) (hrun r hr hc ho)
      · rw [Limit.replaceTask_of_ne hy'] at hname' ⊢
        exact h r hr hc name hn e he ho y hy hname'
    · exact h r hr hc name hn x hx ho tk htk hname'

/-- `closeExecution` completes an execution whose tasks ended. -/
theorem complete {e : Execution} (he : e ∈ s.executions) (ids : (s.executions.map (·.id)).Nodup)
    (hopen : e.complete = false) (hended : ∀ tk ∈ e.tasks, tk.status.ended = true) :
    Good s (s.setExecution { e with complete := true }) where
  tasks x hx tk htk _ := by
    by_cases hid : x.id = e.id
    · obtain rfl : x = e := Limit.eq_of_key ids hx he hid
      exact ⟨{ x with complete := true }, Limit.mem_setExecution_self hx rfl, rfl, htk⟩
    · exact ⟨x, Limit.mem_setExecution_of_ne hx hid, rfl, htk⟩
  done x hx hc _ := by
    by_cases hid : x.id = e.id
    · obtain rfl : x = e := Limit.eq_of_key ids hx he hid
      rw [hopen] at hc
      cases hc
    · exact Limit.mem_setExecution_of_ne hx hid
  doneTasks h := by
    intro x hx hc tk htk
    rcases Limit.mem_setExecution_iff hx with rfl | ⟨hx, -⟩
    · exact hended tk htk
    · exact h x hx hc tk htk
  runTasks h := by
    intro r hr hc name hn x hx ho tk htk hname
    rcases Limit.mem_setExecution_iff hx with rfl | ⟨hx, -⟩
    · exact h r hr hc name hn e he ho tk htk hname
    · exact h r hr hc name hn x hx ho tk htk hname

/-- A run completes. -/
theorem completeRun {r : Run} : Good s (s.setRun { r with complete := true }) where
  tasks e he tk htk _ := ⟨e, he, rfl, htk⟩
  done e he _ _ := he
  doneTasks h := h
  runTasks h := by
    intro x hx hc name hn e he ho tk htk hname
    rcases State.mem_setRun_runs hx with rfl | hx
    · cases hc
    · exact h x hx hc name hn e he ho tk htk hname

/-- A run is added: the root, a sub-workflow run, or the run of a task that became active. -/
theorem appendRun {x : Run} (hr : t.runs = s.runs ++ [x]) (he : t.executions = s.executions)
    (hx : x.complete = false → ∀ name, x.task = some name → ∀ e ∈ s.executions, x.owner = some e.id →
      ∀ tk ∈ e.tasks, tk.name = name → tk.status = .active) : Good s t where
  tasks e he' tk htk _ := ⟨e, by rw [he]; exact he', rfl, htk⟩
  done e he' _ _ := by rw [he]; exact he'
  doneTasks h := by
    intro e he' hc tk htk
    rw [he] at he'
    exact h e he' hc tk htk
  runTasks h := by
    intro R hR hc name hn e he' ho tk htk hname
    rw [he] at he'
    rw [hr] at hR
    rcases List.mem_append.mp hR with hR | hR
    · exact h R hR hc name hn e he' ho tk htk hname
    · obtain rfl := List.mem_singleton.mp hR
      exact hx hc name hn e he' ho tk htk hname

/-- An execution is added, open, and no open task run claims it yet. -/
theorem appendExecution {x : Execution} (hr : t.runs = s.runs) (he : t.executions = s.executions ++ [x])
    (hopen : x.complete = false)
    (hfree : ∀ R ∈ s.runs, R.complete = false → ∀ name, R.task = some name → R.owner ≠ some x.id) : Good s t where
  tasks e he' tk htk _ := ⟨e, by rw [he]; exact List.mem_append_left _ he', rfl, htk⟩
  done e he' _ _ := by rw [he]; exact List.mem_append_left _ he'
  doneTasks h := by
    intro e he' hc tk htk
    rw [he] at he'
    rcases List.mem_append.mp he' with he' | he'
    · exact h e he' hc tk htk
    · obtain rfl := List.mem_singleton.mp he'
      rw [hopen] at hc
      cases hc
  runTasks h := by
    intro R hR hc name hn e he' ho tk htk hname
    rw [hr] at hR
    rw [he] at he'
    rcases List.mem_append.mp he' with he' | he'
    · exact h R hR hc name hn e he' ho tk htk hname
    · obtain rfl := List.mem_singleton.mp he'
      exact absurd ho (hfree R hR hc name hn)

end Good

/-! ### Owners of calls -/

/-- A running or fetching call reports: its task is active, and a task with a call has no run. -/
theorem settleOwner_good {s u t : State} {c : Call} {iv : InvocationStatus} {task : TaskStatus}
    (lim : Limit.Inv s) (h : u.settleOwner c iv task = .ok t) (hc : c ∈ s.calls)
    (hrun : c.status = .running ∨ c.status = .fetching) (hended : task.ended = true)
    (hue : u.executions = s.executions) (hur : u.runs = s.runs) : Good u t := by
  rcases State.settleOwner_eq_ok.mp h with ⟨-, i, -, rfl⟩ | ⟨name, e, ts, hname, he, hts, rfl⟩
  · exact Good.of_eq rfl rfl
  · obtain ⟨heu, heid⟩ := State.execution?_eq_some he
    have htsm := List.mem_of_find?_eq_some hts
    have htsn := Delivery.find?_name_of_task hts
    have hes : e ∈ s.executions := hue ▸ heu
    have hact : ts.status = .active :=
      lim.status_of hes htsm (by rw [heid, htsn]; exact lim.active c hc hrun name hname)
    refine Good.setTask heu (by rw [hue]; exact lim.execIds) htsm rfl
      (fun x hx hxn => lim.coherent e hes x hx ts htsm hxn) (by rw [hact]; rfl) (fun _ => hended)
      (Or.inr fun R hR _ hRo hRt => ?_)
    exact lim.apart c hc R (hur ▸ hR) name hname (by rw [hRt, htsn]) (by rw [hRo, heid])

/-- A cancelling call terminates: its task, if still active, is cancelled. -/
theorem cancelOwner_good {s u t : State} {c : Call} (lim : Limit.Inv s) (h : u.cancelOwner c = .ok t)
    (hc : c ∈ s.calls) (hue : u.executions = s.executions) (hur : u.runs = s.runs) : Good u t := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, i, -, rfl⟩ | ⟨name, e, ts, hname, he, hts, rfl⟩
  · split
    · exact Good.of_eq rfl rfl
    · exact Good.of_eq rfl rfl
  · split
    · rename_i hact
      obtain ⟨heu, heid⟩ := State.execution?_eq_some he
      have htsm := List.mem_of_find?_eq_some hts
      have htsn := Delivery.find?_name_of_task hts
      have hes : e ∈ s.executions := hue ▸ heu
      refine Good.setTask heu (by rw [hue]; exact lim.execIds) htsm rfl
        (fun x hx hxn => lim.coherent e hes x hx ts htsm hxn) (by rw [hact]; rfl) (fun _ => rfl)
        (Or.inr fun R hR _ hRo hRt => ?_)
      exact lim.apart c hc R (hur ▸ hR) name hname (by rw [hRt, htsn]) (by rw [hRo, heid])
    · exact Good.of_eq rfl rfl

/-- A running or fetching call fails: its owner fails, and the policy may stop the workflow. -/
theorem failCall_good {s t : State} {c : Call} {status : CallStatus} {cause : Cause} (lim : Limit.Inv s)
    (hc : c ∈ s.calls) (hrun : c.status = .running ∨ c.status = .fetching)
    (h : s.failCall c status cause = .ok t) : Good s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  exact Good.pre (Good.then_fail (settleOwner_good lim hso hc hrun rfl rfl rfl)) rfl rfl

/-- A task run is stored under the path of its execution and task, so a task has one run. -/
theorem taskRun_path {p : Definition} {s : State} (inv : Delivery.Inv p s) {R : Run} (hR : R ∈ s.runs)
    {name : String} (ht : R.task = some name) {e : Execution} (he : e ∈ s.executions) (ho : R.owner = some e.id) :
    R.path = Key.child (Key.task e.id name) := by
  rcases inv.own.runs R hR with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨name', ht', e₁, he₁, ho₁, hp, -⟩
  · rw [ht] at h; cases h
  · rw [ht] at h; cases h
  · rw [ht] at ht'; cases ht'
    obtain rfl : e₁ = e := inv.wk.execution_eq_of_id he₁ he (Option.some.inj (ho₁.symm.trans ho))
    exact hp

open State in
/-- Every step keeps ended tasks and complete executions, and both invariants. -/
theorem step_good {p : Definition} {s t : State} {op : Op} (inv : Delivery.Inv p s) (lim : Limit.Inv s)
    (dt : DoneTasks s) (rt : RunTasks s) (hs : step p s op = .ok t) : Good s t := by
  cases op with
  | start input =>
    obtain ⟨hst, -, -, -, -, rfl⟩ := Step.start_inv hs
    have hnil : s.runs = [] := (Delivery.runs_nil_or_started inv).resolve_right (by simp [hst])
    exact Good.appendRun (x := { path := [], workflow := p.main, input }) (by simp [hnil]) rfl
      (fun _ n hn => by cases hn)
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, hexec, rfl⟩
    · exact Good.of_eq rfl rfl
    · exact Good.of_eq rfl rfl
    · exact Good.appendRun rfl rfl (fun _ n hn => by cases hn)
    · refine Good.appendExecution rfl rfl rfl fun R hR _ n hn ho => ?_
      obtain ⟨e, he, heid, -⟩ := lim.runs R hR _ n ho hn
      exact execution?_eq_none_iff.mp hexec (List.mem_map.mpr ⟨e, he, heid⟩)
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact Good.of_eq rfl rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, h4, -, hacc, hso⟩ := Step.returned_inv hs
    have fr := accept_frame hacc
    exact (Good.of_eq (by simp [fr.2.2.2.1]) (by simp [fr.2.2.2.2.2.2.1])).trans
      (settleOwner_good lim hso (call?_eq_some hc).1 (Or.inl h4) rfl (by simp [fr.2.2.2.2.2.2.1])
        (by simp [fr.2.2.2.1]))
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, s', -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have fr := accept_frame hacc
    exact Good.of_eq (by simp [fr.2.2.2.1]) (by simp [fr.2.2.2.2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, s', -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    have fr := accept_frame hacc
    exact Good.of_eq (by simp [fr.2.2.2.1]) (by simp [fr.2.2.2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, c, hc, -, h4, hso⟩ := Step.ended_inv hs
    exact Good.pre (settleOwner_good lim hso (call?_eq_some hc).1 (Or.inr h4) rfl rfl rfl) rfl rfl
  | failed id =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.failed_inv hs
    exact failCall_good lim (call?_eq_some hc).1 h3 h
  | timedOut id element =>
    obtain ⟨-, -, c, hc, h3, h⟩ := Step.timedOut_inv hs
    refine failCall_good lim (call?_eq_some hc).1 ?_ h
    rcases h3 with ⟨-, h3, -⟩ | ⟨-, h3, -⟩
    · exact Or.inr h3
    · exact h3
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨h3, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact failCall_good lim (call?_eq_some hc).1 h3 h
    · exact Good.pre (cancelOwner_good lim h (call?_eq_some hc).1 rfl rfl) rfl rfl
  | terminated id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.terminated_inv hs
    exact Good.pre (cancelOwner_good lim h (call?_eq_some hc).1 rfl rfl) rfl rfl
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact Good.of_eq rfl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Good.then_fail (Good.of_eq rfl rfl)
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, _, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    have hem := (execution?_eq_some he).1
    have htsm := List.mem_of_find?_eq_some hts
    exact Good.setTask (ts' := { ts with status := .ready, input := value }) hem lim.execIds htsm rfl
      (fun x hx hxn => lim.coherent e hem x hx ts htsm hxn)
      (by rw [hpend]; rfl) (fun hc => by have := dt e hem hc ts htsm; rw [hpend] at this; cases this)
      (Or.inr fun R hR _ hRo hRt => lim.no_run hem htsm (by simp [Limit.Begun, hpend]) R hR hRt hRo)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, _, _, he, hts, hpend, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    have hem := (execution?_eq_some he).1
    have htsm := List.mem_of_find?_eq_some hts
    exact (Good.setTask (ts' := { ts with status := .failed }) hem lim.execIds htsm rfl
      (fun x hx hxn => lim.coherent e hem x hx ts htsm hxn) (by rw [hpend]; rfl) (fun _ => rfl)
      (Or.inr fun R hR _ hRo hRt => lim.no_run hem htsm (by simp [Limit.Begun, hpend]) R hR hRt hRo)).then_fail
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, hopen, -, hts, hready, -, -, h⟩ := Step.beginTask_inv hs
    have hem := (execution?_eq_some he).1
    have htsm := List.mem_of_find?_eq_some hts
    have htsn := Delivery.find?_name_of_task hts
    have g := Good.setTask (ts' := { ts with status := .active }) hem lim.execIds htsm rfl
      (fun x hx hxn => lim.coherent e hem x hx ts htsm hxn) (by rw [hready]; rfl)
      (fun hc => by rw [hopen] at hc; cases hc) (Or.inl rfl)
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact g.trans (Good.of_eq rfl rfl)
    · refine g.trans (Good.appendRun rfl rfl ?_)
      intro _ n hn x hx ho tk htk htkn
      cases hn
      obtain rfl := eq_of_mem_setTask hx (Option.some.inj ho).symm
      rw [Limit.withTask_tasks', List.mem_map] at htk
      obtain ⟨y, hy, rfl⟩ := htk
      by_cases hy' : y.name = ts.name
      · rw [Limit.replaceTask_of_name (t := { ts with status := .active }) hy']
      · rw [Limit.replaceTask_of_ne (t := { ts with status := .active }) hy'] at htkn
        exact absurd (htkn.trans htsn.symm) hy'
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact Good.of_eq rfl rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Good.then_fail (Good.of_eq rfl rfl)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact Good.of_eq rfl rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, hopen, -, hall, -, -, h⟩ := Step.closeExecution_inv hs
    have g := Good.complete (execution?_eq_some he).1 lim.execIds hopen fun tk htk =>
      (Delivery.taskEnded_iff.mp (List.all_eq_true.mp hall tk htk)).1
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact g.trans (Good.of_eq rfl rfl)
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, hopen, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    have hrm := (run?_eq_some hr).1
    have g : Good s (s.setRun { r with complete := true }) := Good.completeRun
    rcases h with ⟨-, _, -, h⟩ | ⟨name, e, ts, htask, he, hts, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact g.trans (Good.of_eq rfl rfl)
    · obtain ⟨hem, heid⟩ := execution?_eq_some he
      have htsm := List.mem_of_find?_eq_some hts
      have htsn := Delivery.find?_name_of_task hts
      have hro : r.owner = some e.id := by rw [howner, heid]
      have hact : ts.status = .active := rt r hrm hopen name htask e hem hro ts htsm htsn
      -- The run of the task was `r`, which is now complete.
      have hrun : ∀ R ∈ (s.setRun { r with complete := true }).runs, R.complete = false →
          R.owner = some e.id → R.task ≠ some ts.name := by
        intro R hR hRc hRo hRt
        rw [setRun_runs] at hR
        rcases Delivery.mem_map_replace' hR with rfl | ⟨hR, hne⟩
        · cases hRc
        · have h1 := taskRun_path inv hR hRt hem hRo
          have h2 := taskRun_path inv hrm htask hem hro
          rw [htsn] at h1
          simp [h1, h2] at hne
      have gt : ∀ st : TaskStatus, st.ended = true →
          Good (s.setRun { r with complete := true }) ((s.setRun { r with complete := true }).setTask e
            { ts with status := st }) := fun st hst =>
        Good.setTask hem lim.execIds htsm rfl (fun y hy hyn => lim.coherent e hem y hy ts htsm hyn)
          (by rw [hact]; rfl) (fun _ => hst) (Or.inr hrun)
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact g.trans ((gt .succeeded rfl).trans (Good.of_eq rfl rfl))
      · exact g.trans (gt .skipped rfl)
      · exact g.trans (gt .failed rfl)
      · exact g.trans (gt .upstreamFailed rfl)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact Good.stop.trans (Good.of_eq rfl rfl)
    · exact Good.of_eq rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact Good.completeRun.trans (Good.of_eq rfl rfl)
    · exact Good.of_eq rfl rfl

/-- Both invariants hold in every reachable state. -/
theorem reachable_tasks {p : Definition} {s : State} (h : Reachable p s) : DoneTasks s ∧ RunTasks s := by
  induction h with
  | empty => exact ⟨by simp [DoneTasks], by simp [RunTasks]⟩
  | step op hr hs ih =>
    have g := step_good (Delivery.Reachable.inv hr) (Limit.reachable_inv hr) ih.1 ih.2 hs
    exact ⟨g.doneTasks ih.1, g.runTasks ih.2⟩

/-! ### Task results -/

/-- Transforming the output of one task result leaves the task results with other keys. -/
theorem mem_setTaskResult_of_ne {s : State} {r₁ r : TaskResult} {o : TaskOutput} (hr : r ∈ s.taskResults)
    (hne : (r.execution, r.task, r.index) ≠ (r₁.execution, r₁.task, r₁.index)) :
    r ∈ (s.setTaskResult { r₁ with output := o }).taskResults := by
  rw [State.setTaskResult_taskResults]
  refine List.mem_map.mpr ⟨r, hr, ?_⟩
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact absurd (by rw [hc.1.1, hc.1.2, hc.2]) hne
  · rfl

open State in
/-- How a step changes the task results: not at all, by one result of a running task call or a
    closing task run, or by the output transform of one pending result of a task in the output. -/
theorem step_taskResults {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    t.taskResults = s.taskResults ∨
    (∃ x, t.taskResults = s.taskResults ++ [x] ∧ Delivery.NewTaskResult s x) ∨
    (∃ r o e spec, r ∈ s.taskResults ∧ r.output = .pending ∧ s.execution? r.execution = some e ∧
      s.taskSpec p e r.task = .ok spec ∧ spec.output.isSome = true ∧
      t.taskResults = (s.setTaskResult { r with output := o }).taskResults) := by
  cases op with
  | start input =>
    obtain ⟨-, -, -, -, -, rfl⟩ := Step.start_inv hs
    exact Or.inl rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact Or.inl rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact Or.inl rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, h4, -, hacc, hso⟩ := Step.returned_inv hs
    rw [(Delivery.settleOwner_old hso).2.2.2.2.1, setCall_taskResults]
    rcases Delivery.accept_taskResults hacc with h | ⟨name, hn, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨_, h, rfl, Or.inl ⟨c, (call?_eq_some hc).1, rfl, hn, Or.inl h4⟩⟩)
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', -, -, -, h5, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    rw [setInvocation_taskResults, setCall_taskResults]
    rcases Delivery.accept_taskResults hacc with h | ⟨name, hn, -⟩
    · exact Or.inl h
    · rw [h5] at hn; cases hn
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, h4, hacc, rfl⟩ := Step.yielded_inv hs
    rw [setCall_taskResults]
    rcases Delivery.accept_taskResults hacc with h | ⟨name, hn, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨_, h, rfl, Or.inl ⟨c, (call?_eq_some hc).1, rfl, hn, Or.inr h4⟩⟩)
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact Or.inl (by rw [(Delivery.settleOwner_old hso).2.2.2.2.1, setCall_taskResults])
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact Or.inl (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact Or.inl (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact Or.inl (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
    · exact Or.inl (by rw [(Delivery.cancelOwner_old h).2.2.2.2.1, setCall_taskResults])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact Or.inl (by rw [(Delivery.cancelOwner_old h).2.2.2.2.1, setCall_taskResults])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact Or.inl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Or.inl (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Or.inl rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact Or.inl (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact Or.inl rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, _, spec, r, he, -, hspec, hout, hr, hpend, h⟩ := Step.taskOutput_inv hs
    have hkey : (r.execution = eid ∧ r.task = name) ∧ r.index = index := by simpa using List.find?_some hr
    refine Or.inr (Or.inr ⟨r, .value value, e, spec, List.mem_of_find?_eq_some hr, hpend,
      by rw [hkey.1.1]; exact he, by rw [hkey.1.2]; exact hspec, hout, ?_⟩)
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, e, spec, r, he, hspec, hout, hr, hpend, rfl⟩ := Step.taskOutputFailed_inv hs
    have hkey : (r.execution = eid ∧ r.task = name) ∧ r.index = index := by simpa using List.find?_some hr
    exact Or.inr (Or.inr ⟨r, .failed, e, spec, List.mem_of_find?_eq_some hr, hpend,
      by rw [hkey.1.1]; exact he, by rw [hkey.1.2]; exact hspec, hout, by simp⟩)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact Or.inl rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact Or.inl rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, hopen, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨name, e, _, htask, he, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact Or.inl rfl
    · have heid := (execution?_eq_some he).2
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr (Or.inl ⟨_, rfl, rfl, Or.inr ⟨r, (run?_eq_some hr).1, by rw [howner, heid], htask, hopen⟩⟩)
      all_goals exact Or.inl rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact Or.inl rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact Or.inl rfl

end FrozenAux

end Suimon.Round3
