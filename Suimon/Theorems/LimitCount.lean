import Suimon.Theorems.LimitInv
import Suimon.Theorems.Static

/-! Counting the tasks that hold a slot of a concurrency execution (§8.2). A step keeps the run and
    placement of every execution, hence its concurrency and limit, and it never adds a slot holder,
    except `beginTask`, which adds exactly its own task (task names are distinct in a valid definition)
    and only below the limit. -/

namespace Suimon
namespace Limit
open State

/-! ### Lists -/

theorem length_filter_or_le {α : Type} (p q : α → Bool) :
    ∀ l : List α, (l.filter fun x => p x || q x).length ≤ (l.filter p).length + (l.filter q).length
  | [] => by simp
  | x :: l => by
    have ih := length_filter_or_le p q l
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

theorem length_filter_key_le_one {α κ : Type} [BEq κ] [LawfulBEq κ] {f : α → κ} {k : κ} :
    ∀ {l : List α}, (l.map f).Nodup → (l.filter fun x => f x == k).length ≤ 1
  | [], _ => by simp
  | x :: l, hl => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hl
    by_cases hx : f x = k
    · have hnil : l.filter (fun y => f y == k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hyk
        exact hl.1 y hy ((beq_iff_eq.mp hyk).trans hx.symm)
      simp [hx, hnil]
    · simp [hx, length_filter_key_le_one hl.2]

/-! ### Slot holders -/

/-- Task `x` of execution `id` holds a slot: it is active, or a call of it is cancelling. --/
def Holds (s : State) (id : String) (x : TaskState) : Prop :=
  x.status = .active ∨ ∃ c ∈ s.calls, c.owner = id ∧ c.task = some x.name ∧ c.status = .cancelling

theorem holdsSlot_iff {s : State} {e : Execution} {x : TaskState} :
    s.holdsSlot e x = true ↔ Holds s e.id x := by
  simp only [State.holdsSlot, Holds, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
    and_assoc]

theorem holds_of_calls {s t : State} (hc : ∀ c ∈ t.calls, c.status = .cancelling → c ∈ s.calls) {id : String}
    {x : TaskState} (hh : Holds t id x) : Holds s id x := by
  rcases hh with hact | ⟨c, hc', ho, ht, hs⟩
  · exact Or.inl hact
  · exact Or.inr ⟨c, hc c hc' hs, ho, ht, hs⟩

/-- The number of tasks of `e` that hold a slot in `s`. --/
def count (s : State) (e : Execution) : Nat := (e.tasks.filter (s.holdsSlot e)).length

theorem count_le {s t : State} {e e' : Execution} {g : TaskState → TaskState}
    (htasks : e'.tasks = e.tasks.map g) (hid : e'.id = e.id)
    (hpt : ∀ x ∈ e.tasks, Holds t e.id (g x) → Holds s e.id x) : count t e' ≤ count s e := by
  unfold count
  rw [htasks, List.filter_map, List.length_map, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro x hx hh
  rw [Function.comp_apply, holdsSlot_iff, hid] at hh
  exact holdsSlot_iff.mpr (hpt x hx hh)

theorem count_eq_zero {s : State} {e : Execution} (h : ∀ x ∈ e.tasks, ¬Holds s e.id x) : count s e = 0 := by
  unfold count
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx hh
  exact h x hx (holdsSlot_iff.mp hh)

/-! ### What a step keeps -/

/-- Each execution of `t` holds no slot, or continues one of `s` with the same run and placement and
    at most as many slot holders. --/
def Fewer (s t : State) : Prop :=
  ∀ e' ∈ t.executions, count t e' = 0 ∨
    ∃ e ∈ s.executions, e'.run = e.run ∧ e'.placement = e.placement ∧ count t e' ≤ count s e

/-- Each run of `s` is still found under its path, with the same workflow. --/
def RunsKept (s t : State) : Prop :=
  ∀ path r, s.run? path = some r → ∃ r', t.run? path = some r' ∧ r'.workflow = r.workflow

/-- Task names are distinct in each execution. --/
def Names (s : State) : Prop := ∀ e ∈ s.executions, (e.tasks.map (·.name)).Nodup

theorem fewer_of_holds {s t : State} (he : t.executions = s.executions)
    (hh : ∀ e ∈ s.executions, ∀ x ∈ e.tasks, Holds t e.id x → Holds s e.id x) : Fewer s t := fun e' he' => by
  rw [he] at he'
  exact Or.inr ⟨e', he', rfl, rfl, count_le (g := id) (List.map_id _).symm rfl (hh e' he')⟩

theorem runsKept_of_runs {s t : State} (hr : t.runs = s.runs) : RunsKept s t := fun path r h0 =>
  ⟨r, by simp only [State.run?, hr]; exact h0, rfl⟩

theorem runsKept_append {s t : State} {x : Run} (hr : t.runs = s.runs ++ [x]) : RunsKept s t := fun path r h0 => by
  refine ⟨r, ?_, rfl⟩
  simp only [State.run?, hr, List.find?_append] at h0 ⊢
  rw [h0, Option.some_or]

theorem RunsKept.workflow? {p : Definition} {s t : State} (h : RunsKept s t) {path : Path}
    (hs : (s.run? path).isSome) : t.workflow? p path = s.workflow? p path := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨r', hr', hw⟩ := h path r hr
  show (t.run? path >>= fun r => p.workflow? r.workflow) = (s.run? path >>= fun r => p.workflow? r.workflow)
  rw [hr, hr']
  show p.workflow? r'.workflow = p.workflow? r.workflow
  rw [hw]

/-- The concurrency of an execution depends only on its run's workflow and its placement. --/
theorem concurrencyOf_congr {p : Definition} {s t : State} {e e' : Execution}
    (hw : t.workflow? p e.run = s.workflow? p e.run) (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) :
    t.concurrencyOf p e' = s.concurrencyOf p e := by
  simp only [State.concurrencyOf, State.placementOf, hrun, hpl, hw]

theorem names_setTask {s : State} {e : Execution} {ts : TaskState} (hn : Names s) (he : e ∈ s.executions) :
    Names (s.setTask e ts) := by
  intro e' he'
  rw [setTask_eq] at he'
  rcases mem_setExecution_iff he' with rfl | ⟨he', -⟩
  · rw [withTask_tasks', List.map_map]
    have : ((·.name) ∘ replaceTask ts : TaskState → String) = (·.name) := by
      funext x
      simp
    rw [this]
    exact hn e he
  · exact hn e' he'

/-- What a step other than `beginTask` keeps for the concurrency limit. --/
structure Kept (s t : State) : Prop where
  names : Names s → Names t
  runs : RunsKept s t
  fewer : Fewer s t

namespace Kept
variable {s t u : State}

theorem refl (s : State) : Kept s s :=
  ⟨id, fun _ r hr => ⟨r, hr, rfl⟩, fun e he => Or.inr ⟨e, he, rfl, rfl, Nat.le_refl _⟩⟩

theorem trans (h₁ : Kept s t) (h₂ : Kept t u) : Kept s u where
  names := h₂.names ∘ h₁.names
  runs := fun path r hr => by
    obtain ⟨r', hr', hw'⟩ := h₁.runs path r hr
    obtain ⟨r'', hr'', hw''⟩ := h₂.runs path r' hr'
    exact ⟨r'', hr'', hw''.trans hw'⟩
  fewer := fun e'' he'' => by
    rcases h₂.fewer e'' he'' with h0 | ⟨e', he', hr', hp', hc'⟩
    · exact Or.inl h0
    · rcases h₁.fewer e' he' with h0 | ⟨e, he, hr, hp, hc⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨e, he, hr'.trans hr, hp'.trans hp, Nat.le_trans hc' hc⟩

theorem of_holds (he : t.executions = s.executions) (hr : t.runs = s.runs)
    (hh : ∀ e ∈ s.executions, ∀ x ∈ e.tasks, Holds t e.id x → Holds s e.id x) : Kept s t where
  names := fun hn e' he' => hn e' (he ▸ he')
  runs := runsKept_of_runs hr
  fewer := fewer_of_holds he hh

theorem of_eq (hc : t.calls = s.calls) (he : t.executions = s.executions) (hr : t.runs = s.runs) : Kept s t :=
  of_holds he hr fun _ _ _ _ => holds_of_calls fun _ hc' _ => hc ▸ hc'

/-- Storing a call that is not cancelling adds no slot holder. --/
theorem setCall_of_ne {c' : Call} (hq : c'.status ≠ .cancelling) : Kept s (s.setCall c') :=
  of_holds rfl rfl fun _ _ _ _ => holds_of_calls fun c hc hs => by
    rcases mem_setCall_calls hc with rfl | hc
    · exact absurd hs hq
    · exact hc

/-- Cancelling a running call of a task keeps its slot holder: the task was active. --/
theorem setCall (h : Inv s) {c c' : Call} (hc : c ∈ s.calls) (howner : c'.owner = c.owner)
    (htask : c'.task = c.task)
    (hq : c'.status = .cancelling → c.status = .running ∨ c.status = .fetching ∨ c.status = .cancelling) :
    Kept s (s.setCall c') :=
  of_holds rfl rfl fun e he x hx hh => by
    rcases hh with hact | ⟨c2, hc2, ho2, ht2, hs2⟩
    · exact Or.inl hact
    · rcases mem_setCall_calls hc2 with rfl | hc2
      · rw [howner] at ho2
        rw [htask] at ht2
        have hact : ∀ hr : c.status = .running ∨ c.status = .fetching, Holds s e.id x := fun hr => by
          have := h.active c hc hr x.name ht2
          rw [ho2] at this
          exact Or.inl (h.status_of he hx this)
        rcases hq hs2 with hr | hr | hr
        · exact hact (Or.inl hr)
        · exact hact (Or.inr hr)
        · exact Or.inr ⟨c, hc, ho2, ht2, hr⟩
      · exact Or.inr ⟨c2, hc2, ho2, ht2, hs2⟩

/-- Storing a task that is not active adds no slot holder. --/
theorem setTask {e : Execution} {ts : TaskState} (he : e ∈ s.executions) (hna : ts.status ≠ .active) :
    Kept s (s.setTask e ts) where
  names := fun hn => names_setTask hn he
  runs := fun _ r h0 => ⟨r, h0, rfl⟩
  fewer := fun e' he' => by
    rw [setTask_eq] at he'
    rcases mem_setExecution_iff he' with rfl | ⟨he', -⟩
    · refine Or.inr ⟨e, he, rfl, rfl, count_le withTask_tasks' rfl fun x _ hh => ?_⟩
      rcases hh with hact | ⟨c, hc, ho, ht, hs⟩
      · left
        by_cases hn : x.name = ts.name
        · rw [replaceTask_of_name hn] at hact
          exact absurd hact hna
        · rwa [replaceTask_of_ne hn] at hact
      · exact Or.inr ⟨c, hc, ho, by simpa using ht, hs⟩
    · exact Or.inr ⟨e', he', rfl, rfl, count_le (g := id) (List.map_id _).symm rfl fun _ _ hh => hh⟩

/-- A stop turns running calls into cancelling ones, whose tasks were already active. --/
theorem stop (h : Inv s) : Kept s s.stop where
  names := fun hn e' he' => by
    obtain ⟨e, he, rfl⟩ := mem_stop_executions.mp he'
    rw [stopExecution_tasks, List.map_map]
    have : ((·.name) ∘ stopTask : TaskState → String) = (·.name) := by
      funext x
      simp
    rw [this]
    exact hn e he
  runs := fun _ r h0 => ⟨r, h0, rfl⟩
  fewer := fun e' he' => by
    obtain ⟨e, he, rfl⟩ := mem_stop_executions.mp he'
    refine Or.inr ⟨e, he, rfl, rfl, count_le stopExecution_tasks rfl fun x hx hh => ?_⟩
    rcases hh with hact | ⟨c, hc, ho, ht, hst⟩
    · exact Or.inl (stopTask_active hact)
    · obtain ⟨c0, hc0, rfl⟩ := mem_stop_calls.mp hc
      rw [stopCall_owner] at ho
      rw [stopCall_task, stopTask_name] at ht
      rw [stopCall_status] at hst
      by_cases hrun : c0.status = .running ∨ c0.status = .fetching
      · have := h.active c0 hc0 hrun x.name ht
        rw [ho] at this
        exact Or.inl (h.status_of he hx this)
      · rw [ite_eq_right hrun] at hst
        exact Or.inr ⟨c0, hc0, ho, ht, hst⟩

theorem fail (h : Inv s) {f : Failure} {policy : Policy} : Kept s (s.fail f policy) := by
  have k : Kept s { s with failures := s.failures ++ [f] } := of_eq rfl rfl rfl
  cases policy
  · exact k.trans (stop (h.of_eq rfl rfl rfl rfl))
  · exact k

/-- A failure recorded on a state with the same calls, executions, runs and task results. --/
theorem fail_eq {u : State} (h : Inv s) (hc : u.calls = s.calls) (he : u.executions = s.executions)
    (hr : u.runs = s.runs) (htr : u.taskResults = s.taskResults) {f : Failure} {policy : Policy} :
    Kept s (u.fail f policy) :=
  (of_eq hc he hr).trans (fail (h.of_eq hc he hr htr))

theorem setTaskResult {r : TaskResult} : Kept s (s.setTaskResult r) := of_eq rfl rfl rfl

theorem appendCall {x : Call} (hc : t.calls = s.calls ++ [x]) (he : t.executions = s.executions)
    (hr : t.runs = s.runs) (hq : x.status ≠ .cancelling) : Kept s t :=
  of_holds he hr fun _ _ _ _ => holds_of_calls fun c hc' hs => by
    rw [hc] at hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact hc'
    · obtain rfl := List.mem_singleton.mp hc'
      exact absurd hs hq

theorem appendRun {x : Run} (hc : t.calls = s.calls) (he : t.executions = s.executions)
    (hr : t.runs = s.runs ++ [x]) : Kept s t where
  names := fun hn e' he' => hn e' (he ▸ he')
  runs := runsKept_append hr
  fewer := fewer_of_holds he fun _ _ _ _ => holds_of_calls fun _ hc' _ => hc ▸ hc'

/-- A new execution holds no slot: its tasks wait, and no call belongs to its fresh identity. --/
theorem appendExecution (h : Inv s) {x : Execution} (hc : t.calls = s.calls)
    (he : t.executions = s.executions ++ [x]) (hr : t.runs = s.runs) (hfresh : x.id ∉ s.executions.map (·.id))
    (hna : ∀ y ∈ x.tasks, y.status ≠ .active) (hnames : (x.tasks.map (·.name)).Nodup) : Kept s t where
  names := fun hn e' he' => by
    rw [he] at he'
    rcases List.mem_append.mp he' with he' | he'
    · exact hn e' he'
    · obtain rfl := List.mem_singleton.mp he'
      exact hnames
  runs := runsKept_of_runs hr
  fewer := fun e' he' => by
    rw [he] at he'
    rcases List.mem_append.mp he' with he' | he'
    · exact Or.inr ⟨e', he', rfl, rfl, count_le (g := id) (List.map_id _).symm rfl fun _ _ =>
        holds_of_calls fun _ hc' _ => hc ▸ hc'⟩
    · obtain rfl := List.mem_singleton.mp he'
      refine Or.inl (count_eq_zero fun y hy hh => ?_)
      rcases hh with hact | ⟨c, hc', ho, ht, -⟩
      · exact hna y hy hact
      · rw [hc] at hc'
        obtain ⟨e2, he2, hid, -⟩ := h.calls c hc' y.name ht
        exact hfresh (List.mem_map.mpr ⟨e2, he2, hid.trans ho⟩)

theorem setExecution {e e' : Execution} (he : e ∈ s.executions) (hid : e'.id = e.id) (htasks : e'.tasks = e.tasks)
    (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) : Kept s (s.setExecution e') where
  names := fun hn e2 he2 => by
    rcases mem_setExecution_iff he2 with rfl | ⟨he2, -⟩
    · rw [htasks]
      exact hn e he
    · exact hn e2 he2
  runs := fun _ r h0 => ⟨r, h0, rfl⟩
  fewer := fun e2 he2 => by
    rcases mem_setExecution_iff he2 with rfl | ⟨he2, -⟩
    · exact Or.inr ⟨e, he, hrun, hpl, count_le (g := id) (by rw [htasks, List.map_id]) hid fun _ _ hh => hh⟩
    · exact Or.inr ⟨e2, he2, rfl, rfl, count_le (g := id) (List.map_id _).symm rfl fun _ _ hh => hh⟩

theorem setRun {r r' : Run} (hr : s.run? r'.path = some r) (hw : r'.workflow = r.workflow) :
    Kept s (s.setRun r') where
  names := id
  runs := fun path r0 h0 => by
    rw [run?_setRun]
    by_cases hp : r'.path = path
    · subst hp
      rw [ite_eq_left rfl, h0]
      rw [hr] at h0
      cases h0
      exact ⟨r', rfl, hw⟩
    · rw [ite_eq_right hp]
      exact ⟨r0, h0, rfl⟩
  fewer := fewer_of_holds rfl fun _ _ _ _ hh => hh

theorem accept {c : Call} {index : Nat} {value : Value} {arm : Option String}
    (ha : s.accept c index value arm = .ok t) : Kept s t := by
  obtain ⟨-, -, -, hr, -, hc, he, -⟩ := accept_frame ha
  exact of_eq hc he hr

theorem settleOwner {c : Call} {inv : InvocationStatus} {task : TaskStatus} (hna : task ≠ .active)
    (ho : s.settleOwner c inv task = .ok t) : Kept s t := by
  rcases settleOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨name, e, ts, -, he, -, rfl⟩
  · exact of_eq rfl rfl rfl
  · exact setTask (execution?_eq_some he).1 hna

theorem cancelOwner {c : Call} (ho : s.cancelOwner c = .ok t) : Kept s t := by
  rcases cancelOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨name, e, ts, -, he, -, rfl⟩
  · split
    · exact of_eq rfl rfl rfl
    · exact refl s
  · split
    · exact setTask (execution?_eq_some he).1 (by simp)
    · exact refl s

theorem failCall (h : Inv s) {c : Call} {status : CallStatus} {cause : Cause} (hc : c ∈ s.calls)
    (hst : status ≠ .running ∧ status ≠ .fetching)
    (hq : status = .cancelling → c.status = .running ∨ c.status = .fetching)
    (hf : s.failCall c status cause = .ok t) : Kept s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  have h1 := h.setCall (c' := { c with status }) hc rfl rfl rfl fun hr => by
    rcases hr with hr | hr
    · exact absurd hr hst.1
    · exact absurd hr hst.2
  have h2 := h1.settleOwner (h1.quiet_of_setCall hc rfl rfl rfl hst) (by simp [Begun]) hso
  have k1 : Kept s (s.setCall { c with status }) := setCall h hc rfl rfl fun hs => by
    rcases hq hs with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  exact k1.trans ((settleOwner (by simp) hso).trans (fail h2))

end Kept

/-! ### Every step other than `beginTask` -/

theorem step_kept {p : Definition} {s t : State} {op : Op} (valid : p.validate = .ok ()) (h : Inv s)
    (h0 : s = {} ∨ s.started = true) (hs : step p s op = .ok t) (hop : ∀ eid name, op ≠ .beginTask eid name) :
    Kept s t := by
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h0 with rfl | h0
    · exact ⟨fun _ _ he => by simp at he, fun _ _ h0 => by simp [State.run?] at h0, fun _ he => by simp at he⟩
    · simp [h0] at hst
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨judge, arms, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩ |
      ⟨c, hc, he, rfl⟩
    · exact Kept.appendCall rfl rfl rfl (by simp)
    · exact Kept.appendCall rfl rfl rfl (by simp)
    · exact Kept.appendRun rfl rfl rfl
    · refine Kept.appendExecution h rfl rfl rfl (execution?_eq_none_iff.mp he) ?_ ?_
      · intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨ts, -, rfl⟩ := hy
        dsimp only
        split <;> simp
      · rw [List.map_map]
        exact (concurrency_settings valid w (Definition.workflow?_eq_some hw).1 pl
          (Workflow.placement?_eq_some hpl).1 c hc).1
  | fetch id =>
    obtain ⟨-, -, c, hc, -, -, rfl⟩ := Step.fetch_inv hs
    exact Kept.setCall_of_ne (by simp)
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact (Kept.accept hacc).trans ((Kept.setCall_of_ne (by simp)).trans (Kept.settleOwner (by simp) hso))
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact (Kept.accept hacc).trans
      ((Kept.setCall_of_ne (c' := { c with status := .returned }) (by simp)).trans (Kept.of_eq rfl rfl rfl))
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (Kept.accept hacc).trans (Kept.setCall_of_ne (by simp))
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    exact (Kept.setCall_of_ne (by simp)).trans (Kept.settleOwner (by simp) hso)
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact Kept.failCall h (call?_eq_some hc).1 (by simp) (by simp) hf
  | timedOut id element =>
    obtain ⟨-, -, c, hc, hcase, hf⟩ := Step.timedOut_inv hs
    refine Kept.failCall h (call?_eq_some hc).1 (by simp) (fun _ => ?_) hf
    rcases hcase with ⟨-, hst, -⟩ | ⟨-, hst, -⟩
    · exact Or.inr hst
    · exact hst
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact Kept.failCall h (call?_eq_some hc).1 (by simp) (by simp) hf
    · exact (Kept.setCall_of_ne (by simp)).trans (Kept.cancelOwner ho)
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact (Kept.setCall_of_ne (by simp)).trans (Kept.cancelOwner ho)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact Kept.of_eq rfl rfl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Kept.fail_eq h (by rfl) (by rfl) (by rfl) (by rfl)
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact Kept.setTask (execution?_eq_some he).1 (by simp)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, hts, hpend, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    have he' := (execution?_eq_some he).1
    have hts' := (find?_key_eq_some hts).1
    have hnb : ¬Begun ts.status := by simp [Begun, hpend]
    have h1 := h.setTask (ts := { ts with status := .failed }) he' (fun hb => absurd (by simp [Begun]) hb)
      (fun hb => absurd (by simp [Begun]) hb) fun _ c hc _ => h.no_call (x := ts) he' hts' hnb c hc
    exact (Kept.setTask he' (by simp)).trans (Kept.fail h1)
  | beginTask eid name => exact absurd rfl (hop eid name)
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact Kept.of_eq rfl rfl rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Kept.setTaskResult.trans (Kept.fail h.setTaskResult)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact Kept.of_eq rfl rfl rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    have k := Kept.setExecution (e' := { e with complete := true }) (execution?_eq_some he).1 rfl rfl rfl rfl
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact k.trans (Kept.of_eq rfl rfl rfl)
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, -, -, -, -, -, -, -, hcases⟩ := Step.closeRun_inv hs
    have k : Kept s (s.setRun { r with complete := true }) :=
      Kept.setRun (r := r) (by show s.run? r.path = some r; rw [(run?_eq_some hr).2]; exact hr) rfl
    rcases hcases with ⟨-, _, -, hcases⟩ | ⟨name, e, ts, -, he, -, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact k.trans (Kept.of_eq rfl rfl rfl)
    · have k2 : ∀ st : TaskStatus, st ≠ .active →
          Kept s ((s.setRun { r with complete := true }).setTask e { ts with status := st }) :=
        fun st hna => k.trans (Kept.setTask (execution?_eq_some he).1 hna)
      rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (k2 .succeeded (by simp)).trans (Kept.of_eq rfl rfl rfl)
      · exact k2 .skipped (by simp)
      · exact k2 .failed (by simp)
      · exact k2 .upstreamFailed (by simp)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact (Kept.stop h).trans (Kept.of_eq rfl rfl rfl)
    · exact Kept.of_eq rfl rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have k : Kept s (s.setRun { r with complete := true }) :=
        Kept.setRun (r := r) (by show s.run? r.path = some r; rw [(run?_eq_some hr).2]; exact hr) rfl
      exact k.trans (Kept.of_eq rfl rfl rfl)
    · exact Kept.of_eq rfl rfl rfl

/-! ### The limit -/

/-- Every execution holds at most as many slots as its concurrency allows. --/
def WithinLimit (p : Definition) (s : State) : Prop :=
  ∀ e ∈ s.executions, ∀ c, s.concurrencyOf p e = .ok c → count s e ≤ c.limit

theorem WithinLimit.of_kept {p : Definition} {s t : State} (h : Inv s) (hk : Kept s t) (hl : WithinLimit p s) :
    WithinLimit p t := by
  intro e' he' c hc
  rcases hk.fewer e' he' with h0 | ⟨e, he, hrun, hpl, hle⟩
  · rw [h0]
    exact Nat.zero_le _
  · rw [concurrencyOf_congr (hk.runs.workflow? (h.execRuns e he)) hrun hpl] at hc
    exact Nat.le_trans hle (hl e he c hc)

/-- `beginTask` makes its task active below the limit; with distinct task names it is the only new
    slot holder. --/
theorem beginTask_limit {p : Definition} {s t : State} {eid name : String} (h : Inv s) (hn : Names s)
    (hl : WithinLimit p s) (hs : Step.beginTask p s eid name = .ok t) : Names t ∧ WithinLimit p t := by
  obtain ⟨-, -, e, c, ts, spec, he, -, hc, hts, -, hslot, -, hcases⟩ := Step.beginTask_inv hs
  have he' := (execution?_eq_some he).1
  -- `t` stores the begun task, and adds a running call or a run.
  have ht : t.executions = (s.setTask e { ts with status := .active }).executions ∧
      (∀ x ∈ t.calls, x.status = .cancelling → x ∈ s.calls) ∧ RunsKept s t := by
    rcases hcases with ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · refine ⟨rfl, fun x hx hst => ?_, runsKept_of_runs rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hx
      · obtain rfl := List.mem_singleton.mp hx
        simp at hst
    · exact ⟨rfl, fun x hx _ => hx, runsKept_append rfl⟩
  obtain ⟨hexec, hcalls, hruns⟩ := ht
  refine ⟨fun e2 he2 => names_setTask hn he' e2 (hexec ▸ he2), ?_⟩
  intro e2 he2 c2 hc2
  rw [hexec, setTask_eq] at he2
  rcases mem_setExecution_iff he2 with rfl | ⟨he2, -⟩
  · rw [concurrencyOf_congr (e' := withTask e { ts with status := .active }) (hruns.workflow? (h.execRuns e he'))
      rfl rfl, hc] at hc2
    cases hc2
    have hslot' : count s e < c.limit := hslot
    -- Only tasks named like the begun one may newly hold a slot, and there is one such task.
    have hcount : count t (withTask e { ts with status := .active }) ≤ count s e + 1 := by
      unfold count
      rw [withTask_tasks', List.filter_map, List.length_map]
      have hmono : (e.tasks.filter (t.holdsSlot (withTask e { ts with status := .active }) ∘
            replaceTask { ts with status := .active })).length ≤
          (e.tasks.filter fun x => s.holdsSlot e x || x.name == ts.name).length := by
        rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
        apply List.countP_mono_left
        intro x _ hx
        rw [Function.comp_apply, holdsSlot_iff] at hx
        by_cases hname : x.name = ts.name
        · simp [hname]
        · rw [replaceTask_of_ne (t := { ts with status := .active }) hname] at hx
          have : Holds s e.id x := holds_of_calls hcalls hx
          simp [holdsSlot_iff.mpr this]
      have hor := length_filter_or_le (s.holdsSlot e) (fun x => x.name == ts.name) e.tasks
      have hone := length_filter_key_le_one (f := TaskState.name) (k := ts.name) (hn e he')
      omega
    omega
  · rw [concurrencyOf_congr (e' := e2) (hruns.workflow? (h.execRuns e2 he2)) rfl rfl] at hc2
    have : count t e2 ≤ count s e2 :=
      count_le (g := id) (List.map_id _).symm rfl fun _ _ hh => holds_of_calls hcalls hh
    exact Nat.le_trans this (hl e2 he2 c2 hc2)

theorem reachable_limit {p : Definition} {s : State} (valid : p.validate = .ok ()) (hr : Reachable p s) :
    Names s ∧ WithinLimit p s := by
  induction hr with
  | empty => exact ⟨fun _ he => by simp at he, fun _ he => by simp at he⟩
  | step op hr hs ih =>
    have h := reachable_inv hr
    by_cases hop : ∃ eid name, op = .beginTask eid name
    · obtain ⟨eid, name, rfl⟩ := hop
      exact beginTask_limit h ih.1 ih.2 hs
    · have hk := step_kept valid h hr.eq_empty_or_started hs fun eid name heq => hop ⟨eid, name, heq⟩
      exact ⟨hk.names ih.1, ih.2.of_kept h hk⟩

end Limit
end Suimon
