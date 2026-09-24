import Suimon.Theorems.Round3.Enabled
import Suimon.Theorems.Round3.ProgressInv
import Suimon.Theorems.Round3.Fresh

namespace Suimon.Round3
open State

/-! ## [7] Round3/ProgressEasy.lean — task C1 -/

section ProgressEasy
variable {p : Definition} {s : State}

/-- Nothing is left for the engine outside the structure of runs: every eligible result reached its
    connection, every included task result went through its output transform, no task waits for its
    input transform, and every call ended. -/
structure Calm (p : Definition) (s : State) : Prop where
  delivered : ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → ∀ j c, w.connections[j]? = some c →
    c.source = r.placement → (c.arm = none ∨ c.arm = r.arm) → (s.delivery? r.run j r.id).isSome
  outputs : ∀ e ∈ s.executions, ∀ cc, s.concurrencyOf p e = .ok cc → ∀ r ∈ s.taskResults, r.execution = e.id →
    (∃ spec ∈ cc.tasks, spec.name = r.task ∧ spec.output.isSome) → r.output ≠ .pending
  inputs : ∀ e ∈ s.executions, ∀ t ∈ e.tasks, t.status ≠ .pending
  calls : ∀ c ∈ s.calls, c.status.ended = true

/-- An open run with no open run below it (maximal path length among open runs). -/
def DeepestOpen (s : State) (r : Run) : Prop :=
  r ∈ s.runs ∧ r.complete = false ∧ ∀ r' ∈ s.runs, r'.complete = false → r'.path.length ≤ r.path.length

/-- A nonempty list has an element of maximal measure. -/
private theorem exists_max_mem {α : Type} (f : α → Nat) :
    ∀ {l : List α} {a : α}, a ∈ l → ∃ x ∈ l, ∀ y ∈ l, f y ≤ f x
  | [], _, ha => nomatch ha
  | b :: l, _, _ => by
    cases l with
    | nil => exact ⟨b, List.mem_singleton_self b, fun y hy => Nat.le_of_eq (congrArg f (List.mem_singleton.mp hy))⟩
    | cons c l =>
      obtain ⟨x, hx, hmax⟩ := exists_max_mem f (List.mem_cons_self (a := c) (l := l))
      by_cases hle : f b ≤ f x
      · refine ⟨x, List.mem_cons_of_mem b hx, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hle
        · exact hmax y hy
      · refine ⟨b, List.mem_cons_self, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax y hy) (Nat.le_of_lt (Nat.lt_of_not_le hle))

/-- An open run of maximal depth exists while running (from `root_open` and finiteness). -/
theorem exists_deepestOpen (h : Reachable p s) (started : s.started = true) (running : s.status = .running) :
    ∃ r, DeepestOpen s r := by
  obtain ⟨r₀, hr₀, hc₀⟩ := root_open h started running
  have hmem : r₀ ∈ s.runs.filter (fun r => !r.complete) :=
    List.mem_filter.mpr ⟨(State.run?_eq_some hr₀).1, by simp [hc₀]⟩
  obtain ⟨r, hr, hmax⟩ := exists_max_mem (fun r : Run => r.path.length) hmem
  obtain ⟨hrm, hrc⟩ := List.mem_filter.mp hr
  exact ⟨r, hrm, by simpa using hrc, fun r' hr' hc' => hmax r' (List.mem_filter.mpr ⟨hr', by simp [hc']⟩)⟩

/-- The workflow of a run is a workflow of the definition. -/
private theorem workflow_mem {path : Path} {w : Workflow} (hw : s.workflow? p path = some w) :
    w ∈ p.workflows := by
  obtain ⟨_, -, hwf⟩ := Routing.workflow?_eq_some.mp hw
  exact (Definition.workflow?_eq_some hwf).1

/-- The concurrency of an execution has distinct task names (validity). -/
private theorem concurrency_names (valid : p.validate = .ok ()) {e : Execution} {cc : Concurrency}
    (hcc : s.concurrencyOf p e = .ok cc) : (cc.tasks.map (·.name)).Nodup := by
  obtain ⟨pl, hpl, hctrl⟩ := State.concurrencyOf_eq_ok.mp hcc
  obtain ⟨w, hw, hplw⟩ := State.placementOf_eq_ok.mp hpl
  exact (concurrency_settings valid w (workflow_mem hw) pl (Workflow.placement?_eq_some hplw).1 cc hctrl).1

/-- An undelivered eligible result gets its delivery: through `discard`, with the value the behavior
    answers, or as a failed transform when the behavior answers `none`. -/
private theorem deliver_case (valid : p.validate = .ok ()) (wk : s.WellKeyed) (started : s.started = true)
    (running : s.status = .running) (env : Env) {r : Result} (hr : r ∈ s.results) {w : Workflow}
    (hw : s.workflow? p r.run = some w) {j : Nat} {c : Connection} (hc : w.connections[j]? = some c)
    (hsrc : c.source = r.placement) (harm : c.arm = none ∨ c.arm = r.arm) (hnone : s.delivery? r.run j r.id = none) :
    ∃ op t, engine op = true ∧ Conforms env s op ∧ step p s op = .ok t ∧ t ≠ s := by
  have htarget : Step.deliveryTarget p s r.run j r.id = .ok (w, c) :=
    Step.deliveryTarget_eq_ok.mpr
      ⟨hw, hc, ⟨r, wk.result?_of_mem hr, rfl, hsrc.symm, harm.imp id Eq.symm⟩, hnone⟩
  obtain ⟨hdiscard, hdeclared⟩ := deliver_enabled started running htarget
  cases htr : c.transform with
  | discard =>
    obtain ⟨t, ht, hne⟩ := hdiscard htr
    exact ⟨.deliver r.run j r.id none, t, rfl, (fun v hv => nomatch hv), ht, hne⟩
  | declared id =>
    obtain ⟨hval, hfail⟩ := hdeclared id htr
    cases hb : env.behavior.transform r.run j r.id with
    | some v =>
      obtain ⟨t, ht, hne⟩ := hval v
      exact ⟨.deliver r.run j r.id (some v), t, rfl, (fun v' hv' => Option.some.inj hv' ▸ hb), ht, hne⟩
    | none =>
      -- A connection of a valid definition targets a placement of its workflow.
      have htgt : (w.placement? c.target).isSome := by
        obtain ⟨-, dst, -, hdst, -⟩ := typedConnections_of_validate valid w (workflow_mem hw) c
          (List.mem_of_getElem? hc)
        rw [hdst]
        rfl
      obtain ⟨t, ht, hne⟩ := hfail htgt
      exact ⟨.transformFailed r.run j r.id, t, rfl, hb, ht, hne⟩

/-- A pending result of a task in the output goes through the output transform, with the value the
    behavior answers or as a failure. -/
private theorem taskOutput_case (valid : p.validate = .ok ()) (h : Reachable p s) (started : s.started = true)
    (running : s.status = .running) (env : Env) {e : Execution} (he : e ∈ s.executions) {cc : Concurrency}
    (hcc : s.concurrencyOf p e = .ok cc) {r : TaskResult} (hr : r ∈ s.taskResults) (hre : r.execution = e.id)
    {spec : TaskSpec} (hspecm : spec ∈ cc.tasks) (hsn : spec.name = r.task) (hso : spec.output.isSome = true)
    (hpending : r.output = .pending) :
    ∃ op t, engine op = true ∧ Conforms env s op ∧ step p s op = .ok t ∧ t ≠ s := by
  have wk := h.wellKeyed
  have hspec : s.taskSpec p e r.task = .ok spec :=
    State.taskSpec_eq_ok.mpr ⟨cc, hcc, find?_eq_some_of_nodup (concurrency_names valid hcc) hspecm
      (fun y => by simp [hsn])⟩
  have hfind : s.taskResults.find? (fun x => x.execution == e.id && x.task == r.task && x.index == r.index) =
      some r :=
    find?_eq_some_of_nodup wk.taskResults hr (fun y => by simp [hre, and_assoc])
  have hfree : cc.output = .stream → s.result? (Key.taskOutput e.id r.task r.index) = none := fun _ => by
    rw [← hre]
    exact (Reachable.fresh h).taskOutput r hr hpending
  obtain ⟨hval, hfail⟩ :=
    taskOutput_enabled started running (wk.execution?_of_mem he) hcc hspec hso hfind hpending hfree
  cases hb : env.behavior.taskOutput e.id r.task r.index with
  | some v =>
    obtain ⟨t, ht, hne⟩ := hval v
    exact ⟨.taskOutput e.id r.task r.index v, t, rfl, hb, ht, hne⟩
  | none =>
    obtain ⟨t, ht, hne⟩ := hfail
    exact ⟨.taskOutputFailed e.id r.task r.index, t, rfl, hb, ht, hne⟩

/-- A pending task goes through its input transform: through `discard`, with the value the behavior
    answers, or as a failure. A pending task has an input transform (`pending_input`). -/
private theorem taskInput_case (valid : p.validate = .ok ()) (h : Reachable p s) (started : s.started = true)
    (running : s.status = .running) (env : Env) {e : Execution} (he : e ∈ s.executions) {t : TaskState}
    (ht : t ∈ e.tasks) (hpending : t.status = .pending) :
    ∃ op t', engine op = true ∧ Conforms env s op ∧ step p s op = .ok t' ∧ t' ≠ s := by
  have wk := h.wellKeyed
  -- The execution lists the tasks of its concurrency, so the task has a spec.
  obtain ⟨-, -, -, -, -, pl, cc, hpl, hctrl, hnames⟩ := (Settle.reachable h).1.execOwner e he
  have hcc : s.concurrencyOf p e = .ok cc := by
    refine State.concurrencyOf_eq_ok.mpr ⟨pl, State.placementOf_eq_ok.mpr ?_, hctrl⟩
    unfold Settle.placementAt at hpl
    exact Option.bind_eq_some_iff.mp hpl
  have hname : t.name ∈ cc.tasks.map (·.name) := by
    rw [← hnames]
    exact List.mem_map_of_mem ht
  obtain ⟨spec, hspecm, hsn⟩ := List.mem_map.mp hname
  have hspec : s.taskSpec p e t.name = .ok spec :=
    State.taskSpec_eq_ok.mpr ⟨cc, hcc, find?_eq_some_of_nodup (concurrency_names valid hcc) hspecm
      (fun y => by simp [hsn])⟩
  have hts : e.tasks.find? (·.name == t.name) = some t :=
    find?_eq_some_of_nodup (h.taskNames valid e he) ht (fun y => by simp)
  have hinput := pending_input valid h e he t ht hpending spec hspec
  obtain ⟨hdiscard, hdeclared⟩ :=
    taskInput_enabled started running (wk.execution?_of_mem he) hts hpending hspec
  cases hsi : spec.input with
  | none => rw [hsi] at hinput; cases hinput
  | some tr =>
    cases tr with
    | discard =>
      obtain ⟨t', ht', hne⟩ := hdiscard hsi
      exact ⟨.taskInput e.id t.name none, t', rfl, (fun v hv => nomatch hv), ht', hne⟩
    | declared id =>
      obtain ⟨hval, hfail⟩ := hdeclared id hsi
      cases hb : env.behavior.taskInput e.id t.name with
      | some v =>
        obtain ⟨t', ht', hne⟩ := hval v
        exact ⟨.taskInput e.id t.name (some v), t', rfl, (fun v' hv' => Option.some.inj hv' ▸ hb), ht', hne⟩
      | none =>
        obtain ⟨t', ht', hne⟩ := hfail
        exact ⟨.taskInputFailed e.id t.name, t', rfl, hb, ht', hne⟩

/-- An engine operation outside the run structure is accepted: a delivery or failed transform, a task
    input or output transform, a fetch of a running Stream call. Otherwise the state is calm. The
    transform operations take the environment's answer, so the operation conforms. -/
theorem easy_or_calm (valid : p.validate = .ok ()) (h : Reachable p s) (running : s.status = .running)
    (idle : ¬ Waiting s) (env : Env) :
    (∃ op t, engine op = true ∧ Conforms env s op ∧ step p s op = .ok t ∧ t ≠ s) ∨ Calm p s := by
  rcases h.eq_empty_or_started with rfl | started
  · -- The empty state has no records, so it is calm.
    exact Or.inr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  have wk := h.wellKeyed
  by_cases hdel : ∃ r ∈ s.results, ∃ w, s.workflow? p r.run = some w ∧ ∃ j c, w.connections[j]? = some c ∧
      c.source = r.placement ∧ (c.arm = none ∨ c.arm = r.arm) ∧ s.delivery? r.run j r.id = none
  · obtain ⟨r, hr, w, hw, j, c, hc, hsrc, harm, hnone⟩ := hdel
    exact Or.inl (deliver_case valid wk started running env hr hw hc hsrc harm hnone)
  by_cases hout : ∃ e ∈ s.executions, ∃ cc, s.concurrencyOf p e = .ok cc ∧ ∃ r ∈ s.taskResults,
      r.execution = e.id ∧ (∃ spec ∈ cc.tasks, spec.name = r.task ∧ spec.output.isSome) ∧ r.output = .pending
  · obtain ⟨e, he, cc, hcc, r, hr, hre, ⟨spec, hspecm, hsn, hso⟩, hpending⟩ := hout
    exact Or.inl (taskOutput_case valid h started running env he hcc hr hre hspecm hsn hso hpending)
  by_cases hin : ∃ e ∈ s.executions, ∃ t ∈ e.tasks, t.status = .pending
  · obtain ⟨e, he, t, ht, hpending⟩ := hin
    exact Or.inl (taskInput_case valid h started running env he ht hpending)
  by_cases hfetch : ∃ c ∈ s.calls, c.stream = true ∧ c.status = .running
  · obtain ⟨c, hc, hstream, hrun⟩ := hfetch
    obtain ⟨t, ht, hne⟩ := fetch_enabled (p := p) started running (wk.call?_of_mem hc) hstream hrun
    exact Or.inl ⟨.fetch c.id, t, rfl, trivial, ht, hne⟩
  refine Or.inr ⟨?_, ?_, ?_, ?_⟩
  · intro r hr w hw j c hc hsrc harm
    cases hd : s.delivery? r.run j r.id with
    | some _ => rfl
    | none => exact absurd ⟨r, hr, w, hw, j, c, hc, hsrc, harm, hd⟩ hdel
  · intro e he cc hcc r hr hre hspec hpending
    exact hout ⟨e, he, cc, hcc, r, hr, hre, hspec, hpending⟩
  · intro e he t ht hpending
    exact hin ⟨e, he, t, ht, hpending⟩
  · -- Not waiting leaves no fetching, cancelling or running Single call; no running Stream call is left.
    intro c hc
    cases hst : c.status with
    | running =>
      cases hs : c.stream with
      | true => exact absurd ⟨c, hc, hs, hst⟩ hfetch
      | false => exact absurd ⟨c, hc, Or.inr (Or.inr ⟨hst, hs⟩)⟩ idle
    | fetching => exact absurd ⟨c, hc, Or.inl hst⟩ idle
    | cancelling => exact absurd ⟨c, hc, Or.inr (Or.inl hst)⟩ idle
    | returned | failed | lost | cancelled => rfl

end ProgressEasy

end Suimon.Round3
