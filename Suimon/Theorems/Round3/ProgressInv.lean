import Suimon.Theorems.Round3.Conformance
import Suimon.Theorems.Round3.ProgressInvStep

namespace Suimon.Round3
open State

/-! ## [3] Round3/ProgressInv.lean — task B1

Structural invariants for progress. Each is an induction over `Reachable` by `Step.*_inv`, on top of
the Round 2 invariants (`Settle.reachable`, `Delivery.Reachable.inv`, `Limit.reachable_inv`). -/

section ProgressInv
variable {p : Definition} {s : State}

/-- (N1) While running, the root run exists and is open: only `conclude` completes it. -/
theorem root_open (h : Reachable p s) (started : s.started = true) (running : s.status = .running) :
    ∃ r, s.run? [] = some r ∧ r.complete = false := by
  obtain ⟨r, hr, himp⟩ := ProgressInvAux.root_inv h started
  refine ⟨r, hr, ?_⟩
  cases hc : r.complete
  · rfl
  · have := himp hc
    rw [running] at this
    cases this

/-- (N7) Every run's workflow exists in a valid definition. -/
theorem run_workflow (valid : p.validate = .ok ()) (h : Reachable p s) :
    ∀ r ∈ s.runs, (p.workflow? r.workflow).isSome := by
  -- Runs name the main workflow or a workflow that some placement calls; validation declares both.
  suffices ref : ∀ r ∈ s.runs, ProgressInvAux.Referenced p r.workflow from
    fun r hr => ProgressInvAux.referenced_workflow valid (ref r hr)
  induction h with
  | empty => intro r hr; cases hr
  | @step s t op hr hs ih =>
    intro r hr'
    rcases ProgressInvAux.step_runs (Delivery.Reachable.inv hr) hs r hr' with h | ⟨r₀, hr₀, -, hwf, -⟩ | ⟨-, -, href⟩
    · exact ih r h
    · exact hwf ▸ ih r₀ hr₀
    · exact href

/-- The bodies of a stored invocation carry over to the next state under its identity. -/
theorem ProgressInvAux.InvBody.kept {t : State} {i₀ i : Invocation} (h : ProgressInvAux.InvBody p s i₀)
    (hk : Delivery.Kept s t) (wk : t.WellKeyed) (hw₀ : ∃ w, s.workflow? p i₀.run = some w) (hid : i.id = i₀.id)
    (hrun : i.run = i₀.run) (hpl : i.placement = i₀.placement) : ProgressInvAux.InvBody p t i := by
  intro w pl hw hplw
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hw₀' := hk.workflow? wk hw₀
  rw [← hrun, hw] at hw₀'
  cases hw₀'
  obtain ⟨hcall, hrunb, hexec⟩ := h w pl hw₀ (hpl ▸ hplw)
  refine ⟨fun hc => ?_, fun wf out hc => ?_, fun cc hc => ?_⟩
  · obtain ⟨c, hc, h1, h2, h3⟩ := hcall hc
    obtain ⟨c', hc', a1, a2, a3, -⟩ := hk.call c hc
    exact ⟨c', hc', by rw [a1, h1, hid], by rw [a2, h2, hid], by rw [a3, h3]⟩
  · obtain ⟨r, hr, h1, h2, h3, h4⟩ := hrunb wf out hc
    obtain ⟨r', hr', a1, a2, -, a4, a5, -⟩ := hk.run r hr
    exact ⟨r', hr', by rw [a1, h1, hrun, hid], by rw [a4, h2, hid], by rw [a5, h3], by rw [a2, h4]⟩
  · obtain ⟨e, he, h1⟩ := hexec cc hc
    obtain ⟨e', he', a1, -⟩ := hk.execution e he
    exact ⟨e', he', by rw [a1, h1, hid]⟩

/-- (N2) Every invocation has the record its control creates with it in the same step: the call of a
    function or a judge, the run of a sub-workflow, the execution of a concurrency. -/
theorem invocation_body (h : Reachable p s) : ∀ i ∈ s.invocations, ∀ w pl,
    s.workflow? p i.run = some w → w.placement? i.placement = some pl →
    (((∃ f, pl.control = .call (.function f)) ∨ (∃ j arms, pl.control = .branch j arms)) →
        ∃ c ∈ s.calls, c.id = i.id ∧ c.owner = i.id ∧ c.task = none) ∧
    (∀ wf out, pl.control = .call (.workflow wf out) →
        ∃ r ∈ s.runs, r.path = i.run ++ [i.id] ∧ r.owner = some i.id ∧ r.task = none ∧ r.workflow = wf) ∧
    (∀ cc, pl.control = .concurrency cc → ∃ e ∈ s.executions, e.id = i.id) := by
  suffices body : ∀ i ∈ s.invocations, ProgressInvAux.InvBody p s i from body
  induction h with
  | empty => intro i hi; cases hi
  | @step s t op hr hs ih =>
    have inv := Delivery.Reachable.inv hr
    have hk := inv.kept hs
    have wk := (Reachable.step op hr hs).wellKeyed
    -- The workflow of a stored invocation's run is found (`InvocationPlaced`).
    have placed : ∀ i₀ ∈ s.invocations, ∃ w, s.workflow? p i₀.run = some w := fun i₀ hi₀ => by
      obtain ⟨-, w, -, -, hw, -⟩ := inv.own.invocations i₀ hi₀
      exact ⟨w, hw⟩
    intro i hi
    rcases ProgressInvAux.step_invocations hs i hi with (hi' | ⟨⟨i₀, hi₀, a1, a2, a3, -, -⟩, -⟩) | ⟨-, -, hb⟩
    · exact (ih i hi').kept hk wk (placed i hi') rfl rfl rfl
    · exact (ih i₀ hi₀).kept hk wk (placed i₀ hi₀) a1.symm a2.symm a3.symm
    · exact hb

/-- The conjunction of (N3), stated once for the induction. -/
def ProgressInvAux.Closed (s : State) : Prop :=
  (∀ c ∈ s.calls, c.status.ended = true → c.task = none →
      ∀ i ∈ s.invocations, i.id = c.owner → i.status ≠ .active) ∧
  (∀ c ∈ s.calls, c.status.ended = true → ∀ name, c.task = some name →
      ∀ e ∈ s.executions, e.id = c.owner → ∀ t ∈ e.tasks, t.name = name → t.status.ended = true) ∧
  (∀ r ∈ s.runs, r.complete = true → r.task = none →
      ∀ i ∈ s.invocations, r.owner = some i.id → i.status ≠ .active) ∧
  (∀ r ∈ s.runs, r.complete = true → ∀ name, r.task = some name →
      ∀ e ∈ s.executions, r.owner = some e.id → ∀ t ∈ e.tasks, t.name = name → t.status.ended = true) ∧
  (∀ e ∈ s.executions, e.complete = true → ∀ i ∈ s.invocations, i.id = e.id → i.status ≠ .active)

/-- (N3) in every reachable state: a call ends, and a run or an execution completes, only in a step that
    also settles its owner (`step_calls`, `step_runs`, `step_executions`); afterwards an owner never
    becomes active again (`step_invocations`) and an ended task stays ended (`Moved`). -/
theorem ProgressInvAux.closed_inv (h : Reachable p s) : ProgressInvAux.Closed s := by
  induction h with
  | empty => exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  | @step s t op hr hs ih =>
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
    have wk := hr.wellKeyed
    have lim := Limit.reachable_inv hr
    have own := (Settle.reachable hr).1
    have hC := ProgressInvAux.step_calls wk lim hs
    have hR := ProgressInvAux.step_runs (Delivery.Reachable.inv hr) hs
    have hE := ProgressInvAux.step_executions (p := p) hs
    -- An active invocation after the step was stored before, or is the new one.
    have act : ∀ i ∈ t.invocations, i.status = .active → i ∈ s.invocations ∨ s.invocation? i.id = none := by
      intro i hi hact
      rcases ProgressInvAux.step_invocations (p := p) hs i hi with (hi | ⟨-, hne⟩) | ⟨hfresh, -⟩
      · exact Or.inl hi
      · exact absurd hact hne
      · exact Or.inr hfresh
    -- A task that has not ended after the step had not ended before, or its execution is new.
    have live : ∀ e ∈ t.executions, ∀ tk ∈ e.tasks, tk.status.ended = false →
        (∃ e₀ ∈ s.executions, e₀.id = e.id ∧ ∃ tk₀ ∈ e₀.tasks, tk₀.name = tk.name ∧ tk₀.status.ended = false) ∨
          s.execution? e.id = none := by
      intro e he tk htk hlive
      rcases hE e he with ⟨e₀, he₀, h1, -, -, -, htasks⟩ | ⟨hfresh, -⟩
      · obtain ⟨tk₀, htk₀, hn, hm⟩ := htasks tk htk
        refine Or.inl ⟨e₀, he₀, h1, tk₀, htk₀, hn, ?_⟩
        rcases hm with hm | hm | ⟨hm, -⟩ | ⟨hm, -⟩
        · rw [← hm]; exact hlive
        · rw [hm] at hlive; cases hlive
        · rw [hm]; rfl
        · rw [hm]; rfl
      · exact Or.inr hfresh
    have fresh_inv : ∀ {id : String}, s.invocation? id = none → ∀ i ∈ s.invocations, i.id ≠ id := by
      intro id hid i hi hi'
      exact State.invocation?_eq_none_iff.mp hid (List.mem_map.mpr ⟨i, hi, hi'⟩)
    have fresh_exec : ∀ {id : String}, s.execution? id = none → ∀ e ∈ s.executions, e.id ≠ id := by
      intro id hid e he he'
      exact State.execution?_eq_none_iff.mp hid (List.mem_map.mpr ⟨e, he, he'⟩)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc hend htask i hi hid hact
      rcases hC c hc hend with hc' | hclosed
      · rcases act i hi hact with hi' | hfresh
        · exact ih1 c hc' hend htask i hi' hid hact
        · obtain ⟨-, i', hi', hi'id, -⟩ := own.callNone c hc' htask
          exact fresh_inv hfresh i' hi' (hi'id.trans hid.symm)
      · exact hclosed.1 htask i hi hid hact
    · intro c hc hend name htask e he hid tk htk hname
      cases hlive : tk.status.ended
      · rcases hC c hc hend with hc' | hclosed
        · rcases live e he tk htk hlive with ⟨e₀, he₀, h1, tk₀, htk₀, hn, hlive₀⟩ | hfresh
          · rw [ih2 c hc' hend name htask e₀ he₀ (h1.trans hid) tk₀ htk₀ (hn.trans hname)] at hlive₀
            cases hlive₀
          · obtain ⟨e', he', he'id, -⟩ := lim.calls c hc' name htask
            exact absurd (he'id.trans hid.symm) (fresh_exec hfresh e' he')
        · rw [hclosed.2 name htask e he hid tk htk hname] at hlive
          cases hlive
      · rfl
    · intro r hr' hcomp htask i hi ho hact
      rcases hR r hr' with hr₀ | ⟨-, -, -, -, -, -, -, hclosed⟩ | ⟨-, hc, -⟩
      · rcases act i hi hact with hi' | hfresh
        · exact ih3 r hr₀ hcomp htask i hi' ho hact
        · obtain ⟨i', hi', hi'id, -⟩ := own.runNone r hr₀ i.id ho htask
          exact fresh_inv hfresh i' hi' hi'id
      · rcases hclosed with hnone | hclosed
        · rw [hnone] at ho; cases ho
        · exact hclosed.1 htask i hi ho hact
      · rw [hcomp] at hc; cases hc
    · intro r hr' hcomp name htask e he ho tk htk hname
      cases hlive : tk.status.ended
      · rcases hR r hr' with hr₀ | ⟨-, -, -, -, -, -, -, hclosed⟩ | ⟨-, hc, -⟩
        · rcases live e he tk htk hlive with ⟨e₀, he₀, h1, tk₀, htk₀, hn, hlive₀⟩ | hfresh
          · rw [ih4 r hr₀ hcomp name htask e₀ he₀ (by rw [ho, h1]) tk₀ htk₀ (hn.trans hname)] at hlive₀
            cases hlive₀
          · obtain ⟨e', he', he'id, -⟩ := lim.runs r hr₀ e.id name ho htask
            exact absurd he'id (fresh_exec hfresh e' he')
        · rcases hclosed with hnone | hclosed
          · rw [hnone] at ho; cases ho
          · rw [hclosed.2 name htask e he ho tk htk hname] at hlive
            cases hlive
        · rw [hcomp] at hc; cases hc
      · rfl
    · intro e he hcomp i hi hid hact
      rcases hE e he with ⟨e₀, he₀, h1, -, -, hc, -⟩ | ⟨-, hc, -⟩
      · rcases hc hcomp with hc₀ | hclosed
        · rcases act i hi hact with hi' | hfresh
          · exact ih5 e₀ he₀ hc₀ i hi' (hid.trans h1.symm) hact
          · obtain ⟨i', hi', hi'id, -⟩ := own.execOwner e₀ he₀
            exact fresh_inv hfresh i' hi' (hi'id.trans (h1.trans hid.symm))
        · exact hclosed i hi hid hact
      · rw [hcomp] at hc; cases hc

/-- (N2') An active task has its body: a call that has not ended, or a run that is open (§8.2). -/
theorem active_task_body (h : Reachable p s) :
    ∀ e ∈ s.executions, ∀ t ∈ e.tasks, t.status = .active →
      (∃ c ∈ s.calls, c.id = Key.task e.id t.name ∧ c.owner = e.id ∧ c.task = some t.name ∧ c.status.ended = false) ∨
      (∃ r ∈ s.runs, r.path = e.run ++ [Key.task e.id t.name] ∧ r.owner = some e.id ∧ r.task = some t.name ∧
        r.complete = false) := by
  suffices body : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status = .active → ProgressInvAux.TaskBody s e tk.name from
    body
  induction h with
  | empty => intro e he; cases he
  | @step s t op hr hs ih =>
    have hk := (Delivery.Reachable.inv hr).kept hs
    -- Once a body ended, its task ended (N3 in the new state), so a still active task keeps its body.
    obtain ⟨-, closed2, -, closed4, -⟩ := ProgressInvAux.closed_inv (Reachable.step op hr hs)
    intro e he tk htk hact
    rcases ProgressInvAux.step_executions (p := p) hs e he with ⟨e₀, he₀, h1, h2, -, -, htasks⟩ | ⟨-, -, htasks⟩
    · obtain ⟨tk₀, htk₀, hn, hm⟩ := htasks tk htk
      rcases hm with hm | hm | ⟨-, hm⟩ | ⟨-, -, hb⟩
      · have hact₀ : tk₀.status = .active := hm ▸ hact
        rcases ih e₀ he₀ tk₀ htk₀ hact₀ with ⟨c, hc, a1, a2, a3, a4⟩ | ⟨r, hr', a1, a2, a3, a4⟩
        · obtain ⟨c', hc', b1, b2, b3, -⟩ := hk.call c hc
          refine Or.inl ⟨c', hc', by rw [b1, a1, h1, hn], by rw [b2, a2, h1], by rw [b3, a3, hn], ?_⟩
          cases hend : c'.status.ended
          · rfl
          · have := closed2 c' hc' hend tk.name (by rw [b3, a3, hn]) e he (by rw [b2, a2, h1]) tk htk rfl
            rw [hact] at this
            cases this
        · obtain ⟨r', hr'', b1, -, -, b4, b5, -⟩ := hk.run r hr'
          refine Or.inr ⟨r', hr'', by rw [b1, a1, h1, h2, hn], by rw [b4, a2, h1], by rw [b5, a3, hn], ?_⟩
          cases hcomp : r'.complete
          · rfl
          · have := closed4 r' hr'' hcomp tk.name (by rw [b5, a3, hn]) e he (by rw [b4, a2, h1]) tk htk rfl
            rw [hact] at this
            cases this
      · rw [hact] at hm; cases hm
      · rw [hact] at hm; cases hm
      · exact hb
    · exact absurd hact (htasks tk htk).1

/-- (N3) An owner is no longer active once what it waits for is over: an ended call, a completed
    sub-run, a completed execution. (The converse directions are Round 2 `Settle.Active`.) -/
theorem owner_closed (h : Reachable p s) :
    (∀ c ∈ s.calls, c.status.ended = true → c.task = none →
        ∀ i ∈ s.invocations, i.id = c.owner → i.status ≠ .active) ∧
    (∀ c ∈ s.calls, c.status.ended = true → ∀ name, c.task = some name →
        ∀ e ∈ s.executions, e.id = c.owner → ∀ t ∈ e.tasks, t.name = name → t.status.ended = true) ∧
    (∀ r ∈ s.runs, r.complete = true → r.task = none →
        ∀ i ∈ s.invocations, r.owner = some i.id → i.status ≠ .active) ∧
    (∀ r ∈ s.runs, r.complete = true → ∀ name, r.task = some name →
        ∀ e ∈ s.executions, r.owner = some e.id → ∀ t ∈ e.tasks, t.name = name → t.status.ended = true) ∧
    (∀ e ∈ s.executions, e.complete = true → ∀ i ∈ s.invocations, i.id = e.id → i.status ≠ .active) :=
  ProgressInvAux.closed_inv h

/-- The core of (N8): a pending task belongs to a concurrency that takes an input. -/
theorem ProgressInvAux.pending_core (h : Reachable p s) :
    ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status = .pending → ∀ cc, s.concurrencyOf p e = .ok cc →
      cc.input.isSome = true := by
  induction h with
  | empty => intro e he; cases he
  | @step s t op hr hs ih =>
    have hk := (Delivery.Reachable.inv hr).kept hs
    have wk := (Reachable.step op hr hs).wellKeyed
    have lim := Limit.reachable_inv hr
    intro e he tk htk hpend cc hcc
    rcases ProgressInvAux.step_executions (p := p) hs e he with ⟨e₀, he₀, -, h2, h3, -, htasks⟩ | ⟨-, -, htasks⟩
    · obtain ⟨tk₀, htk₀, -, hm⟩ := htasks tk htk
      have hpend₀ : tk₀.status = .pending := by
        rcases hm with hm | hm | ⟨-, hm⟩ | ⟨-, hm, -⟩
        · exact hm ▸ hpend
        · rw [hpend] at hm; cases hm
        · rw [hpend] at hm; cases hm
        · rw [hpend] at hm; cases hm
      obtain ⟨w, pl, hw, hpl, hctl⟩ := Delivery.concurrencyOf_iff.mp hcc
      have hw₀ : s.workflow? p e₀.run = some w :=
        ProgressInvAux.workflow?_back hk wk (lim.execRuns e₀ he₀) (h2 ▸ hw)
      exact ih e₀ he₀ tk₀ htk₀ hpend₀ cc (Delivery.concurrencyOf_iff.mpr ⟨w, pl, hw₀, h3 ▸ hpl, hctl⟩)
    · exact (htasks tk htk).2 hpend cc hcc

/-- (N8) A pending task has an input transform: tasks are pending only when the concurrency takes an
    input, and then validation gives every task one (§8.1). -/
theorem pending_input (valid : p.validate = .ok ()) (h : Reachable p s) :
    ∀ e ∈ s.executions, ∀ t ∈ e.tasks, t.status = .pending → ∀ spec, s.taskSpec p e t.name = .ok spec →
      spec.input.isSome = true := by
  intro e he tk htk hpend spec hspec
  obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec
  have hin := ProgressInvAux.pending_core h e he tk htk hpend cc hcc
  obtain ⟨w, pl, hw, hpl, hctl⟩ := Delivery.concurrencyOf_iff.mp hcc
  obtain ⟨r, -, hwf⟩ := Delivery.workflow?_iff.mp hw
  obtain ⟨at_, hv⟩ := ProgressInvAux.tasks_of_validate valid (Definition.workflow?_eq_some hwf).1
    (Workflow.placement?_eq_some hpl).1 hctl spec (List.mem_of_find?_eq_some hfind)
  exact ProgressInvAux.input_of_validateTask hv hin

end ProgressInv

end Suimon.Round3
