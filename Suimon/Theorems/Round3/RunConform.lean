import Suimon.Theorems.Round3.Conformance
import Suimon.Theorems.Round3.RunConformInv
import Suimon.Theorems.Round3.RunConformStable

namespace Suimon.Round3
open State

/-! ## [13] Round3/RunConform.lean — task E1

Single-run invariants of conforming executions that determinism needs. `callConform` is task E2 in
[14]; the other components are here. -/

section RunConformSection
variable {p : Program} {env : Env} {s t : State}

/-- A stop is never undone and only `conclude` from a running state completes the root run, so the
    state before an unstopped state is unstopped. -/
theorem unstopped_of_step {op : Op} (h : Reachable p s) (hs : step p s op = .ok t) (ht : Unstopped t) :
    Unstopped s := by
  exact RunConformAux.unstopped_back hs ht

/-- A call stands where its script puts it: no more elements than the script; an ending only as the
    script says, after all its elements; without a stop, a call is cancelled only by its own timeout
    (§11.5); and its results are exactly the elements it reported, its returned value, or its judged arm
    on the invocation's input. -/
structure CallConform (env : Env) (s : State) (c : Call) : Prop where
  yields : c.yields ≤ (env.behavior.script c.id).yields.length
  single : c.stream = false → c.yields = 0
  returned : c.status = .returned → (env.behavior.script c.id).Final c ∧
    ((c.stream = false ∧ ((∃ v, (env.behavior.script c.id).ending = .returned v) ∨
        ∃ a, (env.behavior.script c.id).ending = .judged a)) ∨
     (c.stream = true ∧ (env.behavior.script c.id).ending = .ended))
  failed : c.status = .failed → (env.behavior.script c.id).Final c ∧ (env.behavior.script c.id).ending = .failed
  lost : c.status = .lost → (env.behavior.script c.id).Final c ∧ (env.behavior.script c.id).ending = .lost
  cancelled : c.status = .cancelling ∨ c.status = .cancelled →
    (env.behavior.script c.id).Final c ∧ ∃ el, (env.behavior.script c.id).ending = .timedOut el
  results : ∀ k, (∃ r ∈ s.results, r.id = Key.callResult c.id k) ↔
    c.task = none ∧ (if c.stream then k < c.yields else k = 0 ∧ c.status = .returned)
  values : ∀ r ∈ s.results, ∀ k, r.id = Key.callResult c.id k → r.producer = c.id ∧
    ∃ i, s.invocation? c.owner = some i ∧ r.run = i.run ∧ r.placement = i.placement ∧
      (c.stream = true → (env.behavior.script c.id).yields[k]? = some r.value ∧ r.arm = none) ∧
      (∀ v, c.stream = false → (env.behavior.script c.id).ending = .returned v → r.value = v ∧ r.arm = none) ∧
      (∀ a, c.stream = false → (env.behavior.script c.id).ending = .judged a →
        r.value = i.input.getD "" ∧ r.arm = some a)
  taskResults : ∀ name, c.task = some name → ∀ k,
    (∃ r ∈ s.taskResults, r.execution = c.owner ∧ r.task = name ∧ r.index = k) ↔
      (if c.stream then k < c.yields else k = 0 ∧ c.status = .returned)
  taskValues : ∀ name, c.task = some name → ∀ r ∈ s.taskResults, r.execution = c.owner → r.task = name →
    (c.stream = true → (env.behavior.script c.id).yields[r.index]? = some r.value) ∧
    (∀ v, c.stream = false → (env.behavior.script c.id).ending = .returned v → r.value = v)

/-- The owner of an ended call carries its end (§10.1): succeeded after a return or a normal end,
    failed after a failure, a loss or a timeout (a cancelled call was timed out, since nothing stopped). -/
def OwnerConform (s : State) (c : Call) : Prop :=
  (c.status = .returned →
    match c.task with
    | none => ∃ i, s.invocation? c.owner = some i ∧ i.status = .succeeded
    | some name => ∃ e ts, s.execution? c.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ts.status = .succeeded) ∧
  (c.status = .failed ∨ c.status = .lost ∨ c.status = .cancelling ∨ c.status = .cancelled →
    match c.task with
    | none => ∃ i, s.invocation? c.owner = some i ∧ i.status = .failed
    | some name => ∃ e ts, s.execution? c.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ts.status = .failed)

/-- A delivery holds what its transform gave (§4.2): the trigger through `discard`, otherwise the
    behavior's value or failure. -/
def DeliveryConform (p : Program) (env : Env) (s : State) (d : Delivery) : Prop :=
  ∃ w c, s.workflow? p d.run = some w ∧ w.connections[d.connection]? = some c ∧
    match c.transform with
    | .discard => d.outcome = .trigger
    | .declared _ =>
      match env.behavior.transform d.run d.connection d.source with
      | some v => d.outcome = .value v
      | none => d.outcome = .failed

/-- Neither a call nor a run of this task exists. -/
def NotBegun (s : State) (e : Execution) (name : String) : Prop :=
  s.call? (Key.task e.id name) = none ∧ ∀ r ∈ s.runs, ¬ (r.owner = some e.id ∧ r.task = some name)

/-- Tasks follow the behavior's input and output transforms (§8.1); without a stop, a task past `ready`
    started its body unless its input transform failed. -/
structure TaskConform (p : Program) (env : Env) (s : State) : Prop where
  input : ∀ e ∈ s.executions, ∀ t ∈ e.tasks, ∀ spec, s.taskSpec p e t.name = .ok spec → t.status ≠ .pending →
    match spec.input with
    | some (.declared _) =>
      (env.behavior.taskInput e.id t.name = none ∧ t.status = .failed ∧ t.input = none ∧ NotBegun s e t.name) ∨
      (∃ v, env.behavior.taskInput e.id t.name = some v ∧ t.input = some v)
    | _ => t.input = none
  begun : ∀ e ∈ s.executions, ∀ t ∈ e.tasks, t.status ≠ .pending → t.status ≠ .ready → NotBegun s e t.name →
    t.status = .failed ∧ env.behavior.taskInput e.id t.name = none
  output : ∀ r ∈ s.taskResults, (∀ v, r.output = .value v → env.behavior.taskOutput r.execution r.task r.index = some v) ∧
    (r.output = .failed → env.behavior.taskOutput r.execution r.task r.index = none)

/-- In a run that has not stopped, every failure was recorded under the continue policy (a stop policy
    would have stopped it, §11.3). -/
structure PolicyConform (p : Program) (s : State) : Prop where
  calls : ∀ c ∈ s.calls, (c.status = .failed ∨ c.status = .lost ∨ c.status = .cancelling ∨ c.status = .cancelled) →
    c.policy = .continue
  deliveries : ∀ d ∈ s.deliveries, d.outcome = .failed → ∀ w c pl, s.workflow? p d.run = some w →
    w.connections[d.connection]? = some c → w.placement? c.target = some pl → pl.policy = .continue
  tasks : ∀ e ∈ s.executions, ∀ t ∈ e.tasks, t.status = .failed → NotBegun s e t.name → ∀ spec,
    s.taskSpec p e t.name = .ok spec → spec.policy = .continue
  outputs : ∀ r ∈ s.taskResults, r.output = .failed → ∀ e spec, s.execution? r.execution = some e →
    s.taskSpec p e r.task = .ok spec → spec.policy = .continue

/-- The single-run invariants of a conforming execution, in a state that has not stopped. -/
structure RunConform (p : Program) (env : Env) (s : State) : Prop where
  calls : ∀ c ∈ s.calls, CallConform env s c ∧ OwnerConform s c
  deliveries : ∀ d ∈ s.deliveries, DeliveryConform p env s d
  tasks : TaskConform p env s
  policies : PolicyConform p s

/-- Every delivery took the behavior's answer, stopped or not. -/
theorem deliveryConform {tr : List Op} (h : Conforming p env tr s) : ∀ d ∈ s.deliveries, DeliveryConform p env s d := by
  induction h with
  | nil => intro d hd; cases hd
  | @snoc tr s₀ t₀ op hprev hconf hs _ ih =>
    have hr := hprev.reachable
    have K := (Delivery.Reachable.inv hr).kept hs
    have wk' := step_wellKeyed hr.wellKeyed hs
    -- An old delivery keeps its run's workflow.
    have old : ∀ d ∈ s₀.deliveries, DeliveryConform p env t₀ d := by
      intro d hd
      obtain ⟨w, c, hw, hc, hm⟩ := ih d hd
      exact ⟨w, c, K.workflow? wk' hw, hc, hm⟩
    intro d hd
    rcases (Delivery.step_deliveries_settled_eq hs).1 with hdel | ⟨path, j, src, ⟨v, rfl⟩ | rfl⟩
    · exact old d (hdel ▸ hd)
    · obtain ⟨-, -, w, c, outcome, hdt, hcase, ht⟩ := Step.deliver_inv hs
      obtain ⟨hw, hc, -, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
      have hd' : d ∈ s₀.deliveries ++ [{ run := path, connection := j, source := src, outcome }] := by
        rw [ht] at hd; exact hd
      simp only [List.mem_append, List.mem_singleton] at hd'
      rcases hd' with hd' | rfl
      · exact old d hd'
      · refine ⟨w, c, K.workflow? wk' hw, hc, ?_⟩
        rcases hcase with ⟨tid, v', htr, rfl, rfl⟩ | ⟨htr, rfl, rfl⟩
        · simp only [htr, hconf v' rfl]
        · simp only [htr]
    · obtain ⟨-, -, w, c, tid, target, hdt, htr, -, ht⟩ := Step.transformFailed_inv hs
      obtain ⟨hw, hc, -, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
      have hd' : d ∈ s₀.deliveries ++ [{ run := path, connection := j, source := src, outcome := .failed }] := by
        rw [ht] at hd; simpa using hd
      simp only [List.mem_append, List.mem_singleton] at hd'
      rcases hd' with hd' | rfl
      · exact old d hd'
      · refine ⟨w, c, K.workflow? wk' hw, hc, ?_⟩
        simp only [htr, show env.behavior.transform path j src = none from hconf]

theorem taskConform (valid : p.validate = .ok ()) {tr : List Op} (h : Conforming p env tr s) (us : Unstopped s) :
    TaskConform p env s := by
  have inv := RunConformAux.conforming_taskInv valid h us
  refine ⟨?_, inv.begun, inv.output⟩
  intro e he tk htk spec hspec hpend
  cases hin : spec.input with
  | none => exact inv.other e he tk htk spec hspec hpend (by simp [hin])
  | some tr' =>
    cases tr' with
    | declared tid => exact inv.declared e he tk htk spec hspec hpend tid hin
    | discard => exact inv.other e he tk htk spec hspec hpend (by simp [hin])

/-- Conformance is not needed: an unstopped state recorded every failure under `continue`. -/
theorem policyConform (h : Reachable p s) (us : Unstopped s) : PolicyConform p s := by
  have inv := RunConformAux.reachable_policyInv h us
  exact ⟨inv.calls, inv.deliveries, inv.tasks, inv.outputs⟩

/-- An invocation's input is what its trigger carries now: the run input for the entry, the delivered
    value otherwise (deliveries are immutable, and a Single connection carries at most one). -/
def InputStable (p : Program) (s : State) : Prop :=
  ∀ i ∈ s.invocations, ∃ r w, s.run? i.run = some r ∧ p.workflow? r.workflow = some w ∧
    Step.invocationInput p s r w i.placement i.trigger = .ok i.input

theorem Reachable.inputStable (valid : p.validate = .ok ()) (h : Reachable p s) : InputStable p s := by
  induction h with
  | empty => intro i hi; cases hi
  | step op hr hs ih =>
    intro i hi
    rcases Delivery.step_invocations_back hs i hi with ⟨i₀, hi₀, -, hrun, hpl, htr, hin⟩ | hnew
    · obtain ⟨r, w, hr', hw, hinput⟩ := ih i₀ hi₀
      obtain ⟨r', hr'', hwf, hinput'⟩ := RunConformAux.invocationInput_step hr hs hr' hinput
      refine ⟨r', w, ?_, by rw [hwf]; exact hw, ?_⟩
      · rw [← hrun]; exact hr''
      · rw [← hpl, ← htr, ← hin]; exact hinput'
    · obtain ⟨-, -, r, w, pl, hr', -, hw, -, -, hinput, -⟩ := hnew
      obtain ⟨r', hr'', hwf, hinput'⟩ := RunConformAux.invocationInput_step hr hs hr' hinput
      exact ⟨r', w, hr'', by rw [hwf]; exact hw, hinput'⟩

/-- The Stream output of a concurrency is exactly its transformed task results (§8.3). -/
def OutputResults (p : Program) (s : State) : Prop :=
  (∀ tr ∈ s.taskResults, ∀ v, tr.output = .value v → ∀ e cc, s.execution? tr.execution = some e →
      s.concurrencyOf p e = .ok cc → cc.output = .stream →
      ({ id := Key.taskOutput e.id tr.task tr.index, run := e.run, placement := e.placement, producer := e.id,
         value := v } : Result) ∈ s.results) ∧
  (∀ r ∈ s.results, ∀ eid name k, r.id = Key.taskOutput eid name k →
      ∃ tr ∈ s.taskResults, tr.execution = eid ∧ tr.task = name ∧ tr.index = k ∧ tr.output = .value r.value)

theorem Reachable.outputResults (h : Reachable p s) : OutputResults p s := by
  induction h with
  | empty => exact ⟨fun tr htr => (by cases htr), fun r hr => (by cases hr)⟩
  | @step s₀ t₀ op hr hs ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have wk := hr.wellKeyed
    have K := (Delivery.Reachable.inv hr).kept hs
    refine ⟨?_, ?_⟩
    · intro tr htr v hv e cc he hcc hout
      rcases RunConformAux.step_taskResultFrom hs htr with htr₀ | hpend | ⟨-, -, -, -, -, -, -, hcase⟩
      · -- A task result transformed before the step: its result was recorded then.
        obtain ⟨e₀, he₀, heid, -⟩ := (Limit.reachable_inv hr).results tr htr₀
        have he₀' : s₀.execution? tr.execution = some e₀ := by rw [← heid]; exact wk.execution?_of_mem he₀
        obtain ⟨hrun, hpl⟩ := RunConformAux.execution?_step hr hs he₀' he
        have hcc₀ : s₀.concurrencyOf p e₀ = .ok cc := by
          rw [← RunConformAux.concurrencyOf_step hr hs he₀ hrun hpl]; exact hcc
        have heid' : e.id = e₀.id := by rw [(execution?_eq_some he).2, (execution?_eq_some he₀').2]
        rw [heid', hrun, hpl]
        exact K.mem_results (ih₁ tr htr₀ v hv e₀ cc he₀' hcc₀ hout)
      · rw [hpend] at hv; cases hv
      · rcases hcase with ⟨v', hop, hout'⟩ | ⟨-, hout'⟩
        · -- `taskOutput` just transformed it and recorded the result of a Stream output.
          rw [hout'] at hv
          cases hv
          subst hop
          obtain ⟨-, -, e₁, c₁, spec₁, r₁, he₁, hc₁, -, -, -, -, hcase'⟩ := Step.taskOutput_inv hs
          obtain ⟨hrun, hpl⟩ := RunConformAux.execution?_step hr hs he₁ he
          rw [RunConformAux.concurrencyOf_step hr hs (execution?_eq_some he₁).1 hrun hpl, hc₁] at hcc
          cases hcc
          have heid : e.id = tr.execution := (execution?_eq_some he).2
          rcases hcase' with ⟨-, -, rfl⟩ | ⟨hlist, -⟩
          · rw [heid, hrun, hpl]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · rw [hout] at hlist; cases hlist
        · rw [hout'] at hv; cases hv
    · intro r hres eid name k hid
      rcases RunConformAux.step_taskOutput_result hs hres hid with hr₀ | hnew
      · obtain ⟨tr, htr, h1, h2, h3, h4⟩ := ih₂ r hr₀ eid name k hid
        obtain ⟨tr', htr', a1, a2, a3, a4⟩ := K.taskResult tr htr
        exact ⟨tr', htr', a1.trans h1, a2.trans h2, a3.trans h3, by rw [a4 (by rw [h4]; simp)]; exact h4⟩
      · exact hnew

end RunConformSection

end Suimon.Round3
