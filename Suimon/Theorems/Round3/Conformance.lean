import Suimon.Theorems.Basic
import Suimon.Theorems.Static
import Suimon.Theorems.Identity
import Suimon.Theorems.Limit
import Suimon.Theorems.Calls
import Suimon.Theorems.Routing
import Suimon.Theorems.Settle
import Suimon.Theorems.Status
import Suimon.Theorems.Delivery

namespace Suimon.Round3
open State

/-! ## [1] Round3/Conformance.lean — scaffold, no proof task

The outside world, conforming executions, and the facts every other file shares. -/

section Conformance

/-- How one call of a user function or judge ends, after the elements its script yields (§15.4).
    `timedOut` leaves the call cancelling until it terminates (§11.5). -/
inductive Ending where
  | returned (value : Value)
  | judged (arm : String)
  | ended
  | failed
  | timedOut (element : Bool)
  | lost
  deriving DecidableEq, Repr

/-- What one call does (§15.4): the elements it yields in order, then how it ends. "After the n-th
    element" is `yields.length`. A list makes every generator finite (§15.3). How a cancelled call
    terminates is not part of the script: `terminated` and `lost` of a cancelling call have the same
    effect in `Step.lean`, and both always conform. -/
structure Script where
  yields : List Value := []
  ending : Ending
  deriving DecidableEq, Repr

/-- The behavior of user processes and transforms, keyed only by schedule-independent identities
    (§15.4): calls by their identity (`Key.invocation …` or `Key.task …`), connection transforms by
    run, connection and source result, task input transforms by execution and task, task output
    transforms by execution, task and index. `none` is a failed transform. Values never enter
    identities, so "the same behavior" is literally the same `Behavior` value. -/
structure Behavior where
  script : String → Script
  transform : Path → Nat → ResultId → Option Value
  taskInput : String → String → Option Value
  taskOutput : String → String → Nat → Option Value

/-- The caller and the outside world: the external input, the behavior, and whether the caller may
    cancel. -/
structure Env where
  input : Option Value
  behavior : Behavior
  cancels : Bool := false

/-- An ending comes after all the elements of the script. -/
def Script.Final (sc : Script) (c : Call) : Prop := c.yields = sc.yields.length

/-- An operation conforms to the environment at `s`: its external data is what the environment says,
    for the call as it is stored in `s`. Engine decisions without external data always conform; the
    transform operations take the behavior's answer (`none` passes only through `discard`, which the
    step checks); every ending of a call comes after all its elements; a cancelling call may always
    terminate (§15.3). -/
def Conforms (env : Env) (s : State) : Op → Prop
  | .start input => input = env.input
  | .returned id v => ∃ c, s.call? id = some c ∧ (env.behavior.script id).Final c ∧
      (env.behavior.script id).ending = .returned v
  | .judged id a => ∃ c, s.call? id = some c ∧ (env.behavior.script id).Final c ∧
      (env.behavior.script id).ending = .judged a
  | .yielded id v => ∃ c, s.call? id = some c ∧ (env.behavior.script id).yields[c.yields]? = some v
  | .ended id => ∃ c, s.call? id = some c ∧ (env.behavior.script id).Final c ∧
      (env.behavior.script id).ending = .ended
  | .failed id => ∃ c, s.call? id = some c ∧ (env.behavior.script id).Final c ∧
      (env.behavior.script id).ending = .failed
  | .timedOut id element => ∃ c, s.call? id = some c ∧ (env.behavior.script id).Final c ∧
      (env.behavior.script id).ending = .timedOut element
  | .lost id => ∃ c, s.call? id = some c ∧
      (c.status = .cancelling ∨ ((env.behavior.script id).Final c ∧ (env.behavior.script id).ending = .lost))
  | .terminated _ => True
  | .deliver path index source value => ∀ v, value = some v → env.behavior.transform path index source = some v
  | .transformFailed path index source => env.behavior.transform path index source = none
  | .taskInput eid name value => ∀ v, value = some v → env.behavior.taskInput eid name = some v
  | .taskInputFailed eid name => env.behavior.taskInput eid name = none
  | .taskOutput eid name index value => env.behavior.taskOutput eid name index = some value
  | .taskOutputFailed eid name index => env.behavior.taskOutput eid name index = none
  | .cancel => env.cancels = true
  | .invoke .. | .fetch _ | .beginTask .. | .settle .. | .closeExecution _ | .closeRun _ | .conclude => True

/-- A conforming execution `tr` from the empty state to `s`: every operation conforms to the
    environment, is accepted, and changes the state. The only accepted operation that leaves a state
    unchanged is a repeated `cancel` while stopping; counting it would make every bound false. -/
inductive Conforming (p : Definition) (env : Env) : List Op → State → Prop
  | nil : Conforming p env [] {}
  | snoc {tr : List Op} {s t : State} {op : Op} : Conforming p env tr s → Conforms env s op →
      step p s op = .ok t → t ≠ s → Conforming p env (tr ++ [op]) t

theorem Conforming.reachable {p : Definition} {env : Env} {tr : List Op} {s : State} (h : Conforming p env tr s) :
    Reachable p s := by
  induction h with
  | nil => exact .empty
  | snoc _ _ hs _ ih => exact .step _ ih hs

/-- The workflow finished without a stop or a cancellation: the root run completed. Only `conclude`
    from a running state completes the root run, and a stop is never undone. -/
def Done (s : State) : Prop := (s.run? []).any (·.complete) = true

/-- Running, or concluded without a stop. Every state before an unstopped state is unstopped. -/
def Unstopped (s : State) : Prop := s.status = .running ∨ Done s

/-- No conforming operation changes `s`: the execution cannot be extended. -/
def Stuck (p : Definition) (env : Env) (s : State) : Prop :=
  ∀ op t, Conforms env s op → step p s op = .ok t → t = s

/-- Engine operations: decisions of the engine, including the application of transforms. The others
    are reports of user processes (`returned` … `terminated`) and the caller's `cancel`. -/
def engine : Op → Bool
  | .start _ | .invoke .. | .fetch _ | .deliver .. | .transformFailed .. | .taskInput .. | .taskInputFailed ..
  | .beginTask .. | .taskOutput .. | .taskOutputFailed .. | .settle .. | .closeExecution _ | .closeRun _
  | .conclude => true
  | _ => false

/-- The engine waits for the outside world: a call is fetching, cancelling, or running a Single
    function or a judge. A running Stream call does not wait: the engine must fetch (§4.1.1). -/
def Waiting (s : State) : Prop :=
  ∃ c ∈ s.calls, c.status = .fetching ∨ c.status = .cancelling ∨ (c.status = .running ∧ c.stream = false)

/-- The arms of the branch whose judge `c` is. -/
def judgeArms (p : Definition) (s : State) (c : Call) : List String :=
  match (s.invocation? c.owner).bind fun i => (s.workflow? p i.run).bind (·.placement? i.placement) with
  | some { control := .branch _ arms, .. } => arms
  | _ => []

/-- A script fits a call when the call's contract accepts its ending (§4.1, §7.1, §11.5): a Single
    function returns one value, a judge names an arm of its branch, a Stream function ends after its
    elements, and a timeout ends a call only when that timeout is configured. A Single call yields
    nothing, so its script has no elements. -/
def Script.Fits (sc : Script) (c : Call) (arms : List String) : Prop :=
  match sc.ending with
  | .returned _ => c.stream = false ∧ (∃ f, c.target = .function f) ∧ sc.yields = []
  | .judged a => (∃ j, c.target = .judge j) ∧ a ∈ arms ∧ sc.yields = []
  | .ended => c.stream = true
  | .failed | .lost => c.stream = true ∨ sc.yields = []
  | .timedOut true => c.stream = true ∧ c.timeout.elementMs.isSome = true
  | .timedOut false => c.timeout.callMs.isSome = true ∧ (c.stream = true ∨ sc.yields = [])

/-- The outside world answers every call an execution creates within the call's contract (§15.3).
    Semantic: it quantifies over the conforming executions of the same environment. -/
def Env.Fits (p : Definition) (env : Env) : Prop :=
  ∀ tr s, Conforming p env tr s → ∀ c ∈ s.calls, (env.behavior.script c.id).Fits c (judgeArms p s c)

/-- The caller passes an input exactly when the main workflow declares one (§3.1). -/
def Env.InputFits (p : Definition) (env : Env) : Prop :=
  ((p.workflow? p.main).bind (·.input)).isSome = env.input.isSome

/-- Equality up to the order of every record list. -/
structure Same (s t : State) : Prop where
  status : s.status = t.status
  started : s.started = t.started
  cancelled : s.cancelled = t.cancelled
  runs : s.runs.Perm t.runs
  invocations : s.invocations.Perm t.invocations
  calls : s.calls.Perm t.calls
  executions : s.executions.Perm t.executions
  results : s.results.Perm t.results
  taskResults : s.taskResults.Perm t.taskResults
  deliveries : s.deliveries.Perm t.deliveries
  settled : s.settled.Perm t.settled
  failures : s.failures.Perm t.failures

theorem Same.refl (s : State) : Same s s :=
  ⟨rfl, rfl, rfl, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _⟩

theorem Same.symm {s t : State} (h : Same s t) : Same t s :=
  ⟨h.status.symm, h.started.symm, h.cancelled.symm, h.runs.symm, h.invocations.symm, h.calls.symm,
    h.executions.symm, h.results.symm, h.taskResults.symm, h.deliveries.symm, h.settled.symm, h.failures.symm⟩

theorem Same.trans {s t u : State} (h₁ : Same s t) (h₂ : Same t u) : Same s u :=
  ⟨h₁.status.trans h₂.status, h₁.started.trans h₂.started, h₁.cancelled.trans h₂.cancelled,
    h₁.runs.trans h₂.runs, h₁.invocations.trans h₂.invocations, h₁.calls.trans h₂.calls,
    h₁.executions.trans h₂.executions, h₁.results.trans h₂.results, h₁.taskResults.trans h₂.taskResults,
    h₁.deliveries.trans h₂.deliveries, h₁.settled.trans h₂.settled, h₁.failures.trans h₂.failures⟩

/-- A list value is the multiset of its elements (§5.4, §15.4). -/
theorem listValue_perm {l₁ l₂ : List Value} (h : l₁.Perm l₂) : listValue l₁ = listValue l₂ := by
  unfold listValue
  have trans : ∀ a b c : String, decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true :=
    fun a b c hab hbc => decide_eq_true (String.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have total : ∀ a b : String, (decide (a ≤ b) || decide (b ≤ a)) = true := fun a b => by
    rcases String.le_total a b with h | h <;> simp [h]
  have e : l₁.mergeSort (fun a b => decide (a ≤ b)) = l₂.mergeSort (fun a b => decide (a ≤ b)) :=
    List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true)
      (fun a b _ _ hab hba => String.le_antisymm (of_decide_eq_true hab) (of_decide_eq_true hba))
      (List.pairwise_mergeSort trans total l₁) (List.pairwise_mergeSort trans total l₂)
      ((List.mergeSort_perm l₁ _).trans (h.trans (List.mergeSort_perm l₂ _).symm))
  rw [e]

/-- The call ranks of `callsAcyclic`: a workflow calls only workflows of higher rank, below the number
    of workflows. They bound the nesting of runs (fuel `p.depth`). -/
theorem call_rank {p : Definition} (valid : p.validate = .ok ()) :
    ∃ rank : String → Nat, (∀ w ∈ p.workflows, rank w.id < p.workflows.length) ∧
      ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ wf ∈ pl.control.workflowRefs, ∀ w' ∈ p.workflows,
        w'.id = wf → rank w.id < rank w'.id := by
  obtain ⟨rank, hlt, hedge⟩ := acyclic_rank (Definition.validate_ok valid).callsAcyclic
  refine ⟨rank, fun w hw => by simpa using hlt w.id (List.mem_map.mpr ⟨w, hw, rfl⟩), ?_⟩
  intro w hw pl hpl wf hwf w' hw' hid
  subst hid
  refine hedge (w.id, w'.id) ?_ (List.mem_map.mpr ⟨w, hw, rfl⟩) (List.mem_map.mpr ⟨w', hw', rfl⟩)
  exact List.mem_flatMap.mpr ⟨w, hw, List.mem_flatMap.mpr ⟨pl, hpl, List.mem_map.mpr ⟨w'.id, hwf, rfl⟩⟩⟩

/-- The placement ranks of `Workflow.acyclic`: connections go up in rank, below the number of
    placements. They order the placements of a run (progress) and bound `possibleResults`. -/
theorem placement_rank {p : Definition} (valid : p.validate = .ok ()) :
    ∀ w ∈ p.workflows, ∃ rank : String → Nat, (∀ pl ∈ w.placements, rank pl.name < w.placements.length) ∧
      ∀ c ∈ w.connections, rank c.source < rank c.target := by
  intro w hw
  have hwc := (Definition.validate_ok valid).workflows w hw
  obtain ⟨rank, hlt, hedge⟩ := acyclic_rank hwc.acyclic
  refine ⟨rank, fun pl hpl => by simpa using hlt pl.name (List.mem_map.mpr ⟨pl, hpl, rfl⟩), ?_⟩
  intro c hc
  obtain ⟨src, dst, hsrc, hdst, -⟩ := Definition.validateConnection_ok (hwc.connections c hc)
  obtain ⟨hsm, hsn⟩ := Workflow.placement?_eq_some hsrc
  obtain ⟨hdm, hdn⟩ := Workflow.placement?_eq_some hdst
  exact hedge (c.source, c.target) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    (List.mem_map.mpr ⟨src, hsm, hsn⟩) (List.mem_map.mpr ⟨dst, hdm, hdn⟩)

end Conformance

end Suimon.Round3
