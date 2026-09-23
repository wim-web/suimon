import Suimon.Theorems.SettleBase

/-! The invariants behind the settlement theorems, in four layers, each preserved using the ones
    before it.

    `Own` records who owns each call, run and execution and where each invocation is placed;
    `Active` what keeps an owner active; `Prov` which trigger each invocation took and where each
    result, task result and delivery comes from; `SettledInv` records, for each settled placement,
    that its invocations ended, why it takes no new input, that it has no result on an arm it settled
    without a value, and the value of a waitStream result. -/

namespace Suimon.Settle

open State

/-- The placement a run's workflow declares under a name. --/
def placementAt (p : Program) (s : State) (path : Path) (name : String) : Option Placement :=
  (s.workflow? p path).bind (·.placement? name)

/-- Controls that are invoked: calls, branches and concurrencies. --/
def invocable : Control → Bool
  | .call _ | .branch _ _ | .concurrency _ => true
  | _ => false

/-- The tasks whose results a concurrency outputs. --/
def included (cc : Concurrency) : List String := (cc.tasks.filter (·.output.isSome)).map (·.name)

/-- The trigger of an invocation is available on its placement's input (§3.1, §5.3). --/
def TriggerOk (p : Program) (s : State) (w : Workflow) (i : Invocation) : Prop :=
  match w.shape? p i.placement with
  | some .none | some .entry => i.trigger = none
  | some (.single idx c) => ∃ src v, i.trigger = some src ∧ s.resolveSingle i.run idx c = .value src v
  | some (.stream idx _) => ∃ src d, i.trigger = some src ∧ s.delivery? i.run idx src = some d ∧ d.outcome ≠ .failed
  | _ => False

/-- Where a result comes from: the aggregate of a placement settled normally, a call of an
    invocation, an execution, or a completed sub-workflow run. A call without a Stream contract
    and an execution or run give results only to a succeeded invocation; a Stream call gives
    results to an invocation that is never skipped. --/
def ResultOk (p : Program) (s : State) (r : Result) : Prop :=
  (∃ x ∈ s.settled, x.run = r.run ∧ x.placement = r.placement ∧ x.outcome = .normal ∧ x.arms = []) ∨
  (∃ c ∈ s.calls, c.task = none ∧ ∃ i ∈ s.invocations, i.id = c.owner ∧ i.run = r.run ∧ i.placement = r.placement ∧
    ((c.stream = false ∧ i.status = .succeeded ∧ r.arm = i.arm) ∨ (c.stream = true ∧ i.status ≠ .skipped))) ∨
  (∃ e ∈ s.executions, ∃ i ∈ s.invocations, i.id = e.id ∧ i.run = r.run ∧ i.placement = r.placement ∧
    (i.status = .succeeded ∨ (i.status = .active ∧ ∃ tr ∈ s.taskResults, tr.execution = e.id ∧
      ∀ cc, s.concurrencyOf p e = .ok cc → tr.task ∈ included cc))) ∨
  (∃ i ∈ s.invocations, i.run = r.run ∧ i.placement = r.placement ∧ i.status = .succeeded ∧
    ∃ pl wf out, placementAt p s i.run i.placement = some pl ∧ pl.control = .call (.workflow wf out))

/-- Layer 1: who owns each call, run and execution, and where each invocation is placed. --/
structure Own (p : Program) (s : State) : Prop where
  /-- A call of an invocation has the invocation's identity and belongs to a function call or a
      branch; its Stream flag follows the function's contract. --/
  callNone : ∀ c ∈ s.calls, c.task = none → c.id = c.owner ∧ ∃ i ∈ s.invocations, i.id = c.owner ∧ ∃ pl,
    placementAt p s i.run i.placement = some pl ∧
    ((∃ f decl, pl.control = .call (.function f) ∧ p.function? f = some decl ∧
        c.stream = (decl.output.kind == .stream)) ∨
     (∃ j arms, pl.control = .branch j arms ∧ c.stream = false))
  /-- An execution belongs to an invocation of a concurrency and lists its tasks. --/
  execOwner : ∀ e ∈ s.executions, ∃ i ∈ s.invocations, i.id = e.id ∧ i.run = e.run ∧ i.placement = e.placement ∧
    ∃ pl cc, placementAt p s e.run e.placement = some pl ∧ pl.control = .concurrency cc ∧
      e.tasks.map (·.name) = cc.tasks.map (·.name)
  /-- A run called by an invocation is the one run of a sub-workflow call. --/
  runNone : ∀ r ∈ s.runs, ∀ o, r.owner = some o → r.task = none → ∃ i ∈ s.invocations, i.id = o ∧
    r.path = i.run ++ [i.id] ∧ ∃ pl wf out, placementAt p s i.run i.placement = some pl ∧
      pl.control = .call (.workflow wf out)
  /-- A call of a task has the task's identity and a function body. --/
  callTask : ∀ c ∈ s.calls, ∀ name, c.task = some name → c.id = Key.task c.owner name ∧
    ∃ e ∈ s.executions, e.id = c.owner ∧ ∃ spec f, s.taskSpec p e name = .ok spec ∧ spec.body = .function f
  /-- A run of a task is the one run of a task with a workflow body. --/
  runTask : ∀ r ∈ s.runs, ∀ name, r.task = some name → ∃ e ∈ s.executions, r.owner = some e.id ∧
    r.path = e.run ++ [Key.task e.id name] ∧ ∃ spec wf out, s.taskSpec p e name = .ok spec ∧
      spec.body = .workflow wf out
  /-- An invocation is identified by its run, placement and trigger. --/
  invId : ∀ i ∈ s.invocations, i.id = Key.invocation i.run i.placement i.trigger
  /-- An invocation belongs to an invoked placement. --/
  invPlaced : ∀ i ∈ s.invocations, ∃ w pl, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧
    invocable pl.control = true

/-- Layer 2: what keeps an owner active. --/
structure Active (p : Program) (s : State) : Prop where
  /-- A running or fetching call keeps its invocation active. --/
  callActive : ∀ c ∈ s.calls, c.task = none → (c.status = .running ∨ c.status = .fetching) →
    ∃ i ∈ s.invocations, i.id = c.owner ∧ i.status = .active
  /-- An open execution keeps its invocation active. --/
  execActive : ∀ e ∈ s.executions, e.complete = false → ∃ i ∈ s.invocations, i.id = e.id ∧ i.status = .active
  /-- An open sub-workflow run keeps its invocation active. --/
  runActive : ∀ r ∈ s.runs, ∀ o, r.owner = some o → r.task = none → r.complete = false →
    ∃ i ∈ s.invocations, i.id = o ∧ i.status = .active
  /-- A running or fetching task call keeps its task active in an open execution. --/
  taskCallActive : ∀ c ∈ s.calls, ∀ name, c.task = some name → (c.status = .running ∨ c.status = .fetching) →
    ∃ e ∈ s.executions, e.id = c.owner ∧ e.complete = false ∧
      ∃ ts, e.tasks.find? (·.name == name) = some ts ∧ ts.status = .active
  /-- An open task run belongs to an open execution. --/
  taskRunOpen : ∀ r ∈ s.runs, ∀ name, r.task = some name → r.complete = false →
    ∃ e ∈ s.executions, r.owner = some e.id ∧ e.complete = false
  /-- A complete execution transformed every result it outputs. --/
  completeOutputs : ∀ e ∈ s.executions, e.complete = true → ∀ tr ∈ s.taskResults, tr.execution = e.id →
    ∀ cc, s.concurrencyOf p e = .ok cc → tr.task ∈ included cc → tr.output ≠ .pending
  /-- An active invocation has no selected arm yet. --/
  activeArm : ∀ i ∈ s.invocations, i.status = .active → i.arm = none

/-- Layer 3: where triggers, results, task results and deliveries come from. --/
structure Prov (p : Program) (s : State) : Prop where
  /-- An invocation took a trigger available on its placement's input. --/
  invTrigger : ∀ i ∈ s.invocations, ∃ w, s.workflow? p i.run = some w ∧ TriggerOk p s w i
  results : ∀ r ∈ s.results, ResultOk p s r
  /-- A skipped task has no result. --/
  skipped : ∀ e ∈ s.executions, ∀ name ts, e.tasks.find? (·.name == name) = some ts → ts.status = .skipped →
    ∀ tr ∈ s.taskResults, tr.execution = e.id → tr.task ≠ name
  /-- A task result comes from a call of the task or from its completed run. --/
  taskResultSrc : ∀ tr ∈ s.taskResults, (∃ c ∈ s.calls, c.owner = tr.execution ∧ c.task = some tr.task) ∨
    (∃ r ∈ s.runs, r.owner = some tr.execution ∧ r.task = some tr.task ∧ r.complete = true)
  /-- A delivery carries an eligible result of its connection. --/
  deliveries : ∀ d ∈ s.deliveries, ∃ w, s.workflow? p d.run = some w ∧ ∃ c, w.connections[d.connection]? = some c ∧
    ∃ r ∈ s.results, r.id = d.source ∧ r.run = d.run ∧ r.placement = c.source ∧
      (c.arm.isNone || r.arm == c.arm) = true
  /-- A succeeded sub-workflow call has a completed run (§4.5). --/
  callRun : ∀ i ∈ s.invocations, i.status = .succeeded → ∀ pl, placementAt p s i.run i.placement = some pl →
    (∃ wf out, pl.control = .call (.workflow wf out)) →
      ∃ r ∈ s.runs, r.owner = some i.id ∧ r.task = none ∧ r.complete = true
  /-- A completed run settled all its placements (§4.5, §13.3). --/
  completeSettled : ∀ r ∈ s.runs, r.complete = true → ∀ w, p.workflow? r.workflow = some w →
    ∀ pl ∈ w.placements, (s.settled? r.path pl.name).isSome

/-- Why a settled placement takes no new input: the invocation for its trigger exists, or its
    Single input will never carry a value, or its Stream input ended and each delivered element
    started an invocation (§10.3). --/
def Closed (p : Program) (s : State) (x : Settled) (w : Workflow) (pl : Placement) : Prop :=
  match w.shape? p x.placement with
  | some .none | some .entry =>
    invocable pl.control = true → ∃ i ∈ s.invocationsOf x.run x.placement, i.trigger = none
  | some (.single idx c) =>
    (∀ src v, s.resolveSingle x.run idx c = .value src v →
      ∃ i ∈ s.invocationsOf x.run x.placement, i.trigger = some src) ∧
    (s.deliveriesOn x.run idx = [] → ∃ y, s.settled? x.run c.source = some y ∧ State.armOutcome y c.arm ≠ .normal)
  | some (.stream idx c) =>
    (s.settled? x.run c.source).isSome ∧ (∀ r ∈ s.eligible x.run c, (s.delivery? x.run idx r.id).isSome) ∧
    (invocable pl.control = true → Triggered s x.run x.placement idx)
  | _ => True

/-- The settlement invariant. --/
structure SettledInv (p : Program) (s : State) : Prop where
  /-- The invocations of a settled placement ended (§10.3). --/
  ended : ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement, s.invocationEnded i = true
  closed : ∀ x ∈ s.settled, ∃ w pl, s.workflow? p x.run = some w ∧ w.placement? x.placement = some pl ∧
    Closed p s x w pl
  /-- A placement settled without a value on an arm has no result on it (§7.3). --/
  noEligible : ∀ x ∈ s.settled, ∀ arm, State.armOutcome x arm ≠ .normal →
    ∀ r ∈ s.resultsOf x.run x.placement, (arm.isNone || r.arm == arm) = false
  /-- A waitStream result lists the values delivered on its input (§9.1). --/
  waitValue : ∀ r ∈ s.results, ∀ w pl i c, s.workflow? p r.run = some w → w.placement? r.placement = some pl →
    (∃ e, pl.control = .waitStream e) → w.shape? p r.placement = some (.stream i c) →
      r.value = listValue (deliveredValues (s.deliveriesOn r.run i))

end Suimon.Settle
