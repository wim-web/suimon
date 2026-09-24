import Suimon.Theorems.DeliveryFrame

/-! The invariants behind delivery completeness, and the records a step can create.

    Ownership: every run other than the root belongs to a sub-workflow invocation or to a task of an
    execution, every execution to a concurrency invocation, every call to an invocation or a task, and
    every result to the invocation that produced it (or to the aggregate of a settled waitStream or
    Merge). Statuses: an invocation that is no longer active has stopped all it owns, a running task
    call keeps its task active, and a complete execution has stopped all its tasks and transformed
    every result in its output. Settlements: a settled placement has ended all its invocations, used
    up its input, and, for a Single output settled without a value, has no result on that arm. -/

namespace Suimon.Delivery
open State

/-! ### Ownership -/

/-- A run is the root, or the run of a sub-workflow call, or the run of a workflow task (§4.5, §8.1). --/
def RunOwned (p : Definition) (s : State) (r : Run) : Prop :=
  (r.owner = none ∧ r.task = none ∧ r.path = []) ∨
  (r.task = none ∧ ∃ i ∈ s.invocations, r.owner = some i.id ∧ r.path = Key.child i.id ∧
    ∃ w pl wf out, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧
      pl.control = .call (.workflow wf out)) ∨
  (∃ name, r.task = some name ∧ ∃ e ∈ s.executions, r.owner = some e.id ∧ r.path = Key.child (Key.task e.id name) ∧
    (∃ tk ∈ e.tasks, tk.name = name) ∧ ∃ spec wf out, s.taskSpec p e name = .ok spec ∧ spec.body = .workflow wf out)

/-- An invocation is identified by where it comes from, applies an invocable placement of its run, and
    took a trigger that fits the input shape; only a branch records an arm. --/
def InvocationPlaced (p : Definition) (s : State) (i : Invocation) : Prop :=
  i.id = Key.invocation i.run i.placement i.trigger ∧
  ∃ w pl sh, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧ Invocable pl.control ∧
    w.shape? p i.placement = some sh ∧ TriggerOk s i.run i sh ∧ (i.arm = none ∨ ∃ j arms, pl.control = .branch j arms)

/-- A call belongs to the invocation of a function call or branch, or to a task with a function body. --/
def CallOwned (p : Definition) (s : State) (c : Call) : Prop :=
  (c.task = none ∧ c.id = c.owner ∧ ∃ i ∈ s.invocations, i.id = c.owner ∧ ∃ w pl, s.workflow? p i.run = some w ∧
    w.placement? i.placement = some pl ∧
    ((∃ f d, pl.control = .call (.function f) ∧ p.function? f = some d ∧ c.target = .function f ∧
        c.stream = (d.output.kind == .stream)) ∨
     (∃ j arms, pl.control = .branch j arms ∧ c.target = .judge j ∧ c.stream = false))) ∨
  (∃ name, c.task = some name ∧ c.id = Key.task c.owner name ∧ ∃ e ∈ s.executions, e.id = c.owner ∧
    (∃ tk ∈ e.tasks, tk.name = name) ∧ ∃ spec f, s.taskSpec p e name = .ok spec ∧ spec.body = .function f)

/-- An execution belongs to the invocation of its concurrency placement. --/
def ExecutionOwned (p : Definition) (s : State) (e : Execution) : Prop :=
  ∃ i ∈ s.invocations, i.id = e.id ∧ i.run = e.run ∧ i.placement = e.placement ∧ ∃ c, s.concurrencyOf p e = .ok c

/-- A delivery carries a result of its connection's source, on the connection's arm (§6, §7.2). --/
def DeliveryEligible (p : Definition) (s : State) (d : Delivery) : Prop :=
  ∃ w c r, s.workflow? p d.run = some w ∧ w.connections[d.connection]? = some c ∧ r ∈ s.results ∧
    r.id = d.source ∧ r.run = d.run ∧ r.placement = c.source ∧ (c.arm = none ∨ r.arm = c.arm)

structure Own (p : Definition) (s : State) : Prop where
  runs : ∀ r ∈ s.runs, RunOwned p s r
  invocations : ∀ i ∈ s.invocations, InvocationPlaced p s i
  calls : ∀ c ∈ s.calls, CallOwned p s c
  executions : ∀ e ∈ s.executions, ExecutionOwned p s e
  deliveries : ∀ d ∈ s.deliveries, DeliveryEligible p s d

/-! ### Statuses -/

/-- The placement of `i` is a Stream function call or a concurrency with Stream output: its results are
    accepted before its invocation ends and stay if it fails (§4.1, §8.3). --/
def StreamSource (p : Definition) (s : State) (i : Invocation) : Prop :=
  ∃ w pl, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧
    ((∃ f d, pl.control = .call (.function f) ∧ p.function? f = some d ∧ d.output.kind = .stream) ∨
     (∃ c, pl.control = .concurrency c ∧ c.output = .stream))

/-- A result belongs to the invocation that produced it, which succeeded unless its results stream,
    or it is the aggregate of a waitStream or Merge that settled normally (§9, §10.2). --/
def ResultOwned (p : Definition) (s : State) (r : Result) : Prop :=
  (∃ i ∈ s.invocations, i.id = r.producer ∧ i.run = r.run ∧ i.placement = r.placement ∧ i.arm = r.arm ∧
    (i.status = .succeeded ∨ StreamSource p s i)) ∨
  (r.producer = Key.aggregate r.run r.placement ∧ r.arm = none ∧
    ∃ x ∈ s.settled, x.run = r.run ∧ x.placement = r.placement ∧ x.outcome = .normal ∧ x.arms = [])

structure Dyn (p : Definition) (s : State) : Prop where
  /-- Until the conclusion, an invocation that is no longer active runs no call, and its sub-run and
      execution completed; after a stop, the conclusion ends the invocations of open runs and
      executions (`State.endUnfinished`). --/
  nonActive : s.status.terminal = false → ∀ i ∈ s.invocations, i.status ≠ .active →
    (∀ c ∈ s.calls, c.owner = i.id → c.task = none → c.status ≠ .running ∧ c.status ≠ .fetching) ∧
    (∀ r ∈ s.runs, r.owner = some i.id → r.task = none → r.complete = true) ∧
    (∀ e ∈ s.executions, e.id = i.id → e.complete = true)
  /-- A running or fetching task call keeps its task active. --/
  taskActive : ∀ c ∈ s.calls, ∀ name, c.task = some name → (c.status = .running ∨ c.status = .fetching) →
    ∀ e ∈ s.executions, e.id = c.owner → ∀ tk ∈ e.tasks, tk.name = name → tk.status = .active
  /-- A complete execution ended its task calls, completed its task runs and transformed its output. --/
  execDone : ∀ e ∈ s.executions, e.complete = true →
    (∀ c ∈ s.calls, c.owner = e.id → c.task ≠ none → c.status.ended = true) ∧
    (∀ r ∈ s.runs, r.owner = some e.id → r.task ≠ none → r.complete = true) ∧
    (∀ c, s.concurrencyOf p e = .ok c → ∀ r ∈ s.taskResults, r.execution = e.id →
      (∃ spec ∈ c.tasks, spec.name = r.task ∧ spec.output.isSome) → r.output ≠ .pending)
  results : ∀ r ∈ s.results, ResultOwned p s r

/-! ### Settlements -/

structure Sett (p : Definition) (s : State) : Prop where
  /-- A settled placement ended all its invocations (§10.3). --/
  ended : ∀ x ∈ s.settled, ∀ i ∈ s.invocations, i.run = x.run → i.placement = x.placement →
    s.invocationEnded i = true
  /-- A settled placement used up its input. --/
  input : ∀ x ∈ s.settled, ∃ w pl sh, s.workflow? p x.run = some w ∧ w.placement? x.placement = some pl ∧
    w.shape? p x.placement = some sh ∧ InputDone s x.run pl sh
  /-- A Single output settled without a value on an arm has no result on that arm (§7.2, §10.1). --/
  none : ∀ x ∈ s.settled, ∀ w, s.workflow? p x.run = some w → w.outputKind? p x.placement = some .single →
    ∀ a, armOutcome x a ≠ .normal → ∀ r ∈ s.results, r.run = x.run → r.placement = x.placement →
      a ≠ none ∧ r.arm ≠ a
  /-- A complete run ended its invocations and settled every placement (§4.5, §13.3). --/
  runs : ∀ r ∈ s.runs, r.complete = true → (∀ i ∈ s.invocations, i.run = r.path → s.invocationEnded i = true) ∧
    ∀ w, p.workflow? r.workflow = some w → ∀ pl ∈ w.placements, (s.settled? r.path pl.name).isSome

/-- The invariant of reachable states. --/
structure Inv (p : Definition) (s : State) : Prop where
  wk : s.WellKeyed
  fresh : s.started = false → s = {}
  own : Own p s
  dyn : Dyn p s
  sett : Sett p s

/-! ### Records a step creates -/

/-- An invocation `invoke` creates, with what it checked. --/
def NewInvocation (p : Definition) (s : State) (i : Invocation) : Prop :=
  s.started = true ∧ s.status = .running ∧
  ∃ r w pl, s.run? i.run = some r ∧ r.complete = false ∧ p.workflow? r.workflow = some w ∧
    w.placement? i.placement = some pl ∧ Invocable pl.control ∧
    Step.invocationInput p s r w i.placement i.trigger = .ok i.input ∧
    i.id = Key.invocation i.run i.placement i.trigger ∧ i.status = .active ∧ i.arm = none ∧
    (∀ i' ∈ s.invocationsOf i.run i.placement, i'.trigger ≠ i.trigger) ∧ s.invocation? i.id = none

/-- A call `invoke` or `beginTask` creates. --/
def NewCall (p : Definition) (s t : State) (c : Call) : Prop :=
  s.call? c.id = none ∧ c.status = .running ∧
  ((c.task = none ∧ c.id = c.owner ∧ ∃ i ∈ t.invocations, i.id = c.owner ∧ NewInvocation p s i ∧
      ∃ w pl, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧
      ((∃ f d, pl.control = .call (.function f) ∧ p.function? f = some d ∧ c.target = .function f ∧
          c.stream = (d.output.kind == .stream)) ∨
       (∃ j arms, pl.control = .branch j arms ∧ c.target = .judge j ∧ c.stream = false))) ∨
   (∃ name e ts spec f, c.task = some name ∧ c.id = Key.task c.owner name ∧ s.execution? c.owner = some e ∧
      e.complete = false ∧ e.tasks.find? (·.name == name) = some ts ∧ ts.status = .ready ∧
      s.taskSpec p e name = .ok spec ∧ spec.body = .function f ∧
      withTask e { ts with status := .active } ∈ t.executions ∧ s.status = .running))

/-- A run `start`, `invoke` or `beginTask` creates. --/
def NewRun (p : Definition) (s t : State) (r : Run) : Prop :=
  s.run? r.path = none ∧ r.complete = false ∧
  ((s.started = false ∧ r.owner = none ∧ r.task = none ∧ r.path = []) ∨
   (r.task = none ∧ ∃ i ∈ t.invocations, r.owner = some i.id ∧ NewInvocation p s i ∧ r.path = Key.child i.id ∧
      ∃ w pl wf out, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧
        pl.control = .call (.workflow wf out)) ∨
   (∃ name e ts spec wf out, r.task = some name ∧ r.owner = some e.id ∧ s.execution? e.id = some e ∧
      e.complete = false ∧ e.tasks.find? (·.name == name) = some ts ∧ ts.status = .ready ∧
      s.taskSpec p e name = .ok spec ∧ spec.body = .workflow wf out ∧ r.path = Key.child (Key.task e.id name) ∧
      withTask e { ts with status := .active } ∈ t.executions ∧ s.status = .running))

/-- An execution `invoke` creates. --/
def NewExecution (p : Definition) (s t : State) (e : Execution) : Prop :=
  s.execution? e.id = none ∧ e.complete = false ∧
  ∃ i ∈ t.invocations, i.id = e.id ∧ i.run = e.run ∧ i.placement = e.placement ∧ NewInvocation p s i ∧
    ∃ w pl c, s.workflow? p e.run = some w ∧ w.placement? e.placement = some pl ∧ pl.control = .concurrency c ∧
      e.tasks.map (·.name) = c.tasks.map (·.name) ∧ ∀ tk ∈ e.tasks, tk.status ≠ .active

/-- A result a step accepts, with where it came from (§10.2). --/
def NewResult (p : Definition) (s t : State) (r : Result) : Prop :=
  s.started = true ∧ s.status = .running ∧ s.result? r.id = none ∧
  ((∃ c ∈ s.calls, ∃ i ∈ s.invocations, c.task = none ∧ c.status = .running ∧ c.stream = false ∧
      (∃ f, c.target = .function f) ∧ i.id = c.owner ∧ r.run = i.run ∧ r.placement = i.placement ∧
      r.producer = c.id ∧ r.arm = none ∧ { i with status := .succeeded } ∈ t.invocations) ∨
   (∃ c ∈ s.calls, ∃ i ∈ s.invocations, ∃ arm j arms w pl, c.task = none ∧ c.status = .running ∧ i.id = c.owner ∧
      s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧ pl.control = .branch j arms ∧
      r.run = i.run ∧ r.placement = i.placement ∧ r.producer = c.id ∧ r.arm = some arm ∧
      { i with status := .succeeded, arm := some arm } ∈ t.invocations) ∨
   (∃ c ∈ s.calls, ∃ i ∈ s.invocations, c.task = none ∧ c.status = .fetching ∧ c.stream = true ∧ i.id = c.owner ∧
      r.run = i.run ∧ r.placement = i.placement ∧ r.producer = c.id ∧ r.arm = none) ∨
   (∃ e ∈ s.executions, ∃ c tr, s.concurrencyOf p e = .ok c ∧ c.output = .stream ∧ tr ∈ s.taskResults ∧
      tr.execution = e.id ∧ tr.output = .pending ∧ (∃ spec ∈ c.tasks, spec.name = tr.task ∧ spec.output.isSome) ∧
      r.run = e.run ∧ r.placement = e.placement ∧ r.producer = e.id ∧ r.arm = none) ∨
   (∃ e ∈ s.executions, ∃ i ∈ s.invocations, ∃ c, e.complete = false ∧ i.id = e.id ∧ s.concurrencyOf p e = .ok c ∧
      c.output = .list ∧ r.run = e.run ∧ r.placement = e.placement ∧ r.producer = e.id ∧ r.arm = none ∧
      { i with status := .succeeded } ∈ t.invocations) ∨
   (∃ R ∈ s.runs, ∃ i ∈ s.invocations, R.complete = false ∧ R.task = none ∧ R.owner = some i.id ∧
      r.run = i.run ∧ r.placement = i.placement ∧ r.producer = i.id ∧ r.arm = none ∧
      { i with status := .succeeded } ∈ t.invocations) ∨
   (∃ run w pl shape kind x, s.run? r.run = some run ∧ p.workflow? run.workflow = some w ∧
      w.placement? r.placement = some pl ∧ s.settled? r.run r.placement = none ∧ w.shape? p r.placement = some shape ∧
      w.outputKind? p r.placement = some kind ∧ s.settleOutcome r.run pl shape kind = some (x, some r) ∧
      x ∈ t.settled))

/-- A delivery a step records, checked against the state before it. --/
def NewDelivery (p : Definition) (s : State) (d : Delivery) : Prop :=
  s.started = true ∧ s.status = .running ∧ s.delivery? d.run d.connection d.source = none ∧
  ∃ w c r, s.workflow? p d.run = some w ∧ w.connections[d.connection]? = some c ∧ s.result? d.source = some r ∧
    r.run = d.run ∧ r.placement = c.source ∧ (c.arm = none ∨ r.arm = c.arm)

/-- A settlement a step records: `settle` changes nothing else but may add the aggregate. --/
def NewSettled (p : Definition) (s t : State) (x : Settled) : Prop :=
  s.started = true ∧ s.status = .running ∧
  ∃ run w pl shape kind res, s.run? x.run = some run ∧ run.complete = false ∧ p.workflow? run.workflow = some w ∧
    w.placement? x.placement = some pl ∧ s.settled? x.run x.placement = none ∧ w.shape? p x.placement = some shape ∧
    w.outputKind? p x.placement = some kind ∧ s.settleOutcome x.run pl shape kind = some (x, res) ∧
    t.settled = s.settled ++ [x] ∧ t.results = s.results ++ res.toList ∧ t.runs = s.runs ∧
    t.invocations = s.invocations ∧ t.calls = s.calls ∧ t.executions = s.executions ∧ t.deliveries = s.deliveries ∧
    t.taskResults = s.taskResults ∧ ∀ r, res = some r → s.result? r.id = none

end Suimon.Delivery
