import Suimon.Theorems.StepLemmas

/-! Inversion lemmas for the operational rules: for each `Step.*` function (and the helpers they
    call), which preconditions held and exactly which state a successful call returns. -/

namespace Suimon

variable {p : Definition} {s t : State}

/-! ### Dispatch -/

@[simp] theorem step_start {input : Option Value} : step p s (.start input) = Step.start p s input := rfl
@[simp] theorem step_invoke {path : Path} {name : String} {trigger : Option ResultId} :
    step p s (.invoke path name trigger) = Step.invoke p s path name trigger := rfl
@[simp] theorem step_fetch {id : String} : step p s (.fetch id) = Step.fetch s id := rfl
@[simp] theorem step_returned {id : String} {value : Value} : step p s (.returned id value) = Step.returned s id value :=
  rfl
@[simp] theorem step_judged {id arm : String} : step p s (.judged id arm) = Step.judged p s id arm := rfl
@[simp] theorem step_yielded {id : String} {value : Value} : step p s (.yielded id value) = Step.yielded s id value :=
  rfl
@[simp] theorem step_ended {id : String} : step p s (.ended id) = Step.ended s id := rfl
@[simp] theorem step_failed {id : String} : step p s (.failed id) = Step.failed s id := rfl
@[simp] theorem step_timedOut {id : String} {element : Bool} :
    step p s (.timedOut id element) = Step.timedOut s id element := rfl
@[simp] theorem step_lost {id : String} : step p s (.lost id) = Step.lost s id := rfl
@[simp] theorem step_terminated {id : String} : step p s (.terminated id) = Step.terminated s id := rfl
@[simp] theorem step_deliver {path : Path} {index : Nat} {source : ResultId} {value : Option Value} :
    step p s (.deliver path index source value) = Step.deliver p s path index source value := rfl
@[simp] theorem step_transformFailed {path : Path} {index : Nat} {source : ResultId} :
    step p s (.transformFailed path index source) = Step.transformFailed p s path index source := rfl
@[simp] theorem step_taskInput {eid name : String} {value : Option Value} :
    step p s (.taskInput eid name value) = Step.taskInput p s eid name value := rfl
@[simp] theorem step_taskInputFailed {eid name : String} :
    step p s (.taskInputFailed eid name) = Step.taskInputFailed p s eid name := rfl
@[simp] theorem step_beginTask {eid name : String} : step p s (.beginTask eid name) = Step.beginTask p s eid name :=
  rfl
@[simp] theorem step_taskOutput {eid name : String} {index : Nat} {value : Value} :
    step p s (.taskOutput eid name index value) = Step.taskOutput p s eid name index value := rfl
@[simp] theorem step_taskOutputFailed {eid name : String} {index : Nat} :
    step p s (.taskOutputFailed eid name index) = Step.taskOutputFailed p s eid name index := rfl
@[simp] theorem step_settle {path : Path} {name : String} : step p s (.settle path name) = Step.settle p s path name :=
  rfl
@[simp] theorem step_closeExecution {eid : String} : step p s (.closeExecution eid) = Step.closeExecution p s eid :=
  rfl
@[simp] theorem step_closeRun {path : Path} : step p s (.closeRun path) = Step.closeRun p s path := rfl
@[simp] theorem step_cancel : step p s .cancel = Step.cancel s := rfl
@[simp] theorem step_conclude : step p s .conclude = Step.conclude p s := rfl

/-! ### Helpers -/

@[simp] theorem Step.running_eq_ok {u : Unit} : Step.running s = .ok u ↔ s.started = true ∧ s.status = .running := by
  simp [Step.running]

@[simp] theorem Step.getCall_eq_ok {id : String} {c : Call} : Step.getCall s id = .ok c ↔ s.call? id = some c :=
  need_eq_ok

@[simp] theorem Step.getExecution_eq_ok {id : String} {e : Execution} :
    Step.getExecution s id = .ok e ↔ s.execution? id = some e :=
  need_eq_ok

@[simp] theorem State.task_eq_ok {e : Execution} {name : String} {ts : TaskState} :
    State.task e name = .ok ts ↔ e.tasks.find? (·.name == name) = some ts :=
  need_eq_ok

@[simp] theorem Step.taskResult_eq_ok {eid name : String} {index : Nat} {r : TaskResult} :
    Step.taskResult s eid name index = .ok r ↔
      s.taskResults.find? (fun x => x.execution == eid && x.task == name && x.index == index) = some r :=
  need_eq_ok

@[simp] theorem State.placementOf_eq_ok {path : Path} {name : String} {pl : Placement} :
    s.placementOf p path name = .ok pl ↔ ∃ w, s.workflow? p path = some w ∧ w.placement? name = some pl := by
  simp [State.placementOf]

theorem State.concurrencyOf_eq_ok {e : Execution} {c : Concurrency} :
    s.concurrencyOf p e = .ok c ↔ ∃ pl, s.placementOf p e.run e.placement = .ok pl ∧ pl.control = .concurrency c := by
  simp only [State.concurrencyOf, bind_eq_ok]
  constructor
  · rintro ⟨pl, h1, h2⟩
    refine ⟨pl, h1, ?_⟩
    split at h2
    · rename_i c' hc
      simp only [pure_eq_ok] at h2
      rw [hc, h2]
    · simp at h2
  · rintro ⟨pl, h1, h2⟩
    exact ⟨pl, h1, by simp [h2]⟩

theorem State.taskSpec_eq_ok {e : Execution} {name : String} {spec : TaskSpec} :
    s.taskSpec p e name = .ok spec ↔ ∃ c, s.concurrencyOf p e = .ok c ∧ c.tasks.find? (·.name == name) = some spec := by
  simp [State.taskSpec]

theorem State.callFailure_eq_ok {c : Call} {cause : Cause} {f : Failure} :
    s.callFailure c cause = .ok f ↔
      (c.task = none ∧ ∃ i, s.invocation? c.owner = some i ∧ f = { run := i.run, placement := i.placement, cause }) ∨
      (∃ name e, c.task = some name ∧ s.execution? c.owner = some e ∧
        f = { run := e.run, placement := e.placement, task := some name, cause }) := by
  unfold State.callFailure
  split <;> rename_i h <;> simp [h]

theorem State.accept_eq_ok {c : Call} {index : Nat} {value : Value} {arm : Option String} :
    s.accept c index value arm = .ok t ↔
      (c.task = none ∧ ∃ i, s.invocation? c.owner = some i ∧ s.result? (Key.callResult c.id index) = none ∧
        t = { s with results := s.results ++
          [{ id := Key.callResult c.id index, run := i.run, placement := i.placement, producer := c.id, arm,
             value }] }) ∨
      (∃ name, c.task = some name ∧
        (s.taskResults.any fun x => x.execution == c.owner && x.task == name && x.index == index) = false ∧
        t = { s with taskResults := s.taskResults ++ [{ execution := c.owner, task := name, index, value }] }) := by
  unfold State.accept
  split <;> rename_i h <;> simp [h]

theorem State.settleOwner_eq_ok {c : Call} {inv : InvocationStatus} {task : TaskStatus} :
    s.settleOwner c inv task = .ok t ↔
      (c.task = none ∧ ∃ i, s.invocation? c.owner = some i ∧ t = s.setInvocation { i with status := inv }) ∨
      (∃ name e ts, c.task = some name ∧ s.execution? c.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        t = s.setTask e { ts with status := task }) := by
  unfold State.settleOwner
  split <;> rename_i h <;> simp [h]

theorem State.cancelOwner_eq_ok {c : Call} :
    s.cancelOwner c = .ok t ↔
      (c.task = none ∧ ∃ i, s.invocation? c.owner = some i ∧
        t = if i.status = .active then s.setInvocation { i with status := .cancelled } else s) ∨
      (∃ name e ts, c.task = some name ∧ s.execution? c.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        t = if ts.status = .active then s.setTask e { ts with status := .cancelled } else s) := by
  unfold State.cancelOwner
  split <;> rename_i h <;> simp [h]

theorem State.failCall_eq_ok {c : Call} {status : CallStatus} {cause : Cause} :
    s.failCall c status cause = .ok t ↔
      ∃ f s', s.callFailure c cause = .ok f ∧ (s.setCall { c with status }).settleOwner c .failed .failed = .ok s' ∧
        t = s'.fail f c.policy := by
  simp [State.failCall]

theorem State.designatedOutput_eq_ok {r : Run} {output : String} :
    s.designatedOutput p r = .ok output ↔
      ∃ owner, r.owner = some owner ∧
        ((r.task = none ∧ ∃ i pl wf, s.invocation? owner = some i ∧ s.placementOf p i.run i.placement = .ok pl ∧
            pl.control = .call (.workflow wf output)) ∨
         (∃ name e spec wf, r.task = some name ∧ s.execution? owner = some e ∧ s.taskSpec p e name = .ok spec ∧
            spec.body = .workflow wf output)) := by
  unfold State.designatedOutput
  rcases hr : r.owner with _ | owner <;> rcases ht : r.task with _ | name <;> simp
  · constructor
    · rintro ⟨i, hi, pl, hpl, h⟩
      refine ⟨i, hi, pl, hpl, ?_⟩
      split at h
      · split at h
        · simp only [pure_eq_ok] at h
          subst h
          simp_all
        · simp at h
      · simp at h
    · rintro ⟨i, hi, pl, hpl, wf, hc⟩
      exact ⟨i, hi, pl, hpl, by simp [hc]⟩
  · constructor
    · rintro ⟨e, he, spec, hspec, h⟩
      refine ⟨e, he, spec, hspec, ?_⟩
      split at h
      · simp only [pure_eq_ok] at h
        subst h
        simp_all
      · simp at h
    · rintro ⟨e, he, spec, hspec, wf, hc⟩
      exact ⟨e, he, spec, hspec, by simp [hc]⟩

/-- The input an invocation takes, by the shape of its placement's input. --/
theorem Step.invocationInput_inv {r : Run} {w : Workflow} {name : String} {trigger : Option ResultId}
    {input : Option Value} (h : Step.invocationInput p s r w name trigger = .ok input) :
    (w.shape? p name = some .none ∧ trigger = none ∧ input = none) ∨
    (w.shape? p name = some .entry ∧ trigger = none ∧ input = r.input) ∨
    (∃ i c source, w.shape? p name = some (.single i c) ∧ trigger = some source ∧
      s.resolveSingle r.path i c = .value source input) ∨
    (∃ i c source d, w.shape? p name = some (.stream i c) ∧ trigger = some source ∧
      s.delivery? r.path i source = some d ∧
      ((∃ v, d.outcome = .value v ∧ input = some v) ∨ (d.outcome = .trigger ∧ input = none))) := by
  unfold Step.invocationInput at h
  simp only [bind_eq_ok, need_eq_ok] at h
  obtain ⟨shape, hshape, h⟩ := h
  split at h
  · simp only [pure_eq_ok] at h
    exact Or.inl ⟨hshape, rfl, h⟩
  · simp only [pure_eq_ok] at h
    exact Or.inr (Or.inl ⟨hshape, rfl, h⟩)
  · rename_i i c source
    split at h
    · rename_i delivered input' hres
      simp only [bind_eq_ok, require_eq_ok, pure_eq_ok, exists_unit_iff, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨i, c, delivered, hshape, rfl, hres⟩))
    · simp at h
  · rename_i i c source
    split at h
    · rename_i v hd
      simp only [pure_eq_ok] at h
      obtain ⟨d, hd, hout⟩ := Option.map_eq_some_iff.mp hd
      exact Or.inr (Or.inr (Or.inr ⟨i, c, source, d, hshape, rfl, hd, Or.inl ⟨v, hout, h⟩⟩))
    · rename_i hd
      simp only [pure_eq_ok] at h
      obtain ⟨d, hd, hout⟩ := Option.map_eq_some_iff.mp hd
      exact Or.inr (Or.inr (Or.inr ⟨i, c, source, d, hshape, rfl, hd, Or.inr ⟨hout, h⟩⟩))
    · simp at h
  · simp at h

theorem Step.deliveryTarget_eq_ok {path : Path} {index : Nat} {source : ResultId} {w : Workflow} {c : Connection} :
    Step.deliveryTarget p s path index source = .ok (w, c) ↔
      s.workflow? p path = some w ∧ w.connections[index]? = some c ∧
      (∃ r, s.result? source = some r ∧ r.run = path ∧ r.placement = c.source ∧ (c.arm = none ∨ r.arm = c.arm)) ∧
      s.delivery? path index source = none := by
  constructor
  · intro h
    simp [Step.deliveryTarget] at h
    obtain ⟨w', hw, c', hc, r, hr, ⟨⟨h1, h2⟩, h3⟩, hd, rfl, rfl⟩ := h
    exact ⟨hw, hc, ⟨r, hr, h1, h2, h3⟩, hd⟩
  · rintro ⟨hw, hc, ⟨r, hr, h1, h2, h3⟩, hd⟩
    simp [Step.deliveryTarget, hw, hc, hr, h1, h2, h3, hd]

/-- What a settlement records: the placement in its run, and for an aggregate the list result the
    placement accepts in the same transition, produced by the placement in its run (§9). Only settles
    after all invocations ended. --/
theorem State.settleOutcome_some {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {result : Option Result} (h : s.settleOutcome path pl shape kind = some (x, result)) :
    (s.invocationsOf path pl.name).all s.invocationEnded = true ∧ x.run = path ∧ x.placement = pl.name ∧
      ∀ r, result = some r → x.outcome = .normal ∧ r.id = Key.aggregate path pl.name ∧ r.run = path ∧
        r.placement = pl.name ∧ r.producer = Key.aggregate path pl.name ∧ r.arm = none ∧
        ∃ values, r.value = listValue values := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨hall, h⟩ := h
  refine ⟨hall, ?_⟩
  -- Every leaf is `none` or a record for `path` and `pl.name`; peel binds, guards and matches.
  repeat' (first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; refine ⟨rfl, rfl, ?_⟩
       intro r hr; (cases hr) <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, _, rfl⟩)
    | (simp only [reduceCtorEq] at h; done)
    | (simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h)
    | obtain ⟨_, _, h⟩ := h
    | obtain ⟨_, h⟩ := h
    | split at h)

/-- Normalizes a hypothesis `h : <Except do-block> = .ok t` into its preconditions. --/
macro "step_norm" " at " h:ident : tactic => `(tactic|
  simp only [bind_eq_ok, pure_eq_ok, throw_eq_ok, require_eq_ok, need_eq_ok, exists_unit_iff,
    Step.running_eq_ok, Step.getCall_eq_ok, Step.getExecution_eq_ok, State.task_eq_ok, Step.taskResult_eq_ok,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none,
    decide_eq_true_eq] at $h:ident)

/-! ### Operations -/

theorem Step.start_inv {input : Option Value} (h : Step.start p s input = .ok t) :
    s.started = false ∧ s.status = .running ∧ ∃ w, p.workflow? p.main = some w ∧ w.input.isSome = input.isSome ∧
      t = { s with started := true, runs := [{ path := [], workflow := p.main, input }] } := by
  unfold Step.start at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, w, hw, h3, rfl⟩ := h
  exact ⟨h1, h2, w, hw, h3, rfl⟩

theorem Step.invoke_inv {path : Path} {name : String} {trigger : Option ResultId}
    (h : Step.invoke p s path name trigger = .ok t) :
    s.started = true ∧ s.status = .running ∧
    ∃ r w pl input id, s.run? path = some r ∧ r.complete = false ∧ p.workflow? r.workflow = some w ∧
      w.placement? name = some pl ∧ Step.invocationInput p s r w name trigger = .ok input ∧
      id = Key.invocation path name trigger ∧
      (∀ i ∈ s.invocationsOf path name, i.trigger ≠ trigger) ∧ s.invocation? id = none ∧
      ((∃ f decl, pl.control = .call (.function f) ∧ p.function? f = some decl ∧ s.call? id = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            calls := s.calls ++ [{
              id, owner := id, target := .function f, input
              stream := decl.output.kind == .stream, timeout := pl.timeout, policy := pl.policy }] }) ∨
       (∃ judge arms, pl.control = .branch judge arms ∧ s.call? id = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            calls := s.calls ++ [{
              id, owner := id, target := .judge judge, input, timeout := pl.timeout, policy := pl.policy }] }) ∨
       (∃ wf out, pl.control = .call (.workflow wf out) ∧ s.run? (Key.child id) = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            runs := s.runs ++ [{ path := Key.child id, workflow := wf, input, owner := some id }] }) ∨
       (∃ c, pl.control = .concurrency c ∧ s.execution? id = none ∧
          t = { s with
            invocations := s.invocations ++ [{ id, run := path, placement := name, trigger, input }]
            executions := s.executions ++ [{
              id, run := path, placement := name, input
              tasks := c.tasks.map fun ts =>
                { name := ts.name, status := if c.input.isSome then .pending else .ready } }] })) := by
  unfold Step.invoke at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, r, hr, hc, w, hw, pl, hpl, input, hinput, ⟨htrig, hid⟩, h⟩ := h
  refine ⟨h1, h2, r, w, pl, input, _, hr, hc, hw, hpl, hinput, rfl, by simpa using htrig, hid, ?_⟩
  split at h
  · rename_i f hf
    step_norm at h
    obtain ⟨decl, hdecl, hcall, rfl⟩ := h
    exact Or.inl ⟨f, decl, hf, hdecl, hcall, rfl⟩
  · rename_i judge arms hb
    step_norm at h
    obtain ⟨hcall, rfl⟩ := h
    exact Or.inr (Or.inl ⟨judge, arms, hb, hcall, rfl⟩)
  · rename_i wf out hwf
    step_norm at h
    obtain ⟨hrun, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨wf, out, hwf, hrun, rfl⟩))
  · rename_i c hcc
    step_norm at h
    obtain ⟨hexec, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨c, hcc, hexec, rfl⟩))
  · simp at h

theorem Step.fetch_inv {id : String} (h : Step.fetch s id = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ c, s.call? id = some c ∧ c.stream = true ∧ c.status = .running ∧
      t = s.setCall { c with status := .fetching } := by
  unfold Step.fetch at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, ⟨h3, h4⟩, rfl⟩ := h
  exact ⟨h1, h2, c, hc, h3, h4, rfl⟩

theorem Step.returned_inv {id : String} {value : Value} (h : Step.returned s id value = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ c f s', s.call? id = some c ∧ c.stream = false ∧
      c.status = .running ∧ c.target = .function f ∧ s.accept c 0 value = .ok s' ∧
      (s'.setCall { c with status := .returned }).settleOwner c .succeeded .succeeded = .ok t := by
  unfold Step.returned at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, ⟨⟨h3, h4⟩, h5⟩, s', hacc, h⟩ := h
  obtain ⟨f, hf⟩ : ∃ f, c.target = .function f := by
    revert h5; cases c.target <;> simp
  exact ⟨h1, h2, c, f, s', hc, h3, h4, hf, hacc, h⟩

theorem Step.judged_inv {id arm : String} (h : Step.judged p s id arm = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ c j i pl judge arms s', s.call? id = some c ∧
      c.status = .running ∧ c.target = .judge j ∧ c.task = none ∧ s.invocation? c.owner = some i ∧
      s.placementOf p i.run i.placement = .ok pl ∧ pl.control = .branch judge arms ∧ arm ∈ arms ∧
      s.accept c 0 (i.input.getD "") (some arm) = .ok s' ∧
      t = (s'.setCall { c with status := .returned }).setInvocation
        { i with status := .succeeded, arm := some arm } := by
  unfold Step.judged at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, ⟨⟨h3, h4⟩, h5⟩, i, hi, pl, hpl, h⟩ := h
  split at h
  · rename_i judge arms hb
    step_norm at h
    obtain ⟨harm, s', hacc, rfl⟩ := h
    obtain ⟨j, hj⟩ : ∃ j, c.target = .judge j := by
      revert h4; cases c.target <;> simp
    exact ⟨h1, h2, c, j, i, pl, judge, arms, s', hc, h3, hj, h5, hi, hpl, hb, by simpa using harm, hacc, rfl⟩
  · simp at h

theorem Step.yielded_inv {id : String} {value : Value} (h : Step.yielded s id value = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ c s', s.call? id = some c ∧ c.stream = true ∧
      c.status = .fetching ∧ s.accept c c.yields value = .ok s' ∧
      t = s'.setCall { c with status := .running, yields := c.yields + 1 } := by
  unfold Step.yielded at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, ⟨h3, h4⟩, s', hacc, rfl⟩ := h
  exact ⟨h1, h2, c, s', hc, h3, h4, hacc, rfl⟩

theorem Step.ended_inv {id : String} (h : Step.ended s id = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ c, s.call? id = some c ∧ c.stream = true ∧
      c.status = .fetching ∧ (s.setCall { c with status := .returned }).settleOwner c .succeeded .succeeded = .ok t := by
  unfold Step.ended at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, ⟨h3, h4⟩, h⟩ := h
  exact ⟨h1, h2, c, hc, h3, h4, h⟩

theorem Step.failed_inv {id : String} (h : Step.failed s id = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ c, s.call? id = some c ∧
      (c.status = .running ∨ c.status = .fetching) ∧ s.failCall c .failed .error = .ok t := by
  unfold Step.failed at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, h3, h⟩ := h
  exact ⟨h1, h2, c, hc, h3, h⟩

theorem Step.timedOut_inv {id : String} {element : Bool} (h : Step.timedOut s id element = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ c, s.call? id = some c ∧
      ((element = true ∧ c.status = .fetching ∧ c.timeout.elementMs.isSome = true) ∨
       (element = false ∧ (c.status = .running ∨ c.status = .fetching) ∧ c.timeout.callMs.isSome = true)) ∧
      s.failCall c .cancelling .timeout = .ok t := by
  unfold Step.timedOut at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, h3, h⟩ := h
  refine ⟨h1, h2, c, hc, ?_, h⟩
  cases element <;> simp_all

theorem Step.lost_inv {id : String} (h : Step.lost s id = .ok t) :
    s.started = true ∧ (s.status = .running ∨ s.status = .stopping) ∧ ∃ c, s.call? id = some c ∧
      (((c.status = .running ∨ c.status = .fetching) ∧ s.failCall c .lost .lost = .ok t) ∨
       (c.status = .cancelling ∧ (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t)) := by
  unfold Step.lost at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, h⟩ := h
  refine ⟨h1, h2, c, hc, ?_⟩
  split at h
  · rename_i hs; exact Or.inl ⟨Or.inl hs, h⟩
  · rename_i hs; exact Or.inl ⟨Or.inr hs, h⟩
  · rename_i hs; exact Or.inr ⟨hs, h⟩
  · simp at h

theorem Step.terminated_inv {id : String} (h : Step.terminated s id = .ok t) :
    s.started = true ∧ (s.status = .running ∨ s.status = .stopping) ∧ ∃ c, s.call? id = some c ∧
      c.status = .cancelling ∧ (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t := by
  unfold Step.terminated at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, c, hc, h3, h⟩ := h
  exact ⟨h1, h2, c, hc, h3, h⟩

theorem Step.deliver_inv {path : Path} {index : Nat} {source : ResultId} {value : Option Value}
    (h : Step.deliver p s path index source value = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ w c outcome, Step.deliveryTarget p s path index source = .ok (w, c) ∧
      ((∃ tid v, c.transform = .declared tid ∧ value = some v ∧ outcome = .value v) ∨
       (c.transform = .discard ∧ value = none ∧ outcome = .trigger)) ∧
      t = { s with deliveries := s.deliveries ++ [{ run := path, connection := index, source, outcome }] } := by
  unfold Step.deliver at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, ⟨w, c⟩, hdt, h⟩ := h
  refine ⟨h1, h2, w, c, ?_⟩
  split at h
  · rename_i tid v htr
    step_norm at h
    obtain ⟨_, rfl, rfl⟩ := h
    exact ⟨_, hdt, Or.inl ⟨tid, v, htr, rfl, rfl⟩, rfl⟩
  · rename_i htr
    step_norm at h
    obtain ⟨_, rfl, rfl⟩ := h
    exact ⟨_, hdt, Or.inr ⟨htr, rfl, rfl⟩, rfl⟩
  · simp at h

theorem Step.transformFailed_inv {path : Path} {index : Nat} {source : ResultId}
    (h : Step.transformFailed p s path index source = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ w c tid target, Step.deliveryTarget p s path index source = .ok (w, c) ∧
      c.transform = .declared tid ∧ w.placement? c.target = some target ∧
      t = State.fail
        { s with deliveries := s.deliveries ++ [{ run := path, connection := index, source, outcome := .failed }] }
        { run := path, placement := c.target, cause := .transform } target.policy := by
  unfold Step.transformFailed at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, ⟨w, c⟩, hdt, h⟩ := h
  step_norm at h
  obtain ⟨htr, target, htarget, rfl⟩ := h
  obtain ⟨tid, htid⟩ : ∃ tid, c.transform = .declared tid := by
    revert htr; cases c.transform <;> simp
  exact ⟨h1, h2, w, c, tid, target, hdt, htid, htarget, rfl⟩

theorem Step.taskInput_inv {eid name : String} {value : Option Value} (h : Step.taskInput p s eid name value = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ e ts spec, s.execution? eid = some e ∧
      e.tasks.find? (·.name == name) = some ts ∧ ts.status = .pending ∧ s.taskSpec p e name = .ok spec ∧
      ((∃ tid v, spec.input = some (.declared tid) ∧ value = some v) ∨ (spec.input = some .discard ∧ value = none)) ∧
      t = s.setTask e { ts with status := .ready, input := value } := by
  unfold Step.taskInput at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, e, he, ts, hts, h3, spec, hspec, h⟩ := h
  refine ⟨h1, h2, e, ts, spec, he, hts, h3, hspec, ?_⟩
  split at h
  · rename_i tid v hin
    step_norm at h
    exact ⟨Or.inl ⟨tid, v, hin, rfl⟩, h⟩
  · rename_i hin
    step_norm at h
    exact ⟨Or.inr ⟨hin, rfl⟩, h⟩
  · simp at h

theorem Step.taskInputFailed_inv {eid name : String} (h : Step.taskInputFailed p s eid name = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ e ts spec tid, s.execution? eid = some e ∧
      e.tasks.find? (·.name == name) = some ts ∧ ts.status = .pending ∧ s.taskSpec p e name = .ok spec ∧
      spec.input = some (.declared tid) ∧
      t = (s.setTask e { ts with status := .failed }).fail
        { run := e.run, placement := e.placement, task := some name, cause := .transform } spec.policy := by
  unfold Step.taskInputFailed at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, e, he, ts, hts, h3, spec, hspec, hin, rfl⟩ := h
  obtain ⟨tid, htid⟩ : ∃ tid, spec.input = some (.declared tid) := by
    revert hin; rcases spec.input with _ | (_ | _) <;> simp
  exact ⟨h1, h2, e, ts, spec, tid, he, hts, h3, hspec, htid, rfl⟩

theorem Step.beginTask_inv {eid name : String} (h : Step.beginTask p s eid name = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ e c ts spec, s.execution? eid = some e ∧ e.complete = false ∧
      s.concurrencyOf p e = .ok c ∧ e.tasks.find? (·.name == name) = some ts ∧ ts.status = .ready ∧
      (e.tasks.filter (s.holdsSlot e)).length < c.limit ∧ s.taskSpec p e name = .ok spec ∧
      ((∃ f decl, spec.body = .function f ∧ p.function? f = some decl ∧ s.call? (State.taskId e.id name) = none ∧
          t = { s.setTask e { ts with status := .active } with
            calls := s.calls ++ [{
              id := State.taskId e.id name, owner := e.id, task := some name, target := .function f
              input := ts.input, stream := decl.output.kind == .stream, timeout := spec.timeout
              policy := spec.policy }] }) ∨
       (∃ wf out, spec.body = .workflow wf out ∧ s.run? (Key.child (State.taskId e.id name)) = none ∧
          t = { s.setTask e { ts with status := .active } with
            runs := s.runs ++ [{
              path := Key.child (State.taskId e.id name), workflow := wf, input := ts.input, owner := some e.id
              task := some name }] })) := by
  unfold Step.beginTask at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, e, he, h3, c, hc, ts, hts, h4, h5, spec, hspec, h⟩ := h
  refine ⟨h1, h2, e, c, ts, spec, he, h3, hc, hts, h4, h5, hspec, ?_⟩
  split at h
  · rename_i f hf
    step_norm at h
    obtain ⟨decl, hdecl, hcall, rfl⟩ := h
    exact Or.inl ⟨f, decl, hf, hdecl, hcall, rfl⟩
  · rename_i wf out hwf
    step_norm at h
    obtain ⟨hrun, rfl⟩ := h
    exact Or.inr ⟨wf, out, hwf, hrun, rfl⟩

theorem Step.taskOutput_inv {eid name : String} {index : Nat} {value : Value}
    (h : Step.taskOutput p s eid name index value = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ e c spec r, s.execution? eid = some e ∧ s.concurrencyOf p e = .ok c ∧
      s.taskSpec p e name = .ok spec ∧ spec.output.isSome = true ∧
      s.taskResults.find? (fun x => x.execution == eid && x.task == name && x.index == index) = some r ∧
      r.output = .pending ∧
      ((c.output = .stream ∧ s.result? (Key.taskOutput eid name index) = none ∧
          t = { s.setTaskResult { r with output := .value value } with
            results := s.results ++ [{
              id := Key.taskOutput eid name index, run := e.run, placement := e.placement, producer := eid,
              value }] }) ∨
       (c.output = .list ∧ t = s.setTaskResult { r with output := .value value })) := by
  unfold Step.taskOutput at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, e, he, c, hc, spec, hspec, h3, r, hr, h4, h⟩ := h
  refine ⟨h1, h2, e, c, spec, r, he, hc, hspec, h3, hr, h4, ?_⟩
  split at h
  · rename_i hout
    step_norm at h
    obtain ⟨hres, rfl⟩ := h
    exact Or.inl ⟨hout, hres, rfl⟩
  · rename_i hout
    step_norm at h
    exact Or.inr ⟨hout, h⟩

theorem Step.taskOutputFailed_inv {eid name : String} {index : Nat}
    (h : Step.taskOutputFailed p s eid name index = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ e spec r, s.execution? eid = some e ∧ s.taskSpec p e name = .ok spec ∧
      spec.output.isSome = true ∧
      s.taskResults.find? (fun x => x.execution == eid && x.task == name && x.index == index) = some r ∧
      r.output = .pending ∧
      t = (s.setTaskResult { r with output := .failed }).fail
        { run := e.run, placement := e.placement, task := some name, cause := .transform } spec.policy := by
  unfold Step.taskOutputFailed at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, e, he, spec, hspec, h3, r, hr, h4, rfl⟩ := h
  exact ⟨h1, h2, e, spec, r, he, hspec, h3, hr, h4, rfl⟩

theorem Step.settle_inv {path : Path} {name : String} (h : Step.settle p s path name = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ r w pl shape kind x result, s.run? path = some r ∧
      r.complete = false ∧ p.workflow? r.workflow = some w ∧ w.placement? name = some pl ∧
      s.settled? path name = none ∧ w.shape? p name = some shape ∧ w.outputKind? p name = some kind ∧
      s.settleOutcome path pl shape kind = some (x, result) ∧
      ((result = none ∧ t = { s with settled := s.settled ++ [x] }) ∨
       (∃ res, result = some res ∧ s.result? res.id = none ∧
          t = { s with settled := s.settled ++ [x], results := s.results ++ [res] })) := by
  unfold Step.settle at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, r, hr, h3, w, hw, pl, hpl, h4, shape, hshape, kind, hkind, ⟨x, result⟩, hout, h⟩ := h
  refine ⟨h1, h2, r, w, pl, shape, kind, x, result, hr, h3, hw, hpl, h4, hshape, hkind, hout, ?_⟩
  cases result with
  | none =>
    step_norm at h
    exact Or.inl ⟨rfl, h⟩
  | some res =>
    step_norm at h
    obtain ⟨hres, rfl⟩ := h
    exact Or.inr ⟨res, rfl, hres, rfl⟩

theorem Step.cancel_inv (h : Step.cancel s = .ok t) :
    s.started = true ∧ ((s.status = .running ∧ t = { s.stop with cancelled := true }) ∨
      (s.status = .stopping ∧ t = { s with cancelled := true })) := by
  unfold Step.cancel at h
  step_norm at h
  obtain ⟨h1, h⟩ := h
  refine ⟨h1, ?_⟩
  split at h
  · rename_i hs
    step_norm at h
    exact Or.inl ⟨hs, h⟩
  · rename_i hs
    step_norm at h
    exact Or.inr ⟨hs, h⟩
  · simp at h

theorem Step.closeExecution_inv {eid : String} (h : Step.closeExecution p s eid = .ok t) :
    s.started = true ∧ s.status = .running ∧ ∃ e c i, s.execution? eid = some e ∧ e.complete = false ∧
      s.concurrencyOf p e = .ok c ∧ e.tasks.all (s.taskEnded e) = true ∧
      (s.taskResults.filter fun x => x.execution == eid &&
        ((c.tasks.filter (·.output.isSome)).map (·.name)).contains x.task).all (·.output != .pending) = true ∧
      s.invocation? eid = some i ∧
      (((e.tasks.filter fun ts => ((c.tasks.filter (·.output.isSome)).map (·.name)).contains ts.name).all
            (·.status == .skipped) = true ∧
          t = (s.setExecution { e with complete := true }).setInvocation { i with status := .skipped }) ∨
       ((e.tasks.filter fun ts => ((c.tasks.filter (·.output.isSome)).map (·.name)).contains ts.name).all
            (·.status == .skipped) = false ∧ c.output = .list ∧ s.result? (Key.list eid) = none ∧
          t = { (s.setExecution { e with complete := true }).setInvocation { i with status := .succeeded } with
            results := s.results ++ [{
              id := Key.list eid, run := e.run, placement := e.placement, producer := eid
              value := listValue ((s.taskResults.filter fun x => x.execution == eid &&
                ((c.tasks.filter (·.output.isSome)).map (·.name)).contains x.task).filterMap (·.output.value?)) }] }) ∨
       ((e.tasks.filter fun ts => ((c.tasks.filter (·.output.isSome)).map (·.name)).contains ts.name).all
            (·.status == .skipped) = false ∧ c.output = .stream ∧
          t = (s.setExecution { e with complete := true }).setInvocation { i with status := .succeeded })) := by
  unfold Step.closeExecution at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, e, he, h3, c, hc, h4, h5, i, hi, h⟩ := h
  refine ⟨h1, h2, e, c, i, he, h3, hc, h4, h5, hi, ?_⟩
  split at h
  · rename_i hsk
    step_norm at h
    exact Or.inl ⟨hsk, h⟩
  · rename_i hsk
    simp only [Bool.not_eq_true] at hsk
    split at h
    · rename_i hout
      step_norm at h
      obtain ⟨hres, rfl⟩ := h
      exact Or.inr (Or.inl ⟨hsk, hout, hres, rfl⟩)
    · rename_i hout
      step_norm at h
      exact Or.inr (Or.inr ⟨hsk, hout, h⟩)

theorem Step.closeRun_inv {path : Path} (h : Step.closeRun p s path = .ok t) :
    s.started = true ∧ s.status = .running ∧
    ∃ r w output x owner, s.run? path = some r ∧ r.complete = false ∧ path ≠ [] ∧
      p.workflow? r.workflow = some w ∧ w.placements.all (fun pl => (s.settled? path pl.name).isSome) = true ∧
      s.designatedOutput p r = .ok output ∧ s.settled? path output = some x ∧ r.owner = some owner ∧
      ((r.task = none ∧ ∃ i, s.invocation? owner = some i ∧
        ((x.outcome = .normal ∧ ∃ v, ((s.resultsOf path output).head?).map (·.value) = some v ∧
            s.result? (Key.returned i.id) = none ∧
            t = { (s.setRun { r with complete := true }).setInvocation { i with status := .succeeded } with
              results := s.results ++ [{
                id := Key.returned i.id, run := i.run, placement := i.placement, producer := i.id, value := v }] }) ∨
         (x.outcome = .skipped ∧
            t = (s.setRun { r with complete := true }).setInvocation { i with status := .skipped }) ∨
         (x.outcome = .failed ∧
            t = (s.setRun { r with complete := true }).setInvocation { i with status := .failed }) ∨
         (x.outcome = .upstreamFailed ∧
            t = (s.setRun { r with complete := true }).setInvocation { i with status := .upstreamFailed }))) ∨
       (∃ name e ts, r.task = some name ∧ s.execution? owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ((x.outcome = .normal ∧ ∃ v, ((s.resultsOf path output).head?).map (·.value) = some v ∧
            (s.taskResults.any fun y => y.execution == e.id && y.task == name && y.index == 0) = false ∧
            t = { (s.setRun { r with complete := true }).setTask e { ts with status := .succeeded } with
              taskResults := s.taskResults ++ [{ execution := e.id, task := name, index := 0, value := v }] }) ∨
         (x.outcome = .skipped ∧
            t = (s.setRun { r with complete := true }).setTask e { ts with status := .skipped }) ∨
         (x.outcome = .failed ∧
            t = (s.setRun { r with complete := true }).setTask e { ts with status := .failed }) ∨
         (x.outcome = .upstreamFailed ∧
            t = (s.setRun { r with complete := true }).setTask e { ts with status := .upstreamFailed })))) := by
  unfold Step.closeRun at h
  step_norm at h
  obtain ⟨⟨h1, h2⟩, r, hr, ⟨h3, h4⟩, w, hw, h5, output, hout, x, hx, owner, howner, h⟩ := h
  refine ⟨h1, h2, r, w, output, x, owner, hr, h3, by simpa using h4, hw, h5, hout, hx, howner, ?_⟩
  split at h
  · rename_i htask
    step_norm at h
    obtain ⟨i, hi, h⟩ := h
    refine Or.inl ⟨htask, i, hi, ?_⟩
    split at h
    · rename_i v hxo hv
      step_norm at h
      obtain ⟨hres, rfl⟩ := h
      exact Or.inl ⟨hxo, v, hv, hres, rfl⟩
    · simp at h
    · rename_i hxo
      step_norm at h
      exact Or.inr (Or.inl ⟨hxo, h⟩)
    · rename_i hxo
      step_norm at h
      exact Or.inr (Or.inr (Or.inl ⟨hxo, h⟩))
    · rename_i hxo
      step_norm at h
      exact Or.inr (Or.inr (Or.inr ⟨hxo, h⟩))
  · rename_i name htask
    step_norm at h
    obtain ⟨e, he, ts, hts, h⟩ := h
    refine Or.inr ⟨name, e, ts, htask, he, hts, ?_⟩
    split at h
    · rename_i v hxo hv
      step_norm at h
      obtain ⟨hres, rfl⟩ := h
      exact Or.inl ⟨hxo, v, hv, hres, rfl⟩
    · simp at h
    · rename_i hxo
      step_norm at h
      exact Or.inr (Or.inl ⟨hxo, h⟩)
    · rename_i hxo
      step_norm at h
      exact Or.inr (Or.inr (Or.inl ⟨hxo, h⟩))
    · rename_i hxo
      step_norm at h
      exact Or.inr (Or.inr (Or.inr ⟨hxo, h⟩))

theorem Step.conclude_inv (h : Step.conclude p s = .ok t) :
    s.started = true ∧
    ((s.status = .running ∧ ∃ r w, s.run? [] = some r ∧ p.workflow? r.workflow = some w ∧
        w.placements.all (fun pl => (s.settled? [] pl.name).isSome) = true ∧
        t = { s.setRun { r with complete := true } with
          status := if !s.failures.isEmpty then .failed
            else if (w.placements.filter fun pl => w.isEndpoint pl.name).all
                (fun pl => (s.settled? [] pl.name).any (·.outcome == .skipped)) then .skipped
            else .succeeded }) ∨
     (s.status = .stopping ∧ s.calls.all (·.status.ended) = true ∧
        t = { s with status := if s.failures.isEmpty then .cancelled else .failed })) := by
  unfold Step.conclude at h
  simp only [bind_eq_ok, require_eq_ok, exists_unit_iff] at h
  obtain ⟨h1, h⟩ := h
  refine ⟨h1, ?_⟩
  split at h
  · rename_i hs
    simp only [bind_eq_ok, require_eq_ok, need_eq_ok, pure_eq_ok, exists_unit_iff] at h
    obtain ⟨r, hr, w, hw, h3, rfl⟩ := h
    exact Or.inl ⟨hs, r, w, hr, hw, h3, rfl⟩
  · rename_i hs
    simp only [bind_eq_ok, require_eq_ok, pure_eq_ok, exists_unit_iff] at h
    obtain ⟨h3, rfl⟩ := h
    exact Or.inr ⟨hs, h3, rfl⟩
  · simp at h

end Suimon
