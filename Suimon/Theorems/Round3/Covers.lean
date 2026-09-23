import Suimon.Theorems.Round3.CallConform
import Suimon.Theorems.Round3.Stable
import Suimon.Theorems.Round3.Saturated

namespace Suimon.Round3
open State

/-! ## [20] Round3/Covers.lean — scaffold, and task F0 (`covers_footprint_step`)

`Covers p T s`: every record of `s` is in the final state `T` of a complete run of the same
environment, with the fields fixed at its creation and identical once finished; and the frozen
footprint of every settled placement and completed execution of `s` has nothing more in `T`. The second
half handles the rules that compute a value from a set of records (`settle`, `closeExecution`,
`closeRun`). No step is ever commuted, so the order in which tasks get concurrency slots does not
matter: `beginTask` in one run is matched by the completeness of the other. -/

section CoversSection
variable {p : Program} {env : Env}

/-- `Covers p T s`, read "`s` is contained in `T`". -/
structure Covers (p : Program) (T s : State) : Prop where
  runs : ∀ r ∈ s.runs, ∃ r' ∈ T.runs, r'.path = r.path ∧ r'.workflow = r.workflow ∧ r'.input = r.input ∧
    r'.owner = r.owner ∧ r'.task = r.task
  invocations : ∀ i ∈ s.invocations, ∃ i' ∈ T.invocations, i'.id = i.id ∧ i'.run = i.run ∧
    i'.placement = i.placement ∧ i'.trigger = i.trigger ∧ i'.input = i.input ∧ (i.status ≠ .active → i' = i)
  calls : ∀ c ∈ s.calls, ∃ c' ∈ T.calls, c'.id = c.id ∧ c'.owner = c.owner ∧ c'.task = c.task ∧
    c'.target = c.target ∧ c'.input = c.input ∧ c'.stream = c.stream ∧ c'.timeout = c.timeout ∧
    c'.policy = c.policy ∧ (c.status.ended = true → c' = c)
  executions : ∀ e ∈ s.executions, ∃ e' ∈ T.executions, e'.id = e.id ∧ e'.run = e.run ∧
    e'.placement = e.placement ∧ e'.input = e.input ∧ e'.tasks.map (·.name) = e.tasks.map (·.name) ∧
    (∀ t ∈ e.tasks, ∀ t' ∈ e'.tasks, t'.name = t.name →
      (t.status ≠ .pending → t'.input = t.input) ∧ (t.status.ended = true → t' = t)) ∧
    (e.complete = true → e' = e)
  results : ∀ r ∈ s.results, r ∈ T.results
  taskResults : ∀ r ∈ s.taskResults, ∃ r' ∈ T.taskResults, r'.execution = r.execution ∧ r'.task = r.task ∧
    r'.index = r.index ∧ r'.value = r.value ∧ (r.output ≠ .pending → r' = r)
  deliveries : ∀ d ∈ s.deliveries, d ∈ T.deliveries
  settled : ∀ x ∈ s.settled, x ∈ T.settled
  /-- A settled placement of `s` has no invocation, result or input delivery in `T` beyond those of `s`. -/
  footprint : ∀ x ∈ s.settled,
    (∀ i ∈ T.invocationsOf x.run x.placement, i ∈ s.invocations) ∧
    (∀ r ∈ T.resultsOf x.run x.placement, r ∈ s.results) ∧
    ∀ w, s.workflow? p x.run = some w → ∀ j c, (j, c) ∈ w.inputs x.placement →
      ∀ d ∈ T.deliveriesOn x.run j, d ∈ s.deliveries
  /-- A completed execution of `s` has no task result in `T` beyond those of `s`. -/
  execution : ∀ e ∈ s.executions, e.complete = true → ∀ r ∈ T.taskResults, r.execution = e.id → r ∈ s.taskResults

theorem covers_empty (p : Program) (T : State) : Covers p T {} where
  runs _ h := nomatch h
  invocations _ h := nomatch h
  calls _ h := nomatch h
  executions _ h := nomatch h
  results _ h := nomatch h
  taskResults _ h := nomatch h
  deliveries _ h := nomatch h
  settled _ h := nomatch h
  footprint _ h := nomatch h
  execution _ h := nomatch h

/-- The context of one step of run 1 (from `s` to `s'` by `op`) against the final state `T` of a
    complete run 2 of the same environment. -/
structure StepCtx (p : Program) (env : Env) (T s : State) (op : Op) (s' : State) : Prop where
  valid : p.validate = .ok ()
  run : ∃ tr, Conforming p env tr s
  conforms : Conforms env s op
  accepted : step p s op = .ok s'
  changed : s' ≠ s
  unstopped : Unstopped s'
  other : ∃ tr, Conforming p env tr T
  done : Done T
  covers : Covers p T s

/-- An invocation that is no longer active is kept unchanged by a step (Round 2 `Delivery.frozen`). -/
private theorem inactive_invocation_kept {s t : State} {op : Op} (hreach : Reachable p s)
    (hs : step p s op = .ok t) {i : Invocation} (hi : i ∈ s.invocations) (hna : i.status ≠ .active) :
    i ∈ t.invocations := by
  have inv := Delivery.Reachable.inv hreach
  obtain ⟨i', hi', hid, -⟩ := (inv.kept hs).invocation i hi
  exact Delivery.frozen inv hs hi hna hi' hid ▸ hi'

/-- The task results of a completed execution are kept unchanged by a step. Only `taskOutput` and
    `taskOutputFailed` rewrite a stored task result, and only a pending result of a task in the output,
    which a completed execution no longer has (`Reachable.execution_outputs`); every other step keeps or
    extends the list. -/
private theorem complete_taskResult_kept {s t : State} {op : Op} (hreach : Reachable p s)
    (hs : step p s op = .ok t) {e : Execution} (he : e ∈ s.executions) (hc : e.complete = true)
    {r : TaskResult} (hr : r ∈ s.taskResults) (hre : r.execution = e.id) : r ∈ t.taskResults := by
  have wk := hreach.wellKeyed
  have keep : ∀ {u : State} (l : List TaskResult), u.taskResults = s.taskResults ++ l → r ∈ u.taskResults := by
    intro u l hu
    rw [hu]
    exact List.mem_append_left l hr
  have same : ∀ {u : State}, u.taskResults = s.taskResults → r ∈ u.taskResults :=
    fun hu => keep [] (by rw [hu, List.append_nil])
  have accepted : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {u : State},
      s.accept c index value arm = .ok u → r ∈ u.taskResults := by
    intro c index value arm u hacc
    rcases Delivery.accept_taskResults hacc with hu | ⟨_, -, hu⟩
    · exact same hu
    · exact keep _ hu
  -- `setTaskResult` rewrites only the result under the key of the pending result `r₀` it was given, and
  -- `r` is not pending if it has that key.
  have rewrite : ∀ {eid name : String} {index : Nat} {e₀ : Execution} {spec : TaskSpec} {r₀ : TaskResult}
      (o : TaskOutput), s.execution? eid = some e₀ → s.taskSpec p e₀ name = .ok spec →
      spec.output.isSome = true →
      s.taskResults.find? (fun x => x.execution == eid && x.task == name && x.index == index) = some r₀ →
      r₀.output = .pending → r ∈ (s.setTaskResult { r₀ with output := o }).taskResults := by
    intro eid name index e₀ spec r₀ o he₀ hspec hout hr₀ hpend
    rw [State.setTaskResult_taskResults]
    refine List.mem_map.mpr ⟨r, hr, ?_⟩
    have hk : r₀.execution = eid ∧ r₀.task = name ∧ r₀.index = index := by
      simpa [and_assoc] using List.find?_some hr₀
    split
    · rename_i hkey
      exfalso
      simp only [Bool.and_eq_true, beq_iff_eq] at hkey
      obtain ⟨⟨hkx, hkt⟩, hki⟩ := hkey
      have hfind : s.taskResults.find? (fun x => x.execution == eid && x.task == name && x.index == index) =
          some r := by
        refine find?_eq_some_of_nodup wk.taskResults hr fun y => ?_
        simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
        rw [hkx, hkt, hki, hk.1, hk.2.1, hk.2.2]
        exact and_assoc
      have hrr₀ : r = r₀ := Option.some.inj (hfind.symm.trans hr₀)
      subst hrr₀
      obtain ⟨he₀m, he₀id⟩ := State.execution?_eq_some he₀
      have hee₀ : e₀ = e := wk.execution_eq_of_id he₀m he (he₀id.trans (hk.1.symm.trans hre))
      subst hee₀
      obtain ⟨cc, hcc, hfind'⟩ := State.taskSpec_eq_ok.mp hspec
      refine hreach.execution_outputs e₀ he hc cc hcc r hr hre
        ⟨spec, List.mem_of_find?_eq_some hfind', ?_, hout⟩ hpend
      rw [hk.2.1]
      simpa using List.find?_some hfind'
    · rfl
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    rw [(Delivery.settleOwner_old hso).2.2.2.2.1, State.setCall_taskResults]
    exact accepted hacc
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    rw [State.setInvocation_taskResults, State.setCall_taskResults]
    exact accepted hacc
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    rw [State.setCall_taskResults]
    exact accepted hacc
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(Delivery.settleOwner_old hso).2.2.2.2.1, State.setCall_taskResults])
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact same (Delivery.failCall_old (State.call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact same (Delivery.failCall_old (State.call?_eq_some hc).1 (by simp) h).2.2.2.2.1
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact same (Delivery.failCall_old (State.call?_eq_some hc).1 (by simp) h).2.2.2.2.1
    · exact same (by rw [(Delivery.cancelOwner_old h).2.2.2.2.1, State.setCall_taskResults])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact same (by rw [(Delivery.cancelOwner_old h).2.2.2.2.1, State.setCall_taskResults])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, e₀, _, spec, r₀, he₀, -, hspec, hout, hr₀, hpend, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact rewrite _ he₀ hspec hout hr₀ hpend
    · exact rewrite _ he₀ hspec hout hr₀ hpend
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, e₀, spec, r₀, he₀, hspec, hout, hr₀, hpend, rfl⟩ := Step.taskOutputFailed_inv hs
    have hmem := rewrite .failed he₀ hspec hout hr₀ hpend
    cases spec.policy <;> simpa [State.fail] using hmem
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact keep _ rfl
      all_goals exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-- Task F0 (shared by F4–F6). The frozen footprints of `s` carry over to the next state of run 1: the
    invocations of a settled placement ended, so they never change (`step_frozen`); results, deliveries
    and runs only grow; the task results of a completed execution never change. -/
theorem covers_footprint_step {op : Op} {s s' T : State} (h : StepCtx p env T s op s') :
    (∀ x ∈ s.settled, (∀ i ∈ T.invocationsOf x.run x.placement, i ∈ s'.invocations) ∧
      (∀ r ∈ T.resultsOf x.run x.placement, r ∈ s'.results) ∧
      ∀ w, s'.workflow? p x.run = some w → ∀ j c, (j, c) ∈ w.inputs x.placement →
        ∀ d ∈ T.deliveriesOn x.run j, d ∈ s'.deliveries) ∧
    (∀ e ∈ s.executions, e.complete = true → ∀ r ∈ T.taskResults, r.execution = e.id → r ∈ s'.taskResults) := by
  obtain ⟨tr, hrun⟩ := h.run
  have hreach : Reachable p s := hrun.reachable
  have g := step_grows h.accepted
  have runsKept : Routing.RunsKept s s' := by
    refine Routing.step_runsKept h.accepted ?_
    rcases hreach.eq_empty_or_started with h0 | h0
    · exact Or.inl (by rw [h0])
    · exact Or.inr h0
  refine ⟨fun x hx => ⟨fun i hi => ?_, fun r hr => ?_, fun w hw j c hjc d hd => ?_⟩,
    fun e he hc r hr hre => ?_⟩
  · -- `i` is an invocation of `s` of the settled placement, so it ended and the step keeps it.
    have his := (h.covers.footprint x hx).1 i hi
    have hio : i ∈ s.invocationsOf x.run x.placement := by
      simp only [State.invocationsOf, List.mem_filter] at hi ⊢
      exact ⟨his, hi.2⟩
    have hend := hreach.settled_invocations_ended x hx i hio
    have hna : i.status ≠ .active := by
      intro hact
      simp [State.invocationEnded, hact] at hend
    exact inactive_invocation_kept hreach h.accepted his hna
  · exact g.mem_results ((h.covers.footprint x hx).2.1 r hr)
  · -- The run of a settled placement exists in `s`, and `s'` keeps its workflow.
    obtain ⟨w₀, -, hw₀, -, -⟩ := (Settle.reachable hreach).2.2.2.closed x hx
    have e : w₀ = w := Option.some.inj ((runsKept.workflow? (p := p) hw₀).symm.trans hw)
    subst e
    exact g.mem_deliveries ((h.covers.footprint x hx).2.2 _ hw₀ j c hjc d hd)
  · exact complete_taskResult_kept hreach h.accepted he hc (h.covers.execution e he hc r hr hre) hre

end CoversSection

end Suimon.Round3
