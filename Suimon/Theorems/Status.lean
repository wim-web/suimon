import Suimon.Theorems.Basic

namespace Suimon

namespace FinalStatus

/-- Running, or stopping for a recorded failure or for the caller's cancel (§11.3). --/
def Live (s : State) : Prop :=
  s.status = .running ∨ (s.status = .stopping ∧ (s.failures ≠ [] ∨ s.cancelled = true))

/-- A failure recorded while running either keeps the workflow running or stops it, and the stop
    then has that failure on record. --/
theorem fail_live {s : State} {f : Failure} {policy : Policy} (h : s.status = .running) :
    Live (s.fail f policy) := by
  cases policy <;> simp [Live, h]

/-- A failed call reported while running records its failure through `fail`, so the result is live. --/
theorem failCall_live {s t : State} {c : Call} {status : CallStatus} {cause : Cause}
    (h : s.failCall c status cause = .ok t) (running : s.status = .running) : Live t := by
  obtain ⟨_, _, -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  exact fail_live (by simp [(State.settleOwner_update hso).status, running])

open State in
/-- From a running state, a step keeps running, stops for a failure or for the caller's cancel, or
    is the conclusion. --/
theorem step_of_running {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t)
    (running : s.status = .running) : Live t ∨ op = .conclude := by
  have keep : t.status = s.status → Live t ∨ op = .conclude := fun h => Or.inl (Or.inl (h.trans running))
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact keep rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact keep rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact keep (by rw [(settleOwner_update hso).status, setCall_status, (accept_frame hacc).1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact keep (by rw [setInvocation_status, setCall_status, (accept_frame hacc).1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact keep (by rw [setCall_status, (accept_frame hacc).1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact keep (by rw [(settleOwner_update hso).status, setCall_status])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact Or.inl (failCall_live h running)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact Or.inl (failCall_live h running)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact Or.inl (failCall_live h running)
    · exact keep (by rw [(cancelOwner_update h).status, setCall_status])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact keep (by rw [(cancelOwner_update h).status, setCall_status])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact keep rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact Or.inl (fail_live running)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact keep rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact Or.inl (fail_live running)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact keep rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact Or.inl (fail_live running)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact keep rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨hs', rfl⟩⟩ := Step.cancel_inv hs
    · exact Or.inl (Or.inr ⟨rfl, Or.inr rfl⟩)
    · simp [hs'] at running
  | conclude => exact Or.inr rfl

/-- A stopping state has a failure on record or was cancelled by the caller (§11.3): a stop comes
    from a failure with the stop policy or from the cancel, and failures and the cancel are kept. --/
theorem stop_reason {p : Definition} {s : State} (h : Reachable p s) :
    s.status = .stopping → s.failures ≠ [] ∨ s.cancelled = true := by
  induction h with
  | empty => intro h; cases h
  | @step s t op _ hs ih =>
    intro stopping
    by_cases running : s.status = .running
    · rcases step_of_running hs running with (h | ⟨-, h⟩) | rfl
      · rw [h] at stopping; cases stopping
      · exact h
      · obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨h, -⟩⟩ := Step.conclude_inv hs
        · revert stopping
          simp only
          split
          · simp
          · split <;> simp
        · rw [h] at running; cases running
    · obtain ⟨hstop, -, hcases⟩ := step_of_status_ne_running hs running
      rcases hcases with ⟨c, -, -, hf⟩ | ⟨c, -, -, ho⟩ | rfl | ⟨-, rfl⟩
      · -- A lost call records its failure.
        obtain ⟨_, _, -, -, rfl⟩ := State.failCall_eq_ok.mp hf
        exact Or.inl (by simp)
      · have u := State.cancelOwner_update ho
        rw [u.failures, u.cancelled]
        exact ih hstop
      · exact Or.inr rfl
      · revert stopping
        simp only
        split <;> simp

/-- The final status rules of §11.3, §11.4 and §13.3 for a state. --/
def Decided (p : Definition) (s : State) : Prop :=
  (s.status = .failed ↔ s.failures ≠ []) ∧
  (s.status = .cancelled → s.cancelled = true ∧ s.failures = []) ∧
  (s.status = .skipped → s.failures = [] ∧ ∀ r w, s.run? [] = some r → p.workflow? r.workflow = some w →
    ∀ pl ∈ w.placements, w.isEndpoint pl.name = true → (s.settled? [] pl.name).map (·.outcome) = some .skipped)

/-- The conclusion from a running state: failed with a failure on record, otherwise skipped when
    every endpoint of the root run settled skipped, otherwise succeeded (§11.4, §13.3). --/
theorem decided_of_running {p : Definition} {s t : State} {r : Run} {w : Workflow}
    (hr : s.run? [] = some r) (hw : p.workflow? r.workflow = some w)
    (ht : t = { s.setRun { r with complete := true } with
      status := if !s.failures.isEmpty then .failed
        else if (w.placements.filter fun pl => w.isEndpoint pl.name).all
            (fun pl => (s.settled? [] pl.name).any (·.outcome == .skipped)) then .skipped
        else .succeeded }) : Decided p t := by
  have hst := congrArg State.status ht
  have hfail : t.failures = s.failures := by rw [ht]; rfl
  have hset : ∀ name, t.settled? [] name = s.settled? [] name := by intro name; rw [ht]; rfl
  -- Completing the root run keeps its workflow.
  have hroot : ∀ r' w', t.run? [] = some r' → p.workflow? r'.workflow = some w' → w' = w := by
    intro r' w' hr' hw'
    rw [ht] at hr'
    change (s.setRun _).run? [] = _ at hr'
    simp [State.run?_setRun, (State.run?_eq_some hr).2, hr] at hr'
    subst hr'
    rw [hw] at hw'
    exact (Option.some.inj hw').symm
  simp only at hst
  refine ⟨?_, fun hc => ?_, fun hsk => ?_⟩
  · rw [hst, hfail]
    split
    · simp_all
    · split <;> simp_all
  · rw [hst] at hc
    split at hc
    · cases hc
    · split at hc <;> cases hc
  · rw [hst] at hsk
    split at hsk
    · cases hsk
    · split at hsk
      · rename_i hf hE
        refine ⟨by simpa [hfail] using hf, ?_⟩
        intro r' w' hr' hw' pl hpl hend
        obtain rfl := hroot r' w' hr' hw'
        obtain ⟨x, hx, hxo⟩ := (Option.any_eq_true _ _).mp
          (List.all_eq_true.mp hE pl (List.mem_filter.mpr ⟨hpl, hend⟩))
        rw [hset, hx]
        simpa using hxo
      · cases hsk

/-- The conclusion from a stopping state: failed with a failure on record, otherwise cancelled (§11.3). --/
theorem decided_of_stopping {p : Definition} {s t : State} (reason : s.failures ≠ [] ∨ s.cancelled = true)
    (ht : t = { s.endUnfinished with status := if s.failures.isEmpty then .cancelled else .failed }) :
    Decided p t := by
  subst ht
  by_cases hf : s.failures = []
  · have hc : s.cancelled = true := reason.resolve_left (· hf)
    simp [Decided, hf, hc]
  · simp [Decided, hf]

end FinalStatus

/-- The final status follows §11.3, §11.4 and §13.3: failed exactly when a failure was recorded;
    cancelled only if the caller cancelled; skipped only when every endpoint of the workflow was
    skipped; succeeded otherwise. --/
theorem Reachable.final_status {p : Definition} {s : State} (h : Reachable p s) (done : s.status.terminal = true) :
    (s.status = .failed ↔ s.failures ≠ []) ∧
    (s.status = .cancelled → s.cancelled = true ∧ s.failures = []) ∧
    (s.status = .skipped → s.failures = [] ∧ ∀ r w, s.run? [] = some r → p.workflow? r.workflow = some w →
      ∀ pl ∈ w.placements, w.isEndpoint pl.name = true → (s.settled? [] pl.name).map (·.outcome) = some .skipped) := by
  show FinalStatus.Decided p s
  -- A final status is only reached by the conclusion, from a running or a stopping state.
  cases h with
  | empty => simp [Status.terminal] at done
  | @step s0 _ op h0 hs =>
    by_cases running : s0.status = .running
    · rcases FinalStatus.step_of_running hs running with (h | ⟨h, -⟩) | rfl
      · rw [h] at done; simp [Status.terminal] at done
      · rw [h] at done; simp [Status.terminal] at done
      · obtain ⟨-, ⟨-, r, w, hr, hw, -, ht⟩ | ⟨h, -⟩⟩ := Step.conclude_inv hs
        · exact FinalStatus.decided_of_running hr hw ht
        · rw [h] at running; cases running
    · obtain ⟨hstop, -, hcases⟩ := step_of_status_ne_running hs running
      rcases hcases with ⟨c, -, -, hf⟩ | ⟨c, -, -, ho⟩ | rfl | ⟨-, ht⟩
      · rcases State.failCall_status hf with h | h <;> rw [h] at done <;> simp [hstop, Status.terminal] at done
      · rw [(State.cancelOwner_update ho).status] at done; simp [hstop, Status.terminal] at done
      · simp [hstop, Status.terminal] at done
      · exact FinalStatus.decided_of_stopping (FinalStatus.stop_reason h0 hstop) ht

/-- Once final, the status never changes (§13.3). --/
theorem Reachable.final_kept {p : Definition} {s t : State} {op : Op} (h : Reachable p s) (done : s.status.terminal = true) :
    Suimon.step p s op ≠ .ok t := by
  -- Reachability is not needed: a final state accepts no operation at all.
  have _ := h
  intro hs
  rcases step_source_status hs with h | h <;> simp [h, Status.terminal] at done

/-- What the conclusion after a stop leaves once every call ended: no invocation is active, every task
    has ended, and no task holds a slot of its concurrency (§8.2, §11.3). --/
theorem endUnfinished_ended {s : State} (hended : s.calls.all (·.status.ended) = true) (status : Status) :
    (∀ i ∈ ({ s.endUnfinished with status } : State).invocations, i.status ≠ .active) ∧
    ∀ e ∈ ({ s.endUnfinished with status } : State).executions, ∀ ts ∈ e.tasks,
      ts.status.ended = true ∧ ({ s.endUnfinished with status } : State).holdsSlot e ts = false := by
  refine ⟨fun i hi => ?_, fun e he ts hts => ?_⟩
  · obtain ⟨i₀, -, rfl⟩ := State.mem_endUnfinished_invocations.mp hi
    exact State.endInvocation_status_ne
  · obtain ⟨e₀, -, rfl⟩ := State.mem_endUnfinished_executions.mp he
    rw [State.endExecution_tasks, List.mem_map] at hts
    obtain ⟨ts₀, -, rfl⟩ := hts
    refine ⟨State.endTask_ended, ?_⟩
    -- Every call ended, so none is cancelling.
    have hquiet : ∀ c ∈ s.calls, c.status ≠ .cancelling := fun c hc hcan => by
      have := List.all_eq_true.mp hended c hc
      rw [hcan] at this
      cases this
    simp only [State.holdsSlot, Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.any_eq_false,
      Bool.and_eq_true, beq_iff_eq, not_and]
    exact ⟨State.endTask_status_ne_active, fun c hc _ hcan => hquiet c hc hcan⟩

/-- The conclusion after a stop leaves nothing running: no invocation is active, every task has ended,
    and no task holds a slot of its concurrency (§8.2, §11.3). --/
theorem step_conclude_stopping {p : Definition} {s t : State} (hs : step p s .conclude = .ok t)
    (stopping : s.status = .stopping) :
    (∀ i ∈ t.invocations, i.status ≠ .active) ∧
    ∀ e ∈ t.executions, ∀ ts ∈ e.tasks, ts.status.ended = true ∧ t.holdsSlot e ts = false := by
  obtain ⟨-, ⟨h, -⟩ | ⟨-, hended, rfl⟩⟩ := Step.conclude_inv hs
  · rw [h] at stopping; cases stopping
  · exact endUnfinished_ended hended _

/-- In a final state reached through a stop, which the root run did not complete, nothing is running:
    no invocation is active, every task has ended, and no task holds a slot (§8.2, §11.3). A final
    state accepts no operation, so it is the conclusion of a stopping state; the conclusion from a
    running state completes the root run. --/
theorem Reachable.stopped_final {p : Definition} {s : State} (h : Reachable p s) (final : s.status.terminal = true)
    (stopped : (s.run? []).any (·.complete) = false) :
    (∀ i ∈ s.invocations, i.status ≠ .active) ∧
    ∀ e ∈ s.executions, ∀ ts ∈ e.tasks, ts.status.ended = true ∧ s.holdsSlot e ts = false := by
  cases h with
  | empty => simp [Status.terminal] at final
  | @step s0 _ op _ hs =>
    by_cases running : s0.status = .running
    · rcases FinalStatus.step_of_running hs running with (h | ⟨h, -⟩) | rfl
      · rw [h] at final; simp [Status.terminal] at final
      · rw [h] at final; simp [Status.terminal] at final
      · -- The conclusion from a running state completes the root run.
        obtain ⟨-, ⟨-, r, w, hr, -, -, rfl⟩ | ⟨h, -⟩⟩ := Step.conclude_inv hs
        · exfalso
          have hroot : (s0.setRun { r with complete := true }).run? [] = some { r with complete := true } := by
            rw [State.run?_setRun]
            simp [(State.run?_eq_some hr).2, hr]
          change ((s0.setRun { r with complete := true }).run? []).any (·.complete) = false at stopped
          rw [hroot] at stopped
          cases stopped
        · rw [h] at running; cases running
    · obtain ⟨hstop, -, hcases⟩ := step_of_status_ne_running hs running
      rcases hcases with ⟨c, -, -, hf⟩ | ⟨c, -, -, ho⟩ | rfl | ht
      · rcases State.failCall_status hf with h | h <;> rw [h] at final <;> simp [hstop, Status.terminal] at final
      · rw [(State.cancelOwner_update ho).status] at final; simp [hstop, Status.terminal] at final
      · simp [hstop, Status.terminal] at final
      · obtain ⟨hended, rfl⟩ := ht
        exact endUnfinished_ended hended _

/-- The workflow ends normally only after every placement of the root run settled (§13.3). --/
theorem step_conclude_running {p : Definition} {s t : State} (hs : step p s .conclude = .ok t)
    (running : s.status = .running) :
    ∃ r w, s.run? [] = some r ∧ p.workflow? r.workflow = some w ∧ ∀ pl ∈ w.placements, (s.settled? [] pl.name).isSome := by
  obtain ⟨-, ⟨-, r, w, hr, hw, hall, -⟩ | ⟨h, -⟩⟩ := Step.conclude_inv hs
  · exact ⟨r, w, hr, hw, List.all_eq_true.mp hall⟩
  · rw [h] at running; cases running

end Suimon
