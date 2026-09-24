import Suimon.Theorems.Basic

namespace Suimon

namespace Routing

/-! ### Static lookups -/

theorem workflow?_eq_some {p : Definition} {s : State} {path : Path} {w : Workflow} :
    s.workflow? p path = some w ↔ ∃ r, s.run? path = some r ∧ p.workflow? r.workflow = some w := by
  unfold State.workflow?
  exact option_bind_eq_some

/-- An input connection of a placement is the connection at its index, and targets the placement. --/
theorem mem_inputs {w : Workflow} {name : String} {i : Nat} {c : Connection} (h : (i, c) ∈ w.inputs name) :
    w.connections[i]? = some c ∧ c.target = name := by
  unfold Workflow.inputs at h
  obtain ⟨⟨c', i'⟩, hmem, heq⟩ := List.mem_filterMap.mp h
  by_cases ht : c'.target = name
  · simp only [ht, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨List.mem_zipIdx_iff_getElem?.mp hmem, ht⟩
  · simp [ht] at heq

/-- A Single or Stream input comes through the one input connection of the placement. --/
theorem shape?_connection {p : Definition} {w : Workflow} {name : String} {i : Nat} {c : Connection}
    (h : w.shape? p name = some (.single i c) ∨ w.shape? p name = some (.stream i c)) :
    w.connections[i]? = some c ∧ c.target = name := by
  suffices w.inputs name = [(i, c)] from mem_inputs (this ▸ List.mem_singleton_self _)
  rcases h with h | h <;>
  · unfold Workflow.shape? at h
    simp only [option_bind_eq_some] at h
    obtain ⟨pl, -, h⟩ := h
    repeat' (first | (simp_all; done) | split at h)

/-- A Single connection resolves to a value only through a delivery on it that did not fail. --/
theorem resolveSingle_value {s : State} {path : Path} {i : Nat} {c : Connection} {source : ResultId}
    {input : Option Value} (h : s.resolveSingle path i c = .value source input) :
    ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = i ∧ d.source = source ∧ d.outcome ≠ .failed := by
  unfold State.resolveSingle at h
  split at h
  · rename_i d rest hds
    have hd : d ∈ s.deliveriesOn path i := by rw [hds]; exact List.mem_cons_self
    simp only [State.deliveriesOn, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hd
    obtain ⟨hd, hrun, hconn⟩ := hd
    split at h <;> rename_i hout
    · simp only [State.Resolution.value.injEq] at h
      exact ⟨d, hd, hrun, hconn, h.1, by simp [hout]⟩
    · simp only [State.Resolution.value.injEq] at h
      exact ⟨d, hd, hrun, hconn, h.1, by simp [hout]⟩
    · simp at h
  · split at h
    · simp at h
    · split at h <;> simp at h


/-! ### Runs keep their workflow -/

/-- Every run of `s` is still found in `t`, with the same workflow. --/
def RunsKept (s t : State) : Prop :=
  ∀ ⦃path : Path⦄ ⦃r : Run⦄, s.run? path = some r → ∃ r', t.run? path = some r' ∧ r'.workflow = r.workflow

namespace RunsKept
variable {s t u : State}

theorem refl (s : State) : RunsKept s s := fun _ r h => ⟨r, h, rfl⟩

theorem trans (h₁ : RunsKept s t) (h₂ : RunsKept t u) : RunsKept s u := fun _ _ h => by
  obtain ⟨r', h', hw⟩ := h₁ h
  obtain ⟨r'', h'', hw'⟩ := h₂ h'
  exact ⟨r'', h'', hw'.trans hw⟩

theorem of_runs_eq (h : t.runs = s.runs) : RunsKept s t := fun path r hr =>
  ⟨r, by simpa only [State.run?, h] using hr, rfl⟩

theorem of_runs_append {l : List Run} (h : t.runs = s.runs ++ l) : RunsKept s t := fun path r hr => by
  refine ⟨r, ?_, rfl⟩
  simp only [State.run?] at hr ⊢
  simp [h, List.find?_append, hr]

/-- Closing a run keeps its workflow. --/
theorem of_runs_eq_setRun {path : Path} {r : Run} (hr : s.run? path = some r)
    (h : t.runs = (s.setRun { r with complete := true }).runs) : RunsKept s t := by
  intro path' r' hr'
  have e : t.run? path' = (s.setRun { r with complete := true }).run? path' := by
    simp only [State.run?, h]
  rw [e, State.run?_setRun]
  split
  · rename_i hp
    have hpath : path' = path := hp.symm.trans (State.run?_eq_some hr).2
    subst hpath
    rw [hr] at hr'
    cases hr'
    exact ⟨{ r with complete := true }, by rw [hr]; rfl, rfl⟩
  · exact ⟨r', hr', rfl⟩

theorem workflow? {p : Definition} (h : RunsKept s t) {path : Path} {w : Workflow}
    (hw : s.workflow? p path = some w) : t.workflow? p path = some w := by
  obtain ⟨r, hr, hw⟩ := workflow?_eq_some.mp hw
  obtain ⟨r', hr', hrw⟩ := h hr
  exact workflow?_eq_some.mpr ⟨r', hr', hrw ▸ hw⟩

end RunsKept

open State in
/-- A step never removes a run or changes its workflow; closing a run only marks it complete. --/
theorem step_runsKept {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t)
    (h : s.runs = [] ∨ s.started = true) : RunsKept s t := by
  cases op with
  | start input =>
    obtain ⟨h1, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h with h | h
    · intro path r hr
      simp [State.run?, h] at hr
    · simp [h] at h1
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact .of_runs_eq rfl
    · exact .of_runs_eq rfl
    · exact .of_runs_append rfl
    · exact .of_runs_eq rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact .of_runs_eq rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact .of_runs_eq (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact .of_runs_eq (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact .of_runs_eq (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact .of_runs_eq (by rw [(settleOwner_update hso).runs, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact .of_runs_eq (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact .of_runs_eq (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact .of_runs_eq (failCall_runs h)
    · exact .of_runs_eq (by rw [(cancelOwner_update h).runs, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact .of_runs_eq (by rw [(cancelOwner_update h).runs, setCall_runs])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact .of_runs_eq rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact .of_runs_eq (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact .of_runs_eq rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact .of_runs_eq (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact .of_runs_eq rfl
    · exact .of_runs_append rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact .of_runs_eq rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact .of_runs_eq (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact .of_runs_eq rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact .of_runs_eq rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, hr, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    refine .of_runs_eq_setRun hr ?_
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact .of_runs_eq rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact .of_runs_eq_setRun hr rfl
    · exact .of_runs_eq rfl

/-- Before the start there are no runs; afterwards the workflow stays started. --/
theorem runs_nil_or_started {p : Definition} {s : State} (h : Reachable p s) : s.runs = [] ∨ s.started = true :=
  h.eq_empty_or_started.imp (fun he => by rw [he]) id

/-! ### Invocations keep their run, placement and trigger -/

/-- Every invocation of `t` has the run, placement and trigger of an invocation of `s`. --/
def InvocationsKept (s t : State) : Prop :=
  ∀ x ∈ t.invocations, ∃ y ∈ s.invocations, y.run = x.run ∧ y.placement = x.placement ∧ y.trigger = x.trigger

namespace InvocationsKept
variable {s t u : State}

theorem refl (s : State) : InvocationsKept s s := fun x hx => ⟨x, hx, rfl, rfl, rfl⟩

theorem trans (h₁ : InvocationsKept s t) (h₂ : InvocationsKept t u) : InvocationsKept s u := fun x hx => by
  obtain ⟨y, hy, h1, h2, h3⟩ := h₂ x hx
  obtain ⟨z, hz, h1', h2', h3'⟩ := h₁ y hy
  exact ⟨z, hz, h1'.trans h1, h2'.trans h2, h3'.trans h3⟩

theorem of_eq (h : t.invocations = s.invocations) : InvocationsKept s t := fun x hx =>
  ⟨x, h ▸ hx, rfl, rfl, rfl⟩

/-- Updating a stored invocation keeps its run, placement and trigger. --/
theorem setInvocation {i i' : Invocation} (hi : i ∈ s.invocations) (hrun : i.run = i'.run)
    (hpl : i.placement = i'.placement) (htr : i.trigger = i'.trigger) : InvocationsKept s (s.setInvocation i') :=
  fun x hx => by
    rcases State.mem_setInvocation_invocations hx with rfl | hx
    · exact ⟨i, hi, hrun, hpl, htr⟩
    · exact ⟨x, hx, rfl, rfl, rfl⟩

theorem settleOwner {c : Call} {inv : InvocationStatus} {task : TaskStatus} (h : s.settleOwner c inv task = .ok t) :
    InvocationsKept s t := by
  rcases State.settleOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · exact .setInvocation (State.invocation?_eq_some hi).1 rfl rfl rfl
  · exact .of_eq rfl

theorem cancelOwner {c : Call} (h : s.cancelOwner c = .ok t) : InvocationsKept s t := by
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, i, hi, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ <;> split
  · exact .setInvocation (State.invocation?_eq_some hi).1 rfl rfl rfl
  · exact .refl _
  · exact .of_eq rfl
  · exact .refl _

theorem failCall {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    InvocationsKept s t := by
  obtain ⟨_, _, -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  exact (InvocationsKept.of_eq rfl).trans ((settleOwner hso).trans (.of_eq State.fail_invocations))

/-- Ending the unfinished invocations changes only their status. --/
theorem endUnfinished (h : t.invocations = s.endUnfinished.invocations) : InvocationsKept s t := fun x hx => by
  rw [h] at hx
  obtain ⟨y, hy, rfl⟩ := State.mem_endUnfinished_invocations.mp hx
  exact ⟨y, hy, by simp, by simp, by simp⟩

end InvocationsKept

open State in
/-- Every invocation after a step is one from before with the same run, placement and trigger, or
    the one this step invoked. --/
theorem step_invocations {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ x ∈ t.invocations, (∃ y ∈ s.invocations, y.run = x.run ∧ y.placement = x.placement ∧ y.trigger = x.trigger) ∨
      op = .invoke x.run x.placement x.trigger := by
  intro x hx
  suffices hk : (∀ path name trigger, op ≠ .invoke path name trigger) → InvocationsKept s t by
    cases op with
    | invoke path name trigger =>
      obtain ⟨-, -, _, _, _, input, id, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
      have ht : t.invocations = s.invocations ++ [{ id, run := path, placement := name, trigger, input }] := by
        rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> rfl
      rw [ht, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl ⟨x, hx, rfl, rfl, rfl⟩
      · exact Or.inr rfl
    | _ => exact Or.inl (hk (fun _ _ _ h => by cases h) x hx)
  intro hop
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact .of_eq rfl
  | invoke path name trigger => exact absurd rfl (hop path name trigger)
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact .of_eq rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact (InvocationsKept.of_eq (by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1])).trans
      (.settleOwner hso)
  | judged id arm =>
    obtain ⟨-, -, _, _, i, _, _, _, _, -, -, -, -, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have hinv := (accept_frame hacc).2.2.2.2.1
    exact (InvocationsKept.of_eq (by rw [setCall_invocations, hinv])).trans
      (.setInvocation (i := i) (by rw [setCall_invocations, hinv]; exact (invocation?_eq_some hi).1) rfl rfl rfl)
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact .of_eq (by rw [setCall_invocations, (accept_frame hacc).2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact (InvocationsKept.of_eq (by rfl)).trans (.settleOwner hso)
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact .failCall h
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact .failCall h
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact .failCall h
    · exact (InvocationsKept.of_eq (by rfl)).trans (.cancelOwner h)
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact (InvocationsKept.of_eq (by rfl)).trans (.cancelOwner h)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact .of_eq rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact .of_eq (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact .of_eq rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact .of_eq (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact .of_eq rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact .of_eq rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact .of_eq (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact .of_eq rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, i, -, -, -, -, -, hi, h⟩ := Step.closeExecution_inv hs
    have hi' := (invocation?_eq_some hi).1
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact .setInvocation hi' rfl rfl rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, i, hi, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · have hi' := (invocation?_eq_some hi).1
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact .setInvocation hi' rfl rfl rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact .of_eq rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact .of_eq rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact .of_eq rfl
    · exact .endUnfinished rfl

/-! ### Deliveries -/

theorem failCall_deliveries {s t : State} {c : Call} {status : CallStatus} {cause : Cause}
    (h : s.failCall c status cause = .ok t) : t.deliveries = s.deliveries := by
  obtain ⟨_, _, -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  simp [(State.settleOwner_update hso).deliveries]

open State in
/-- Every delivery after a step is one from before, or one this step checked with `deliveryTarget`. --/
theorem step_deliveries {p : Definition} {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ d ∈ t.deliveries, d ∈ s.deliveries ∨ ∃ w c, Step.deliveryTarget p s d.run d.connection d.source = .ok (w, c) := by
  intro d hd
  have keep : t.deliveries = s.deliveries →
      d ∈ s.deliveries ∨ ∃ w c, Step.deliveryTarget p s d.run d.connection d.source = .ok (w, c) :=
    fun h => Or.inl (h ▸ hd)
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
    exact keep (by rw [(settleOwner_update hso).deliveries, setCall_deliveries, (accept_frame hacc).2.2.2.2.2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact keep (by rw [setInvocation_deliveries, setCall_deliveries, (accept_frame hacc).2.2.2.2.2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact keep (by rw [setCall_deliveries, (accept_frame hacc).2.2.2.2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact keep (by rw [(settleOwner_update hso).deliveries, setCall_deliveries])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact keep (failCall_deliveries h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact keep (failCall_deliveries h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact keep (failCall_deliveries h)
    · exact keep (by rw [(cancelOwner_update h).deliveries, setCall_deliveries])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact keep (by rw [(cancelOwner_update h).deliveries, setCall_deliveries])
  | deliver path index source value =>
    obtain ⟨-, -, w, c, _, hdt, -, rfl⟩ := Step.deliver_inv hs
    rcases List.mem_append.mp hd with hd | hd
    · exact Or.inl hd
    · rw [List.mem_singleton] at hd
      subst hd
      exact Or.inr ⟨w, c, hdt⟩
  | transformFailed path index source =>
    obtain ⟨-, -, w, c, _, _, hdt, -, -, rfl⟩ := Step.transformFailed_inv hs
    rw [fail_deliveries] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact Or.inl hd
    · rw [List.mem_singleton] at hd
      subst hd
      exact Or.inr ⟨w, c, hdt⟩
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact keep rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact keep (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact keep rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact keep (by simp)
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
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact keep rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact keep rfl

end Routing

/-- A delivery carries a result of its connection's source, on the connection's arm for a branch (§6, §7.2). --/
theorem Reachable.deliveries_eligible {p : Definition} {s : State} (h : Reachable p s) :
    ∀ d ∈ s.deliveries, ∃ r ∈ s.results, r.id = d.source ∧ r.run = d.run ∧
      ∃ w c, s.workflow? p d.run = some w ∧ w.connections[d.connection]? = some c ∧ r.placement = c.source ∧
        (c.arm = none ∨ r.arm = c.arm) := by
  induction h with
  | empty => intro d hd; cases hd
  | step op hr hs ih =>
    have kept := Routing.step_runsKept hs (Routing.runs_nil_or_started hr)
    have g := step_grows hs
    intro d hd
    rcases Routing.step_deliveries hs d hd with hd | ⟨w, c, hdt⟩
    · obtain ⟨r, hr, hid, hrun, w, c, hw, hc, hpl, harm⟩ := ih d hd
      exact ⟨r, g.mem_results hr, hid, hrun, w, c, kept.workflow? hw, hc, hpl, harm⟩
    · -- A new delivery was checked against the state before the step.
      obtain ⟨hw, hc, ⟨r, hres, hrun, hpl, harm⟩, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
      obtain ⟨hr, hid⟩ := State.result?_eq_some hres
      exact ⟨r, g.mem_results hr, hid, hrun, w, c, kept.workflow? hw, hc, hpl, harm⟩

/-- An invocation with a trigger starts only from a value delivered on its input connection (§5.3, §7.2);
    a failed transform starts nothing (§4.2). --/
theorem Reachable.invocations_triggered {p : Definition} {s : State} (h : Reachable p s) :
    ∀ i ∈ s.invocations, ∀ src, i.trigger = some src →
      ∃ d ∈ s.deliveries, d.run = i.run ∧ d.source = src ∧ d.outcome ≠ .failed ∧
        ∃ w c, s.workflow? p i.run = some w ∧ w.connections[d.connection]? = some c ∧ c.target = i.placement := by
  induction h with
  | empty => intro i hi; cases hi
  | step op hr hs ih =>
    have kept := Routing.step_runsKept hs (Routing.runs_nil_or_started hr)
    have g := step_grows hs
    intro x hx src hsrc
    rcases Routing.step_invocations hs x hx with ⟨y, hy, hrun, hpl, htr⟩ | hop
    · obtain ⟨d, hd, hdrun, hdsrc, hdout, w, c, hw, hc, htgt⟩ := ih y hy src (htr.trans hsrc)
      refine ⟨d, g.mem_deliveries hd, hdrun.trans hrun, hdsrc, hdout, w, c, ?_, hc, htgt.trans hpl⟩
      exact kept.workflow? (hrun ▸ hw)
    · -- The invocation this step added took its input from a delivery on its input connection.
      subst hop
      obtain ⟨-, -, r, w, _, _, _, hr, -, hw, -, hin, -⟩ := Step.invoke_inv hs
      have hwx : _ = some w := kept.workflow? (Routing.workflow?_eq_some.mpr ⟨r, hr, hw⟩)
      have hpath := (State.run?_eq_some hr).2
      rcases Step.invocationInput_inv hin with ⟨-, htr, -⟩ | ⟨-, htr, -⟩ |
          ⟨i, c, source, hshape, htr, hres⟩ | ⟨i, c, source, d, hshape, htr, hd, hout⟩
      · rw [hsrc] at htr; cases htr
      · rw [hsrc] at htr; cases htr
      · rw [hsrc] at htr; cases htr
        obtain ⟨d, hd, hdrun, hdconn, hdsrc, hdout⟩ := Routing.resolveSingle_value hres
        obtain ⟨hc, htgt⟩ := Routing.shape?_connection (Or.inl hshape)
        exact ⟨d, g.mem_deliveries hd, hdrun.trans hpath, hdsrc, hdout, w, c, hwx, hdconn ▸ hc, htgt⟩
      · rw [hsrc] at htr; cases htr
        obtain ⟨hd, hdrun, hdconn, hdsrc⟩ := State.delivery?_eq_some hd
        obtain ⟨hc, htgt⟩ := Routing.shape?_connection (Or.inr hshape)
        refine ⟨d, g.mem_deliveries hd, hdrun.trans hpath, hdsrc, ?_, w, c, hwx, hdconn ▸ hc, htgt⟩
        rcases hout with ⟨v, hv, -⟩ | ⟨hv, -⟩ <;> rw [hv] <;> simp

/-- A branch result carries the arm its judge selected, so a connection of another arm never
    delivers it, and that arm's target and transform never see it (§7.2). --/
theorem Reachable.other_arms_untouched {p : Definition} {s : State} (h : Reachable p s) :
    ∀ d ∈ s.deliveries, ∀ r ∈ s.results, r.id = d.source → ∀ w c, s.workflow? p d.run = some w →
      w.connections[d.connection]? = some c → ∀ a, c.arm = some a → r.arm = some a := by
  intro d hd r hr hid w c hw hc a ha
  obtain ⟨r', hr', hid', -, w', c', hw', hc', -, harm⟩ := h.deliveries_eligible d hd
  -- Results are identified by their id, so `r` is the result the delivery was checked against.
  obtain rfl : r = r' := h.wellKeyed.result_eq_of_id hr hr' (hid.trans hid'.symm)
  rw [hw, Option.some.injEq] at hw'
  subst hw'
  rw [hc, Option.some.injEq] at hc'
  subst hc'
  rcases harm with harm | harm
  · rw [ha] at harm; cases harm
  · rw [harm, ha]

/-- An invocation belongs to an existing run, and a placement of that run's workflow. --/
theorem Reachable.invocations_placed {p : Definition} {s : State} (h : Reachable p s) :
    ∀ i ∈ s.invocations, ∃ w, s.workflow? p i.run = some w ∧ (w.placement? i.placement).isSome := by
  induction h with
  | empty => intro i hi; cases hi
  | step op hr hs ih =>
    have kept := Routing.step_runsKept hs (Routing.runs_nil_or_started hr)
    intro x hx
    rcases Routing.step_invocations hs x hx with ⟨y, hy, hrun, hpl, -⟩ | hop
    · obtain ⟨w, hw, hpw⟩ := ih y hy
      exact ⟨w, kept.workflow? (hrun ▸ hw), hpl ▸ hpw⟩
    · subst hop
      obtain ⟨-, -, r, w, pl, -, -, hr, -, hw, hpl, -⟩ := Step.invoke_inv hs
      exact ⟨w, kept.workflow? (Routing.workflow?_eq_some.mpr ⟨r, hr, hw⟩), by rw [hpl]; rfl⟩

end Suimon
