import Suimon.Theorems.Round3.Universe
import Suimon.Theorems.Round3.Progress

namespace Suimon.Round3
open State

/-! ## [12] Round3/Termination.lean — task D3 -/

/-! ### Calls waiting for the outside world

What liveness needs about calls, in every reachable state: a fetching call is a Stream call, the owner
of every call exists, and a judge that can name an arm belongs to a branch invocation. -/

namespace Liveness
variable {p : Definition} {s t u : State}

/-- Every fetching call of `t` is a call of `s` or a Stream call. -/
def FetchKept (s t : State) : Prop :=
  ∀ x ∈ t.calls, x.status = .fetching → x ∈ s.calls ∨ x.stream = true

namespace FetchKept

theorem of_calls (h : t.calls = s.calls) : FetchKept s t := fun _ hx _ => Or.inl (h ▸ hx)

theorem trans (h₁ : FetchKept s u) (h₂ : FetchKept u t) : FetchKept s t := fun x hx hf =>
  (h₂ x hx hf).elim (fun hu => h₁ x hu hf) Or.inr

theorem append {c : Call} (h : t.calls = s.calls ++ [c]) (hc : c.status = .running) : FetchKept s t := by
  intro x hx hf
  rw [h, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact Or.inl hx
  · rw [hc] at hf
    cases hf

theorem setCall {c : Call} (hc : c.status = .fetching → c.stream = true) : FetchKept s (s.setCall c) := by
  intro x hx hf
  rcases State.mem_setCall_calls hx with rfl | hx
  · exact Or.inr (hc hf)
  · exact Or.inl hx

theorem stop : FetchKept s s.stop := fun _ hx hf => absurd hf (State.stop_calls_quiet hx).2

theorem fail {f : Failure} {policy : Policy} : FetchKept s (s.fail f policy) := by
  have h : FetchKept s { s with failures := s.failures ++ [f] } := of_calls rfl
  cases policy
  · exact h.trans stop
  · exact h

theorem failCall {c : Call} {status : CallStatus} {cause : Cause} (hst : status ≠ .fetching)
    (hf : s.failCall c status cause = .ok t) : FetchKept s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp hf
  exact ((setCall fun h => absurd h hst).trans (of_calls (State.settleOwner_update hso).calls)).trans fail

end FetchKept

/-- Only `fetch` stores a fetching call, and it requires a Stream call. -/
theorem step_fetchKept {op : Op} (hs : step p s op = .ok t) : FetchKept s t := by
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact FetchKept.of_calls rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact FetchKept.append rfl rfl
    · exact FetchKept.append rfl rfl
    · exact FetchKept.of_calls rfl
    · exact FetchKept.of_calls rfl
  | fetch id =>
    obtain ⟨-, -, c, -, hstream, -, rfl⟩ := Step.fetch_inv hs
    exact FetchKept.setCall fun _ => hstream
  | returned id value =>
    obtain ⟨-, -, c, _, s', -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact ((FetchKept.of_calls (State.accept_frame hacc).2.2.2.2.2.1).trans
      (FetchKept.setCall fun h => by simp at h)).trans (FetchKept.of_calls (State.settleOwner_update hso).calls)
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact ((FetchKept.of_calls (State.accept_frame hacc).2.2.2.2.2.1).trans
      (FetchKept.setCall fun h => by simp at h)).trans (FetchKept.of_calls rfl)
  | yielded id value =>
    obtain ⟨-, -, c, s', -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (FetchKept.of_calls (State.accept_frame hacc).2.2.2.2.2.1).trans
      (FetchKept.setCall fun h => by simp at h)
  | ended id =>
    obtain ⟨-, -, c, -, -, -, hso⟩ := Step.ended_inv hs
    exact (FetchKept.setCall fun h => by simp at h).trans (FetchKept.of_calls (State.settleOwner_update hso).calls)
  | failed id =>
    obtain ⟨-, -, c, -, -, hf⟩ := Step.failed_inv hs
    exact FetchKept.failCall (by simp) hf
  | timedOut id element =>
    obtain ⟨-, -, c, -, -, hf⟩ := Step.timedOut_inv hs
    exact FetchKept.failCall (by simp) hf
  | lost id =>
    obtain ⟨-, -, c, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact FetchKept.failCall (by simp) hf
    · exact (FetchKept.setCall fun h => by simp at h).trans (FetchKept.of_calls (State.cancelOwner_update ho).calls)
  | terminated id =>
    obtain ⟨-, -, c, -, -, ho⟩ := Step.terminated_inv hs
    exact (FetchKept.setCall fun h => by simp at h).trans (FetchKept.of_calls (State.cancelOwner_update ho).calls)
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact FetchKept.of_calls rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact (FetchKept.of_calls rfl).trans FetchKept.fail
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact FetchKept.of_calls rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (FetchKept.of_calls rfl).trans FetchKept.fail
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact FetchKept.append rfl rfl
    · exact FetchKept.of_calls rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact FetchKept.of_calls rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (FetchKept.of_calls rfl).trans FetchKept.fail
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact FetchKept.of_calls rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact FetchKept.of_calls rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact FetchKept.of_calls rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact FetchKept.stop.trans (FetchKept.of_calls rfl)
    · exact FetchKept.of_calls rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;>
      exact FetchKept.of_calls rfl

/-- A fetching call is a Stream call: only `fetch` makes a call fetch (§4.1.1). -/
theorem fetching_stream (h : Reachable p s) : ∀ c ∈ s.calls, c.status = .fetching → c.stream = true := by
  induction h with
  | empty => intro c hc; nomatch hc
  | step op _ hs ih =>
    intro c hc hf
    exact (step_fetchKept hs c hc hf).elim (fun hc' => ih c hc' hf) id

/-- The owner record of every call exists: its invocation, or its execution with the task. -/
theorem ownerFound (h : Reachable p s) {c : Call} (hc : c ∈ s.calls) : OwnerFound s c := by
  have inv := Delivery.Reachable.inv h
  rcases inv.own.calls c hc with
    ⟨htask, -, i, hi, hid, -⟩ | ⟨name, htask, -, e, he, heo, ⟨tk, htk, hname⟩, -⟩
  · simp only [OwnerFound, htask]
    exact ⟨i, hid ▸ inv.wk.invocation?_of_mem hi⟩
  · simp only [OwnerFound, htask]
    have hsome : (e.tasks.find? (·.name == name)).isSome := List.find?_isSome.mpr ⟨tk, htk, by simp [hname]⟩
    obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨e, ts, heo ▸ inv.wk.execution?_of_mem he, hts⟩

/-- An arm of a judge's branch comes from the branch placement of the judge's owner. -/
theorem mem_judgeArms {c : Call} {a : String} (ha : a ∈ judgeArms p s c) :
    ∃ i pl j arms, s.invocation? c.owner = some i ∧ s.placementOf p i.run i.placement = .ok pl ∧
      pl.control = .branch j arms ∧ a ∈ arms := by
  unfold judgeArms at ha
  split at ha
  · rename_i heq
    obtain ⟨i, hi, hpl⟩ := Option.bind_eq_some_iff.mp heq
    obtain ⟨w, hw, hwpl⟩ := Option.bind_eq_some_iff.mp hpl
    exact ⟨i, _, _, _, hi, State.placementOf_eq_ok.mpr ⟨w, hw, hwpl⟩, rfl, ha⟩
  · simp at ha

/-- A judge with an arm to name belongs to a branch invocation, not to a task (a task's owner is a
    concurrency invocation), and it does not stream. -/
theorem judge_call (h : Reachable p s) {c : Call} (hc : c ∈ s.calls) {j a : String} (hj : c.target = .judge j)
    (ha : a ∈ judgeArms p s c) : c.task = none ∧ c.stream = false := by
  have inv := Delivery.Reachable.inv h
  obtain ⟨i, pl, j', arms, hi, hpl, hbranch, -⟩ := mem_judgeArms ha
  rcases inv.own.calls c hc with ⟨htask, -, _, -, -, _, _, -, -, hcases⟩ | ⟨name, htask, -, e, he, heo, -, -⟩
  · refine ⟨htask, ?_⟩
    rcases hcases with ⟨f, d, -, -, hf, -⟩ | ⟨-, -, -, -, hstream⟩
    · rw [hj] at hf
      cases hf
    · exact hstream
  · exfalso
    obtain ⟨i', hi', hid, hrun, hplc, cc, hcc⟩ := inv.own.executions e he
    have h1 := inv.wk.invocation?_of_mem hi'
    rw [hid, heo, hi] at h1
    cases h1
    obtain ⟨pl', hpl', hctrl⟩ := State.concurrencyOf_eq_ok.mp hcc
    rw [← hrun, ← hplc, hpl] at hpl'
    cases hpl'
    rw [hbranch] at hctrl
    cases hctrl

end Liveness

section Termination
variable {p : Definition} {env : Env} {s : State}

/-- The outside world answers (§15.3): a waiting call gets the report its script prescribes, and the
    step accepts it. A fetching call gets its next element or its ending, a running Single function or
    judge its ending, a cancelling call `terminated`. -/
theorem waiting_answers (valid : p.validate = .ok ()) (fits : env.Fits p) {tr : List Op} (h : Conforming p env tr s)
    (live : s.status.terminal = false) (waiting : Waiting s) :
    ∃ op t, Conforms env s op ∧ step p s op = .ok t ∧ t ≠ s := by
  -- Validity is not needed: every fact used holds in all reachable states.
  have _ := valid
  have hr := h.reachable
  obtain ⟨c, hc, hwait⟩ := waiting
  have started : s.started = true := by
    rcases hr.eq_empty_or_started with rfl | hs
    · nomatch hc
    · exact hs
  have hlive : s.status = .running ∨ s.status = .stopping := by
    cases hst : s.status with
    | running => exact Or.inl rfl
    | stopping => exact Or.inr rfl
    | _ => simp [hst, Status.terminal] at live
  have hcall : s.call? c.id = some c := hr.wellKeyed.call?_of_mem hc
  have howner : OwnerFound s c := Liveness.ownerFound hr hc
  -- A running or fetching call leaves the state running: the stop cancels every such call.
  have running_of : c.status = .running ∨ c.status = .fetching → s.status = .running := by
    intro hst
    rcases hlive with hrun | hstop
    · exact hrun
    · obtain ⟨h1, h2⟩ := hr.quiet hstop c hc
      exact (hst.elim h1 h2).elim
  have hyields := h.yields_le c hc
  have hfit := fits tr s h c hc
  have hfree := (Reachable.fresh hr).callIndex c hc
  rcases hwait with hfetch | hcan | ⟨hrun, hsingle⟩
  · -- A fetching call gets its next element, or its ending once every element was reported.
    have running := running_of (Or.inr hfetch)
    have hstream := Liveness.fetching_stream hr c hc hfetch
    have hfree' := hfree (Or.inr hfetch)
    by_cases hlt : c.yields < (env.behavior.script c.id).yields.length
    · obtain ⟨t, ht, hne⟩ := yielded_enabled (p := p) started running hcall hstream hfetch howner
        (hfree' _ (Nat.le_refl _)) ((env.behavior.script c.id).yields[c.yields])
      exact ⟨.yielded c.id _, t, ⟨c, hcall, List.getElem?_eq_getElem hlt⟩, ht, hne⟩
    have hfinal : (env.behavior.script c.id).Final c := by
      unfold Script.Final
      omega
    cases hend : (env.behavior.script c.id).ending with
    | returned v =>
      simp only [Script.Fits, hend] at hfit
      rw [hstream] at hfit
      exact absurd hfit.1 (by simp)
    | judged a =>
      simp only [Script.Fits, hend] at hfit
      obtain ⟨⟨j, hj⟩, ha, -⟩ := hfit
      rw [(Liveness.judge_call hr hc hj ha).2] at hstream
      cases hstream
    | ended =>
      obtain ⟨t, ht, hne⟩ := ended_enabled (p := p) started running hcall hstream hfetch howner
      exact ⟨.ended c.id, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
    | failed =>
      obtain ⟨t, ht, hne⟩ := failed_enabled (p := p) started running hcall (Or.inr hfetch) howner
      exact ⟨.failed c.id, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
    | timedOut el =>
      cases el with
      | true =>
        simp only [Script.Fits, hend] at hfit
        obtain ⟨t, ht, hne⟩ := timedOut_enabled (p := p) (element := true) started running hcall howner
          ⟨hfetch, hfit.2⟩
        exact ⟨.timedOut c.id true, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
      | false =>
        simp only [Script.Fits, hend] at hfit
        obtain ⟨t, ht, hne⟩ := timedOut_enabled (p := p) (element := false) started running hcall howner
          ⟨Or.inr hfetch, hfit.1⟩
        exact ⟨.timedOut c.id false, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
    | lost =>
      obtain ⟨t, ht, hne⟩ := lost_enabled (p := p) started hlive hcall (Or.inr (Or.inl hfetch)) howner
      exact ⟨.lost c.id, t, ⟨c, hcall, Or.inr ⟨hfinal, hend⟩⟩, ht, hne⟩
  · -- A cancelling call terminates (§15.3).
    obtain ⟨t, ht, hne⟩ := terminated_enabled (p := p) started hlive hcall hcan howner
    exact ⟨.terminated c.id, t, trivial, ht, hne⟩
  · -- A running Single function or judge: a fitting script yields nothing, so its ending conforms now.
    have running := running_of (Or.inl hrun)
    have hfree' := hfree (Or.inl hrun)
    have final_of : (env.behavior.script c.id).yields = [] →
        (env.behavior.script c.id).Final c ∧ IndexFree s c 0 := by
      intro hnil
      rw [hnil] at hyields
      have h0 : c.yields = 0 := Nat.le_zero.mp hyields
      exact ⟨by simp [Script.Final, hnil, h0], hfree' 0 (by omega)⟩
    cases hend : (env.behavior.script c.id).ending with
    | returned v =>
      simp only [Script.Fits, hend] at hfit
      obtain ⟨-, hf, hnil⟩ := hfit
      obtain ⟨hfinal, hfree0⟩ := final_of hnil
      obtain ⟨t, ht, hne⟩ := returned_enabled (p := p) started running hcall hsingle hrun hf howner hfree0 v
      exact ⟨.returned c.id v, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
    | judged a =>
      simp only [Script.Fits, hend] at hfit
      obtain ⟨⟨j, hj⟩, ha, hnil⟩ := hfit
      obtain ⟨hfinal, hfree0⟩ := final_of hnil
      obtain ⟨i, pl, j', arms, hi, hpl, hbranch, ha'⟩ := Liveness.mem_judgeArms ha
      obtain ⟨t, ht, hne⟩ := judged_enabled (p := p) started running hcall hrun ⟨j, hj⟩
        (Liveness.judge_call hr hc hj ha).1 hi hpl hbranch ha' hfree0
      exact ⟨.judged c.id a, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
    | ended =>
      simp only [Script.Fits, hend] at hfit
      rw [hsingle] at hfit
      cases hfit
    | failed =>
      simp only [Script.Fits, hend] at hfit
      obtain ⟨hfinal, -⟩ := final_of (hfit.resolve_left (by simp [hsingle]))
      obtain ⟨t, ht, hne⟩ := failed_enabled (p := p) started running hcall (Or.inl hrun) howner
      exact ⟨.failed c.id, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
    | timedOut el =>
      cases el with
      | true =>
        simp only [Script.Fits, hend] at hfit
        rw [hsingle] at hfit
        exact absurd hfit.1 (by simp)
      | false =>
        simp only [Script.Fits, hend] at hfit
        obtain ⟨hfinal, -⟩ := final_of (hfit.2.resolve_left (by simp [hsingle]))
        obtain ⟨t, ht, hne⟩ := timedOut_enabled (p := p) (element := false) started running hcall howner
          ⟨Or.inl hrun, hfit.1⟩
        exact ⟨.timedOut c.id false, t, ⟨c, hcall, hfinal, hend⟩, ht, hne⟩
    | lost =>
      simp only [Script.Fits, hend] at hfit
      obtain ⟨hfinal, -⟩ := final_of (hfit.resolve_left (by simp [hsingle]))
      obtain ⟨t, ht, hne⟩ := lost_enabled (p := p) started hlive hcall (Or.inl hrun) howner
      exact ⟨.lost c.id, t, ⟨c, hcall, Or.inr ⟨hfinal, hend⟩⟩, ht, hne⟩

/-- The caller's input starts the workflow. Proven. -/
theorem start_accepted (valid : p.validate = .ok ()) (hin : env.InputFits p) :
    ∃ t, step p {} (.start env.input) = .ok t ∧ t ≠ {} := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (Definition.validate_ok valid).main
  have hmatch : w.input.isSome = env.input.isSome := by
    have := hin
    simp only [Env.InputFits, hw, Option.bind_some] at this
    exact this
  refine ⟨{ started := true, runs := [{ path := [], workflow := p.main, input := env.input }] }, ?_, ?_⟩
  · simp [step, Step.start, require, need, hw, hmatch, pure, Except.pure, bind, Except.bind]
  · intro heq
    have := congrArg State.started heq
    simp at this

/-- An execution that cannot be extended has a final status. -/
theorem stuck_terminal (valid : p.validate = .ok ()) (hin : env.InputFits p) (fits : env.Fits p) {tr : List Op}
    (h : Conforming p env tr s) (stuck : Stuck p env s) : s.status.terminal = true := by
  cases hterm : s.status.terminal
  · exfalso
    rcases h.reachable.eq_empty_or_started with rfl | started
    · obtain ⟨t, ht, hne⟩ := start_accepted valid hin
      exact hne (stuck (.start env.input) t rfl ht)
    · by_cases hw : Waiting s
      · obtain ⟨op, t, hop, ht, hne⟩ := waiting_answers valid fits h hterm hw
        exact hne (stuck _ _ hop ht)
      · obtain ⟨op, t, -, hop, ht, hne⟩ := progress valid h.reachable started hterm hw env
        exact hne (stuck _ _ hop ht)
  · rfl

/-- **Termination (終了, §15.2, §15.3).** Every conforming execution is at most `N` long, and one that
    cannot be extended has ended in a final status. So any scheduler that keeps taking a conforming
    operation while one exists reaches a final status within `N` operations. -/
theorem termination (valid : p.validate = .ok ()) (hin : env.InputFits p) (fits : env.Fits p) :
    ∃ N, ∀ tr s, Conforming p env tr s → tr.length ≤ N ∧ (Stuck p env s → s.status.terminal = true) :=
  ⟨workBound p env.behavior, fun _ _ h => ⟨bounded valid h, stuck_terminal valid hin fits h⟩⟩

/-- Every conforming execution can be continued to a final status. -/
theorem can_finish (valid : p.validate = .ok ()) (hin : env.InputFits p) (fits : env.Fits p) {tr : List Op}
    (h : Conforming p env tr s) : ∃ tr' t, Conforming p env (tr ++ tr') t ∧ t.status.terminal = true := by
  suffices key : ∀ n (tr : List Op) (s : State), workBound p env.behavior - tr.length = n →
      Conforming p env tr s → ∃ tr' t, Conforming p env (tr ++ tr') t ∧ t.status.terminal = true from
    key _ tr s rfl h
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro tr s hn h
    by_cases hstuck : Stuck p env s
    · exact ⟨[], s, by simpa using h, stuck_terminal valid hin fits h hstuck⟩
    · have hmove : ∃ op t, Conforms env s op ∧ step p s op = .ok t ∧ t ≠ s :=
        Classical.byContradiction fun hno => hstuck fun op t hc hs =>
          Classical.byContradiction fun hne => hno ⟨op, t, hc, hs, hne⟩
      obtain ⟨op, t, hc, hs, hne⟩ := hmove
      have h' : Conforming p env (tr ++ [op]) t := .snoc h hc hs hne
      have hb := bounded valid h'
      have hlt : workBound p env.behavior - (tr ++ [op]).length < n := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hb ⊢
        omega
      obtain ⟨tr', u, hu, hterm⟩ := ih _ hlt (tr ++ [op]) t rfl h'
      exact ⟨op :: tr', u, by simpa using hu, hterm⟩

end Termination

end Suimon.Round3
