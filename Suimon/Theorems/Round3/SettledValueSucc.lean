import Suimon.Theorems.Round3.SettledValueOutcome

/-! A succeeded invocation of a Single body has its result (task B2): `returned` accepts the value of
    a Single function, `judged` the input of a branch on the chosen arm, a normal `closeRun` adds
    `Key.returned`, and a concurrency with a List output adds `Key.list` when it closes. A Stream
    function (`ended`) and a concurrency with a Stream output may succeed without a result, so they are
    not Single bodies. -/

namespace Suimon.Round3.SettledAux
open State

/-- A succeeded invocation of a Single body has its result, on the invocation's arm. -/
def SuccResult (p : Definition) (s : State) : Prop :=
  ∀ i ∈ s.invocations, i.status = .succeeded → ∀ pl, Settle.placementAt p s i.run i.placement = some pl →
    SingleBody p pl.control → ∃ r ∈ s.results, r.run = i.run ∧ r.placement = i.placement ∧ r.arm = i.arm

namespace SuccResult
variable {p : Definition} {s t : State}

theorem empty : SuccResult p {} := fun _ h => nomatch h

/-- The placement of a run's workflow stays in the next state. -/
theorem placementAt_kept (hk : Delivery.Kept s t) (wk' : t.WellKeyed) {path : Path} {name : String}
    {pl : Placement} (h : Settle.placementAt p s path name = some pl) : Settle.placementAt p t path name = some pl := by
  unfold Settle.placementAt at h ⊢
  cases hw : s.workflow? p path with
  | none => rw [hw] at h; cases h
  | some w => rw [hw] at h; rw [hk.workflow? wk' hw]; exact h

/-- An invocation from before keeps its result. -/
theorem keep (h : SuccResult p s) (own : Settle.Own p s) (hk : Delivery.Kept s t) (wk' : t.WellKeyed)
    {i : Invocation} (hi : i ∈ s.invocations) (hsucc : i.status = .succeeded) {pl : Placement}
    (hpl : Settle.placementAt p t i.run i.placement = some pl) (hb : SingleBody p pl.control) :
    ∃ r ∈ t.results, r.run = i.run ∧ r.placement = i.placement ∧ r.arm = i.arm := by
  obtain ⟨w, pl', hw, hpl', -⟩ := own.invPlaced i hi
  have hs : Settle.placementAt p s i.run i.placement = some pl' := by rw [Settle.placementAt_eq hw]; exact hpl'
  rw [placementAt_kept hk wk' hs] at hpl
  cases hpl
  obtain ⟨r, hr, h1, h2, h3⟩ := h i hi hsucc _ hs hb
  exact ⟨r, hk.mem_results hr, h1, h2, h3⟩

/-- A step whose succeeded invocations are from before, or the one invocation `i'` it updated, with
    its result. -/
theorem of_update (h : SuccResult p s) (own : Settle.Own p s) (hk : Delivery.Kept s t) (wk' : t.WellKeyed)
    {i' : Invocation} (hold : ∀ i ∈ t.invocations, i.status = .succeeded → i = i' ∨ i ∈ s.invocations)
    (hnew : ∀ pl, Settle.placementAt p t i'.run i'.placement = some pl → SingleBody p pl.control →
      ∃ r ∈ t.results, r.run = i'.run ∧ r.placement = i'.placement ∧ r.arm = i'.arm) : SuccResult p t := by
  intro i hi hsucc pl hpl hb
  rcases hold i hi hsucc with rfl | hi'
  · exact hnew pl hpl hb
  · exact keep h own hk wk' hi' hsucc hpl hb

/-- A step whose succeeded invocations are all from before. -/
theorem of_old (h : SuccResult p s) (own : Settle.Own p s) (hk : Delivery.Kept s t) (wk' : t.WellKeyed)
    (hold : ∀ i ∈ t.invocations, i.status = .succeeded → i ∈ s.invocations) : SuccResult p t :=
  fun i hi hsucc _ hpl hb => keep h own hk wk' (hold i hi hsucc) hsucc hpl hb

/-- A failed call fails its owner, never lets it succeed. -/
theorem failCall_old {c : Call} {status : CallStatus} {cause : Cause} (h : s.failCall c status cause = .ok t) :
    ∀ i ∈ t.invocations, i.status = .succeeded → i ∈ s.invocations := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp h
  intro i hi hsucc
  rw [State.fail_invocations] at hi
  rcases State.settleOwner_eq_ok.mp hso with ⟨-, i₁, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · rcases State.mem_setInvocation_invocations hi with rfl | hi
    · cases hsucc
    · exact hi
  · exact hi

/-- A terminated call cancels its owner, never lets it succeed. -/
theorem cancelOwner_old {c : Call} (h : s.cancelOwner c = .ok t) :
    ∀ i ∈ t.invocations, i.status = .succeeded → i ∈ s.invocations := by
  intro i hi hsucc
  rcases State.cancelOwner_eq_ok.mp h with ⟨-, i₁, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
  · split at hi
    · rcases State.mem_setInvocation_invocations hi with rfl | hi
      · cases hsucc
      · exact hi
    · exact hi
  · split at hi <;> exact hi

theorem step (h : SuccResult p s) (hr : Reachable p s) {op : Op} (hs : Suimon.step p s op = .ok t) :
    SuccResult p t := by
  obtain ⟨own, act, -, -⟩ := Settle.reachable hr
  have wk := hr.wellKeyed
  have wk' := step_wellKeyed wk hs
  have hk := Delivery.Inv.kept (Delivery.Reachable.inv hr) hs
  have same : t.invocations = s.invocations → SuccResult p t := fun he =>
    of_old h own hk wk' fun i hi _ => he ▸ hi
  -- An invocation updated to a status other than succeeded.
  have other : ∀ {i₁ : Invocation} {st : InvocationStatus}, st ≠ .succeeded →
      (∀ i ∈ t.invocations, i = { i₁ with status := st } ∨ i ∈ s.invocations) → SuccResult p t := by
    intro i₁ st hst hmem
    refine of_old h own hk wk' fun i hi hsucc => ?_
    rcases hmem i hi with rfl | h'
    · exact absurd hsucc hst
    · exact h'
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    refine of_old h own hk wk' fun i hi hsucc => ?_
    rw [(Delivery.invocable_of_invoke hcases).2, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact hi
    · cases hsucc
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, -, hrun, -, hacc, hso⟩ := Step.returned_inv hs
    rcases State.accept_eq_ok.mp hacc with ⟨htask, i₁, hi₁, -, rfl⟩ | ⟨name, htask, -, rfl⟩
    · rcases State.settleOwner_eq_ok.mp hso with ⟨-, i₂, hi₂, rfl⟩ | ⟨_, _, _, htask', -⟩
      · have hi₂' : s.invocation? c.owner = some i₂ := hi₂
        rw [hi₁] at hi₂'
        cases hi₂'
        -- The call runs, so its invocation is active and has no arm yet.
        obtain ⟨i', hi', hi'id, hi'act⟩ := act.callActive c (State.call?_eq_some hc).1 htask (Or.inl hrun)
        obtain ⟨hi₁m, hi₁id⟩ := State.invocation?_eq_some hi₁
        obtain rfl := wk.invocation_eq_of_id hi' hi₁m (hi'id.trans hi₁id.symm)
        have harm := act.activeArm _ hi' hi'act
        refine of_update h own hk wk' (i' := { i' with status := .succeeded })
          (fun i hi _ => State.mem_setInvocation_invocations hi) (fun pl _ _ => ?_)
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, harm.symm⟩
      · rw [htask] at htask'; cases htask'
    · rcases State.settleOwner_eq_ok.mp hso with ⟨htask', -⟩ | ⟨_, _, _, -, -, -, rfl⟩
      · rw [htask] at htask'; cases htask'
      · exact same rfl
  | judged id arm =>
    obtain ⟨-, -, c, j, i₁, pl, judge, arms, s', hc, hrun, hj, htask, hi₁, hpl, hb, harm, hacc, rfl⟩ :=
      Step.judged_inv hs
    rcases State.accept_eq_ok.mp hacc with ⟨-, i₂, hi₂, -, rfl⟩ | ⟨name, htask', -, rfl⟩
    · rw [hi₁] at hi₂
      cases hi₂
      refine of_update h own hk wk' (i' := { i₁ with status := .succeeded, arm := some arm })
        (fun i hi _ => State.mem_setInvocation_invocations hi) (fun pl _ _ => ?_)
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
    · rw [htask] at htask'; cases htask'
  | yielded id value =>
    obtain ⟨-, -, c, s', -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by rw [State.setCall_invocations, (accept_frame hacc).2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, c, hc, hstr, -, hso⟩ := Step.ended_inv hs
    rcases State.settleOwner_eq_ok.mp hso with ⟨htask, i₁, hi₁, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩
    · have hi₁' : s.invocation? c.owner = some i₁ := hi₁
      obtain ⟨hi₁m, hi₁id⟩ := State.invocation?_eq_some hi₁'
      obtain ⟨pl₁, hpl₁, hctrl⟩ :=
        Settle.ctrl_of_call own wk (State.call?_eq_some hc).1 htask hi₁m hi₁id.symm
      refine of_update h own hk wk' (i' := { i₁ with status := .succeeded })
        (fun i hi _ => State.mem_setInvocation_invocations hi) (fun pl hpl hb => ?_)
      -- A Stream call belongs to a Stream function, which is not a Single body.
      have hpl' : Settle.placementAt p _ i₁.run i₁.placement = some pl := hpl
      rw [placementAt_kept hk wk' hpl₁] at hpl'
      cases hpl'
      exfalso
      rcases hctrl with ⟨f, decl, hcf, hdecl, hsd⟩ | ⟨jd, arms, -, hsf⟩
      · rw [hcf] at hb
        obtain ⟨decl', hdecl', hk'⟩ := hb
        rw [hdecl] at hdecl'
        cases hdecl'
        rw [hk', hstr] at hsd
        cases hsd
      · rw [hstr] at hsf; cases hsf
    · exact same rfl
  | failed id =>
    obtain ⟨-, -, c, -, -, hf⟩ := Step.failed_inv hs
    exact of_old h own hk wk' (failCall_old hf)
  | timedOut id element =>
    obtain ⟨-, -, c, -, -, hf⟩ := Step.timedOut_inv hs
    exact of_old h own hk wk' (failCall_old hf)
  | lost id =>
    obtain ⟨-, -, c, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact of_old h own hk wk' (failCall_old hf)
    · have hold := cancelOwner_old ho
      exact of_old h own hk wk' hold
  | terminated id =>
    obtain ⟨-, -, c, -, -, ho⟩ := Step.terminated_inv hs
    have hold := cancelOwner_old ho
    exact of_old h own hk wk' hold
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
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    rcases hcases with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact same (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, cc, i₁, he, hcomp, hcc, -, -, hi₁, hcases⟩ := Step.closeExecution_inv hs
    obtain ⟨hem, heid⟩ := State.execution?_eq_some he
    obtain ⟨hi₁m, hi₁id⟩ := State.invocation?_eq_some hi₁
    -- The invocation of the execution is placed where the execution is.
    obtain ⟨i₃, hi₃, hi₃e, hi₃r, hi₃p, pl₃, cc₃, hpl₃, hcc₃, -⟩ := own.execOwner e hem
    obtain rfl := wk.invocation_eq_of_id hi₃ hi₁m (hi₃e.trans (heid.trans hi₁id.symm))
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hout, rfl⟩
    · exact other (by decide) fun i hi => State.mem_setInvocation_invocations hi
    · -- The open execution keeps its invocation active, without an arm.
      obtain ⟨i', hi', hi'id, hi'act⟩ := act.execActive e hem hcomp
      obtain rfl := wk.invocation_eq_of_id hi' hi₃ (hi'id.trans hi₃e.symm)
      have harm := act.activeArm _ hi' hi'act
      refine of_update h own hk wk' (i' := { i' with status := .succeeded })
        (fun i hi _ => State.mem_setInvocation_invocations hi) (fun pl _ _ => ?_)
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hi₃r.symm, hi₃p.symm, harm.symm⟩
    · -- A Stream output is not a Single body.
      refine of_update h own hk wk' (i' := { i₃ with status := .succeeded })
        (fun i hi _ => State.mem_setInvocation_invocations hi) (fun pl hpl hb => ?_)
      exfalso
      have hpl' : Settle.placementAt p _ i₃.run i₃.placement = some pl := hpl
      have hs3 : Settle.placementAt p s i₃.run i₃.placement = some pl₃ := by rw [hi₃r, hi₃p]; exact hpl₃
      rw [placementAt_kept hk wk' hs3] at hpl'
      cases hpl'
      obtain ⟨pl', hpl', hc'⟩ := State.concurrencyOf_eq_ok.mp hcc
      obtain ⟨w', hw', hpl''⟩ := State.placementOf_eq_ok.mp hpl'
      rw [Settle.placementAt_eq hw', hpl''] at hpl₃
      cases hpl₃
      rw [hcc₃] at hc'
      cases hc'
      rw [hcc₃] at hb
      have hb' : cc.output = .list := hb
      rw [hout] at hb'
      cases hb'
  | closeRun path =>
    obtain ⟨-, -, r, w, output, x, owner, hr, hcomp, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨htask, i₁, hi₁, hcases⟩ | ⟨name, e, ts, htask, -, -, hcases⟩
    · obtain ⟨hi₁m, hi₁id⟩ := State.invocation?_eq_some hi₁
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · -- The open run keeps its invocation active, without an arm.
        obtain ⟨i', hi', hi'id, hi'act⟩ := act.runActive r (State.run?_eq_some hr).1 owner howner htask hcomp
        obtain rfl := wk.invocation_eq_of_id hi' hi₁m (hi'id.trans hi₁id.symm)
        have harm := act.activeArm _ hi' hi'act
        refine of_update h own hk wk' (i' := { i' with status := .succeeded })
          (fun i hi _ => State.mem_setInvocation_invocations hi) (fun pl _ _ => ?_)
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, harm.symm⟩
      · exact other (by decide) fun i hi => State.mem_setInvocation_invocations hi
      · exact other (by decide) fun i hi => State.mem_setInvocation_invocations hi
      · exact other (by decide) fun i hi => State.mem_setInvocation_invocations hi
    · rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

end SuccResult

/-- A succeeded invocation of a Single body has its result in every reachable state. -/
theorem reachable_succResult {p : Definition} {s : State} (h : Reachable p s) : SuccResult p s := by
  induction h with
  | empty => exact SuccResult.empty
  | step op hr hs ih => exact ih.step hr hs

end Suimon.Round3.SettledAux
