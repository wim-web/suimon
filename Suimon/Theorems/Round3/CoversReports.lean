import Suimon.Theorems.Round3.Covers
import Suimon.Theorems.Round3.CoversReportsArm
import Suimon.Theorems.Round3.CoversReportsBase

namespace Suimon.Round3
open State CoversReportsAux

/-! ## [23] Round3/CoversReports.lean — task F5

A report of a call in run 1 is matched by the same call in `T`, which ended there; its ending is fixed
by the behavior (`CallConform` and `OwnerConform` in both runs), so the call, its results and its owner
agree. -/

section CoversReports
variable {p : Definition} {env : Env} {s s' T : State}

theorem covers_returned {id : String} {value : Value} (h : StepCtx p env T s (.returned id value) s') :
    Covers p T s' := by
  have F := facts h
  obtain ⟨-, -, c, f, s₁, hc, hstream, hstatus, htarget, hacc, hso⟩ := Step.returned_inv h.accepted
  obtain ⟨hcm, rfl⟩ := call?_eq_some hc
  obtain ⟨c₀, hc₀, hfinal, hend⟩ := h.conforms
  rw [Option.some.inj (hc₀.symm.trans hc)] at hfinal
  obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
  obtain ⟨ccT, ocT⟩ := F.rcT.calls cT hcT
  have hcTeq : cT = { c with status := .returned } :=
    covered_call_eq ccT (F.satT.calls cT hcT) e1 e2 e3 e4 e5 e6 e7 e8 (Or.inl ⟨value, hend⟩) hfinal
  have hstT : cT.status = .returned := by rw [hcTeq]
  obtain ⟨hinvT, htaskT⟩ := owner_succeeded F hcm hcT ocT e2 e3 e4 e6 (Or.inl hstatus) hstT
    (fun j hj _ => by rw [htarget] at hj; cases hj)
  have hk : if cT.stream then 0 < cT.yields else 0 = 0 ∧ cT.status = .returned := by
    simp [e6, hstream, hstT]
  rcases accept_eq_ok.mp hacc with ⟨htask, i, hi, -, rfl⟩ | ⟨name, htask, -, rfl⟩
  · -- The returned value is a result of the invocation, the same one in `T`.
    obtain ⟨r, hr, h1, h2, h3, h4, -, h6, -⟩ := call_result h.covers F.wkT ccT e1 e2 e6 (e3.trans htask) hi hk
    obtain ⟨h7, h8⟩ := h6 value hstream hend
    refine covers_settleOwner h hcm (Or.inl hstatus) hso rfl rfl rfl rfl rfl rfl ?_ h.covers.taskResults
      rfl rfl rfl rfl rfl rfl rfl rfl ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun _ => hcTeq⟩ hinvT htaskT
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.covers.results x hx
    · rw [List.mem_singleton.mp hx, ← result_eq h1 h2 h3 h4 h8 h7]
      exact hr
  · -- The returned value is a result of the task, the same one in `T`.
    obtain ⟨r, hr, h1, h2, h3, -, h5⟩ := call_taskResult ccT e1 e2 e6 (e3.trans htask) hk
    refine covers_settleOwner h hcm (Or.inl hstatus) hso rfl rfl rfl rfl rfl rfl h.covers.results ?_
      rfl rfl rfl rfl rfl rfl rfl rfl ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun _ => hcTeq⟩ hinvT htaskT
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.covers.taskResults x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨r, hr, h1, h2, h3, h5 value hstream hend, fun hne => absurd rfl hne⟩

theorem covers_judged {id arm : String} (h : StepCtx p env T s (.judged id arm) s') : Covers p T s' := by
  have F := facts h
  obtain ⟨-, -, c, j, i, pl, judge, arms, s₁, hc, hstatus, htarget, htask, hi, -, -, -, hacc, rfl⟩ :=
    Step.judged_inv h.accepted
  obtain ⟨hcm, rfl⟩ := call?_eq_some hc
  obtain ⟨c₀, hc₀, hfinal, hend⟩ := h.conforms
  rw [Option.some.inj (hc₀.symm.trans hc)] at hfinal
  obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
  obtain ⟨ccT, ocT⟩ := F.rcT.calls cT hcT
  have hcTeq : cT = { c with status := .returned } :=
    covered_call_eq ccT (F.satT.calls cT hcT) e1 e2 e3 e4 e5 e6 e7 e8 (Or.inr (Or.inl ⟨arm, hend⟩)) hfinal
  have hstT : cT.status = .returned := by rw [hcTeq]
  -- The script ends in a judgment, so the call does not stream.
  have hstream : c.stream = false := by
    obtain ⟨-, hs⟩ := ccT.returned hstT
    rw [e1] at hs
    rcases hs with ⟨hs, -⟩ | ⟨-, he⟩
    · rw [← e6]
      exact hs
    · rw [hend] at he
      cases he
  have hk : if cT.stream then 0 < cT.yields else 0 = 0 ∧ cT.status = .returned := by
    simp [e6, hstream, hstT]
  obtain ⟨r, hr, h1, h2, h3, h4, -, -, h7⟩ := call_result h.covers F.wkT ccT e1 e2 e6 (e3.trans htask) hi hk
  obtain ⟨h8, h9⟩ := h7 arm hstream hend
  -- `T`'s invocation succeeded with the same arm: it owns the judge's result.
  obtain ⟨iT, hiT, hst⟩ := (ownerConform_none ocT (e3.trans htask)).1 hstT
  rw [e2] at hiT
  have harm : iT.arm = some arm := by
    rcases F.dynT.results r hr with ⟨i₀, hi₀, hid₀, -, -, ha₀, -⟩ | ⟨-, ha, -⟩
    · have hcid := call_id_owner F.ownT hcT (e3.trans htask)
      obtain ⟨hiTm, hiTid⟩ := invocation?_eq_some hiT
      have hii : i₀ = iT := F.wkT.invocation_eq_of_id hi₀ hiTm (by rw [hid₀, h4, ← e1, hcid, e2, hiTid])
      rw [← hii, ha₀, h9]
    · rw [h9] at ha
      cases ha
  obtain ⟨him, hiid⟩ := invocation?_eq_some hi
  have hcov := owner_covered h.covers F.wkT him (by rw [hiid]; exact hiT)
  rw [hst, harm] at hcov
  rcases accept_eq_ok.mp hacc with ⟨-, i', hi', -, rfl⟩ | ⟨_, htask', -⟩
  · have hii : i' = i := Option.some.inj (hi'.symm.trans hi)
    subst hii
    refine covers_of_parts h rfl rfl rfl (inv_replace h.covers rfl hcov)
      (calls_replace h.covers rfl ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun _ => hcTeq⟩)
      h.covers.executions (fun e he hc => ⟨e, he, rfl, hc⟩) ?_ h.covers.taskResults
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.covers.results x hx
    · rw [List.mem_singleton.mp hx, ← result_eq h1 h2 h3 h4 h9 h8]
      exact hr
  · rw [htask] at htask'
    cases htask'

theorem covers_yielded {id : String} {value : Value} (h : StepCtx p env T s (.yielded id value) s') :
    Covers p T s' := by
  have F := facts h
  obtain ⟨-, -, c, s₁, hc, hstream, -, hacc, rfl⟩ := Step.yielded_inv h.accepted
  obtain ⟨hcm, rfl⟩ := call?_eq_some hc
  obtain ⟨c₀, hc₀, hval⟩ := h.conforms
  rw [Option.some.inj (hc₀.symm.trans hc)] at hval
  obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
  obtain ⟨ccT, -⟩ := F.rcT.calls cT hcT
  -- `T`'s call ended after every element of the script, so it reported this one.
  have hk : if cT.stream then c.yields < cT.yields else c.yields = 0 ∧ cT.status = .returned := by
    have hF := (endsAs_of_conform ccT (F.satT.calls cT hcT)).2
    unfold Script.Final at hF
    rw [e1] at hF
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hval
    simp [e6, hstream, hF, hlt]
  have hcall : CallCovered T { c with status := .running, yields := c.yields + 1 } :=
    ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun h' => by simp [CallStatus.ended] at h'⟩
  rcases accept_eq_ok.mp hacc with ⟨htask, i, hi, -, rfl⟩ | ⟨name, htask, -, rfl⟩
  · obtain ⟨r, hr, h1, h2, h3, h4, h5, -, -⟩ := call_result h.covers F.wkT ccT e1 e2 e6 (e3.trans htask) hi hk
    obtain ⟨h6, h7⟩ := h5 hstream
    rw [hval] at h6
    refine covers_of_parts h rfl rfl rfl h.covers.invocations (calls_replace h.covers rfl hcall)
      h.covers.executions (fun e he hc => ⟨e, he, rfl, hc⟩) ?_ h.covers.taskResults
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.covers.results x hx
    · rw [List.mem_singleton.mp hx, ← result_eq h1 h2 h3 h4 h7 (Option.some.inj h6).symm]
      exact hr
  · obtain ⟨r, hr, h1, h2, h3, h4, -⟩ := call_taskResult ccT e1 e2 e6 (e3.trans htask) hk
    have h5 := h4 hstream
    rw [hval] at h5
    refine covers_of_parts h rfl rfl rfl h.covers.invocations (calls_replace h.covers rfl hcall)
      h.covers.executions (fun e he hc => ⟨e, he, rfl, hc⟩) h.covers.results ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.covers.taskResults x hx
    · rw [List.mem_singleton.mp hx]
      exact ⟨r, hr, h1, h2, h3, (Option.some.inj h5).symm, fun hne => absurd rfl hne⟩

theorem covers_ended {id : String} (h : StepCtx p env T s (.ended id) s') : Covers p T s' := by
  have F := facts h
  obtain ⟨-, -, c, hc, hstream, hstatus, hso⟩ := Step.ended_inv h.accepted
  obtain ⟨hcm, rfl⟩ := call?_eq_some hc
  obtain ⟨c₀, hc₀, hfinal, hend⟩ := h.conforms
  rw [Option.some.inj (hc₀.symm.trans hc)] at hfinal
  obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
  obtain ⟨ccT, ocT⟩ := F.rcT.calls cT hcT
  have hcTeq : cT = { c with status := .returned } :=
    covered_call_eq ccT (F.satT.calls cT hcT) e1 e2 e3 e4 e5 e6 e7 e8 (Or.inr (Or.inr hend)) hfinal
  have hstT : cT.status = .returned := by rw [hcTeq]
  -- A Stream call is not a judge's.
  obtain ⟨hinvT, htaskT⟩ := owner_succeeded F hcm hcT ocT e2 e3 e4 e6 (Or.inr hstatus) hstT
    (fun _ _ hs => by rw [hstream] at hs; cases hs)
  exact covers_settleOwner h hcm (Or.inr hstatus) hso rfl rfl rfl rfl rfl rfl h.covers.results
    h.covers.taskResults rfl rfl rfl rfl rfl rfl rfl rfl ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun _ => hcTeq⟩
    hinvT htaskT

theorem covers_failed {id : String} (h : StepCtx p env T s (.failed id) s') : Covers p T s' := by
  have F := facts h
  obtain ⟨-, -, c, hc, hrun, hf⟩ := Step.failed_inv h.accepted
  obtain ⟨hcm, rfl⟩ := call?_eq_some hc
  obtain ⟨c₀, hc₀, hfinal, hend⟩ := h.conforms
  rw [Option.some.inj (hc₀.symm.trans hc)] at hfinal
  obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
  obtain ⟨ccT, ocT⟩ := F.rcT.calls cT hcT
  have hcTeq : cT = { c with status := .failed } :=
    covered_call_eq ccT (F.satT.calls cT hcT) e1 e2 e3 e4 e5 e6 e7 e8 hend hfinal
  have hstT : cT.status = .failed := by rw [hcTeq]
  obtain ⟨hinvT, htaskT⟩ := owner_failed F hcm ocT e2 e3 hrun (Or.inl hstT)
  obtain ⟨f, s'', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  have hpol : c.policy = .continue := policy_continue F.pol'
    (by rw [(Delivery.settleOwner_old hso).2.1]; exact mem_setCall_status hcm _) (Or.inl rfl)
  exact covers_settleOwner h hcm hrun hso rfl rfl rfl rfl rfl rfl h.covers.results h.covers.taskResults
    fail_runs fail_invocations (by rw [hpol]; rfl) (by rw [hpol]; rfl) fail_results fail_taskResults
    fail_deliveries fail_settled ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun _ => hcTeq⟩ hinvT htaskT

theorem covers_timedOut {id : String} {element : Bool} (h : StepCtx p env T s (.timedOut id element) s') :
    Covers p T s' := by
  have F := facts h
  obtain ⟨-, -, c, hc, h3, hf⟩ := Step.timedOut_inv h.accepted
  have hrun : c.status = .running ∨ c.status = .fetching := by
    rcases h3 with ⟨-, h', -⟩ | ⟨-, h', -⟩
    · exact Or.inr h'
    · exact h'
  obtain ⟨hcm, rfl⟩ := call?_eq_some hc
  obtain ⟨-, -, -, hend⟩ := h.conforms
  obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
  obtain ⟨ccT, ocT⟩ := F.rcT.calls cT hcT
  -- `T`'s call was timed out as well and has terminated since.
  have hstT : cT.status = .cancelled := covered_status ccT (F.satT.calls cT hcT) e1 ⟨element, hend⟩
  obtain ⟨hinvT, htaskT⟩ := owner_failed F hcm ocT e2 e3 hrun (Or.inr (Or.inr (Or.inr hstT)))
  obtain ⟨f, s'', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  have hpol : c.policy = .continue := policy_continue F.pol'
    (by rw [(Delivery.settleOwner_old hso).2.1]; exact mem_setCall_status hcm _) (Or.inr (Or.inr rfl))
  exact covers_settleOwner h hcm hrun hso rfl rfl rfl rfl rfl rfl h.covers.results h.covers.taskResults
    fail_runs fail_invocations (by rw [hpol]; rfl) (by rw [hpol]; rfl) fail_results fail_taskResults
    fail_deliveries fail_settled
    ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun h' => by simp [CallStatus.ended] at h'⟩ hinvT htaskT

theorem covers_lost {id : String} (h : StepCtx p env T s (.lost id) s') : Covers p T s' := by
  obtain ⟨-, -, c, hc, ⟨hrun, hf⟩ | ⟨hcan, ho⟩⟩ := Step.lost_inv h.accepted
  · have F := facts h
    obtain ⟨hcm, rfl⟩ := call?_eq_some hc
    obtain ⟨c₀, hc₀, hcase⟩ := h.conforms
    rw [Option.some.inj (hc₀.symm.trans hc)] at hcase
    -- A live call is lost only as its script says.
    obtain ⟨hfinal, hend⟩ : (env.behavior.script c.id).Final c ∧ (env.behavior.script c.id).ending = .lost := by
      rcases hcase with hcan | hl
      · rcases hrun with h' | h' <;> rw [h'] at hcan <;> cases hcan
      · exact hl
    obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
    obtain ⟨ccT, ocT⟩ := F.rcT.calls cT hcT
    have hcTeq : cT = { c with status := .lost } :=
      covered_call_eq ccT (F.satT.calls cT hcT) e1 e2 e3 e4 e5 e6 e7 e8 hend hfinal
    have hstT : cT.status = .lost := by rw [hcTeq]
    obtain ⟨hinvT, htaskT⟩ := owner_failed F hcm ocT e2 e3 hrun (Or.inr (Or.inl hstT))
    obtain ⟨f, s'', -, hso, rfl⟩ := failCall_eq_ok.mp hf
    have hpol : c.policy = .continue := policy_continue F.pol'
      (by rw [(Delivery.settleOwner_old hso).2.1]; exact mem_setCall_status hcm _) (Or.inr (Or.inl rfl))
    exact covers_settleOwner h hcm hrun hso rfl rfl rfl rfl rfl rfl h.covers.results h.covers.taskResults
      fail_runs fail_invocations (by rw [hpol]; rfl) (by rw [hpol]; rfl) fail_results fail_taskResults
      fail_deliveries fail_settled ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun _ => hcTeq⟩ hinvT htaskT
  · exact covers_cancelled h (call?_eq_some hc).1 hcan ho

theorem covers_terminated {id : String} (h : StepCtx p env T s (.terminated id) s') : Covers p T s' := by
  obtain ⟨-, -, c, hc, hcan, ho⟩ := Step.terminated_inv h.accepted
  exact covers_cancelled h (call?_eq_some hc).1 hcan ho

end CoversReports

end Suimon.Round3
