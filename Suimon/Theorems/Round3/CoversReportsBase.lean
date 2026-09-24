import Suimon.Theorems.Round3.Covers
import Suimon.Theorems.Round3.CoversReportsArm

namespace Suimon.Round3.CoversReportsAux
open State

/-! ## Helpers for [23] Round3/CoversReports.lean — task F5

A report ends or advances one call of run 1. The same call exists in the final state `T` of the complete
run 2 (`Covers`), where it ended (`Saturated`), and `CallConform` in both runs pins its ending to the
script. So the call, the results it reported and its owner agree with `T`. -/

section Base
variable {p : Definition} {env : Env} {T s s' : State}

/-! ### How a script ends a call -/

/-- The final status a script's ending gives a call. -/
def EndsAs (sc : Script) : CallStatus → Prop
  | .returned => (∃ v, sc.ending = .returned v) ∨ (∃ a, sc.ending = .judged a) ∨ sc.ending = .ended
  | .failed => sc.ending = .failed
  | .lost => sc.ending = .lost
  | .cancelled => ∃ el, sc.ending = .timedOut el
  | _ => False

theorem endsAs_unique {sc : Script} {st₁ st₂ : CallStatus} (h₁ : EndsAs sc st₁) (h₂ : EndsAs sc st₂) :
    st₁ = st₂ := by
  cases hE : sc.ending <;> cases st₁ <;> cases st₂ <;> simp_all [EndsAs]

/-- An ended call of a conforming unstopped run ended as its script says, after all its elements. -/
theorem endsAs_of_conform {c : Call} (h : CallConform env s c) (hend : c.status.ended = true) :
    EndsAs (env.behavior.script c.id) c.status ∧ (env.behavior.script c.id).Final c := by
  cases hst : c.status with
  | running | fetching | cancelling => simp [hst, CallStatus.ended] at hend
  | returned =>
    obtain ⟨hf, h'⟩ := h.returned hst
    refine ⟨?_, hf⟩
    rcases h' with ⟨-, ⟨v, hv⟩ | ⟨a, ha⟩⟩ | ⟨-, he⟩
    · exact Or.inl ⟨v, hv⟩
    · exact Or.inr (Or.inl ⟨a, ha⟩)
    · exact Or.inr (Or.inr he)
  | failed => exact ⟨(h.failed hst).2, (h.failed hst).1⟩
  | lost => exact ⟨(h.lost hst).2, (h.lost hst).1⟩
  | cancelled =>
    obtain ⟨hf, el, he⟩ := h.cancelled (Or.inr hst)
    exact ⟨⟨el, he⟩, hf⟩

/-- The status of an ended call of `T` is the one its script gives. -/
theorem covered_status {c cT : Call} {st : CallStatus} (hT : CallConform env T cT)
    (hendT : cT.status.ended = true) (hid : cT.id = c.id) (hends : EndsAs (env.behavior.script c.id) st) :
    cT.status = st := by
  have h := (endsAs_of_conform hT hendT).1
  rw [hid] at h
  exact endsAs_unique h hends

/-- An ended call of `T` with the fixed fields of `c` and the status its script gives is `c` with that
    status, once `c` reported all its elements. -/
theorem covered_call_eq {c cT : Call} {st : CallStatus} (hT : CallConform env T cT)
    (hendT : cT.status.ended = true) (hid : cT.id = c.id) (howner : cT.owner = c.owner)
    (htask : cT.task = c.task) (htarget : cT.target = c.target) (hinput : cT.input = c.input)
    (hstream : cT.stream = c.stream) (htimeout : cT.timeout = c.timeout) (hpolicy : cT.policy = c.policy)
    (hends : EndsAs (env.behavior.script c.id) st) (hfinal : (env.behavior.script c.id).Final c) :
    cT = { c with status := st } := by
  obtain ⟨hE, hF⟩ := endsAs_of_conform hT hendT
  rw [hid] at hE hF
  have hst : cT.status = st := endsAs_unique hE hends
  unfold Script.Final at hF hfinal
  have hy : cT.yields = c.yields := hF.trans hfinal.symm
  cases cT
  simp only at hid howner htask htarget hinput hstream htimeout hpolicy hst hy
  subst hid howner htask htarget hinput hstream htimeout hpolicy hst hy
  rfl

/-! ### Owner statuses -/

theorem ownerConform_none {c : Call} (h : OwnerConform s c) (htask : c.task = none) :
    (c.status = .returned → ∃ i, s.invocation? c.owner = some i ∧ i.status = .succeeded) ∧
    (c.status = .failed ∨ c.status = .lost ∨ c.status = .cancelling ∨ c.status = .cancelled →
      ∃ i, s.invocation? c.owner = some i ∧ i.status = .failed) := by
  unfold OwnerConform at h
  rw [htask] at h
  exact h

theorem ownerConform_some {c : Call} {name : String} (h : OwnerConform s c) (htask : c.task = some name) :
    (c.status = .returned → ∃ e ts, s.execution? c.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
      ts.status = .succeeded) ∧
    (c.status = .failed ∨ c.status = .lost ∨ c.status = .cancelling ∨ c.status = .cancelled →
      ∃ e ts, s.execution? c.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧ ts.status = .failed) := by
  unfold OwnerConform at h
  rw [htask] at h
  exact h

/-- The owner of a running or fetching call is active, so it has no arm. -/
theorem running_owner_arm (act : Settle.Active p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls)
    (htask : c.task = none) (hrun : c.status = .running ∨ c.status = .fetching) {i : Invocation}
    (hi : s.invocation? c.owner = some i) : i.arm = none := by
  obtain ⟨i', hi', hid', hact⟩ := act.callActive c hc htask hrun
  obtain ⟨him, hiid⟩ := invocation?_eq_some hi
  obtain rfl : i = i' := wk.invocation_eq_of_id him hi' (hiid.trans hid'.symm)
  exact act.activeArm i hi' hact

/-- The owner of a call that is not a judge's has no arm: only branches record one. -/
theorem nonjudge_owner_arm (own : Delivery.Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls)
    (htask : c.task = none) (hnj : ∀ j, c.target = .judge j → c.stream = false → False) {i : Invocation}
    (hi : s.invocation? c.owner = some i) : i.arm = none := by
  rcases own.calls c hc with ⟨-, -, i', hi', hid', w, pl, hw, hpl, hcase⟩ | ⟨name, htask', -⟩
  · obtain ⟨him, hiid⟩ := invocation?_eq_some hi
    obtain rfl : i = i' := wk.invocation_eq_of_id him hi' (hiid.trans hid'.symm)
    refine Delivery.arm_none own him ⟨w, hw, hpl⟩ fun j arms hb => ?_
    rcases hcase with ⟨f, d, hctl, -, -, -⟩ | ⟨j', arms', hctl, htgt, hstr⟩
    · rw [hctl] at hb
      cases hb
    · exact hnj j' htgt hstr
  · rw [htask] at htask'
    cases htask'

/-! ### What both runs give at a report step -/

/-- The facts a report step of run 1 gives about both runs. -/
structure Facts (p : Definition) (env : Env) (T s s' : State) : Prop where
  reach : Reachable p s
  wk : s.WellKeyed
  act : Settle.Active p s
  rcS : RunConform p env s
  pol' : PolicyConform p s'
  wkT : T.WellKeyed
  rcT : RunConform p env T
  satT : Saturated p T
  ownT : Delivery.Own p T
  dynT : Delivery.Dyn p T
  armT : ArmSucceeded T
  cohT : ∀ e ∈ T.executions, ∀ x ∈ e.tasks, ∀ y ∈ e.tasks, x.name = y.name → x = y

theorem facts {op : Op} (h : StepCtx p env T s op s') : Facts p env T s s' := by
  obtain ⟨tr, hrun⟩ := h.run
  obtain ⟨trT, hrunT⟩ := h.other
  have hreach := hrun.reachable
  have hreachT := hrunT.reachable
  have hreach' : Reachable p s' := .step op hreach h.accepted
  have us : Unstopped s := unstopped_of_step hreach h.accepted h.unstopped
  have invT := Delivery.Reachable.inv hreachT
  exact {
    reach := hreach
    wk := hreach.wellKeyed
    act := (Settle.reachable hreach).2.1
    rcS := runConform h.valid hrun us
    pol' := policyConform hreach' h.unstopped
    wkT := hreachT.wellKeyed
    rcT := runConform h.valid hrunT (Or.inr h.done)
    satT := saturated h.valid hreachT h.done
    ownT := invT.own
    dynT := invT.dyn
    armT := Reachable.armSucceeded hreachT
    cohT := (Limit.reachable_inv hreachT).coherent }

/-! ### Assembling `Covers` -/

/-- The clause of `Covers.invocations` for one invocation. -/
def InvCovered (T : State) (i : Invocation) : Prop :=
  ∃ i' ∈ T.invocations, i'.id = i.id ∧ i'.run = i.run ∧ i'.placement = i.placement ∧ i'.trigger = i.trigger ∧
    i'.input = i.input ∧ (i.status ≠ .active → i' = i)

/-- The clause of `Covers.calls` for one call. -/
def CallCovered (T : State) (c : Call) : Prop :=
  ∃ c' ∈ T.calls, c'.id = c.id ∧ c'.owner = c.owner ∧ c'.task = c.task ∧ c'.target = c.target ∧
    c'.input = c.input ∧ c'.stream = c.stream ∧ c'.timeout = c.timeout ∧ c'.policy = c.policy ∧
    (c.status.ended = true → c' = c)

/-- The clause of `Covers.executions` for one execution. -/
def ExecCovered (T : State) (e : Execution) : Prop :=
  ∃ e' ∈ T.executions, e'.id = e.id ∧ e'.run = e.run ∧ e'.placement = e.placement ∧ e'.input = e.input ∧
    e'.tasks.map (·.name) = e.tasks.map (·.name) ∧
    (∀ t ∈ e.tasks, ∀ t' ∈ e'.tasks, t'.name = t.name →
      (t.status ≠ .pending → t'.input = t.input) ∧ (t.status.ended = true → t' = t)) ∧
    (e.complete = true → e' = e)

/-- The clause of `Covers.taskResults` for one task result. -/
def TaskResultCovered (T : State) (r : TaskResult) : Prop :=
  ∃ r' ∈ T.taskResults, r'.execution = r.execution ∧ r'.task = r.task ∧ r'.index = r.index ∧
    r'.value = r.value ∧ (r.output ≠ .pending → r' = r)

/-- `Covers p T s'` after a report: runs, deliveries and settlements are those of `s`, and the
    footprints carry over (`covers_footprint_step`); the changed records are given. -/
theorem covers_of_parts {op : Op} (h : StepCtx p env T s op s')
    (hruns : s'.runs = s.runs) (hdel : s'.deliveries = s.deliveries) (hset : s'.settled = s.settled)
    (hinv : ∀ i ∈ s'.invocations, InvCovered T i) (hcalls : ∀ c ∈ s'.calls, CallCovered T c)
    (hexec : ∀ e ∈ s'.executions, ExecCovered T e)
    (hback : ∀ e ∈ s'.executions, e.complete = true → ∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.complete = true)
    (hres : ∀ r ∈ s'.results, r ∈ T.results) (htr : ∀ r ∈ s'.taskResults, TaskResultCovered T r) :
    Covers p T s' := by
  obtain ⟨foot, exec⟩ := covers_footprint_step h
  refine ⟨?_, hinv, hcalls, hexec, hres, htr, ?_, ?_, ?_, ?_⟩
  · rw [hruns]
    exact h.covers.runs
  · rw [hdel]
    exact h.covers.deliveries
  · rw [hset]
    exact h.covers.settled
  · intro x hx
    rw [hset] at hx
    exact foot x hx
  · intro e he hc r hr hre
    obtain ⟨e₀, he₀, hid, hc₀⟩ := hback e he hc
    exact exec e₀ he₀ hc₀ r hr (hre.trans hid.symm)

theorem inv_replace {u : State} (cov : Covers p T s) (hu : u.invocations = s.invocations) {i' : Invocation}
    (hi' : InvCovered T i') : ∀ x ∈ (u.setInvocation i').invocations, InvCovered T x := by
  intro x hx
  rcases mem_setInvocation_invocations hx with rfl | hx
  · exact hi'
  · rw [hu] at hx
    exact cov.invocations x hx

theorem calls_replace {u : State} (cov : Covers p T s) (hu : u.calls = s.calls) {c' : Call}
    (hc' : CallCovered T c') : ∀ x ∈ (u.setCall c').calls, CallCovered T x := by
  intro x hx
  rcases mem_setCall_calls hx with rfl | hx
  · exact hc'
  · rw [hu] at hx
    exact cov.calls x hx

/-- The invocation of `T` under the identity of an invocation `i` of `s` is `i` with its status and arm. -/
theorem owner_covered (cov : Covers p T s) (wkT : T.WellKeyed) {i iT : Invocation} (hi : i ∈ s.invocations)
    (hT : T.invocation? i.id = some iT) : InvCovered T { i with status := iT.status, arm := iT.arm } := by
  obtain ⟨i', hi', h1, h2, h3, h4, h5, -⟩ := cov.invocations i hi
  obtain ⟨hTm, hTid⟩ := invocation?_eq_some hT
  obtain rfl : iT = i' := wkT.invocation_eq_of_id hTm hi' (hTid.trans h1.symm)
  refine ⟨iT, hTm, h1, h2, h3, h4, h5, fun _ => ?_⟩
  cases iT
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-- The execution of a task call's owner after `settleOwner`, when `T` has the task with the new status. -/
theorem task_covered (cov : Covers p T s) (wkT : T.WellKeyed)
    (cohT : ∀ e ∈ T.executions, ∀ x ∈ e.tasks, ∀ y ∈ e.tasks, x.name = y.name → x = y)
    {e eT : Execution} (he : e ∈ s.executions) (hec : e.complete = false) (hT : T.execution? e.id = some eT)
    {name : String} {ts tsT : TaskState} (hts : e.tasks.find? (·.name == name) = some ts)
    (hpend : ts.status ≠ .pending) (htsT : eT.tasks.find? (·.name == name) = some tsT) {st : TaskStatus}
    (hst : tsT.status = st) : ExecCovered T (withTask e { ts with status := st }) := by
  obtain ⟨e', he', h1, h2, h3, h4, h5, h6, -⟩ := cov.executions e he
  obtain ⟨heTm, heTid⟩ := execution?_eq_some hT
  obtain rfl : eT = e' := wkT.execution_eq_of_id heTm he' (heTid.trans h1.symm)
  have htsm : ts ∈ e.tasks := List.mem_of_find?_eq_some hts
  have htsn : ts.name = name := by simpa using List.find?_some hts
  have htsTm : tsT ∈ eT.tasks := List.mem_of_find?_eq_some htsT
  have htsTn : tsT.name = name := by simpa using List.find?_some htsT
  have hinput : tsT.input = ts.input := (h6 ts htsm tsT htsTm (htsTn.trans htsn.symm)).1 hpend
  refine ⟨eT, heTm, h1, h2, h3, h4, h5.trans (Delivery.Kept.withTask_names e _).symm, ?_, ?_⟩
  · intro t ht t' ht' hname
    rw [withTask_tasks] at ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    split
    · -- The task of the call: `T` has it with the new status and the same input.
      rename_i hxn
      have hn : t'.name = name := by
        rw [hname]
        split <;> first | exact htsn | (rename_i hne; exact absurd hxn hne)
      obtain rfl : t' = tsT := cohT eT heTm t' ht' tsT htsTm (hn.trans htsTn.symm)
      refine ⟨fun _ => hinput, fun _ => ?_⟩
      cases t'
      simp only at hinput hst htsTn
      subst hinput hst
      simp only [TaskState.mk.injEq, and_true]
      exact htsTn.trans htsn.symm
    · rename_i hxn
      have hn : t'.name = x.name := by
        rw [hname]
        split
        · rename_i h'
          exact absurd h' hxn
        · rfl
      exact h6 x hx t' ht' hn
  · intro hc
    rw [withTask_complete, hec] at hc
    cases hc

/-! ### Results of a covered call in `T` -/

theorem result_eq {r : Result} {id : ResultId} {run : Path} {placement producer : String} {arm : Option String}
    {value : Value} (h1 : r.id = id) (h2 : r.run = run) (h3 : r.placement = placement) (h4 : r.producer = producer)
    (h5 : r.arm = arm) (h6 : r.value = value) :
    r = { id, run, placement, producer, arm, value } := by
  cases r
  simp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- The result of index `k` of a call of an invocation, when the covering call of `T` reported it: it
    exists in `T` with the identity, run, placement and producer the step of run 1 gives it, and its value
    is fixed by the script. -/
theorem call_result {c cT : Call} {i : Invocation} (cov : Covers p T s) (wkT : T.WellKeyed)
    (hT : CallConform env T cT) (hid : cT.id = c.id) (howner : cT.owner = c.owner) (hstream : cT.stream = c.stream)
    (htask : cT.task = none) (hi : s.invocation? c.owner = some i) {k : Nat}
    (hk : if cT.stream then k < cT.yields else k = 0 ∧ cT.status = .returned) :
    ∃ r ∈ T.results, r.id = Key.callResult c.id k ∧ r.run = i.run ∧ r.placement = i.placement ∧
      r.producer = c.id ∧
      (c.stream = true → (env.behavior.script c.id).yields[k]? = some r.value ∧ r.arm = none) ∧
      (∀ v, c.stream = false → (env.behavior.script c.id).ending = .returned v → r.value = v ∧ r.arm = none) ∧
      (∀ a, c.stream = false → (env.behavior.script c.id).ending = .judged a →
        r.value = i.input.getD "" ∧ r.arm = some a) := by
  obtain ⟨r, hr, hrid⟩ := (hT.results k).mpr ⟨htask, hk⟩
  obtain ⟨hp, iT, hiT, h1, h2, h3, h4, h5⟩ := hT.values r hr k hrid
  obtain ⟨him, hiid⟩ := invocation?_eq_some hi
  obtain ⟨i', hi', a1, a2, a3, -, a5, -⟩ := cov.invocations i him
  obtain ⟨hiTm, hiTid⟩ := invocation?_eq_some hiT
  obtain rfl : iT = i' := wkT.invocation_eq_of_id hiTm hi' (by rw [hiTid, a1, hiid, howner])
  rw [hid] at hrid hp h3 h4 h5
  rw [hstream] at h3 h4 h5
  refine ⟨r, hr, hrid, h1.trans a2, h2.trans a3, hp, h3, h4, fun a hs he => ?_⟩
  rw [← a5]
  exact h5 a hs he

/-- The task result of index `k` of a task call, when the covering call of `T` reported it. -/
theorem call_taskResult {c cT : Call} (hT : CallConform env T cT) (hid : cT.id = c.id)
    (howner : cT.owner = c.owner) (hstream : cT.stream = c.stream) {name : String} (htask : cT.task = some name)
    {k : Nat} (hk : if cT.stream then k < cT.yields else k = 0 ∧ cT.status = .returned) :
    ∃ r ∈ T.taskResults, r.execution = c.owner ∧ r.task = name ∧ r.index = k ∧
      (c.stream = true → (env.behavior.script c.id).yields[k]? = some r.value) ∧
      (∀ v, c.stream = false → (env.behavior.script c.id).ending = .returned v → r.value = v) := by
  obtain ⟨r, hr, h1, h2, h3⟩ := (hT.taskResults name htask k).mpr hk
  obtain ⟨v1, v2⟩ := hT.taskValues name htask r hr h1 h2
  rw [hid, hstream] at v1 v2
  rw [h3] at v1
  exact ⟨r, hr, h1.trans howner, h2, h3, v1, v2⟩

/-! ### A report that settles the call's owner -/

theorem mem_setCall_status {c : Call} (hc : c ∈ s.calls) (st : CallStatus) :
    { c with status := st } ∈ (s.setCall { c with status := st }).calls := by
  rw [setCall_calls]
  exact List.mem_map.mpr ⟨c, hc, by simp⟩

/-- A call of an invocation has the invocation's identity. -/
theorem call_id_owner (own : Delivery.Own p s) {c : Call} (hc : c ∈ s.calls) (htask : c.task = none) :
    c.id = c.owner := by
  rcases own.calls c hc with ⟨-, h, -⟩ | ⟨name, h', -⟩
  · exact h
  · rw [htask] at h'
    cases h'

/-- A report that leaves a call that is not a judge's returned: `T`'s owner of the call succeeded, and an
    invocation owner has no arm in either run. -/
theorem owner_succeeded (F : Facts p env T s s') {c cT : Call} (hcm : c ∈ s.calls) (hcT : cT ∈ T.calls)
    (ocT : OwnerConform T cT) (howner : cT.owner = c.owner) (htask : cT.task = c.task)
    (htarget : cT.target = c.target) (hstream : cT.stream = c.stream)
    (hrun : c.status = .running ∨ c.status = .fetching) (hstT : cT.status = .returned)
    (hnj : ∀ j, c.target = .judge j → c.stream = false → False) :
    (c.task = none → ∀ i, s.invocation? c.owner = some i →
      ∃ iT, T.invocation? c.owner = some iT ∧ iT.status = .succeeded ∧ iT.arm = i.arm) ∧
    (∀ name, c.task = some name → ∃ eT tsT, T.execution? c.owner = some eT ∧
      eT.tasks.find? (·.name == name) = some tsT ∧ tsT.status = .succeeded) := by
  refine ⟨fun htc i hi => ?_, fun name htc => ?_⟩
  · obtain ⟨iT, hiT, hst⟩ := (ownerConform_none ocT (htask.trans htc)).1 hstT
    rw [howner] at hiT
    refine ⟨iT, hiT, hst, ?_⟩
    rw [running_owner_arm F.act F.wk hcm htc hrun hi]
    refine nonjudge_owner_arm F.ownT F.wkT hcT (htask.trans htc) (fun j hj hs => ?_) (by rw [howner]; exact hiT)
    rw [htarget] at hj
    rw [hstream] at hs
    exact hnj j hj hs
  · obtain ⟨eT, tsT, heT, htsT, hst⟩ := (ownerConform_some ocT (htask.trans htc)).1 hstT
    rw [howner] at heT
    exact ⟨eT, tsT, heT, htsT, hst⟩

/-- A report that fails the call (or times it out): `T`'s owner of the call failed, and an invocation
    owner has no arm in either run (`ArmSucceeded` in `T`). -/
theorem owner_failed (F : Facts p env T s s') {c cT : Call} (hcm : c ∈ s.calls)
    (ocT : OwnerConform T cT) (howner : cT.owner = c.owner) (htask : cT.task = c.task)
    (hrun : c.status = .running ∨ c.status = .fetching)
    (hstT : cT.status = .failed ∨ cT.status = .lost ∨ cT.status = .cancelling ∨ cT.status = .cancelled) :
    (c.task = none → ∀ i, s.invocation? c.owner = some i →
      ∃ iT, T.invocation? c.owner = some iT ∧ iT.status = .failed ∧ iT.arm = i.arm) ∧
    (∀ name, c.task = some name → ∃ eT tsT, T.execution? c.owner = some eT ∧
      eT.tasks.find? (·.name == name) = some tsT ∧ tsT.status = .failed) := by
  refine ⟨fun htc i hi => ?_, fun name htc => ?_⟩
  · obtain ⟨iT, hiT, hst⟩ := (ownerConform_none ocT (htask.trans htc)).2 hstT
    rw [howner] at hiT
    refine ⟨iT, hiT, hst, ?_⟩
    rw [running_owner_arm F.act F.wk hcm htc hrun hi]
    cases ha : iT.arm with
    | none => rfl
    | some a =>
      have h' := F.armT iT (invocation?_eq_some hiT).1 (by rw [ha]; simp)
      rw [hst] at h'
      cases h'
  · obtain ⟨eT, tsT, heT, htsT, hst⟩ := (ownerConform_some ocT (htask.trans htc)).2 hstT
    rw [howner] at heT
    exact ⟨eT, tsT, heT, htsT, hst⟩


/-- A policy that stopped the run would leave it stopping, but the run is unstopped: the failed call's
    policy is `continue`. -/
theorem policy_continue {u : State} {f : Failure} {c : Call} {cs : CallStatus}
    (pol : PolicyConform p (u.fail f c.policy)) (hmem : { c with status := cs } ∈ u.calls)
    (hcs : cs = .failed ∨ cs = .lost ∨ cs = .cancelling) : c.policy = .continue := by
  cases hp : c.policy with
  | «continue» => rfl
  | stop =>
    exfalso
    rw [hp] at pol
    have hm : { c with status := cs } ∈ (u.fail f .stop).calls := by
      rw [fail_stop, stop_calls]
      refine List.mem_map.mpr ⟨{ c with status := cs }, hmem, ?_⟩
      rcases hcs with rfl | rfl | rfl <;> simp [stopCall]
    have h2 : ({ c with status := cs } : Call).policy = .continue :=
      pol.calls _ hm (by rcases hcs with rfl | rfl | rfl <;> simp)
    have h3 : c.policy = .continue := h2
    rw [hp] at h3
    cases h3

/-- A report that sets the call's status and then settles its owner (`returned`, `ended`, `failed`,
    `timedOut`, `lost` of a live call). `u` is `s` with the result the report accepted, and `s'` has the
    records of `v`. `T` has the call with the new status (when it is final) and its owner with the new
    owner status and the same arm. -/
theorem covers_settleOwner {op : Op} (h : StepCtx p env T s op s') {c : Call} (hcm : c ∈ s.calls)
    (hrun : c.status = .running ∨ c.status = .fetching) {u v : State} {cs : CallStatus}
    {st : InvocationStatus} {tst : TaskStatus}
    (ho : (u.setCall { c with status := cs }).settleOwner c st tst = .ok v)
    (hur : u.runs = s.runs) (hui : u.invocations = s.invocations) (huc : u.calls = s.calls)
    (hue : u.executions = s.executions) (hud : u.deliveries = s.deliveries) (hus : u.settled = s.settled)
    (hres : ∀ r ∈ u.results, r ∈ T.results) (htr : ∀ r ∈ u.taskResults, TaskResultCovered T r)
    (hvr : s'.runs = v.runs) (hvi : s'.invocations = v.invocations) (hvc : s'.calls = v.calls)
    (hve : s'.executions = v.executions) (hvres : s'.results = v.results) (hvtr : s'.taskResults = v.taskResults)
    (hvd : s'.deliveries = v.deliveries) (hvs : s'.settled = v.settled)
    (hcall : CallCovered T { c with status := cs })
    (hinvT : c.task = none → ∀ i, s.invocation? c.owner = some i →
      ∃ iT, T.invocation? c.owner = some iT ∧ iT.status = st ∧ iT.arm = i.arm)
    (htaskT : ∀ name, c.task = some name →
      ∃ eT tsT, T.execution? c.owner = some eT ∧ eT.tasks.find? (·.name == name) = some tsT ∧ tsT.status = tst) :
    Covers p T s' := by
  have F := facts h
  obtain ⟨-, hvc', hvr', -, hvtr', hvres', hvd', hvs'⟩ := Delivery.settleOwner_old ho
  have hr' : s'.runs = s.runs := by rw [hvr, hvr', setCall_runs, hur]
  have hd' : s'.deliveries = s.deliveries := by rw [hvd, hvd', setCall_deliveries, hud]
  have hs' : s'.settled = s.settled := by rw [hvs, hvs', setCall_settled, hus]
  have hc' : ∀ x ∈ s'.calls, CallCovered T x := by
    rw [hvc, hvc']
    exact calls_replace h.covers huc hcall
  have hres' : ∀ r ∈ s'.results, r ∈ T.results := by
    rw [hvres, hvres', setCall_results]
    exact hres
  have htr' : ∀ r ∈ s'.taskResults, TaskResultCovered T r := by
    rw [hvtr, hvtr', setCall_taskResults]
    exact htr
  rcases settleOwner_eq_ok.mp ho with ⟨htask, i, hi, rfl⟩ | ⟨name, e, ts, htask, he, hts, rfl⟩
  · -- The owner is an invocation.
    have hi' : s.invocation? c.owner = some i := by
      unfold State.invocation? at hi ⊢
      rw [setCall_invocations, hui] at hi
      exact hi
    obtain ⟨iT, hiT, hst, harm⟩ := hinvT htask i hi'
    obtain ⟨him, hiid⟩ := invocation?_eq_some hi'
    rw [← hiid] at hiT
    have hcov := owner_covered h.covers F.wkT him hiT
    rw [hst, harm] at hcov
    refine covers_of_parts h hr' hd' hs' ?_ hc' ?_ ?_ hres' htr'
    · rw [hvi]
      exact inv_replace h.covers (by rw [setCall_invocations, hui]) hcov
    · rw [hve, setInvocation_executions, setCall_executions, hue]
      exact h.covers.executions
    · rw [hve, setInvocation_executions, setCall_executions, hue]
      exact fun e he hc => ⟨e, he, rfl, hc⟩
  · -- The owner is a task of an execution, active while its call runs.
    have he' : s.execution? c.owner = some e := by
      unfold State.execution? at he ⊢
      rw [setCall_executions, hue] at he
      exact he
    obtain ⟨hem, heid⟩ := execution?_eq_some he'
    obtain ⟨e₁, he₁, he₁id, he₁c, ts₁, hts₁, hact⟩ := F.act.taskCallActive c hcm name htask hrun
    obtain rfl : e₁ = e := F.wk.execution_eq_of_id he₁ hem (he₁id.trans heid.symm)
    rw [hts] at hts₁
    obtain rfl : ts₁ = ts := (Option.some.inj hts₁).symm
    obtain ⟨eT, tsT, heT, htsT, hst⟩ := htaskT name htask
    rw [← heid] at heT
    have hcov := task_covered h.covers F.wkT F.cohT hem he₁c heT hts (by rw [hact]; simp) htsT hst
    refine covers_of_parts h hr' hd' hs' ?_ hc' ?_ ?_ hres' htr'
    · rw [hvi, setTask_invocations, setCall_invocations, hui]
      exact h.covers.invocations
    · rw [hve]
      intro x hx
      rcases mem_setTask_executions hx with rfl | hx
      · exact hcov
      · rw [setCall_executions, hue] at hx
        exact h.covers.executions x hx
    · rw [hve]
      intro x hx hxc
      rcases mem_setTask_executions hx with rfl | hx
      · rw [withTask_complete, he₁c] at hxc
        cases hxc
      · rw [setCall_executions, hue] at hx
        exact ⟨x, hx, rfl, hxc⟩

/-! ### A cancelling call terminates -/

/-- A cancelling call terminates (`lost` or `terminated`). Without a stop it is cancelling because it
    timed out, which already failed its owner, so `cancelOwner` changes nothing; and `T`'s call was
    cancelled as well, its script ending in that timeout. -/
theorem covers_cancelled {op : Op} (h : StepCtx p env T s op s') {c : Call} (hcm : c ∈ s.calls)
    (hcan : c.status = .cancelling) (ho : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok s') :
    Covers p T s' := by
  have F := facts h
  obtain ⟨ccS, ocS⟩ := F.rcS.calls c hcm
  obtain ⟨hfinal, el, hend⟩ := ccS.cancelled (Or.inl hcan)
  have hfail : c.status = .failed ∨ c.status = .lost ∨ c.status = .cancelling ∨ c.status = .cancelled :=
    Or.inr (Or.inr (Or.inl hcan))
  have hs' : s' = s.setCall { c with status := .cancelled } := by
    rcases cancelOwner_eq_ok.mp ho with ⟨htask, i, hi, rfl⟩ | ⟨name, e, ts, htask, he, hts, rfl⟩
    · obtain ⟨i', hi', hst⟩ := (ownerConform_none ocS htask).2 hfail
      have hii : i = i' := Option.some.inj (hi.symm.trans hi')
      rw [hii]
      simp [hst]
    · obtain ⟨e', ts', he', hts', hst⟩ := (ownerConform_some ocS htask).2 hfail
      have hee : e = e' := Option.some.inj (he.symm.trans he')
      rw [← hee, hts] at hts'
      rw [Option.some.inj hts']
      simp [hst]
  subst hs'
  obtain ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h.covers.calls c hcm
  obtain ⟨ccT, -⟩ := F.rcT.calls cT hcT
  have hcTeq : cT = { c with status := .cancelled } :=
    covered_call_eq ccT (F.satT.calls cT hcT) e1 e2 e3 e4 e5 e6 e7 e8 ⟨el, hend⟩ hfinal
  exact covers_of_parts h rfl rfl rfl h.covers.invocations
    (calls_replace h.covers rfl ⟨cT, hcT, e1, e2, e3, e4, e5, e6, e7, e8, fun _ => hcTeq⟩)
    h.covers.executions (fun e he hc => ⟨e, he, rfl, hc⟩) h.covers.results h.covers.taskResults

end Base

end Suimon.Round3.CoversReportsAux
