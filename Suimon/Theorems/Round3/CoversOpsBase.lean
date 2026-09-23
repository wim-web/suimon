import Suimon.Theorems.Round3.Covers
import Suimon.Theorems.Round3.ProgressInv
import Suimon.Theorems.Round3.CoversOpsInv

/-! Helpers for [22] Round3/CoversOps.lean — task F4: reading the complete run `T` of a step context.

`Covers` puts the runs, deliveries and executions of run 1 into `T`, so lookups by path, delivery key
and execution agree; a delivered Single connection resolves in `T` as in run 1 (it carries at most
one delivery); a failure policy that would stop contradicts the unstopped next state; and a task
result that run 1 is about to transform is already transformed in `T` with the behavior's answer. -/

namespace Suimon.Round3
namespace CoversOpsAux
open State

variable {p : Program} {env : Env} {s s' t T : State}

/-! ### Unstopped states -/

/-- The root run of a running state is open, so a state with its runs is not done. -/
theorem not_done_of_running (h : Reachable p s) (started : s.started = true) (running : s.status = .running)
    (hr : t.runs = s.runs) : ¬ Done t := by
  obtain ⟨r, hr', hc⟩ := root_open h started running
  intro hd
  have e : t.run? [] = s.run? [] := by simp [State.run?, hr]
  simp [Done, e, hr', hc] at hd

/-- A failure recorded under a stop policy stops the workflow, which an unstopped next state excludes. -/
theorem StepCtx.policy {op : Op} (h : StepCtx p env T s op s') {u : State} {f : Failure} {policy : Policy}
    (hs' : s' = u.fail f policy) (hu : u.runs = s.runs) (started : s.started = true)
    (running : s.status = .running) : policy = .continue := by
  cases policy
  · exfalso
    obtain ⟨tr, hrun⟩ := h.run
    rcases h.unstopped with hr | hd
    · rw [hs'] at hr
      simp at hr
    · exact not_done_of_running hrun.reachable started running (by rw [hs']; simp [hu]) hd
  · rfl

/-- The next state of an unstopped step context is unstopped before the step as well. -/
theorem StepCtx.unstopped₀ {op : Op} (h : StepCtx p env T s op s') : Unstopped s := by
  obtain ⟨tr, hrun⟩ := h.run
  exact unstopped_of_step hrun.reachable h.accepted h.unstopped

/-! ### Assembling `Covers` -/

/-- `Covers` of the next state from its records; the frozen footprints carry over when the step adds no
    settlement and completes no execution (`covers_footprint_step`). -/
theorem covers_mk {op : Op} (h : StepCtx p env T s op s')
    (runs : ∀ r ∈ s'.runs, ∃ r' ∈ T.runs, r'.path = r.path ∧ r'.workflow = r.workflow ∧ r'.input = r.input ∧
      r'.owner = r.owner ∧ r'.task = r.task)
    (invocations : ∀ i ∈ s'.invocations, ∃ i' ∈ T.invocations, i'.id = i.id ∧ i'.run = i.run ∧
      i'.placement = i.placement ∧ i'.trigger = i.trigger ∧ i'.input = i.input ∧ (i.status ≠ .active → i' = i))
    (calls : ∀ c ∈ s'.calls, ∃ c' ∈ T.calls, c'.id = c.id ∧ c'.owner = c.owner ∧ c'.task = c.task ∧
      c'.target = c.target ∧ c'.input = c.input ∧ c'.stream = c.stream ∧ c'.timeout = c.timeout ∧
      c'.policy = c.policy ∧ (c.status.ended = true → c' = c))
    (executions : ∀ e ∈ s'.executions, ∃ e' ∈ T.executions, e'.id = e.id ∧ e'.run = e.run ∧
      e'.placement = e.placement ∧ e'.input = e.input ∧ e'.tasks.map (·.name) = e.tasks.map (·.name) ∧
      (∀ t ∈ e.tasks, ∀ t' ∈ e'.tasks, t'.name = t.name →
        (t.status ≠ .pending → t'.input = t.input) ∧ (t.status.ended = true → t' = t)) ∧
      (e.complete = true → e' = e))
    (results : ∀ r ∈ s'.results, r ∈ T.results)
    (taskResults : ∀ r ∈ s'.taskResults, ∃ r' ∈ T.taskResults, r'.execution = r.execution ∧ r'.task = r.task ∧
      r'.index = r.index ∧ r'.value = r.value ∧ (r.output ≠ .pending → r' = r))
    (deliveries : ∀ d ∈ s'.deliveries, d ∈ T.deliveries)
    (hsettled : s'.settled = s.settled)
    (hcomplete : ∀ e ∈ s'.executions, e.complete = true → ∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.complete = true) :
    Covers p T s' := by
  have fp := covers_footprint_step h
  refine ⟨runs, invocations, calls, executions, results, taskResults, deliveries,
    fun x hx => h.covers.settled x (hsettled ▸ hx), fun x hx => fp.1 x (hsettled ▸ hx), fun e he hc r hr hre => ?_⟩
  obtain ⟨e₀, he₀, hid, hc₀⟩ := hcomplete e he hc
  exact fp.2 e₀ he₀ hc₀ r hr (hre.trans hid.symm)

/-! ### Lookups in `T` -/

theorem covers_run (cov : Covers p T s) (wkT : T.WellKeyed) {path : Path} {r : Run} (hr : s.run? path = some r) :
    ∃ rT, T.run? path = some rT ∧ rT.workflow = r.workflow ∧ rT.input = r.input ∧ rT.owner = r.owner ∧
      rT.task = r.task := by
  obtain ⟨hrm, rfl⟩ := State.run?_eq_some hr
  obtain ⟨rT, hrT, a1, a2, a3, a4, a5⟩ := cov.runs r hrm
  exact ⟨rT, a1 ▸ wkT.run?_of_mem hrT, a2, a3, a4, a5⟩

theorem covers_workflow? (cov : Covers p T s) (wkT : T.WellKeyed) {path : Path} {w : Workflow}
    (hw : s.workflow? p path = some w) : T.workflow? p path = some w := by
  obtain ⟨r, hr, hwf⟩ := Delivery.workflow?_iff.mp hw
  obtain ⟨rT, hrT, a2, -⟩ := covers_run cov wkT hr
  exact Delivery.workflow?_iff.mpr ⟨rT, hrT, a2 ▸ hwf⟩

theorem covers_concurrencyOf (cov : Covers p T s) (wkT : T.WellKeyed) {e e' : Execution} (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) {cc : Concurrency} (h : s.concurrencyOf p e = .ok cc) :
    T.concurrencyOf p e' = .ok cc := by
  obtain ⟨w, pl, hw, hpl', hctl⟩ := Delivery.concurrencyOf_iff.mp h
  exact Delivery.concurrencyOf_iff.mpr ⟨w, pl, hrun ▸ covers_workflow? cov wkT hw, hpl ▸ hpl', hctl⟩

theorem covers_taskSpec (cov : Covers p T s) (wkT : T.WellKeyed) {e e' : Execution} (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) {name : String} {spec : TaskSpec} (h : s.taskSpec p e name = .ok spec) :
    T.taskSpec p e' name = .ok spec := by
  obtain ⟨cc, hcc, hf⟩ := State.taskSpec_eq_ok.mp h
  exact State.taskSpec_eq_ok.mpr ⟨cc, covers_concurrencyOf cov wkT hrun hpl hcc, hf⟩

/-- The execution of `T` under the identity of an execution of run 1. -/
theorem covers_execution (cov : Covers p T s) (wkT : T.WellKeyed) {e : Execution} (he : e ∈ s.executions) :
    ∃ e' ∈ T.executions, T.execution? e.id = some e' ∧ e'.id = e.id ∧ e'.run = e.run ∧ e'.placement = e.placement ∧
      e'.tasks.map (·.name) = e.tasks.map (·.name) ∧
      (∀ t ∈ e.tasks, ∀ t' ∈ e'.tasks, t'.name = t.name →
        (t.status ≠ .pending → t'.input = t.input) ∧ (t.status.ended = true → t' = t)) := by
  obtain ⟨e', he', a1, a2, a3, -, a5, a6, -⟩ := cov.executions e he
  exact ⟨e', he', a1 ▸ wkT.execution?_of_mem he', a1, a2, a3, a5, a6⟩

/-- The task of an execution of `T` named like a task of the execution of run 1. -/
theorem task_of_names {e e' : Execution} (hnames : e'.tasks.map (·.name) = e.tasks.map (·.name)) {ts : TaskState}
    (hts : ts ∈ e.tasks) : ∃ t' ∈ e'.tasks, t'.name = ts.name := by
  have : ts.name ∈ e'.tasks.map (·.name) := by rw [hnames]; exact List.mem_map.mpr ⟨ts, hts, rfl⟩
  obtain ⟨t', ht', hn⟩ := List.mem_map.mp this
  exact ⟨t', ht', hn⟩

/-! ### Single connections -/

/-- A connection whose source has a Single output carries at most one delivery (Round 2 `Deliv.one`,
    `DeliveryEligible` and unique delivery keys). -/
theorem single_delivery (h : Reachable p s) {path : Path} {w : Workflow} {j : Nat} {c : Connection}
    (hw : s.workflow? p path = some w) (hc : w.connections[j]? = some c) (hk : w.outputKind? p c.source = some .single)
    {d d' : Delivery} (hd : d ∈ s.deliveriesOn path j) (hd' : d' ∈ s.deliveriesOn path j) : d = d' := by
  have inv := Delivery.Reachable.inv h
  have dl := Delivery.Reachable.deliv h
  obtain ⟨hdm, hdr, hdj⟩ := Delivery.mem_deliveriesOn.mp hd
  obtain ⟨hdm', hdr', hdj'⟩ := Delivery.mem_deliveriesOn.mp hd'
  obtain ⟨w₁, c₁, r, hw₁, hc₁, hr, hrid, hrr, hrp, -⟩ := inv.own.deliveries d hdm
  obtain ⟨w₂, c₂, r', hw₂, hc₂, hr', hrid', hrr', hrp', -⟩ := inv.own.deliveries d' hdm'
  rw [hdr, hw] at hw₁
  cases hw₁
  rw [hdr', hw] at hw₂
  cases hw₂
  rw [hdj, hc] at hc₁
  cases hc₁
  rw [hdj', hc] at hc₂
  cases hc₂
  have hid := dl.one w path c.source hw hk r hr r' hr' (hrr.trans hdr) hrp (hrr'.trans hdr') hrp'
  have hkey : (d.run, d.connection, d.source) = (d'.run, d'.connection, d'.source) := by
    rw [hdr, hdj, hdr', hdj', ← hrid, ← hrid', hid]
  exact Limit.eq_of_key inv.wk.deliveries hdm hdm' hkey

/-- A delivered Single connection resolves in `T` as in run 1: `T` has the same delivery and no other. -/
theorem covers_resolveSingle (cov : Covers p T s) (hT : Reachable p T) {path : Path} {w : Workflow} {j : Nat}
    {c : Connection} (hwT : T.workflow? p path = some w) (hc : w.connections[j]? = some c)
    (hk : w.outputKind? p c.source = some .single) {src : ResultId} {inp : Option Value}
    (h : s.resolveSingle path j c = .value src inp) : T.resolveSingle path j c = .value src inp := by
  obtain ⟨d, rest, hd, hsrc, hout⟩ := Delivery.resolveSingle_value_iff.mp h
  have hds : d ∈ s.deliveriesOn path j := by rw [hd]; exact List.mem_cons_self
  obtain ⟨hdm, hdr, hdj⟩ := Delivery.mem_deliveriesOn.mp hds
  have hdT : d ∈ T.deliveriesOn path j := Delivery.mem_deliveriesOn.mpr ⟨cov.deliveries d hdm, hdr, hdj⟩
  rcases hTd : T.deliveriesOn path j with _ | ⟨d', rest'⟩
  · rw [hTd] at hdT
    cases hdT
  · have e : d' = d := single_delivery hT hwT hc hk (by rw [hTd]; exact List.mem_cons_self) hdT
    subst e
    exact Delivery.resolveSingle_value_iff.mpr ⟨d', rest', hTd, hsrc, hout⟩

/-- An invocation input that run 1 computed, `T` computes the same way. -/
theorem covers_invocationInput (cov : Covers p T s) (hT : Reachable p T) {r rT : Run} {w : Workflow}
    {name : String} {trigger : Option ResultId} {input : Option Value} (hpath : rT.path = r.path)
    (hin : rT.input = r.input) (hwT : T.workflow? p r.path = some w)
    (h : Step.invocationInput p s r w name trigger = .ok input) :
    Step.invocationInput p T rT w name trigger = .ok input := by
  have wkT := hT.wellKeyed
  rcases Step.invocationInput_inv h with ⟨hsh, rfl, rfl⟩ | ⟨hsh, rfl, rfl⟩ | ⟨j, c, src, hsh, rfl, hres⟩ |
      ⟨j, c, src, d, hsh, rfl, hd, hout⟩
  · simp [Step.invocationInput, hsh]
  · simp [Step.invocationInput, hsh, hin]
  · obtain ⟨-, hc, -, hk⟩ := Delivery.shape?_single hsh
    have hresT := covers_resolveSingle cov hT hwT hc hk hres
    simp [Step.invocationInput, hsh, hpath, hresT]
  · obtain ⟨hdm, hdr, hdj, hds⟩ := State.delivery?_eq_some hd
    have hdT : T.delivery? r.path j src = some d := by
      rw [← hdr, ← hdj, ← hds]
      exact wkT.delivery?_of_mem (cov.deliveries d hdm)
    rcases hout with ⟨v, hv, rfl⟩ | ⟨hv, rfl⟩ <;> simp [Step.invocationInput, hsh, hpath, hdT, hv]

/-! ### Deliveries -/

/-- For an eligible delivery that run 1 is about to record, `T` recorded one under the same key
    (`Saturated.delivered`), holding what the transform gave (`DeliveryConform`). -/
theorem covers_delivery {op : Op} (h : StepCtx p env T s op s') {path : Path} {j : Nat} {source : ResultId}
    {w : Workflow} {c : Connection} (hdt : Step.deliveryTarget p s path j source = .ok (w, c)) :
    ∃ dT ∈ T.deliveries, dT.run = path ∧ dT.connection = j ∧ dT.source = source ∧
      match c.transform with
      | .discard => dT.outcome = .trigger
      | .declared _ =>
        match env.behavior.transform path j source with
        | some v => dT.outcome = .value v
        | none => dT.outcome = .failed := by
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have cov := h.covers
  obtain ⟨hw, hc, ⟨r, hr, hrr, hrp, harm⟩, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
  obtain ⟨hrm, hrid⟩ := State.result?_eq_some hr
  have hwT := covers_workflow? cov wkT hw
  have hdel := (saturated h.valid hT h.done).delivered r (cov.results r hrm) w (hrr ▸ hwT) j c hc hrp.symm
    (harm.imp id Eq.symm)
  obtain ⟨dT, hdT⟩ := Option.isSome_iff_exists.mp hdel
  obtain ⟨hdTm, hdTr, hdTj, hdTs⟩ := State.delivery?_eq_some hdT
  obtain ⟨w', c', hw', hc', hconf⟩ := deliveryConform h₂ dT hdTm
  rw [hdTr, hrr, hwT] at hw'
  cases hw'
  rw [hdTj, hc] at hc'
  cases hc'
  refine ⟨dT, hdTm, hdTr.trans hrr, hdTj, hdTs.trans hrid, ?_⟩
  rw [hdTr, hrr, hdTj, hdTs, hrid] at hconf
  exact hconf

/-! ### Tasks and task results -/

/-- The executions after a task of an open execution changed are covered when `T`'s copy of the task
    agrees with the new one. -/
theorem covers_setTask (cov : Covers p T s) {e : Execution} (he : e ∈ s.executions) (hopen : e.complete = false)
    {ts' : TaskState}
    (hnew : ∀ e' ∈ T.executions, e'.id = e.id → e'.run = e.run → e'.placement = e.placement →
      (∀ t ∈ e.tasks, ∀ t' ∈ e'.tasks, t'.name = t.name →
        (t.status ≠ .pending → t'.input = t.input) ∧ (t.status.ended = true → t' = t)) →
      ∀ t' ∈ e'.tasks, t'.name = ts'.name →
        (ts'.status ≠ .pending → t'.input = ts'.input) ∧ (ts'.status.ended = true → t' = ts')) :
    ∀ x ∈ (s.setTask e ts').executions, ∃ e' ∈ T.executions, e'.id = x.id ∧ e'.run = x.run ∧
      e'.placement = x.placement ∧ e'.input = x.input ∧ e'.tasks.map (·.name) = x.tasks.map (·.name) ∧
      (∀ t ∈ x.tasks, ∀ t' ∈ e'.tasks, t'.name = t.name →
        (t.status ≠ .pending → t'.input = t.input) ∧ (t.status.ended = true → t' = t)) ∧
      (x.complete = true → e' = x) := by
  intro x hx
  rcases State.mem_setTask_executions hx with rfl | hx
  · obtain ⟨e', he', a1, a2, a3, a4, a5, a6, -⟩ := cov.executions e he
    refine ⟨e', he', a1, a2, a3, a4, by rw [a5, Delivery.Kept.withTask_names], fun t ht t' ht' hn => ?_,
      fun hc => ?_⟩
    · rcases Delivery.mem_withTask ht with rfl | ⟨ht, -⟩
      · exact hnew e' he' a1 a2 a3 a6 t' ht' hn
      · exact a6 t ht t' ht' hn
    · rw [withTask_complete, hopen] at hc
      cases hc
  · exact cov.executions x hx

/-- A task update completes no execution. -/
theorem complete_setTask {e : Execution} (he : e ∈ s.executions) {ts' : TaskState} :
    ∀ x ∈ (s.setTask e ts').executions, x.complete = true → ∃ e₀ ∈ s.executions, e₀.id = x.id ∧ e₀.complete = true := by
  intro x hx hc
  rcases State.mem_setTask_executions hx with rfl | hx
  · exact ⟨e, he, rfl, hc⟩
  · exact ⟨x, hx, rfl, hc⟩

/-- The task results after a transform are covered when `T` holds the transformed result. -/
theorem covers_setTaskResult (cov : Covers p T s) {r : TaskResult} {o : TaskOutput}
    (hT : { r with output := o } ∈ T.taskResults) :
    ∀ x ∈ (s.setTaskResult { r with output := o }).taskResults, ∃ x' ∈ T.taskResults, x'.execution = x.execution ∧
      x'.task = x.task ∧ x'.index = x.index ∧ x'.value = x.value ∧ (x.output ≠ .pending → x' = x) := by
  intro x hx
  rcases State.mem_setTaskResult_taskResults hx with rfl | hx
  · exact ⟨_, hT, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · exact cov.taskResults x hx

/-- An execution with a task that has not ended is open: a completed execution ended all its tasks. -/
theorem open_of_task (h : Reachable p s) {e : Execution} (he : e ∈ s.executions) {ts : TaskState}
    (hts : ts ∈ e.tasks) (hlive : ts.status.ended = false) : e.complete = false := by
  cases hc : e.complete
  · rfl
  · rw [Saturated.reachable_tasks_ended h e he hc ts hts] at hlive
    cases hlive

/-- The copy in `T` of a task result that run 1 is about to transform was transformed in `T` (`Saturated`),
    with the behavior's answer (`TaskConform` of `T`). -/
theorem covers_taskResult {op : Op} (h : StepCtx p env T s op s') {eid name : String} {index : Nat}
    {e : Execution} {spec : TaskSpec} {r : TaskResult} (he : s.execution? eid = some e)
    (hspec : s.taskSpec p e name = .ok spec) (hout : spec.output.isSome = true)
    (hr : s.taskResults.find? (fun x => x.execution == eid && x.task == name && x.index == index) = some r) :
    ∃ o, { r with output := o } ∈ T.taskResults ∧ o ≠ .pending ∧
      (∀ v, o = .value v → env.behavior.taskOutput eid name index = some v) ∧
      (o = .failed → env.behavior.taskOutput eid name index = none) := by
  obtain ⟨tr₂, h₂⟩ := h.other
  have hT := h₂.reachable
  have wkT := hT.wellKeyed
  have cov := h.covers
  have hk : r.execution = eid ∧ r.task = name ∧ r.index = index := by
    simpa [and_assoc] using List.find?_some hr
  obtain ⟨hem, heid⟩ := State.execution?_eq_some he
  obtain ⟨rT, hrTm, a1, a2, a3, a4, -⟩ := cov.taskResults r (List.mem_of_find?_eq_some hr)
  obtain ⟨eT, heTm, -, heTid, heTrun, heTpl, -⟩ := covers_execution cov wkT hem
  obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec
  have hccT := covers_concurrencyOf cov wkT heTrun heTpl hcc
  have hnp : rT.output ≠ .pending := by
    refine (saturated h.valid hT h.done).outputs eT heTm cc hccT rT hrTm (by rw [a1, hk.1, heTid, heid]) ?_
    refine ⟨spec, List.mem_of_find?_eq_some hfind, ?_, hout⟩
    rw [a2, hk.2.1]
    simpa using List.find?_some hfind
  have hrT : rT = { r with output := rT.output } := by
    obtain ⟨x1, x2, x3, x4, x5⟩ := rT
    simp only at a1 a2 a3 a4 ⊢
    rw [a1, a2, a3, a4]
  obtain ⟨hv, hf⟩ := (taskConform h.valid h₂ (Or.inr h.done)).output rT hrTm
  rw [a1, a2, a3, hk.1, hk.2.1, hk.2.2] at hv hf
  exact ⟨rT.output, hrT ▸ hrTm, hnp, hv, hf⟩

end CoversOpsAux
end Suimon.Round3
