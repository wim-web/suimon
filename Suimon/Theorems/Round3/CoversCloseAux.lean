import Suimon.Theorems.Round3.Covers
import Suimon.Theorems.Round3.ProgressInv
import Suimon.Theorems.Round3.ProgressCalmTaskRun
import Suimon.Theorems.Round3.CoversCloseOrigin

/-! Helpers for [24] Round3/CoversClose.lean — task F6: lookups that `Covers` carries from run 1 to
the complete run 2, static facts about the bodies of sub-workflow calls and workflow tasks (their
designated output is an endpoint, hence Single), and what a Single connection delivers. -/

namespace Suimon.Round3
open State

namespace CoversCloseAux

variable {p : Definition} {s t T : State}

/-! ### Lookups carried by `Covers` -/

/-- The workflow of a run is a workflow of the definition. -/
theorem workflow_mem {path : Path} {w : Workflow} (hw : s.workflow? p path = some w) : w ∈ p.workflows := by
  obtain ⟨_, -, hwf⟩ := Routing.workflow?_eq_some.mp hw
  exact (Definition.workflow?_eq_some hwf).1

/-- A run of `s` runs the same workflow in `T`. -/
theorem covers_workflow? (cov : Covers p T s) (wkT : T.WellKeyed) {path : Path} {w : Workflow}
    (h : s.workflow? p path = some w) : T.workflow? p path = some w := by
  obtain ⟨r, hr, hw⟩ := Delivery.workflow?_iff.mp h
  obtain ⟨hrm, hrp⟩ := State.run?_eq_some hr
  obtain ⟨r', hr', h1, h2, -⟩ := cov.runs r hrm
  exact Delivery.workflow?_iff.mpr ⟨r', by rw [← hrp, ← h1]; exact wkT.run?_of_mem hr', by rw [h2]; exact hw⟩

/-- The concurrency of an execution depends only on the workflow of its run. -/
theorem concurrencyOf_of_workflow? {u v : State} {e e' : Execution} {path : Path} {w : Workflow} {cc : Concurrency}
    (hrun : e.run = path) (hrun' : e'.run = path) (hpl : e'.placement = e.placement)
    (hu : u.workflow? p path = some w) (hv : v.workflow? p path = some w) (h : u.concurrencyOf p e = .ok cc) :
    v.concurrencyOf p e' = .ok cc := by
  obtain ⟨w₁, pl, hw₁, hpl₁, hc⟩ := Delivery.concurrencyOf_iff.mp h
  have hww : w₁ = w := by
    rw [hrun, hu] at hw₁
    exact (Option.some.inj hw₁).symm
  rw [hww] at hpl₁
  exact Delivery.concurrencyOf_iff.mpr ⟨w, pl, by rw [hrun']; exact hv, by rw [hpl]; exact hpl₁, hc⟩

/-- The execution of `T` with the run and placement of an execution of `s` has its concurrency. -/
theorem covers_concurrencyOf (cov : Covers p T s) (wkT : T.WellKeyed) {e e' : Execution} (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) {cc : Concurrency} (h : s.concurrencyOf p e = .ok cc) :
    T.concurrencyOf p e' = .ok cc := by
  obtain ⟨w, pl, hw, hpl', hctl⟩ := Delivery.concurrencyOf_iff.mp h
  exact Delivery.concurrencyOf_iff.mpr ⟨w, pl, hrun ▸ covers_workflow? cov wkT hw, hpl ▸ hpl', hctl⟩

/-- Only a branch invocation carries an arm (`InvocationPlaced`). -/
theorem arm_none {u : State} (inv : Delivery.Inv p u) {i : Invocation} (hi : i ∈ u.invocations) {w : Workflow}
    {pl : Placement} (hw : u.workflow? p i.run = some w) (hpl : w.placement? i.placement = some pl)
    (hnb : ∀ j arms, pl.control ≠ .branch j arms) : i.arm = none := by
  obtain ⟨-, w', pl', -, hw', hpl', -, -, -, harm⟩ := inv.own.invocations i hi
  rw [hw] at hw'
  cases hw'
  rw [hpl] at hpl'
  cases hpl'
  rcases harm with h | ⟨j, arms, h⟩
  · exact h
  · exact absurd h (hnb j arms)

/-! ### Records of `T` -/

/-- Two task lists with the same names agree when tasks of the same name agree. -/
theorem tasks_eq_of_names : ∀ {l₁ l₂ : List TaskState}, l₂.map (·.name) = l₁.map (·.name) →
    (∀ a ∈ l₁, ∀ b ∈ l₂, b.name = a.name → b = a) → l₂ = l₁
  | [], [], _, _ => rfl
  | [], _ :: _, hn, _ => by simp at hn
  | _ :: _, [], hn, _ => by simp at hn
  | a :: as, b :: bs, hn, h => by
    simp only [List.map_cons, List.cons.injEq] at hn
    rw [h a List.mem_cons_self b List.mem_cons_self hn.1,
      tasks_eq_of_names hn.2 fun a' ha' b' hb' => h a' (List.mem_cons_of_mem _ ha') b' (List.mem_cons_of_mem _ hb')]

/-- Invocations with equal fields are equal. -/
theorem invocation_ext {a b : Invocation} (h1 : a.id = b.id) (h2 : a.run = b.run) (h3 : a.placement = b.placement)
    (h4 : a.trigger = b.trigger) (h5 : a.input = b.input) (h6 : a.status = b.status) (h7 : a.arm = b.arm) : a = b := by
  cases a
  cases b
  simp_all

/-- Executions with equal fields are equal. -/
theorem execution_ext {a b : Execution} (h1 : a.id = b.id) (h2 : a.run = b.run) (h3 : a.placement = b.placement)
    (h4 : a.input = b.input) (h5 : a.tasks = b.tasks) (h6 : a.complete = b.complete) : a = b := by
  cases a
  cases b
  simp_all

/-- Tasks with equal fields are equal. -/
theorem task_ext {a b : TaskState} (h1 : a.name = b.name) (h2 : a.input = b.input) (h3 : a.status = b.status) :
    a = b := by
  cases a
  cases b
  simp_all

/-- An execution of `T` itself meets the executions clause of `Covers`: tasks of the same name in one
    execution are equal (`Limit.Inv.coherent`). -/
theorem exec_self (limT : Limit.Inv T) {e : Execution} (he : e ∈ T.executions) :
    ∃ e' ∈ T.executions, e'.id = e.id ∧ e'.run = e.run ∧ e'.placement = e.placement ∧ e'.input = e.input ∧
      e'.tasks.map (·.name) = e.tasks.map (·.name) ∧
      (∀ t ∈ e.tasks, ∀ t' ∈ e'.tasks, t'.name = t.name →
        (t.status ≠ .pending → t'.input = t.input) ∧ (t.status.ended = true → t' = t)) ∧
      (e.complete = true → e' = e) :=
  ⟨e, he, rfl, rfl, rfl, rfl, rfl, fun t ht t' ht' hn => by
    rw [limT.coherent e he t' ht' t ht hn]
    exact ⟨fun _ => rfl, fun _ => rfl⟩, fun _ => rfl⟩

/-- A list whose image has no duplicates has none itself. -/
theorem nodup_of_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ hne heq => hne (heq ▸ rfl)) h

/-- When `s` transformed every included result of an execution and `T` has no other result of it, both
    list the same included results. -/
theorem includedOutputs_perm (cov : Covers p T s) (wkS : s.WellKeyed) (wkT : T.WellKeyed) {eid : String}
    {cc : Concurrency} (hdone : ∀ x ∈ includedOutputs s eid cc, x.output ≠ .pending)
    (back : ∀ r ∈ T.taskResults, r.execution = eid → r ∈ s.taskResults) :
    (includedOutputs s eid cc).Perm (includedOutputs T eid cc) := by
  unfold includedOutputs
  refine (List.perm_ext_iff_of_nodup (List.Pairwise.filter _ (nodup_of_map wkS.taskResults))
    (List.Pairwise.filter _ (nodup_of_map wkT.taskResults))).mpr fun x => ?_
  constructor
  · intro hx
    have hxs := List.mem_filter.mp hx
    obtain ⟨x', hx', -, -, -, -, heq⟩ := cov.taskResults x hxs.1
    rw [heq (hdone x hx)] at hx'
    exact List.mem_filter.mpr ⟨hx', hxs.2⟩
  · intro hx
    have hxT := List.mem_filter.mp hx
    have hexec : x.execution = eid := by
      have := hxT.2
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.1
    exact List.mem_filter.mpr ⟨back x hxT.1 hexec, hxT.2⟩

/-- The designated output of a run of `s` is the designated output of `T`'s run with the same owner. -/
theorem covers_designatedOutput (cov : Covers p T s) (wkT : T.WellKeyed) {r R : Run} (ho : R.owner = r.owner)
    (ht : R.task = r.task) {output : String} (h : s.designatedOutput p r = .ok output) :
    T.designatedOutput p R = .ok output := by
  obtain ⟨owner, howner, hcase⟩ := State.designatedOutput_eq_ok.mp h
  refine State.designatedOutput_eq_ok.mpr ⟨owner, ho.trans howner, ?_⟩
  rcases hcase with ⟨htask, i, pl, wf, hi, hpl, hctrl⟩ | ⟨name, e, spec, wf, htask, he, hspec, hbody⟩
  · obtain ⟨him, hiid⟩ := invocation?_eq_some hi
    obtain ⟨i₀, hi₀, b1, b2, b3, -⟩ := cov.invocations i him
    obtain ⟨w₀, hw₀, hpl₀⟩ := State.placementOf_eq_ok.mp hpl
    refine Or.inl ⟨ht.trans htask, i₀, pl, wf, ?_, ?_, hctrl⟩
    · rw [← hiid, ← b1]
      exact wkT.invocation?_of_mem hi₀
    · rw [b2, b3]
      exact State.placementOf_eq_ok.mpr ⟨w₀, covers_workflow? cov wkT hw₀, hpl₀⟩
  · obtain ⟨hem, heid⟩ := execution?_eq_some he
    obtain ⟨e₀, he₀, a1, a2, a3, -⟩ := cov.executions e hem
    obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec
    obtain ⟨w₀, pl₀, hw₀, -, -⟩ := Delivery.concurrencyOf_iff.mp hcc
    refine Or.inr ⟨name, e₀, spec, wf, ht.trans htask, ?_, ?_, hbody⟩
    · rw [← heid, ← a1]
      exact wkT.execution?_of_mem he₀
    · exact State.taskSpec_eq_ok.mpr ⟨cc, concurrencyOf_of_workflow? rfl a2 a3 hw₀ (covers_workflow? cov wkT hw₀) hcc,
        hfind⟩

/-! ### Validated bodies -/

/-- Reduces a successful validator computation to its conditions. -/
local macro "close_validate_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, exists_const, and_true, true_and, Bool.false_eq_true,
    ↓reduceIte, false_and, and_false, exists_false] at $h:ident)

theorem validateWorkflow_of_valid (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows) :
    p.validateWorkflow w = .ok () :=
  Definition.validateWorkflow_of_validate valid hw

theorem validatePlacement_of_valid (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) : p.validatePlacement w pl = .ok () := by
  have h := validateWorkflow_of_valid valid hw
  unfold Definition.validateWorkflow at h
  close_validate_simp at h
  obtain ⟨-, -, -, -, u, -, -, h⟩ := h
  split at h <;> close_validate_simp at h
  case' h_1 => obtain ⟨_, -, h⟩ := h
  all_goals
    obtain ⟨u₁, h1, -⟩ := h
    exact Static.forIn_yield_ok h1 pl hpl

theorem validateBody_of_call {w : Workflow} {pl : Placement} (h : p.validatePlacement w pl = .ok ())
    {body : Body} (hc : pl.control = .call body) : ∃ at_ input, p.validateBody at_ body = .ok input := by
  rcases pl with ⟨name, control, policy, timeout⟩
  simp only at hc
  subst hc
  unfold Definition.validatePlacement at h
  close_validate_simp at h
  obtain ⟨input, hb, -⟩ := h
  exact ⟨_, input, hb⟩

theorem validateBody_of_task {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) : ∃ at' input, p.validateBody at' task.body = .ok input := by
  unfold Definition.validateTask at h
  close_validate_simp at h
  obtain ⟨-, input, hb, -⟩ := h
  exact ⟨_, input, hb⟩

theorem workflow_of_validateBody {at_ wf out : String} {input : Option ValueType}
    (h : p.validateBody at_ (.workflow wf out) = .ok input) :
    ∃ w, p.workflow? wf = some w ∧ (w.placement? out).isSome = true ∧ w.isEndpoint out = true := by
  unfold Definition.validateBody at h
  close_validate_simp at h
  obtain ⟨w, hw, h1, h2, -⟩ := h
  exact ⟨w, hw, h1, h2⟩

/-- The designated output of a validated workflow body is a placement of that workflow with a Single
    output. -/
theorem body_output (valid : p.validate = .ok ()) {at_ wf out : String} {input : Option ValueType}
    (h : p.validateBody at_ (.workflow wf out) = .ok input) :
    ∃ w plo, p.workflow? wf = some w ∧ w.placement? out = some plo ∧ plo ∈ w.placements ∧
      w.outputKind? p out = some .single := by
  obtain ⟨w, hw, hplo, hend⟩ := workflow_of_validateBody h
  obtain ⟨plo, hplo'⟩ := Option.isSome_iff_exists.mp hplo
  obtain ⟨hplom, hplon⟩ := Workflow.placement?_eq_some hplo'
  refine ⟨w, plo, hw, hplo', hplom, ?_⟩
  rw [← hplon]
  exact (kinds_of_validate valid w (Definition.workflow?_eq_some hw).1 plo hplom).2.1 (by rw [hplon]; exact hend)

/-- The run of a sub-workflow invocation, and its designated output. -/
theorem subrun_output (valid : p.validate = .ok ()) (h : Reachable p s) {i : Invocation} (hi : i ∈ s.invocations)
    {w : Workflow} {pl : Placement} (hw : s.workflow? p i.run = some w) (hpl : w.placement? i.placement = some pl)
    {wf out : String} (hctrl : pl.control = .call (.workflow wf out)) :
    ∃ R ∈ s.runs, R.path = Key.child i.id ∧ R.owner = some i.id ∧ R.task = none ∧ R.workflow = wf ∧
      s.designatedOutput p R = .ok out ∧ ∃ w' plo, p.workflow? wf = some w' ∧ w'.placement? out = some plo ∧
        plo ∈ w'.placements ∧ w'.outputKind? p out = some .single := by
  obtain ⟨R, hR, hRp, hRo, hRt, hRwf⟩ := (invocation_body h i hi w pl hw hpl).2.1 wf out hctrl
  refine ⟨R, hR, hRp, hRo, hRt, hRwf, ?_, ?_⟩
  · exact State.designatedOutput_eq_ok.mpr ⟨i.id, hRo, Or.inl ⟨hRt, i, pl, wf, h.wellKeyed.invocation?_of_mem hi,
      State.placementOf_eq_ok.mpr ⟨w, hw, hpl⟩, hctrl⟩⟩
  · obtain ⟨at_, _, hbv⟩ := validateBody_of_call
      (validatePlacement_of_valid valid (workflow_mem hw) (Workflow.placement?_eq_some hpl).1) hctrl
    exact body_output valid hbv

/-- The designated output of a run is a placement of its workflow with a Single output: a
    sub-workflow run runs the call's workflow (`invocation_body`), a task run its task's
    (`TaskRunWf`), and a validated body names an endpoint. -/
theorem run_output (valid : p.validate = .ok ()) (h : Reachable p s) {r : Run} (hr : r ∈ s.runs)
    {output : String} (hout : s.designatedOutput p r = .ok output) {w : Workflow} (hw : p.workflow? r.workflow = some w) :
    (∃ plo ∈ w.placements, plo.name = output) ∧ w.outputKind? p output = some .single := by
  have wk := h.wellKeyed
  obtain ⟨owner, howner, hcase⟩ := State.designatedOutput_eq_ok.mp hout
  obtain ⟨w', plo, hw', hplo, hplom, hk⟩ : ∃ w' plo, p.workflow? r.workflow = some w' ∧ w'.placement? output = some plo ∧
      plo ∈ w'.placements ∧ w'.outputKind? p output = some .single := by
    rcases hcase with ⟨htask, i, pl, wf, hi, hpl, hctrl⟩ | ⟨name, e, spec, wf, htask, he, hspec, hbody⟩
    · obtain ⟨w₀, hw₀, hpl₀⟩ := State.placementOf_eq_ok.mp hpl
      obtain ⟨him, hiid⟩ := invocation?_eq_some hi
      obtain ⟨R, hR, -, hRo, hRt, hRwf, -, hrest⟩ := subrun_output valid h him hw₀ hpl₀ hctrl
      have hRr : R = r :=
        (Settle.reachable h).1.run_unique wk hR hr hRo (howner.trans (by rw [hiid])) hRt htask
      rw [← hRr, hRwf]
      exact hrest
    · obtain ⟨e', he', heo', spec', out', hspec', hbody'⟩ := CalmAux.Reachable.taskRunWf h r hr name htask
      obtain ⟨hem, heid⟩ := execution?_eq_some he
      have hee : e' = e := wk.execution_eq_of_id he' hem (Option.some.inj (heo'.symm.trans (howner.trans (by rw [heid]))))
      subst hee
      have hsp : spec' = spec := Settle.taskSpec_det hspec' hspec
      subst hsp
      rw [hbody] at hbody'
      cases hbody'
      obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec
      obtain ⟨plc, hplc, hctrl⟩ := State.concurrencyOf_eq_ok.mp hcc
      obtain ⟨we, hwe, hplce⟩ := State.placementOf_eq_ok.mp hplc
      obtain ⟨-, -, -, htasks⟩ := ((Definition.validate_ok valid).workflows we (workflow_mem hwe)).placements plc
        (Workflow.placement?_eq_some hplce).1 |>.concurrency cc hctrl
      obtain ⟨at_, hv⟩ := htasks spec' (List.mem_of_find?_eq_some hfind)
      obtain ⟨at', _, hbv⟩ := validateBody_of_task hv
      rw [hbody] at hbv
      exact body_output valid hbv
  rw [hw] at hw'
  cases hw'
  exact ⟨⟨plo, hplom, (Workflow.placement?_eq_some hplo).2⟩, hk⟩

/-! ### Settlements -/

/-- A waitStream or Merge settled normally records its aggregate. -/
theorem aggregate_of_normal {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {result : Option Result} (h : s.settleOutcome path pl shape kind = some (x, result))
    (hn : x.outcome = .normal) (hctrl : ∃ e, pl.control = .waitStream e ∨ pl.control = .merge e) :
    ∃ res, result = some res ∧ res.id = Key.aggregate path pl.name := by
  obtain ⟨e, he | he⟩ := hctrl
  · obtain ⟨i, c, o, -, -, ⟨-, hx, -⟩ | ⟨-, hres⟩⟩ := Settle.settleOutcome_waitStream h he
    · rw [hx] at hn
      cases hn
    · exact ⟨_, hres, rfl⟩
  · rcases Settle.settleOutcome_merge h he with ⟨hx, -⟩ | ⟨-, values, hres⟩
    · rw [hx] at hn
      cases hn
    · exact ⟨_, hres, rfl⟩

/-- On a Single connection, `T` delivers nothing beyond `s` once both resolve it alike: with a
    delivery in `s`, the source has one result (`Deliv.one`), hence `T` has that one delivery; without
    one, `s` resolves from the source's settlement, and so does `T`, which has no delivery either. -/
theorem single_deliveries_sub (hT : Reachable p T) (cov : Covers p T s) {path : Path} {w : Workflow} {j : Nat}
    {c : Connection} (hwT : T.workflow? p path = some w) (hc : w.connections[j]? = some c)
    (hk : w.outputKind? p c.source = some .single) (hres : s.resolveSingle path j c = T.resolveSingle path j c) :
    ∀ d ∈ T.deliveriesOn path j, d ∈ s.deliveries := by
  intro d hd
  have wkT := hT.wellKeyed
  have own := (Delivery.Reachable.inv hT).own
  cases hs : s.deliveriesOn path j with
  | nil =>
    exfalso
    cases hTd : T.deliveriesOn path j with
    | nil =>
      rw [hTd] at hd
      cases hd
    | cons d₀ rest =>
      unfold State.resolveSingle at hres
      rw [hs, hTd] at hres
      revert hres
      cases s.settled? path c.source with
      | none => cases ho : d₀.outcome <;> simp [ho]
      | some y => cases ha : armOutcome y c.arm <;> cases ho : d₀.outcome <;> simp [ha, ho]
  | cons d₀ rest =>
    have hd₀ : d₀ ∈ s.deliveriesOn path j := by rw [hs]; exact List.mem_cons_self
    obtain ⟨hd₀m, hd₀r, hd₀c⟩ := Delivery.mem_deliveriesOn.mp hd₀
    have hd₀T := cov.deliveries d₀ hd₀m
    obtain ⟨hdm, hdr, hdc⟩ := Delivery.mem_deliveriesOn.mp hd
    obtain ⟨w₁, c₁, r₁, hw₁, hc₁, hr₁, hr₁id, hr₁r, hr₁p, -⟩ := own.deliveries d hdm
    obtain ⟨w₂, c₂, r₂, hw₂, hc₂, hr₂, hr₂id, hr₂r, hr₂p, -⟩ := own.deliveries d₀ hd₀T
    rw [hdr, hwT] at hw₁
    cases hw₁
    rw [hd₀r, hwT] at hw₂
    cases hw₂
    rw [hdc, hc] at hc₁
    cases hc₁
    rw [hd₀c, hc] at hc₂
    cases hc₂
    -- Both carry a result of the Single source, so the same one.
    have hid := (Delivery.Reachable.deliv hT).one w path c.source hwT hk r₁ hr₁ r₂ hr₂ (hr₁r.trans hdr) hr₁p
      (hr₂r.trans hd₀r) hr₂p
    have h1 := wkT.delivery?_of_mem hdm
    have h2 := wkT.delivery?_of_mem hd₀T
    rw [hdr, hdc, ← hr₁id, hid, hr₂id, ← hd₀r, ← hd₀c] at h1
    rw [h1] at h2
    rw [Option.some.inj h2]
    exact hd₀m

end CoversCloseAux

end Suimon.Round3
