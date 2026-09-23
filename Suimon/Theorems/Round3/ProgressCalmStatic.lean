import Suimon.Theorems.Round3.Conformance

/-! Static facts for `calm_progress` (task C2): what validation says about the bodies of calls and
    tasks, which `PlacementChecked` does not record. -/

namespace Suimon.Round3.CalmAux

/-- Reduces a successful validator computation to its conditions. -/
local macro "calm_validate_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, exists_const, and_true, true_and, Bool.false_eq_true,
    ↓reduceIte, false_and, and_false, exists_false] at $h:ident)

variable {p : Program}

theorem validateWorkflow_of_valid (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows) :
    p.validateWorkflow w = .ok () := by
  unfold Program.validate at valid
  calm_validate_simp at valid
  obtain ⟨-, -, -, -, -, -, -, u, hloop⟩ := valid
  exact Static.forIn_yield_ok hloop w hw

theorem validatePlacement_of_workflow {w : Workflow} (h : p.validateWorkflow w = .ok ()) {pl : Placement}
    (hpl : pl ∈ w.placements) : p.validatePlacement w pl = .ok () := by
  unfold Program.validateWorkflow at h
  calm_validate_simp at h
  obtain ⟨-, -, -, -, u, -, -, h⟩ := h
  split at h <;> calm_validate_simp at h
  case' h_1 => obtain ⟨_, -, h⟩ := h
  all_goals
    obtain ⟨u₁, h1, -⟩ := h
    exact Static.forIn_yield_ok h1 pl hpl

theorem validatePlacement_of_valid (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) : p.validatePlacement w pl = .ok () :=
  validatePlacement_of_workflow (validateWorkflow_of_valid valid hw) hpl

theorem validateBody_of_call {w : Workflow} {pl : Placement} (h : p.validatePlacement w pl = .ok ())
    {body : Body} (hc : pl.control = .call body) : ∃ at_, p.validateBody at_ body = .ok () := by
  rcases pl with ⟨name, control, policy, timeout⟩
  simp only at hc
  subst hc
  unfold Program.validatePlacement at h
  calm_validate_simp at h
  obtain ⟨_, hb, -⟩ := h
  exact ⟨_, hb⟩

theorem validateBody_of_task {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) : ∃ at', p.validateBody at' task.body = .ok () := by
  unfold Program.validateTask at h
  calm_validate_simp at h
  obtain ⟨-, u, hb, -⟩ := h
  exact ⟨_, hb⟩

theorem function_of_validateBody {at_ f : String} (h : p.validateBody at_ (.function f) = .ok ()) :
    (p.function? f).isSome = true := by
  unfold Program.validateBody at h
  calm_validate_simp at h
  exact h

theorem workflow_of_validateBody {at_ wf out : String} (h : p.validateBody at_ (.workflow wf out) = .ok ()) :
    ∃ w, p.workflow? wf = some w ∧ (w.placement? out).isSome = true ∧ w.isEndpoint out = true := by
  unfold Program.validateBody at h
  calm_validate_simp at h
  obtain ⟨w, hw, h1, h2⟩ := h
  exact ⟨w, hw, h1, h2⟩

/-- Every body a valid program calls, from a placement or from a task, is validated. -/
theorem body_valid (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows) {pl : Placement}
    (hpl : pl ∈ w.placements) :
    (∀ body, pl.control = .call body → ∃ at_, p.validateBody at_ body = .ok ()) ∧
    (∀ cc, pl.control = .concurrency cc → ∀ spec ∈ cc.tasks,
      ∃ at_, p.validateBody at_ spec.body = .ok ()) := by
  refine ⟨fun body hc => validateBody_of_call (validatePlacement_of_valid valid hw hpl) hc, ?_⟩
  intro cc hc spec hspec
  obtain ⟨-, -, -, htasks⟩ := (((Program.validate_ok valid).workflows w hw).placements pl hpl).concurrency cc hc
  obtain ⟨at_, hv⟩ := htasks spec hspec
  exact validateBody_of_task hv

end Suimon.Round3.CalmAux
