import Suimon.Theorems.Json
import Suimon.Theorems.StaticLemmas

/-! The validator is sound for `Definition.Normal`: a definition it accepts is normal (§15.2), so the
    canonical form that a record header holds for it decodes back to it. -/

namespace Suimon

/-- Reduces a successful validator computation to its conditions. --/
local macro "normal_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, Definition.validateTypes_eq_ok, exists_const, and_true,
    true_and, Bool.false_eq_true, ↓reduceIte, false_and, and_false, exists_false] at $h:ident)

private theorem find?_key {α κ : Type} [BEq κ] [LawfulBEq κ] {l : List α} {f : α → κ} {k : κ} {x : α}
    (h : l.find? (fun x => f x == k) = some x) : x ∈ l ∧ f x = k :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

namespace Definition
variable {p : Definition}

theorem validateBody_normal {at_ : String} {body : Body} {input : Option ValueType}
    (h : p.validateBody at_ body = .ok input) : body.Normal p ∧ p.bodyInput body = some input := by
  cases body with
  | function id =>
    unfold validateBody at h
    normal_simp at h
    obtain ⟨f, hf, rfl⟩ := h
    exact ⟨by simp [Body.Normal, hf], by simp [bodyInput, hf]⟩
  | workflow id output =>
    unfold validateBody at h
    normal_simp at h
    obtain ⟨w, hw, hpl, hend, rfl⟩ := h
    exact ⟨⟨w, hw, hpl, hend⟩, by simp [bodyInput, hw]⟩

theorem validateTimeout_legal {at_ : String} {t : Timeout} {function : Option Contract} {judge : Bool}
    (h : validateTimeout at_ t function judge = .ok ()) : t.Legal function judge := by
  unfold validateTimeout at h
  split at h
  · rename_i he
    obtain rfl : t = {} := by
      rcases t with ⟨_ | _, _ | _⟩ <;> simp_all [Timeout.isEmpty]
    exact ⟨fun hne => absurd rfl hne, by simp, by simp⟩
  · normal_simp at h
    obtain ⟨htarget, hpos, hmax, h⟩ := h
    refine ⟨fun _ => by simpa using htarget, fun ms hms => ?_, fun he => ?_⟩
    · simp only [Bool.and_eq_true, Option.all_eq_true_iff_get, decide_eq_true_eq] at hpos hmax
      rcases List.mem_append.1 hms with hms | hms <;> simp only [Option.mem_toList] at hms
      · exact ⟨by simpa [hms] using hpos.1, by simpa [hms] using hmax.1⟩
      · exact ⟨by simpa [hms] using hpos.2, by simpa [hms] using hmax.2⟩
    · simp only [he, ↓reduceIte] at h
      normal_simp at h
      cases function with
      | none => simp at h
      | some c => exact ⟨c, rfl, by simpa using h⟩

theorem validateTask_normal {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) : task.Normal p c := by
  unfold validateTask at h
  normal_simp at h
  obtain ⟨hname, input, hbody, h⟩ := h
  obtain ⟨hnormal, hinput⟩ := validateBody_normal hbody
  refine ⟨by simpa using hname, hnormal, ⟨input, hinput, ?_⟩, fun id hid => ?_, ?_⟩
  · split at h <;> normal_simp at h
    case h_1 =>
      rename_i hti
      obtain ⟨hci, -⟩ := h
      cases hc : c.input with
      | none => exact ⟨rfl, hti⟩
      | some _ => simp [hc] at hci
    case h_2 =>
      rename_i hti
      obtain ⟨hci, -⟩ := h
      cases hc : c.input with
      | none => simp [hc] at hci
      | some _ => exact ⟨.discard, hti, trivial⟩
    case h_6 =>
      rename_i id hti
      obtain ⟨t, ht, source, hsource, hin, hout, -⟩ := h
      rw [hsource]
      exact ⟨.declared id, hti, t, ht, beq_iff_eq.1 hin, beq_iff_eq.1 hout⟩
  · -- Every accepted input transform continues with the same output check.
    simp only [Option.mem_def] at hid
    simp only [hid] at h
    split at h <;> normal_simp at h
    case' h_1 => obtain ⟨-, h⟩ := h
    case' h_2 => obtain ⟨-, h⟩ := h
    case' h_6 => obtain ⟨-, -, -, -, -, -, h⟩ := h
    all_goals
      obtain ⟨t, ht, element, helement, hin, hout, -⟩ := h
      exact ⟨t, ht, by rw [helement, beq_iff_eq.1 hin], beq_iff_eq.1 hout⟩
  · split at h <;> normal_simp at h
    case' h_1 => obtain ⟨-, h⟩ := h
    case' h_2 => obtain ⟨-, h⟩ := h
    case' h_6 => obtain ⟨-, -, -, -, -, -, h⟩ := h
    all_goals
      split at h
      case' h_1 =>
        normal_simp at h
        obtain ⟨-, -, -, -, -, -, h⟩ := h
      all_goals exact validateTimeout_legal h

theorem validateConnection_normal {w : Workflow} {c : Connection}
    (h : p.validateConnection w c = .ok ()) : c.Normal p w := by
  unfold validateConnection at h
  normal_simp at h
  obtain ⟨src, hsrc, dst, hdst, h⟩ := h
  refine ⟨src, dst, hsrc, hdst, fun judge arms hb => ?_, fun hnb => ?_, ?_⟩
  · split at h <;> normal_simp at h
    case h_1 =>
      rename_i arms' arm hctl harm
      rw [hctl] at hb
      cases hb
      exact ⟨arm, by simpa using h.1, harm⟩
    case h_4 => rename_i hne; exact absurd hb (hne judge arms)
  · split at h <;> normal_simp at h
    case h_1 => rename_i j arms arm hctl harm; exact absurd hctl (hnb j arms)
    case h_4 => rename_i harm _; exact harm
  · split at h <;> normal_simp at h
    case' h_1 => obtain ⟨-, h⟩ := h
    all_goals
      obtain ⟨produced, hprod, input, hinput, h⟩ := h
      refine ⟨produced, input, hprod, hinput, ?_⟩
      split at h <;> normal_simp at h
      case' h_1 => rename_i hc; rw [hc]; trivial
      case' h_4 =>
        rename_i id expected hc
        obtain ⟨t, ht, hin, hout⟩ := h
        rw [hc]
        exact ⟨t, ht, beq_iff_eq.1 hin, beq_iff_eq.1 hout⟩

theorem validateEntry_normal {w : Workflow} {e : Entry} (h : p.validateEntry w e = .ok ()) : e.Normal p w := by
  unfold validateEntry at h
  normal_simp at h
  obtain ⟨htype, pl, hpl, hmerge, expected, hexp, heq, halone⟩ := h
  refine ⟨by simpa using htype, ⟨pl, hpl, fun el hel => ?_, by rw [hexp, beq_iff_eq.1 heq]⟩, by simpa using halone⟩
  simp [hel] at hmerge

theorem validatePlacement_normal {w : Workflow} {pl : Placement} (h : p.validatePlacement w pl = .ok ()) :
    pl.Normal p w := by
  rcases pl with ⟨name, control, policy, timeout⟩
  unfold validatePlacement at h
  cases control with
  | call body =>
    normal_simp at h
    obtain ⟨a, hbody, h⟩ := h
    obtain ⟨hnormal, hinput⟩ := validateBody_normal hbody
    split at h <;> normal_simp at h
    case' isTrue ha =>
      obtain ⟨hc, h⟩ := h
      have hcount : w.inputCount name ≤ 1 ∧ (a.isSome → w.inputCount name = 1) := by
        simp only [beq_iff_eq] at hc; exact ⟨by unfold Workflow.inputCount; omega, fun _ => hc⟩
    case' isFalse ha =>
      obtain ⟨hc, h⟩ := h
      have hcount : w.inputCount name ≤ 1 ∧ (a.isSome → w.inputCount name = 1) :=
        ⟨by simpa [Workflow.inputCount] using hc, fun h' => absurd h' ha⟩
    all_goals
      obtain ⟨hkind, htimeout⟩ := h
      have htimeout := validateTimeout_legal htimeout
      refine ⟨fun b hb => ?_, nofun, nofun, nofun, nofun, ⟨a, hinput, fun _ => hcount⟩, hkind, ?_⟩
      · cases hb; exact hnormal
      · cases body <;> exact htimeout
  | branch judge arms =>
    normal_simp at h
    obtain ⟨j, hj, harms, hconn, _, rfl, h⟩ := h
    simp only [Option.isSome_some, ↓reduceIte] at h
    normal_simp at h
    obtain ⟨hc, hkind, htimeout⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at harms
    obtain ⟨⟨hne, hu⟩, hnames⟩ := harms
    simp only [List.any_eq_true, beq_iff_eq] at hconn
    refine ⟨nofun, fun judge' arms' hb => ?_, nofun, nofun, nofun, ⟨some j.input, by simp [inputType, hj], fun _ => ?_⟩,
      hkind, validateTimeout_legal htimeout⟩
    · cases hb
      exact ⟨by simp [hj], hne, nodup_of_unique hu, fun arm ha => by simpa using hnames arm ha, hconn⟩
    · simp only [beq_iff_eq] at hc
      exact ⟨by dsimp only [Workflow.inputCount]; omega, fun _ => hc⟩
  | waitStream element =>
    normal_simp at h
    obtain ⟨htype, _, rfl, h⟩ := h
    simp only [Option.isSome_some, ↓reduceIte] at h
    normal_simp at h
    obtain ⟨hc, hwait, hkind, htimeout⟩ := h
    refine ⟨nofun, nofun, fun e he => ?_, nofun, nofun, ⟨some element, rfl, fun _ => ?_⟩, hkind,
      validateTimeout_legal htimeout⟩
    · cases he
      exact ⟨by simpa using htype, by simpa using hwait⟩
    · simp only [beq_iff_eq] at hc
      exact ⟨by dsimp only [Workflow.inputCount]; omega, fun _ => hc⟩
  | merge element =>
    normal_simp at h
    obtain ⟨htype, hne, _, rfl, u, hloop, hkind, htimeout⟩ := h
    refine ⟨nofun, nofun, nofun, fun e he => ?_, nofun, ⟨some element, rfl, fun hm => absurd rfl (hm element)⟩,
      hkind, validateTimeout_legal htimeout⟩
    cases he
    refine ⟨by simpa using htype, by simpa using hne, fun c hc => ?_⟩
    have := Static.forIn_yield_ok hloop c hc
    normal_simp at this
    simpa using this
  | concurrency c =>
    normal_simp at h
    obtain ⟨htypes, hlimit, hmax, hne, hunique, hany, u, hloop, _, rfl, h⟩ := h
    split at h <;> normal_simp at h
    case' isTrue ha =>
      obtain ⟨hc, h⟩ := h
      have hcount : w.inputCount name ≤ 1 ∧ (c.input.isSome → w.inputCount name = 1) := by
        simp only [beq_iff_eq] at hc; exact ⟨by unfold Workflow.inputCount; omega, fun _ => hc⟩
    case' isFalse ha =>
      obtain ⟨hc, h⟩ := h
      have hcount : w.inputCount name ≤ 1 ∧ (c.input.isSome → w.inputCount name = 1) :=
        ⟨by simpa [Workflow.inputCount] using hc, fun h' => absurd h' ha⟩
    all_goals
      obtain ⟨hkind, htimeout⟩ := h
      refine ⟨nofun, nofun, nofun, nofun, fun c' hc' => ?_, ⟨c.input, rfl, fun _ => hcount⟩, hkind,
        validateTimeout_legal htimeout⟩
      cases hc'
      exact ⟨by simpa using htypes, by simpa using hlimit, by simpa using hmax, by simpa using hne,
        nodup_of_unique hunique, List.any_eq_true.1 hany,
        fun task ht => validateTask_normal (Static.forIn_yield_ok hloop task ht)⟩

theorem validateWorkflow_normal {w : Workflow} (h : p.validateWorkflow w = .ok ()) : w.Normal p := by
  have hwc := validateWorkflow_ok h
  have hconnections := fun c hc => validateConnection_normal (hwc.connections c hc)
  unfold validateWorkflow at h
  normal_simp at h
  obtain ⟨hid, -, hnames, -, -, -, -, h⟩ := h
  have hplacements : ∀ pl ∈ w.placements, p.validatePlacement w pl = .ok () := by
    split at h <;> normal_simp at h
    case' h_1 => obtain ⟨_, -, h⟩ := h
    all_goals
      obtain ⟨u, hloop, -⟩ := h
      exact Static.forIn_yield_ok hloop
  obtain ⟨rank, -, hedge⟩ := acyclic_rank hwc.acyclic
  refine ⟨by simpa using hid, hwc.nonempty, by simpa using hnames, hwc.names, hconnections,
    ⟨rank, fun c hc => ?_⟩, fun e he => validateEntry_normal (hwc.entry e he),
    fun pl hpl => validatePlacement_normal (hplacements pl hpl), hwc.endpoints⟩
  obtain ⟨src, dst, hsrc, hdst, -⟩ := (hconnections c hc).ends
  obtain ⟨hsm, hsn⟩ := find?_key hsrc
  obtain ⟨hdm, hdn⟩ := find?_key hdst
  exact hedge (c.source, c.target) (List.mem_map.2 ⟨c, hc, rfl⟩) (List.mem_map.2 ⟨src, hsm, hsn⟩)
    (List.mem_map.2 ⟨dst, hdm, hdn⟩)

theorem validateFunction_ok {f : FunctionDecl} (h : validateFunction f = .ok ()) :
    f.id ≠ "" ∧ ∀ t ∈ f.input.toList ++ [f.output.element], t.name ≠ "" := by
  unfold validateFunction at h
  normal_simp at h
  exact ⟨by simpa using h.1, h.2⟩

theorem validateJudge_ok {j : JudgeDecl} (h : validateJudge j = .ok ()) : j.id ≠ "" ∧ j.input.name ≠ "" := by
  unfold validateJudge at h
  normal_simp at h
  exact ⟨by simpa using h.1, by simpa using h.2⟩

theorem validateTransform_ok {t : TransformDecl} (h : validateTransform t = .ok ()) :
    t.id ≠ "" ∧ t.input.name ≠ "" ∧ t.output.name ≠ "" := by
  unfold validateTransform at h
  normal_simp at h
  exact ⟨by simpa using h.1, by simpa using h.2⟩

end Definition

/-- A workflow that a normal placement calls is declared. --/
theorem Placement.Normal.workflowRef {p : Definition} {w : Workflow} {pl : Placement} (h : pl.Normal p w)
    {id : String} (hid : id ∈ pl.control.workflowRefs) : ∃ w', p.workflow? id = some w' := by
  rcases hctl : pl.control with body | ⟨judge, arms⟩ | e | e | c <;> rw [hctl] at hid <;>
    simp only [Control.workflowRefs, List.not_mem_nil] at hid
  · cases body with
    | function f => simp [Body.workflowRef] at hid
    | workflow id' out =>
      simp only [Body.workflowRef, Option.toList_some, List.mem_singleton] at hid
      subst hid
      obtain ⟨w', hw', -⟩ := h.call _ hctl
      exact ⟨w', hw'⟩
  · obtain ⟨task, htask, href⟩ := List.mem_filterMap.1 hid
    obtain ⟨-, -, -, -, -, -, htasks⟩ := h.concurrency c hctl
    have hb := (htasks task htask).body
    cases hbody : task.body with
    | function f => simp [hbody, Body.workflowRef] at href
    | workflow id' out =>
      rw [hbody] at href hb
      simp only [Body.workflowRef, Option.some.injEq] at href
      subst href
      obtain ⟨w', hw', -⟩ := hb
      exact ⟨w', hw'⟩

/-- The validator is sound: a definition it accepts is normal (§15.2). --/
theorem Definition.normal_of_validate {p : Definition} (h : p.validate = .ok ()) : p.Normal := by
  have hc := validate_ok h
  unfold Definition.validate at h
  normal_simp at h
  obtain ⟨-, -, -, -, -, -, -, u₁, hf, u₂, hj, u₃, ht, u₄, hw⟩ := h
  have hworkflows := fun w hw' => validateWorkflow_normal (Static.forIn_yield_ok hw w hw')
  obtain ⟨rank, -, hedge⟩ := acyclic_rank hc.callsAcyclic
  refine ⟨fun f hf' => validateFunction_ok (Static.forIn_yield_ok hf f hf'),
    fun j hj' => validateJudge_ok (Static.forIn_yield_ok hj j hj'),
    fun t ht' => validateTransform_ok (Static.forIn_yield_ok ht t ht'),
    hc.functions, hc.judges, hc.transforms, hc.discard, hc.workflowIds, hc.main,
    ⟨rank, fun w hw' pl hpl id hid => ?_⟩, hworkflows⟩
  obtain ⟨w', hw''⟩ := ((hworkflows w hw').placements pl hpl).workflowRef hid
  obtain ⟨hwm, hwn⟩ := find?_key hw''
  exact hedge (w.id, id)
    (List.mem_flatMap.2 ⟨w, hw', List.mem_flatMap.2 ⟨pl, hpl, List.mem_map.2 ⟨id, hid, rfl⟩⟩⟩)
    (List.mem_map.2 ⟨w, hw', rfl⟩) (List.mem_map.2 ⟨w', hwm, hwn⟩)

end Suimon

namespace Suimon.Codec

/-- The canonical form of a definition that validation accepts decodes back to it. --/
theorem definition_definitionWire_of_validate {p : Definition} (h : p.validate = .ok ()) :
    definition (definitionWire p).toJson = .ok p :=
  definition_definitionWire (Definition.normal_of_validate h)

/-- Loading the header of a record written for a definition that validation accepts, as the CLI loads a
    definition (decode, then validate), gives the definition back. --/
theorem load_definitionWire {p : Definition} (h : p.validate = .ok ()) :
    (do let q ← definition (definitionWire p).toJson; q.validate; return q) = Except.ok p := by
  simp [definition_definitionWire_of_validate h, h, bind, Except.bind, pure, Except.pure]

end Suimon.Codec
