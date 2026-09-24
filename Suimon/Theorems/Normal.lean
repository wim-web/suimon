import Suimon.Theorems.Json
import Suimon.Theorems.StaticLemmas

/-! The validator decides `Definition.Normal`: a definition it accepts is normal (§15.2), and it accepts
    every normal definition. The canonical form that a record header holds for an accepted definition
    loads back to it (`Codec.load_definitionWire`), and no other accepted definition has the same
    canonical form (`Codec.definitionWire_inj`). -/

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


/-! ## The validator is complete

It accepts every normal definition, so `Definition.Normal` states all that it checks
(`Definition.validate_eq_ok_iff`). -/

/-- Reduces a validator computation to the conditions under which it succeeds. --/
local macro "complete_simp" : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, Definition.validateTypes_eq_ok, exists_const, and_true,
    true_and, Bool.false_eq_true, ↓reduceIte, false_and, and_false, exists_false])

namespace Definition
variable {p : Definition}

theorem validateBody_of_normal {at_ : String} {body : Body} {input : Option ValueType} (h : body.Normal p)
    (hinput : p.bodyInput body = some input) : p.validateBody at_ body = .ok input := by
  cases body with
  | function id =>
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 h
    simp only [bodyInput, hf, Option.map_some, Option.some.injEq] at hinput
    unfold validateBody
    complete_simp
    exact ⟨f, hf, hinput⟩
  | workflow id output =>
    obtain ⟨w, hw, hpl, hend⟩ := h
    simp only [bodyInput, hw, Option.map_some, Option.some.injEq] at hinput
    unfold validateBody
    complete_simp
    exact ⟨w, hw, hpl, hend, hinput⟩

theorem validateTimeout_of_legal {at_ : String} {t : Timeout} {function : Option Contract} {judge : Bool}
    (h : t.Legal function judge) : validateTimeout at_ t function judge = .ok () := by
  unfold validateTimeout
  split
  · rfl
  · rename_i he
    have hne : t ≠ {} := fun ht => by simp [ht, Timeout.isEmpty] at he
    have hpos := h.positive
    complete_simp
    refine ⟨by simpa using h.target hne, ?_, ?_, ?_⟩
    · rcases t with ⟨_ | c, _ | e⟩ <;> simp_all
    · rcases t with ⟨_ | c, _ | e⟩ <;> simp_all
    · split
      · rename_i hel
        obtain ⟨c, rfl, hc⟩ := h.element hel
        complete_simp
        simp [hc]
      · rfl

theorem validateTask_of_normal {at_ : String} {c : Concurrency} {task : TaskSpec} (h : task.Normal p c) :
    p.validateTask at_ c task = .ok () := by
  obtain ⟨input, hinput, hin⟩ := h.input
  have hbody : ∀ at_, p.validateBody at_ task.body = .ok input := fun _ => validateBody_of_normal h.body hinput
  have htimeout : ∀ at_, validateTimeout at_ task.timeout (match task.body with
      | .function id => (p.function? id).map (·.output)
      | .workflow .. => none) false = .ok () := by
    intro at_
    have := validateTimeout_of_legal (at_ := at_) h.timeout
    cases hb : task.body <;> simp only [hb, calledContract] at this ⊢ <;> exact this
  have hout : ∀ id ∈ task.output, ∃ t, p.transform? id = some t ∧
      p.bodyElement p.depth task.body = some t.input ∧ t.output = c.element := h.output
  have hname : task.name.isEmpty = false := by simpa using h.name
  -- The input transform, then the output transform.
  have hcases : (c.input = none ∧ input = none ∧ task.input = none) ∨
      (∃ source, c.input = some source ∧ input = none ∧ task.input = some .discard) ∨
      (∃ source expected id t, c.input = some source ∧ input = some expected ∧ task.input = some (.declared id) ∧
        p.transform? id = some t ∧ t.input = source ∧ t.output = expected) := by
    cases hc : c.input with
    | none => rw [hc] at hin; exact .inl ⟨rfl, hin⟩
    | some source =>
      rw [hc] at hin
      obtain ⟨transform, hti, hfits⟩ := hin
      cases transform with
      | discard =>
        cases input with
        | none => exact .inr (.inl ⟨source, rfl, rfl, hti⟩)
        | some _ => cases hfits
      | declared id =>
        cases input with
        | none => cases hfits
        | some expected =>
          obtain ⟨t, ht, hin, hout⟩ := hfits
          exact .inr (.inr ⟨source, expected, id, t, rfl, rfl, hti, ht, hin, hout⟩)
  have houtput : task.output = none ∨ ∃ id t, task.output = some id ∧ p.transform? id = some t ∧
      p.bodyElement p.depth task.body = some t.input ∧ t.output = c.element := by
    cases hto : task.output with
    | none => exact .inl rfl
    | some id =>
      obtain ⟨t, ht, helement, hout⟩ := hout id hto
      exact .inr ⟨id, t, rfl, ht, helement, hout⟩
  unfold validateTask
  rcases hcases with ⟨hc, rfl, hti⟩ | ⟨source, hc, rfl, hti⟩ | ⟨source, expected, id, t, hc, rfl, hti, ht, htin, htout⟩
  all_goals
    rcases houtput with hto | ⟨oid, ot, hto, hot, helement, hoout⟩
    all_goals
      simp [Validate.check, Validate.need, bind, Except.bind, pure, Except.pure, *]
      exact htimeout _

theorem validateConnection_of_normal {w : Workflow} {c : Connection} (h : c.Normal p w) :
    p.validateConnection w c = .ok () := by
  obtain ⟨src, dst, hsrc, hdst, hbranch, hnot, produced, input, hprod, hinput, hfits⟩ := h.ends
  have htr : (c.transform = .discard ∧ input = none) ∨ (∃ id t expected, c.transform = .declared id ∧
      input = some expected ∧ p.transform? id = some t ∧ t.input = produced ∧ t.output = expected) := by
    cases htc : c.transform with
    | discard =>
      rw [htc] at hfits
      cases input with
      | none => exact .inl ⟨rfl, rfl⟩
      | some _ => cases hfits
    | declared id =>
      rw [htc] at hfits
      cases input with
      | none => cases hfits
      | some e =>
        obtain ⟨t, ht, h1, h2⟩ := hfits
        exact .inr ⟨id, t, e, rfl, rfl, ht, h1, h2⟩
  unfold validateConnection
  by_cases hb : ∃ judge arms, src.control = .branch judge arms
  · obtain ⟨judge, arms, hctl⟩ := hb
    obtain ⟨arm, harm, hca⟩ := hbranch judge arms hctl
    rw [hctl] at hprod
    rcases htr with ⟨htc, rfl⟩ | ⟨id, t, expected, htc, rfl, ht, h1, h2⟩
    all_goals simp [Validate.check, Validate.need, bind, Except.bind, pure, Except.pure, *]
  · have hca : c.arm = none := hnot fun j a h => hb ⟨j, a, h⟩
    rcases hctl : src.control with body | ⟨judge, arms⟩ | e | e | cc
    case branch => exact absurd ⟨judge, arms, hctl⟩ hb
    all_goals
      rw [hctl] at hprod
      rcases htr with ⟨htc, rfl⟩ | ⟨id, t, expected, htc, rfl, ht, h1, h2⟩
      all_goals simp [Validate.check, Validate.need, bind, Except.bind, pure, Except.pure, *]

theorem validateEntry_of_normal {w : Workflow} {e : Entry} (h : e.Normal p w) : p.validateEntry w e = .ok () := by
  obtain ⟨pl, hpl, hmerge, hinput⟩ := h.placement
  unfold validateEntry
  complete_simp
  refine ⟨by simpa using h.type, pl, hpl, ?_, some e.valueType, hinput, by simp, by simpa using h.alone⟩
  cases hc : pl.control with
  | merge el => exact absurd hc (hmerge el)
  | _ => rfl

theorem validatePlacement_of_normal {w : Workflow} {pl : Placement} (h : pl.Normal p w) :
    p.validatePlacement w pl = .ok () := by
  obtain ⟨input, hinput, hcount⟩ := h.inputs
  have hkind := h.kind
  have htimeout : ∀ at_, validateTimeout at_ pl.timeout (pl.control.body?.bind p.calledContract)
      (pl.control matches .branch ..) = .ok () := fun _ => validateTimeout_of_legal h.timeout
  rcases pl with ⟨name, control, policy, timeout⟩
  simp only [Workflow.inputCount] at hcount
  unfold validatePlacement
  cases control with
  | call body =>
    have hbody : ∀ at_, p.validateBody at_ body = .ok input := fun _ => validateBody_of_normal (h.call body rfl) hinput
    have hcount := hcount nofun
    cases body <;> simp only [Control.body?, Option.bind, calledContract] at htimeout <;> cases input <;>
      simp [hbody, Validate.check, bind, Except.bind, pure, Except.pure, hcount, hkind, htimeout]
  | branch judge arms =>
    obtain ⟨hj, hne, hu, hnames, arm, harm, c, hc, hca⟩ := h.branch judge arms rfl
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hj
    simp only [inputType, hj, Option.map_some, Option.some.injEq] at hinput
    subst hinput
    have hcount := hcount nofun
    have harms : (!arms.isEmpty && unique arms && arms.all (!·.isEmpty)) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
      exact ⟨⟨hne, unique_of_nodup hu⟩, fun a ha => by simpa using hnames a ha⟩
    have hconn : (arms.any fun arm => (w.outgoing name).any (·.arm == some arm)) = true := by
      simp only [List.any_eq_true, beq_iff_eq]
      exact ⟨arm, harm, c, hc, hca⟩
    simp only [Control.body?, Option.bind] at htimeout
    simp [hj, harms, hconn, Validate.check, Validate.need, bind, Except.bind, pure, Except.pure, hcount, hkind,
      htimeout]
  | waitStream e =>
    obtain ⟨htype, hwait⟩ := h.waitStream e rfl
    simp only [inputType, Option.some.injEq] at hinput
    subst hinput
    have hcount := hcount nofun
    have htypes : ∀ at_, validateTypes at_ [e] = .ok () := fun _ => validateTypes_eq_ok.2 (by simpa using htype)
    simp only [Control.body?, Option.bind] at htimeout
    simp [htypes, hwait, Validate.check, bind, Except.bind, pure, Except.pure, hcount, hkind,
      htimeout]
  | merge e =>
    obtain ⟨htype, hne, hsingle⟩ := h.merge e rfl
    dsimp only at hne hsingle hkind
    have htypes : ∀ at_, validateTypes at_ [e] = .ok () := fun _ => validateTypes_eq_ok.2 (by simpa using htype)
    simp only [Control.body?, Option.bind] at htimeout
    simp [htypes, hne, Validate.check, bind, Except.bind, pure, Except.pure, hkind, htimeout]
    rw [Codec.forIn_ok_of_yield]
    intro c hc
    simp [hsingle c hc]
  | concurrency c =>
    obtain ⟨htypes, hlimit, hmax, hne, hu, hany, htasks⟩ := h.concurrency c rfl
    simp only [inputType, Option.some.injEq] at hinput
    subst hinput
    have hcount := hcount nofun
    dsimp only at hkind
    simp only [Control.body?, Option.bind] at htimeout
    complete_simp
    refine ⟨htypes, by simpa using hlimit, by simpa using hmax, by simpa using hne, unique_of_nodup hu,
      List.any_eq_true.2 hany, (), Codec.forIn_ok_of_yield fun task ht => ?_, c.input, rfl, ?_⟩
    · simp [validateTask_of_normal (htasks task ht), bind, Except.bind, pure, Except.pure]
    · split
      · rename_i hsome
        complete_simp
        exact ⟨by simpa using hcount.2 hsome, hkind, htimeout _⟩
      · complete_simp
        exact ⟨by simpa using hcount.1, hkind, htimeout _⟩

theorem validateWorkflow_of_normal {w : Workflow} (h : w.Normal p) : p.validateWorkflow w = .ok () := by
  have hacyclic : w.acyclic = true := by
    obtain ⟨rank, hrank⟩ := h.acyclic
    refine acyclic_of_rank (rank := rank) (fun e he => ?_) (by simp)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    exact hrank c hc
  have hconnections : ∀ c ∈ w.connections, p.validateConnection w c = .ok () :=
    fun c hc => validateConnection_of_normal (h.connections c hc)
  have hplacements : ∀ pl ∈ w.placements, p.validatePlacement w pl = .ok () :=
    fun pl hpl => validatePlacement_of_normal (h.placements pl hpl)
  unfold validateWorkflow
  complete_simp
  refine ⟨by simpa using h.id, by simpa using h.nonempty, by simpa using h.names, unique_of_nodup h.distinct, (),
    Codec.forIn_ok_of_yield fun c hc => by simp [hconnections c hc, bind, Except.bind, pure, Except.pure],
    hacyclic, ?_⟩
  have hloops : (∃ a, (forIn w.placements PUnit.unit fun (pl : Placement) _ => do
      p.validatePlacement w pl
      pure (ForInStep.yield PUnit.unit)) = .ok a) ∧ ∃ a, (forIn w.placements PUnit.unit fun (pl : Placement) _ =>
        if w.isEndpoint pl.name = true then do
          Validate.check (w.outputKind? p pl.name == some Kind.single)
            s!"workflow {w.id}: endpoint {pl.name} must be Single"
          pure (ForInStep.yield PUnit.unit)
        else pure (ForInStep.yield PUnit.unit)) = .ok a := by
    refine ⟨⟨(), Codec.forIn_ok_of_yield fun pl hpl => ?_⟩, (), Codec.forIn_ok_of_yield fun pl hpl => ?_⟩
    · simp [hplacements pl hpl, bind, Except.bind, pure, Except.pure]
    · split
      · rename_i hend
        simp [Validate.check, h.endpoints pl hpl hend, bind, Except.bind, pure, Except.pure]
      · rfl
  rcases hwi : w.input with _ | e
  · dsimp only
    complete_simp
    obtain ⟨⟨a, ha⟩, b, hb⟩ := hloops
    exact ⟨a, ha, b, hb⟩
  · dsimp only
    complete_simp
    obtain ⟨⟨a, ha⟩, b, hb⟩ := hloops
    exact ⟨(), validateEntry_of_normal (h.entry e hwi), a, ha, b, hb⟩

/-- The validator is complete: it accepts every normal definition. --/
theorem validate_of_normal (h : p.Normal) : p.validate = .ok () := by
  have hcalls : p.callsAcyclic = true := by
    obtain ⟨rank, hrank⟩ := h.calls
    refine acyclic_of_rank (rank := rank) (fun e he => ?_) (by simp)
    obtain ⟨w, hw, he⟩ := List.mem_flatMap.1 he
    obtain ⟨pl, hpl, he⟩ := List.mem_flatMap.1 he
    obtain ⟨id, hid, rfl⟩ := List.mem_map.1 he
    exact hrank w hw pl hpl id hid
  have hdiscard : (!p.transforms.any (·.id == TransformRef.discardName)) = true := by
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    exact h.discard
  unfold validate
  complete_simp
  refine ⟨unique_of_nodup h.functionIds, unique_of_nodup h.judgeIds, unique_of_nodup h.transformIds, hdiscard,
    unique_of_nodup h.workflowIds, h.main, hcalls, (), Codec.forIn_ok_of_yield fun f hf => ?_,
    (), Codec.forIn_ok_of_yield fun j hj => ?_, (), Codec.forIn_ok_of_yield fun t ht => ?_,
    (), Codec.forIn_ok_of_yield fun w hw => ?_⟩
  · have : validateFunction f = .ok () := by
      unfold validateFunction
      complete_simp
      exact ⟨by simpa using (h.functions f hf).1, (h.functions f hf).2⟩
    simp [this, bind, Except.bind, pure, Except.pure]
  · have : validateJudge j = .ok () := by
      unfold validateJudge
      complete_simp
      exact ⟨by simpa using (h.judges j hj).1, by simpa using (h.judges j hj).2⟩
    simp [this, bind, Except.bind, pure, Except.pure]
  · have : validateTransform t = .ok () := by
      unfold validateTransform
      complete_simp
      exact ⟨by simpa using (h.transforms t ht).1, by simpa using (h.transforms t ht).2⟩
    simp [this, bind, Except.bind, pure, Except.pure]
  · simp [validateWorkflow_of_normal (h.workflows w hw), bind, Except.bind, pure, Except.pure]

/-- Validation accepts exactly the normal definitions. --/
theorem validate_eq_ok_iff : p.validate = .ok () ↔ p.Normal :=
  ⟨normal_of_validate, validate_of_normal⟩

end Definition

end Suimon

namespace Suimon.Codec

/-- The canonical form of a definition that validation accepts decodes back to it. --/
theorem definition_definitionWire_of_validate {p : Definition} (h : p.validate = .ok ()) :
    definition (definitionWire p).toJson = .ok p :=
  definition_definitionWire (Definition.normal_of_validate h)

/-- Loading the header of a record written for a definition that validation accepts, as the CLI loads a
    definition (decode, then validate), gives the definition back. --/
theorem load_definitionWire {p : Definition} (h : p.validate = .ok ()) : load (definitionWire p) = .ok p := by
  simp [load, loadJson, definition_definitionWire_of_validate h, h, bind, Except.bind, pure, Except.pure]

/-- The canonical form is injective on the definitions that validation accepts, so the header of a
    record holds the canonical form of at most one of them (§12.1). --/
theorem definitionWire_inj {p q : Definition} (hp : p.validate = .ok ()) (hq : q.validate = .ok ()) :
    definitionWire p = definitionWire q ↔ p = q :=
  definitionWire_inj_of_expressible (Definition.normal_of_validate hp).expressible
    (Definition.normal_of_validate hq).expressible

/-- Every definition `load` reads passes validation. --/
theorem validate_of_load {w : Wire} {q : Definition} (h : load w = .ok q) : q.validate = .ok () := by
  simp only [load, loadJson] at h
  cases hd : definition w.toJson with
  | error e => simp [hd, bind, Except.bind] at h
  | ok q' =>
    cases hv : q'.validate with
    | error e => simp [hd, hv, bind, Except.bind] at h
    | ok u =>
      simp only [hd, hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hv

/-- A header whose definition `load` reads with the canonical form of a definition `p` that validation
    accepts holds `p` itself. --/
theorem load_eq_of_definitionWire {p q : Definition} (hp : p.validate = .ok ()) {w : Wire} (h : load w = .ok q)
    (hw : definitionWire q = definitionWire p) : q = p :=
  (definitionWire_inj (validate_of_load h) hp).1 hw

end Suimon.Codec
