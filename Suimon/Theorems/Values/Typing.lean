import Suimon.Theorems.Normal
import Suimon.Theorems.Round3.Conformance

/-! # Typed values: the typing and the contracts of the outside world

Values are opaque identities in the model (§4.4, §15.1): the engine moves them and never reads them.
The theorems of `Suimon/Theorems/Static.lean` therefore relate only declarations: the types of a
source, a transform and a target agree. This directory states the same rows of §15.2 for values.

A typing of values is a parameter (`ValueTyping`): a relation between values and types that the
model never computes. The outside world keeps its typing contracts (`TypedEnv`, §15.3): the caller
passes an input of the declared type, a function returns and yields values of its declared element
type, and a declared transform maps a value of its input type to a value of its output type. Under
these contracts every value that a conforming execution of a valid definition passes has the type
that its place declares (`Suimon/Theorems/Values/Rows.lean`).

This file holds the typing, the contracts, and facts about the declared types of a valid
definition. -/

namespace Suimon.Values
open Round3

/-- Which values have which types. The model never inspects a value, so the relation is a parameter
    of the theorems: they hold for every typing under which the outside world keeps its contracts. -/
structure ValueTyping where
  HasType : Value → ValueType → Prop

namespace ValueTyping
variable (τ : ValueTyping)

/-- A value, or its absence, fits a declared input: no value where the declaration takes none, and a
    value of the declared type where it takes one (§3.1, §4.2). -/
def Fits : Option Value → Option ValueType → Prop
  | none, none => True
  | some v, some T => τ.HasType v T
  | _, _ => False

/-- The identity of a list of values of type `T` has type `List<T>`. The engine builds the lists of a
    waitStream, a Merge and a concurrency with List output as the identity of their elements
    (`listValue`, §8.3, §9); this is how the typing reads such an identity. -/
def Lists : Prop :=
  ∀ (values : List Value) (T : ValueType), (∀ v ∈ values, τ.HasType v T) → τ.HasType (listValue values) (.list T)

/-- A delivery fits the input of its target: a value of the input type, or a trigger for a target
    without input (§3.2, §4.2). A failed transform delivers nothing. -/
def DeliveredFits : Delivered → Option ValueType → Prop
  | .value v, input => τ.Fits (some v) input
  | .trigger, input => input = none
  | .failed, _ => True

variable {τ}

theorem fits_some {v : Value} {input : Option ValueType} :
    τ.Fits (some v) input ↔ ∃ T, input = some T ∧ τ.HasType v T := by
  cases input <;> simp [Fits]

theorem fits_none {input : Option ValueType} : τ.Fits none input ↔ input = none := by
  cases input <;> simp [Fits]

end ValueTyping

/-- The typing contracts of the outside world (§3.1, §4.1, §4.2, §8.1, §15.3). The behavior answers by
    identities (`Behavior`), so each contract is stated, like `Env.Fits`, for the calls, results and
    executions of the conforming executions of the environment. A transform is assumed to keep types
    only on a value of its input type, and a function only on an input of its input type. `discard`
    passes no value and needs no contract. -/
structure TypedEnv (p : Definition) (env : Env) (τ : ValueTyping) : Prop where
  /-- The caller passes a value of the input type that the main workflow declares (§3.1). -/
  input : ∀ w e v, p.workflow? p.main = some w → w.input = some e → env.input = some v → τ.HasType v e.valueType
  /-- A function called with an input of its input type returns, and yields, values of its output
      element type (§4.1). -/
  function : ∀ tr s, Conforming p env tr s → ∀ c ∈ s.calls, ∀ f decl, c.target = .function f →
    p.function? f = some decl → τ.Fits c.input decl.input →
      (∀ v ∈ (env.behavior.script c.id).yields, τ.HasType v decl.output.element) ∧
      (∀ v, (env.behavior.script c.id).ending = .returned v → τ.HasType v decl.output.element)
  /-- The transform of a connection, applied to a result of its source of the transform's input type,
      gives a value of its output type (§4.2). -/
  transform : ∀ tr s, Conforming p env tr s → ∀ path w index c id t, s.workflow? p path = some w →
    w.connections[index]? = some c → c.transform = .declared id → p.transform? id = some t →
    ∀ r ∈ s.results, r.run = path → r.placement = c.source → τ.HasType r.value t.input →
    ∀ v, env.behavior.transform path index r.id = some v → τ.HasType v t.output
  /-- The input transform of a task, applied to the input of its execution of the transform's input
      type, gives a value of its output type (§8.1). -/
  taskInput : ∀ tr s, Conforming p env tr s → ∀ e ∈ s.executions, ∀ name spec id t u,
    s.taskSpec p e name = .ok spec → spec.input = some (.declared id) → p.transform? id = some t →
    e.input = some u → τ.HasType u t.input →
    ∀ v, env.behavior.taskInput e.id name = some v → τ.HasType v t.output
  /-- The output transform of a task, applied to a result of the task of the transform's input type,
      gives a value of its output type (§8.1, §8.3). -/
  taskOutput : ∀ tr s, Conforming p env tr s → ∀ e ∈ s.executions, ∀ x ∈ s.taskResults, x.execution = e.id →
    ∀ spec id t, s.taskSpec p e x.task = .ok spec → spec.output = some id → p.transform? id = some t →
    τ.HasType x.value t.input →
    ∀ v, env.behavior.taskOutput e.id x.task x.index = some v → τ.HasType v t.output

/-! ## Declared types of a valid definition -/

section Declared
variable {p : Definition}

/-- More fuel never changes the element type of a body. -/
theorem bodyElement_mono : ∀ {n m : Nat} {body : Body} {T : ValueType},
    p.bodyElement n body = some T → n ≤ m → p.bodyElement m body = some T
  | 0, _, _, _, h, _ => by simp [Definition.bodyElement] at h
  | n + 1, m, body, T, h, hle => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases body with
    | function id => simpa [Definition.bodyElement] using h
    | workflow id output =>
      simp only [Definition.bodyElement, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨w, hw, pl, hpl, h⟩ := h
      refine ⟨w, hw, pl, hpl, ?_⟩
      cases hc : pl.control <;> rw [hc] at h
      case call body => exact bodyElement_mono h (by omega)
      all_goals exact h

/-- The element type of a function call is the function's output element type. -/
theorem bodyElement_function {f : String} {decl : FunctionDecl} (h : p.function? f = some decl) :
    p.bodyElement p.depth (.function f) = some decl.output.element := by
  simp [Definition.depth, Definition.bodyElement, h]

/-- The result type of a function call placement is the function's output element type. -/
theorem resultType_function {f : String} {decl : FunctionDecl} (h : p.function? f = some decl) :
    p.resultType (.call (.function f)) = some decl.output.element :=
  bodyElement_function h

/-- The element type of a call of a workflow is the result type of its designated endpoint. -/
theorem bodyElement_workflow {wf out : String} {w : Workflow} {pl : Placement} {T T' : ValueType}
    (h : p.bodyElement p.depth (.workflow wf out) = some T) (hw : p.workflow? wf = some w)
    (hpl : w.placement? out = some pl) (h' : p.resultType pl.control = some T') : T' = T := by
  simp only [Definition.depth, Definition.bodyElement, Option.bind_eq_bind, hw, hpl, Option.bind_some] at h
  cases hc : pl.control <;> rw [hc] at h h'
  case call body =>
    have := bodyElement_mono h (Nat.le_succ _)
    simp only [Definition.resultType, Definition.depth] at h'
    rw [this] at h'
    exact (Option.some.inj h').symm
  all_goals
    simp only [Definition.resultType] at h'
    dsimp only at h
    rw [h] at h'
    exact (Option.some.inj h').symm

/-- The bodies that a control calls: the body of a call, or the body of a task of a concurrency. -/
def CallsBody (control : Control) (body : Body) : Prop :=
  control = .call body ∨ ∃ c task, control = .concurrency c ∧ task ∈ c.tasks ∧ task.body = body

theorem CallsBody.normal (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows) {pl : Placement}
    (hpl : pl ∈ w.placements) {body : Body} (hb : CallsBody pl.control body) : body.Normal p := by
  have hpN := ((Definition.normal_of_validate valid).workflows w hw).placements pl hpl
  rcases hb with hb | ⟨c, task, hc, htask, rfl⟩
  · exact hpN.call body hb
  · obtain ⟨-, -, -, -, -, -, htasks⟩ := hpN.concurrency c hc
    exact (htasks task htask).body

theorem CallsBody.workflowRef {control : Control} {id out : String} (hb : CallsBody control (.workflow id out)) :
    id ∈ control.workflowRefs := by
  rcases hb with rfl | ⟨c, task, rfl, htask, hbody⟩
  · simp [Control.workflowRefs, Body.workflowRef]
  · exact List.mem_filterMap.mpr ⟨task, htask, by simp [hbody, Body.workflowRef]⟩

/-- In a valid definition, every body a placement calls has an element type: a function is declared,
    and the chain of workflows a call goes through is bounded by the call ranks (§13.1). -/
theorem bodyElement_isSome (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) {body : Body} (hb : CallsBody pl.control body) :
    (p.bodyElement p.depth body).isSome := by
  obtain ⟨rank, hlt, hedge⟩ := call_rank valid
  have normal := Definition.normal_of_validate valid
  suffices key : ∀ n, ∀ w ∈ p.workflows, p.workflows.length ≤ rank w.id + n → ∀ pl ∈ w.placements,
      ∀ body, CallsBody pl.control body → (p.bodyElement n body).isSome from
    key p.depth w hw (by have := hlt w hw; simp only [Definition.depth]; omega) pl hpl body hb
  intro n
  induction n with
  | zero =>
    intro w hw hle
    have := hlt w hw
    omega
  | succ n ih =>
    intro w hw hle pl hpl body hb
    have hbody := hb.normal valid hw hpl
    cases body with
    | function f =>
      simp only [Body.Normal] at hbody
      obtain ⟨decl, hdecl⟩ := Option.isSome_iff_exists.mp hbody
      simp [Definition.bodyElement, hdecl]
    | workflow id out =>
      obtain ⟨w', hw', hpl', -⟩ := hbody
      obtain ⟨pl', hpl'⟩ := Option.isSome_iff_exists.mp hpl'
      obtain ⟨hw'm, hw'id⟩ := Definition.workflow?_eq_some hw'
      have hrank := hedge w hw pl hpl id hb.workflowRef w' hw'm hw'id
      have hpl'm := (Workflow.placement?_eq_some hpl').1
      simp only [Definition.bodyElement, Option.bind_eq_bind, hw', hpl', Option.bind_some]
      cases hc : pl'.control with
      | call body' => exact ih w' hw'm (by omega) pl' hpl'm body' (Or.inl hc)
      | branch judge arms =>
        obtain ⟨hj, -⟩ := ((normal.workflows w' hw'm).placements pl' hpl'm).branch judge arms hc
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hj
        simp [Definition.localResult, hj]
      | waitStream e => rfl
      | merge e => rfl
      | concurrency c => rfl

/-- In a valid definition, every placement has a result type. -/
theorem resultType_isSome (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) : (p.resultType pl.control).isSome := by
  cases hc : pl.control with
  | call body => exact bodyElement_isSome valid hw hpl (Or.inl hc)
  | branch judge arms =>
    obtain ⟨hj, -⟩ := (((Definition.normal_of_validate valid).workflows w hw).placements pl hpl).branch judge arms hc
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hj
    simp [Definition.resultType, Definition.localResult, hj]
  | waitStream e => rfl
  | merge e => rfl
  | concurrency c => rfl

/-- In a valid definition, every placement declares what it takes. -/
theorem inputType_isSome (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) : ∃ input, p.inputType pl.control = some input := by
  obtain ⟨input, h, -⟩ := (((Definition.normal_of_validate valid).workflows w hw).placements pl hpl).inputs
  exact ⟨input, h⟩

end Declared

end Suimon.Values
