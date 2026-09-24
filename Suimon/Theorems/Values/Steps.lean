import Suimon.Theorems.Values.Invariant
import Suimon.Theorems.Round3.CoversOpsInv
import Suimon.Theorems.Round3.ProgressInv

/-! # Typed values: every step keeps the invariant

Each operation of a conforming execution keeps `Typed`. A new value comes from the outside world,
which keeps its contracts (`TypedEnv`), or from the engine, which passes a value it holds to a place
that declares the same type: an invocation takes a delivered value or the input of its run, a call or
a run takes the input of its invocation or task, a branch passes on its input, a sub-workflow call
returns the result of its designated endpoint, and a waitStream, a Merge or a concurrency with List
output collects values of its element type (`ValueTyping.Lists`). -/

namespace Suimon.Values
open Round3 State

variable {τ : ValueTyping} {p : Definition} {s : State}

/-! ## Where an invocation's input comes from -/

theorem shape?_none_inv {w : Workflow} {name : String} (h : w.shape? p name = some .none) :
    ∃ pl, w.placement? name = some pl ∧ (∀ e, pl.control ≠ .merge e) ∧ w.isEntry name = false ∧
      w.inputs name = [] := by
  unfold Workflow.shape? at h
  simp only [option_bind_eq_some] at h
  obtain ⟨pl, hpl, h⟩ := h
  refine ⟨pl, hpl, ?_⟩
  cases hctl : pl.control <;> simp only [hctl] at h
  case merge e => simp [pure] at h
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨by simp, ?_⟩
    split at h
    · simp [pure] at h
    · rename_i hent
      refine ⟨by simpa using hent, ?_⟩
      split at h
      · assumption
      · split at h <;> simp [pure] at h
      · simp at h

theorem isEntry_eq_true {w : Workflow} {name : String} (h : w.isEntry name = true) :
    ∃ e, w.input = some e ∧ e.placement = name := by
  unfold Workflow.isEntry at h
  cases hin : w.input with
  | none => simp [hin] at h
  | some e => exact ⟨e, rfl, by simpa [hin] using h⟩

theorem shape?_entry_inv {w : Workflow} {name : String} (h : w.shape? p name = some .entry) :
    ∃ pl, w.placement? name = some pl ∧ ∃ e, w.input = some e ∧ e.placement = name := by
  unfold Workflow.shape? at h
  simp only [option_bind_eq_some] at h
  obtain ⟨pl, hpl, h⟩ := h
  refine ⟨pl, hpl, ?_⟩
  cases hctl : pl.control <;> simp only [hctl] at h
  case merge e => simp [pure] at h
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i hent
      exact isEntry_eq_true hent
    · split at h
      · simp [pure] at h
      · split at h <;> simp [pure] at h
      · simp at h

theorem shape?_merge_inv {w : Workflow} {name : String} {cs : List (Nat × Connection)}
    (h : w.shape? p name = some (.merge cs)) : cs = w.inputs name := by
  unfold Workflow.shape? at h
  simp only [option_bind_eq_some] at h
  obtain ⟨pl, hpl, h⟩ := h
  cases hctl : pl.control <;> simp only [hctl] at h
  case merge e => simpa [pure] using h.symm
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · simp [pure] at h
    · split at h
      · simp [pure] at h
      · split at h <;> simp [pure] at h
      · simp at h

/-- A Single connection resolves to the outcome of its first delivery. -/
theorem resolveSingle_value_input {path : Path} {i : Nat} {c : Connection} {source : ResultId}
    {input : Option Value} (h : s.resolveSingle path i c = .value source input) :
    ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = i ∧
      ((∃ v, d.outcome = .value v ∧ input = some v) ∨ (d.outcome = .trigger ∧ input = none)) := by
  unfold State.resolveSingle at h
  split at h
  · rename_i d rest hds
    have hd : d ∈ s.deliveriesOn path i := by rw [hds]; exact List.mem_cons_self
    simp only [State.deliveriesOn, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hd
    obtain ⟨hd, hrun, hconn⟩ := hd
    split at h <;> rename_i hout
    · simp only [State.Resolution.value.injEq] at h
      exact ⟨d, hd, hrun, hconn, Or.inl ⟨_, hout, h.2.symm⟩⟩
    · simp only [State.Resolution.value.injEq] at h
      exact ⟨d, hd, hrun, hconn, Or.inr ⟨hout, h.2.symm⟩⟩
    · simp at h
  · split at h
    · simp at h
    · split at h <;> simp at h

/-- A typed delivery on the input connection of a placement fits what the placement takes. -/
theorem DeliveryTyped.input {d : Delivery} (h : DeliveryTyped τ p s d) {w : Workflow} {c : Connection}
    {name : String} {pl : Placement} (hw : s.workflow? p d.run = some w) (hc : w.connections[d.connection]? = some c)
    (hct : c.target = name) (hpl : w.placement? name = some pl) :
    ∃ x, p.inputType pl.control = some x ∧ τ.DeliveredFits d.outcome x := by
  obtain ⟨w', c', pl', x, hw', hc', hpl', hx, hfits⟩ := h
  rw [hw] at hw'
  cases hw'
  rw [hc] at hc'
  cases hc'
  rw [hct, hpl] at hpl'
  cases hpl'
  exact ⟨x, hx, hfits⟩

theorem fits_of_delivered {d : Delivery} {x : Option ValueType} {input : Option Value} (h : τ.DeliveredFits d.outcome x)
    (hout : (∃ v, d.outcome = .value v ∧ input = some v) ∨ (d.outcome = .trigger ∧ input = none)) :
    τ.Fits input x := by
  rcases hout with ⟨v, hv, rfl⟩ | ⟨hv, rfl⟩
  · rw [hv] at h
    exact h
  · rw [hv] at h
    subst h
    trivial

/-- The input an invocation takes fits what its placement takes: nothing for a placement without
    input, the input of its run for the entry, and a delivered value otherwise (§3.1, §3.2). -/
theorem invocationInput_typed (valid : p.validate = .ok ()) (h : Typed τ p s) {path : Path} {r : Run}
    {w : Workflow} {name : String} {pl : Placement} {trigger : Option ResultId} {input : Option Value}
    (hr : s.run? path = some r) (hw : p.workflow? r.workflow = some w) (hpl : w.placement? name = some pl)
    (hinput : Step.invocationInput p s r w name trigger = .ok input) :
    ∃ x, p.inputType pl.control = some x ∧ τ.Fits input x := by
  obtain ⟨hrm, rfl⟩ := State.run?_eq_some hr
  have hwm := (Definition.workflow?_eq_some hw).1
  have hplm := Workflow.placement?_eq_some hpl
  have hwN := (Definition.normal_of_validate valid).workflows w hwm
  have hws : s.workflow? p r.path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
  rcases Step.invocationInput_inv hinput with ⟨hsh, -, rfl⟩ | ⟨hsh, -, rfl⟩ |
      ⟨i, c, source, hsh, -, hres⟩ | ⟨i, c, source, d, hsh, -, hd, hout⟩
  · obtain ⟨pl', hpl', hnm, hent, hinputs⟩ := shape?_none_inv hsh
    rw [hpl] at hpl'
    cases hpl'
    obtain ⟨x, hx, hcount⟩ := (hwN.placements pl hplm.1).inputs
    refine ⟨x, hx, ?_⟩
    have hinc : w.incoming name = [] := by rw [← Delivery.inputs_map_snd, hinputs]; rfl
    cases x with
    | none => trivial
    | some T =>
      have := (hcount hnm).2 rfl
      simp [Workflow.inputCount, hplm.2, hinc, hent] at this
  · obtain ⟨pl', hpl', e, he, hep⟩ := shape?_entry_inv hsh
    rw [hpl] at hpl'
    cases hpl'
    obtain ⟨pl₂, hpl₂, -, hx⟩ := (hwN.entry e he).placement
    rw [hep, hpl] at hpl₂
    cases hpl₂
    obtain ⟨w', hw', hfits⟩ := h.runs r hrm
    rw [hw] at hw'
    cases hw'
    rw [he] at hfits
    exact ⟨_, hx, hfits⟩
  · obtain ⟨hci, hct⟩ := Routing.shape?_connection (Or.inl hsh)
    obtain ⟨d, hd, hdrun, hdconn, hout⟩ := resolveSingle_value_input hres
    obtain ⟨x, hx, hfits⟩ := (h.deliveries d hd).input (hdrun ▸ hws) (hdconn ▸ hci) hct hpl
    exact ⟨x, hx, fits_of_delivered hfits hout⟩
  · obtain ⟨hci, hct⟩ := Routing.shape?_connection (Or.inr hsh)
    obtain ⟨hdm, hdrun, hdconn, -⟩ := State.delivery?_eq_some hd
    obtain ⟨x, hx, hfits⟩ := (h.deliveries d hdm).input (hdrun ▸ hws) (hdconn ▸ hci) hct hpl
    exact ⟨x, hx, fits_of_delivered hfits hout⟩

/-! ## The list a waitStream or a Merge collects -/

/-- A settlement that accepts a result aggregates a waitStream or a Merge: its value is the list of
    the values delivered on its input connections (§9). -/
theorem settleOutcome_aggregate {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    {x : Settled} {res : Result} (h : s.settleOutcome path pl shape kind = some (x, some res)) :
    ∃ element vs, res.value = listValue vs ∧
      ((pl.control = .waitStream element ∧ ∃ i c, shape = .stream i c ∧
          ∀ v ∈ vs, ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = i ∧ d.outcome = .value v) ∨
       (pl.control = .merge element ∧ ∃ cs, shape = .merge cs ∧
          ∀ v ∈ vs, ∃ jc ∈ cs, ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = jc.1 ∧ d.outcome = .value v)) := by
  unfold State.settleOutcome at h
  simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
  obtain ⟨-, h⟩ := h
  cases hc : pl.control
  case waitStream element =>
    cases hsh : shape
    case stream i c =>
      simp only [hc, hsh, option_bind_eq_some] at h
      obtain ⟨ended, -, h⟩ := h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨element, _, rfl, Or.inl ⟨rfl, i, c, rfl, fun v hv => ?_⟩⟩
        obtain ⟨d, hd, hdv⟩ := List.mem_filterMap.mp hv
        simp only [State.deliveriesOn, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨hd, hrun, hconn⟩ := hd
        refine ⟨d, hd, hrun, hconn, ?_⟩
        split at hdv
        · rename_i v' hv'
          simp only [Option.some.injEq] at hdv
          rw [hv', hdv]
        · simp at hdv
    all_goals simp [hc, hsh] at h
  case merge element =>
    cases hsh : shape
    case merge cs =>
      simp only [hc, hsh, option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h
      obtain ⟨-, h⟩ := h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨element, _, rfl, Or.inr ⟨rfl, cs, rfl, fun v hv => ?_⟩⟩
        obtain ⟨r, hr, hrv⟩ := List.mem_filterMap.mp hv
        obtain ⟨jc, hjc, rfl⟩ := List.mem_map.mp hr
        split at hrv
        · rename_i src v' hres
          simp only [Option.some.injEq] at hrv
          subst hrv
          obtain ⟨d, hd, hrun, hconn, hout⟩ := resolveSingle_value_input hres
          rcases hout with ⟨v'', hv'', hsome⟩ | ⟨-, hnone⟩
          · simp only [Option.some.injEq] at hsome
            exact ⟨jc, hjc, d, hd, hrun, hconn, hsome ▸ hv''⟩
          · cases hnone
        · simp at hrv
    all_goals simp [hc, hsh] at h
  -- A branch, a call and a concurrency settle without a result.
  all_goals
    simp only [hc] at h
    repeat' (first
      | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h; done)
      | (simp only [option_bind_eq_some, option_guard_eq_some, exists_unit_iff] at h)
      | obtain ⟨_, _, h⟩ := h
      | obtain ⟨_, h⟩ := h
      | split at h)

/-! ## Composite updates -/

/-- Accepting a value of a call keeps the invariant when the value has the result type of the owner's
    placement, or the element type of the owner's task. -/
theorem Typed.accept (h : Typed τ p s) {c : Call} {index : Nat} {value : Value} {arm : Option String} {t : State}
    (ha : s.accept c index value arm = .ok t)
    (hres : c.task = none → ∀ i, s.invocation? c.owner = some i → ∃ w pl T, s.workflow? p i.run = some w ∧
      w.placement? i.placement = some pl ∧ p.resultType pl.control = some T ∧ τ.HasType value T)
    (htr : ∀ name, c.task = some name → ∃ e ∈ s.executions, e.id = c.owner ∧ ∃ cc spec T,
      s.concurrencyOf p e = .ok cc ∧ cc.tasks.find? (·.name == name) = some spec ∧
      p.bodyElement p.depth spec.body = some T ∧ τ.HasType value T) :
    Typed τ p t := by
  rcases State.accept_eq_ok.mp ha with ⟨hn, i, hi, -, rfl⟩ | ⟨name, hn, -, rfl⟩
  · exact h.appendResult (hres hn i hi)
  · obtain ⟨e, he, heid, cc, spec, T, hcc, hspec, hT, hv⟩ := htr name hn
    exact h.appendTaskResult ⟨e, he, heid, cc, spec, T, hcc, hspec, hT, hv, fun v hv' => by cases hv'⟩

theorem Typed.settleOwner (h : Typed τ p s) (wk : s.WellKeyed) {c : Call} {inv : InvocationStatus}
    {task : TaskStatus} {t : State} (ho : s.settleOwner c inv task = .ok t) (htask : task ≠ .ready) : Typed τ p t := by
  rcases State.settleOwner_eq_ok.mp ho with ⟨-, i, hi, rfl⟩ | ⟨name, e, ts, -, he, hts, rfl⟩
  · exact h.setInvocation (State.invocation?_eq_some hi).1 rfl rfl rfl
  · exact h.setTaskStatus wk (State.execution?_eq_some he).1 (find?_key_eq_some hts).1 htask

theorem Typed.cancelOwner (h : Typed τ p s) (wk : s.WellKeyed) {c : Call} {t : State}
    (ho : s.cancelOwner c = .ok t) : Typed τ p t := by
  rcases State.cancelOwner_eq_ok.mp ho with ⟨-, i, hi, rfl⟩ | ⟨name, e, ts, -, he, hts, rfl⟩
  · split
    · exact h.setInvocation (State.invocation?_eq_some hi).1 rfl rfl rfl
    · exact h
  · split
    · exact h.setTaskStatus wk (State.execution?_eq_some he).1 (find?_key_eq_some hts).1 (by decide)
    · exact h

theorem Typed.failCall (h : Typed τ p s) (wk : s.WellKeyed) {c : Call} {status : CallStatus} {cause : Cause}
    {t : State} (hc : c ∈ s.calls) (hf : s.failCall c status cause = .ok t) : Typed τ p t := by
  obtain ⟨f, s', -, hso, rfl⟩ := State.failCall_eq_ok.mp hf
  exact ((h.setCall (c' := { c with status }) hc rfl rfl).settleOwner (wk.setCall _) hso (by simp)).fail f c.policy

/-- A state that differs only in its status, flags, settlements or failures is typed alike. -/
theorem Typed.of_records {t : State} (h : Typed τ p s) (hr : t.runs = s.runs) (hi : t.invocations = s.invocations)
    (hc : t.calls = s.calls) (he : t.executions = s.executions) (hres : t.results = s.results)
    (htr : t.taskResults = s.taskResults) (hd : t.deliveries = s.deliveries) : Typed τ p t :=
  h.of_frame (Keeps.of_eq hr he) (fun r hr' => h.runs r (hr ▸ hr')) (fun c hc' => h.calls c (hc ▸ hc'))
    (same_invocations hi) (same_executions he) (fun _ hr' => Or.inl (hres ▸ hr')) (same_taskResults htr)
    (fun _ hd' => Or.inl (hd ▸ hd'))

theorem Typed.empty : Typed τ p {} :=
  ⟨nofun, nofun, nofun, nofun, nofun, nofun, nofun⟩

/-! ## What owns a call, a run and a result -/

/-- A Stream call calls a function: a judge's call returns an arm. -/
theorem target_function_of_stream (hr : Reachable p s) {c : Call} (hc : c ∈ s.calls) (hstream : c.stream = true) :
    ∃ f, c.target = .function f := by
  have inv := Delivery.Reachable.inv hr
  have created := CoversOpsAux.Reachable.created hr
  rcases inv.own.calls c hc with ⟨-, -, i, -, -, w, pl, -, -, ⟨f, d, -, -, htarget, -⟩ | ⟨j, arms, -, -, hst⟩⟩ |
      ⟨name, hn, -, e, he, heid, -, spec, f', hspec, -⟩
  · exact ⟨f, htarget⟩
  · rw [hst] at hstream
    cases hstream
  · obtain ⟨-, -, f₀, -, -, -, htarget, -⟩ := (created.taskCall c hc name hn e he heid).2 spec hspec
    exact ⟨f₀, htarget⟩

/-- A value that a call of a function returns or yields, of the function's output element type, has
    the result type of the placement of the invocation that owns the call, or the element type of the
    body of the task that owns it (§4.1, §8.1). -/
theorem Typed.acceptFunction (h : Typed τ p s) (hr : Reachable p s) {c : Call} (hc : c ∈ s.calls) {f : String}
    {decl : FunctionDecl} (htarget : c.target = .function f) (hdecl : p.function? f = some decl) {value : Value}
    (hv : τ.HasType value decl.output.element) {index : Nat} {t : State} (ha : s.accept c index value = .ok t) :
    Typed τ p t := by
  have inv := Delivery.Reachable.inv hr
  have created := CoversOpsAux.Reachable.created hr
  refine h.accept ha (fun hn i hi => ?_) (fun name hn => ?_)
  · obtain ⟨him, hid⟩ := State.invocation?_eq_some hi
    rcases inv.own.calls c hc with ⟨-, -, i', hi', hid', w, pl, hw, hpl, hbody⟩ | ⟨name, hn', -⟩
    · obtain rfl : i' = i := inv.wk.invocation_eq_of_id hi' him (hid'.trans hid.symm)
      rcases hbody with ⟨f', d, hctl, hd, htarget', -⟩ | ⟨j, arms, -, htarget', -⟩
      · rw [htarget] at htarget'
        cases htarget'
        rw [hdecl] at hd
        cases hd
        exact ⟨w, pl, _, hw, hpl, by rw [hctl]; exact resultType_function hdecl, hv⟩
      · rw [htarget] at htarget'
        cases htarget'
    · rw [hn] at hn'
      cases hn'
  · rcases inv.own.calls c hc with ⟨hn', -⟩ | ⟨name', hn', -, e, he, heid, -, spec, f', hspec, -⟩
    · rw [hn] at hn'
      cases hn'
    · obtain rfl : name' = name := Option.some.inj (hn'.symm.trans hn)
      obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec
      obtain ⟨-, -, f₀, decl₀, hbody, hdecl₀, htarget₀, -⟩ := (created.taskCall c hc name' hn e he heid).2 spec hspec
      rw [htarget] at htarget₀
      cases htarget₀
      rw [hdecl] at hdecl₀
      cases hdecl₀
      exact ⟨e, he, heid, cc, spec, _, hcc, hfind, by rw [hbody]; exact bodyElement_function hdecl, hv⟩

/-- The list that a waitStream or a Merge accepts has the list type of its element type: every value
    in it was delivered to the placement, which takes the element type (§9). -/
theorem settle_result_typed (lists : τ.Lists) (h : Typed τ p s) {path : Path} {run : Run} {w : Workflow}
    {name : String} {pl : Placement} {shape : Workflow.Shape} {kind : Kind} {x : Settled} {res : Result}
    (hrun : s.run? path = some run) (hw : p.workflow? run.workflow = some w) (hpl : w.placement? name = some pl)
    (hshape : w.shape? p name = some shape) (hout : s.settleOutcome path pl shape kind = some (x, some res)) :
    ResultTyped τ p s res := by
  have hws : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨run, hrun, hw⟩
  obtain ⟨-, -, -, hres⟩ := State.settleOutcome_some hout
  obtain ⟨-, -, hrrun, hrpl, -⟩ := hres res rfl
  have hname := (Workflow.placement?_eq_some hpl).2
  obtain ⟨element, vs, hval, hcases⟩ := settleOutcome_aggregate hout
  have hv : ∀ v, (∃ j c, w.connections[j]? = some c ∧ c.target = name ∧
      ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = j ∧ d.outcome = .value v) →
      p.inputType pl.control = some (some element) → τ.HasType v element := by
    rintro v ⟨j, c, hc, hct, d, hd, hdrun, hdconn, hdv⟩ hin
    obtain ⟨x', hx', hfits⟩ := (h.deliveries d hd).input (by rw [hdrun]; exact hws) (by rw [hdconn]; exact hc) hct hpl
    rw [hin] at hx'
    cases hx'
    rw [hdv] at hfits
    exact hfits
  have hplace : w.placement? res.placement = some pl := by rw [hrpl, hname]; exact hpl
  have hwres : s.workflow? p res.run = some w := by rw [hrrun]; exact hws
  rcases hcases with ⟨hctl, i, c, rfl, hvs⟩ | ⟨hctl, cs, rfl, hvs⟩
  · obtain ⟨hci, hct⟩ := Routing.shape?_connection (Or.inr hshape)
    refine ⟨w, pl, .list element, hwres, hplace, by rw [hctl]; rfl, ?_⟩
    rw [hval]
    refine lists vs element fun v hv' => hv v ?_ (by rw [hctl]; rfl)
    obtain ⟨d, hd, hdrun, hdconn, hdv⟩ := hvs v hv'
    exact ⟨i, c, hci, hct, d, hd, hdrun, hdconn, hdv⟩
  · have hcs := shape?_merge_inv hshape
    refine ⟨w, pl, .list element, hwres, hplace, by rw [hctl]; rfl, ?_⟩
    rw [hval]
    refine lists vs element fun v hv' => hv v ?_ (by rw [hctl]; rfl)
    obtain ⟨jc, hjc, d, hd, hdrun, hdconn, hdv⟩ := hvs v hv'
    rw [hcs] at hjc
    obtain ⟨hjcc, hjct⟩ := Routing.mem_inputs hjc
    exact ⟨jc.1, jc.2, hjcc, hjct, d, hd, hdrun, hdconn, hdv⟩

/-- The run of a sub-workflow call runs the workflow that the invoking placement calls (§4.5). -/
theorem run_workflow_of_call (hr : Reachable p s) {r : Run} (hrm : r ∈ s.runs) {i : Invocation}
    (him : i ∈ s.invocations) (hown : r.owner = some i.id) (htask : r.task = none) {w : Workflow}
    {pl : Placement} {wf out : String} (hw : s.workflow? p i.run = some w) (hpl : w.placement? i.placement = some pl)
    (hctl : pl.control = .call (.workflow wf out)) : r.workflow = wf := by
  have inv := Delivery.Reachable.inv hr
  obtain ⟨-, hrun', -⟩ := invocation_body hr i him w pl hw hpl
  obtain ⟨r', hr', hpath', -, -, hwf'⟩ := hrun' wf out hctl
  rcases inv.own.runs r hrm with ⟨hno, -, -⟩ | ⟨-, i₂, hi₂, hown₂, hpath₂, -⟩ | ⟨name, htask', -⟩
  · rw [hown] at hno
    cases hno
  · obtain rfl : i₂ = i := inv.wk.invocation_eq_of_id hi₂ him (Option.some.inj (hown₂.symm.trans hown))
    obtain rfl : r = r' := inv.wk.run_eq_of_path hrm hr' (hpath₂.trans hpath'.symm)
    exact hwf'
  · rw [htask] at htask'
    cases htask'

end Suimon.Values
