import Suimon.Theorems.Values.Preserve
import Suimon.Theorems.Round3.CoversViewInv

/-! # Typed values: the rows of §15.2

The rows 「型付き接続」, 「concurrencyの出力の型」 and 「外部入力の境界」 of §15.2, stated for the values of
every conforming execution of a valid definition, under the typing contracts of the outside world
(`TypedEnv`, §15.3) and the typing of list identities (`ValueTyping.Lists`). The same rows for the
declarations are `typedConnections_of_validate`, `concurrency_output_typed` and `start_boundary`
(`Suimon/Theorems/Static.lean`).

- 型付き接続: a delivered value comes from a result of the connection's source of the transform's
  input type, and has the transform's output type, which the target takes (`typed_connection`); every
  call, run and invocation takes an input of the type it declares (`typed_connection_input`); every
  result has the result type of the placement that produced it (`typed_connection_result`,
  `typed_connection_result_controls`).
- concurrencyの出力の型: every value a task puts in the output of a concurrency has the common element
  type `T` (`concurrency_output_type`).
- 外部入力の境界: the caller's input, of the main workflow's input type, is the input of the root run
  and goes to the entry placement once, without a trigger (`external_input_boundary`). -/

namespace Suimon.Values
open Round3 State

variable {τ : ValueTyping} {p : Definition} {env : Env}

/-! ## 外部入力の境界 -/

/-- The root run runs the main workflow with the caller's input, which the main workflow's input
    admits (§3.1). -/
theorem root_run {tr : List Op} {s : State} (h : Conforming p env tr s) :
    ∀ r ∈ s.runs, r.path = [] → r.workflow = p.main ∧ r.input = env.input ∧
      ∃ w, p.workflow? p.main = some w ∧ w.input.isSome = env.input.isSome := by
  induction h with
  | nil => intro r hr; cases hr
  | @snoc tr s t op hc hop hs _ ih =>
    by_cases hst : s.started = true
    · intro r hr hpath
      rcases Delivery.step_runs_back (Or.inr hst) hs r hr with ⟨r₀, hr₀, a1, a2, a3, -⟩ | ⟨-, -, hnew⟩
      · obtain ⟨b1, b2, b3⟩ := ih r₀ hr₀ (a1.trans hpath)
        exact ⟨a2 ▸ b1, a3 ▸ b2, b3⟩
      · rcases hnew with ⟨hst', -⟩ | ⟨-, i, -, -, -, hp, -⟩ | ⟨name, e, ts, spec, wf, out, -, -, -, -, -, -, -, -, hp, -⟩
        · rw [hst] at hst'
          cases hst'
        · rw [hp] at hpath
          exact absurd hpath (Key.child_ne_nil _)
        · rw [hp] at hpath
          exact absurd hpath (Key.child_ne_nil _)
    · obtain ⟨input, rfl, rfl⟩ := ProgressInvAux.step_not_started hs (by simpa using hst)
      obtain ⟨-, -, w, hw, hin, -⟩ := Step.start_inv hs
      have hinput : input = env.input := hop
      subst hinput
      obtain rfl := (Delivery.Reachable.inv hc.reachable).fresh (by simpa using hst)
      intro r hr _
      rw [List.mem_singleton.mp hr]
      exact ⟨rfl, rfl, w, hw, hin⟩

/-- The shape of an entry: the entry of its workflow, or a Merge, which the validator rejects. -/
theorem shape?_of_isEntry {w : Workflow} {name : String} (hent : w.isEntry name = true) {sh : Workflow.Shape}
    (h : w.shape? p name = some sh) : sh = .entry ∨ ∃ cs, sh = .merge cs := by
  unfold Workflow.shape? at h
  simp only [option_bind_eq_some] at h
  obtain ⟨pl, -, h⟩ := h
  cases hctl : pl.control <;> simp only [hctl] at h
  case merge e =>
    simp only [↓reduceIte, pure, Option.some.injEq] at h
    exact Or.inr ⟨_, h.symm⟩
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, hent, pure, Option.some.injEq] at h
    exact Or.inl h.symm

/-- The entry of a run takes the run's input, without a trigger (§3.1, §4.5). -/
theorem entry_input {s : State} (h : Reachable p s) : ∀ i ∈ s.invocations, ∀ r ∈ s.runs, r.path = i.run →
    ∀ w e, p.workflow? r.workflow = some w → w.input = some e → e.placement = i.placement →
      i.trigger = none ∧ i.input = r.input := by
  induction h with
  | empty => intro i hi; cases hi
  | @step s t op hr hs ih =>
    have inv := Delivery.Reachable.inv hr
    -- A run of `t` at the path of a run of `s` is that run.
    have old : ∀ path, (s.run? path).isSome → ∀ r ∈ t.runs, r.path = path →
        ∃ r₀ ∈ s.runs, r₀.path = r.path ∧ r₀.workflow = r.workflow ∧ r₀.input = r.input := by
      intro path hpath r hr' hrp
      rcases Delivery.step_runs_back (Delivery.runs_nil_or_started inv) hs r hr' with
        ⟨r₀, hr₀, a1, a2, a3, -⟩ | ⟨hfresh, -⟩
      · exact ⟨r₀, hr₀, a1, a2, a3⟩
      · rw [hrp] at hfresh
        rw [hfresh] at hpath
        cases hpath
    intro i hi r hrt hpath w e hw he hep
    rcases Delivery.step_invocations_back hs i hi with ⟨i₀, hi₀, a1, a2, a3, a4, a5⟩ | hnew
    · obtain ⟨-, w₀, -, -, hw₀, -⟩ := inv.own.invocations i₀ hi₀
      obtain ⟨r₁, hr₁, -⟩ := Delivery.workflow?_iff.mp hw₀
      obtain ⟨r₀, hr₀, b1, b2, b3⟩ := old i.run (by rw [← a2, hr₁]; rfl) r hrt hpath
      obtain ⟨c1, c2⟩ := ih i₀ hi₀ r₀ hr₀ (b1.trans (hpath.trans a2.symm)) w e (b2 ▸ hw) he (hep.trans a3.symm)
      exact ⟨a4 ▸ c1, a5 ▸ c2.trans b3⟩
    · obtain ⟨-, -, r', w', pl, hr', -, hw', -, -, hinput, -⟩ := hnew
      obtain ⟨hr'm, hr'p⟩ := State.run?_eq_some hr'
      obtain ⟨r₀, hr₀, b1, b2, b3⟩ := old i.run (by rw [hr']; rfl) r hrt hpath
      obtain rfl : r₀ = r' := inv.wk.run_eq_of_path hr₀ hr'm (b1.trans (hpath.trans hr'p.symm))
      rw [b2, hw] at hw'
      cases hw'
      have hent : w.isEntry i.placement = true := by simp [Workflow.isEntry, he, hep]
      rcases Step.invocationInput_inv hinput with ⟨hsh, -, -⟩ | ⟨-, htr, hin⟩ | ⟨j, c, src, hsh, -, -⟩ |
          ⟨j, c, src, d, hsh, -⟩
      · rcases shape?_of_isEntry hent hsh with h' | ⟨cs, h'⟩ <;> cases h'
      · exact ⟨htr, hin.trans b3⟩
      · rcases shape?_of_isEntry hent hsh with h' | ⟨cs, h'⟩ <;> cases h'
      · rcases shape?_of_isEntry hent hsh with h' | ⟨cs, h'⟩ <;> cases h'

/-- **外部入力の境界** (§3.1, §15.2), for values. The caller's input is the input of the root run, which
    runs the main workflow, and has the input type that the main workflow declares. The entry placement
    takes that type and has no input connection; each invocation of it in the root run takes the
    caller's input as it is, without a trigger, and there is at most one. The caller builds no internal
    connection, Single/Stream kind or end of a Stream. -/
theorem external_input_boundary (valid : p.validate = .ok ()) (typed : TypedEnv p env τ) {tr : List Op}
    {s : State} (h : Conforming p env tr s) :
    ∀ r ∈ s.runs, r.path = [] → r.workflow = p.main ∧ r.input = env.input ∧
      ∃ w, p.workflow? p.main = some w ∧ τ.Fits env.input (w.input.map (·.valueType)) ∧
        ∀ e, w.input = some e →
          (∃ pl, w.placement? e.placement = some pl ∧ p.inputType pl.control = some (some e.valueType) ∧
            w.incoming e.placement = []) ∧
          (∀ i ∈ s.invocations, i.run = [] → i.placement = e.placement → i.trigger = none ∧ i.input = env.input) ∧
          ∀ i ∈ s.invocations, ∀ i' ∈ s.invocations, i.run = [] → i'.run = [] → i.placement = e.placement →
            i'.placement = e.placement → i = i' := by
  have hr := h.reachable
  have inv := Delivery.Reachable.inv hr
  intro r hrm hpath
  obtain ⟨hwf, hin, w, hw, hsome⟩ := root_run h r hrm hpath
  refine ⟨hwf, hin, w, hw, ?_, fun e he => ?_⟩
  · cases hwi : w.input with
    | none =>
      rw [hwi] at hsome
      cases hv : env.input with
      | none => trivial
      | some v => rw [hv] at hsome; cases hsome
    | some e =>
      rw [hwi] at hsome
      cases hv : env.input with
      | none => rw [hv] at hsome; cases hsome
      | some v => exact typed.input w e v hw hwi hv
  · have hwm := (Definition.workflow?_eq_some hw).1
    obtain ⟨-, ⟨pl, hpl, -, hx⟩, halone⟩ := ((Definition.normal_of_validate valid).workflows w hwm).entry e he
    have hentry : ∀ i ∈ s.invocations, i.run = [] → i.placement = e.placement →
        i.trigger = none ∧ i.input = env.input := by
      intro i hi hirun hipl
      obtain ⟨htr, hiin⟩ := entry_input hr i hi r hrm (hpath.trans hirun.symm) w e (hwf ▸ hw) he hipl.symm
      exact ⟨htr, hiin.trans hin⟩
    refine ⟨⟨pl, hpl, hx, halone⟩, hentry, fun i hi i' hi' hirun hi'run hipl hi'pl => ?_⟩
    obtain ⟨hid, -⟩ := inv.own.invocations i hi
    obtain ⟨hid', -⟩ := inv.own.invocations i' hi'
    refine inv.wk.invocation_eq_of_id hi hi' ?_
    rw [hid, hid', hirun, hi'run, hipl, hi'pl, (hentry i hi hirun hipl).1, (hentry i' hi' hi'run hi'pl).1]

/-! ## 型付き接続 -/

/-- **型付き接続** (§4.2, §6, §15.2), for values. Every value delivered on a connection is a value of
    the output type of the connection's declared transform, which is the input type of the target;
    the source result it comes from has the transform's input type, which is the result type of the
    source. A trigger goes through `discard` to a target without input. -/
theorem typed_connection (valid : p.validate = .ok ()) (lists : τ.Lists) (typed : TypedEnv p env τ)
    {tr : List Op} {s : State} (h : Conforming p env tr s) :
    ∀ d ∈ s.deliveries, ∃ w c src dst r, s.workflow? p d.run = some w ∧ w.connections[d.connection]? = some c ∧
      w.placement? c.source = some src ∧ w.placement? c.target = some dst ∧
      s.result? d.source = some r ∧ r.run = d.run ∧ r.placement = c.source ∧
      ((∃ id t v, c.transform = .declared id ∧ p.transform? id = some t ∧ d.outcome = .value v ∧
          p.resultType src.control = some t.input ∧ p.inputType dst.control = some (some t.output) ∧
          τ.HasType r.value t.input ∧ τ.HasType v t.output) ∨
        (c.transform = .discard ∧ d.outcome = .trigger ∧ p.inputType dst.control = some none) ∨
        d.outcome = .failed) := by
  have hr := h.reachable
  have inv := Delivery.Reachable.inv hr
  have ht := Conforming.typed valid lists typed h
  intro d hd
  obtain ⟨w, c, dst, input, hw, hc, hdst, hinput, hfits⟩ := ht.deliveries d hd
  obtain ⟨w', c', r, hw', hc', hrm, hrid, hrrun, hrpl, -⟩ := inv.own.deliveries d hd
  rw [hw] at hw'
  cases hw'
  rw [hc] at hc'
  cases hc'
  obtain ⟨run, -, hwf⟩ := Delivery.workflow?_iff.mp hw
  have hwm := (Definition.workflow?_eq_some hwf).1
  obtain ⟨src, dst', hsrc, hdst', -, -, produced, input', hprod, hinput', hfitsT⟩ :=
    (((Definition.normal_of_validate valid).workflows w hwm).connections c (List.mem_of_getElem? hc)).ends
  rw [hdst] at hdst'
  cases hdst'
  rw [hinput] at hinput'
  cases hinput'
  have hrs : s.result? d.source = some r := by rw [← hrid]; exact inv.wk.result?_of_mem hrm
  refine ⟨w, c, src, dst, r, hw, hc, hsrc, hdst, hrs, hrrun, hrpl, ?_⟩
  cases hout : d.outcome with
  | value v =>
    rw [hout] at hfits
    obtain ⟨T, rfl, hv⟩ := ValueTyping.fits_some.mp hfits
    cases htr : c.transform with
    | discard => rw [htr] at hfitsT; exact hfitsT.elim
    | declared id =>
      rw [htr] at hfitsT
      obtain ⟨t, htid, htin, htout⟩ := hfitsT
      -- The source result has the source's result type, which the transform takes.
      obtain ⟨w₁, pl₁, T₁, hw₁, hpl₁, hT₁, hv₁⟩ := ht.results r hrm
      rw [hrrun, hw] at hw₁
      cases hw₁
      rw [hrpl, hsrc] at hpl₁
      cases hpl₁
      rw [hprod] at hT₁
      cases hT₁
      exact Or.inl ⟨id, t, v, rfl, htid, rfl, by rw [hprod, htin], by rw [hinput, htout], htin ▸ hv₁,
        htout ▸ hv⟩
  | trigger =>
    rw [hout] at hfits
    subst hfits
    cases htr : c.transform with
    | discard => exact Or.inr (Or.inl ⟨rfl, rfl, hinput⟩)
    | declared id => rw [htr] at hfitsT; exact hfitsT.elim
  | failed => exact Or.inr (Or.inr rfl)

/-- **型付き接続** (§3.1, §3.2, §4.1, §4.5, §7.1, §8.1, §15.2), for the inputs of the nodes. Every call
    of a function takes an input of the function's input type, and every call of a judge one of the
    judge's input type. Every run, of the main workflow, of a sub-workflow call or of a workflow task,
    takes an input of its workflow's input type. Every invocation takes an input of the type its
    placement takes, and every execution of a concurrency one of the concurrency's input type. A
    declaration without input receives no value. -/
theorem typed_connection_input (valid : p.validate = .ok ()) (lists : τ.Lists) (typed : TypedEnv p env τ)
    {tr : List Op} {s : State} (h : Conforming p env tr s) :
    (∀ c ∈ s.calls, ∀ f, c.target = .function f → ∃ decl, p.function? f = some decl ∧ τ.Fits c.input decl.input) ∧
    (∀ c ∈ s.calls, ∀ j, c.target = .judge j → ∃ decl, p.judge? j = some decl ∧ τ.Fits c.input (some decl.input)) ∧
    (∀ r ∈ s.runs, ∃ w, p.workflow? r.workflow = some w ∧ τ.Fits r.input (w.input.map (·.valueType))) ∧
    (∀ i ∈ s.invocations, ∃ w pl input, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧
      p.inputType pl.control = some input ∧ τ.Fits i.input input) ∧
    (∀ e ∈ s.executions, ∃ c, s.concurrencyOf p e = .ok c ∧ τ.Fits e.input c.input) := by
  have ht := Conforming.typed valid lists typed h
  refine ⟨fun c hc f hf => ?_, fun c hc j hj => ?_, ht.runs, ht.invocations, fun e he => ?_⟩
  · have := ht.calls c hc
    unfold CallTyped at this
    rw [hf] at this
    exact this
  · have := ht.calls c hc
    unfold CallTyped at this
    rw [hj] at this
    exact this
  · obtain ⟨c, hc, hfits, -⟩ := ht.executions e he
    exact ⟨c, hc, hfits⟩

/-- **型付き接続** (§4.1, §4.5, §5.2, §7.1, §8.3, §9, §15.2), for results. Every result has the result
    type of the placement that produced it, and every result of a task the element type of the task's
    body. -/
theorem typed_connection_result (valid : p.validate = .ok ()) (lists : τ.Lists) (typed : TypedEnv p env τ)
    {tr : List Op} {s : State} (h : Conforming p env tr s) :
    (∀ r ∈ s.results, ∃ w pl T, s.workflow? p r.run = some w ∧ w.placement? r.placement = some pl ∧
      p.resultType pl.control = some T ∧ τ.HasType r.value T) ∧
    (∀ x ∈ s.taskResults, ∃ e ∈ s.executions, e.id = x.execution ∧ ∃ c spec T, s.concurrencyOf p e = .ok c ∧
      c.tasks.find? (·.name == x.task) = some spec ∧ p.bodyElement p.depth spec.body = some T ∧
      τ.HasType x.value T) := by
  have ht := Conforming.typed valid lists typed h
  refine ⟨ht.results, fun x hx => ?_⟩
  obtain ⟨e, he, heid, c, spec, T, hc, hspec, hT, hv, -⟩ := ht.taskResults x hx
  exact ⟨e, he, heid, c, spec, T, hc, hspec, hT, hv⟩

/-- `typed_connection_result` for each control (§4.1, §4.5, §7.1, §8.3, §9): a function call returns
    values of the function's output element type; a sub-workflow call returns a value of the result type
    of its designated endpoint; a branch passes on a value of its judge's input type; a waitStream and a
    Merge give a list of their element type; a concurrency gives a list of its element type for List
    output, and values of it for Stream output. -/
theorem typed_connection_result_controls (valid : p.validate = .ok ()) (lists : τ.Lists)
    (typed : TypedEnv p env τ) {tr : List Op} {s : State} (h : Conforming p env tr s) :
    ∀ r ∈ s.results, ∀ w pl, s.workflow? p r.run = some w → w.placement? r.placement = some pl →
      (∀ f decl, pl.control = .call (.function f) → p.function? f = some decl →
        τ.HasType r.value decl.output.element) ∧
      (∀ wf out w' pl' T, pl.control = .call (.workflow wf out) → p.workflow? wf = some w' →
        w'.placement? out = some pl' → p.resultType pl'.control = some T → τ.HasType r.value T) ∧
      (∀ j arms jd, pl.control = .branch j arms → p.judge? j = some jd → τ.HasType r.value jd.input) ∧
      (∀ T, pl.control = .waitStream T → τ.HasType r.value (.list T)) ∧
      (∀ T, pl.control = .merge T → τ.HasType r.value (.list T)) ∧
      (∀ c, pl.control = .concurrency c → c.output = .list → τ.HasType r.value (.list c.element)) ∧
      (∀ c, pl.control = .concurrency c → c.output = .stream → τ.HasType r.value c.element) := by
  intro r hr w pl hw hpl
  obtain ⟨w', pl', T, hw', hpl', hT, hv⟩ := (typed_connection_result valid lists typed h).1 r hr
  rw [hw] at hw'
  cases hw'
  rw [hpl] at hpl'
  cases hpl'
  refine ⟨fun f decl hctl hdecl => ?_, fun wf out w₂ pl₂ T₂ hctl hw₂ hpl₂ hT₂ => ?_, fun j arms jd hctl hjd => ?_,
    fun T' hctl => ?_, fun T' hctl => ?_, fun c hctl hout => ?_, fun c hctl hout => ?_⟩
  · rw [hctl, resultType_function hdecl] at hT
    cases hT
    exact hv
  · rw [hctl] at hT
    rw [bodyElement_workflow hT hw₂ hpl₂ hT₂]
    exact hv
  · rw [hctl] at hT
    simp only [Definition.resultType, Definition.localResult, hjd, Option.map_some, Option.some.injEq] at hT
    rw [hT]
    exact hv
  · rw [hctl] at hT
    cases hT
    exact hv
  · rw [hctl] at hT
    cases hT
    exact hv
  · rw [hctl] at hT
    simp only [Definition.resultType, Definition.localResult, hout, Option.some.injEq] at hT
    rw [hT]
    exact hv
  · rw [hctl] at hT
    simp only [Definition.resultType, Definition.localResult, hout, Option.some.injEq] at hT
    rw [hT]
    exact hv

/-! ## concurrencyの出力の型 -/

/-- **concurrencyの出力の型** (§8.1, §8.3, §15.2), for values. Every value that the output transform of a
    task puts in the output of a concurrency execution has the common element type `T` of the
    concurrency: the task is in the output, its output transform returns `T`, and the result it
    transformed has the transform's input type, the element type of the task's body. The concurrency's
    results have type `T` for a Stream output and `List<T>` for a List output. -/
theorem concurrency_output_type (valid : p.validate = .ok ()) (lists : τ.Lists) (typed : TypedEnv p env τ)
    {tr : List Op} {s : State} (h : Conforming p env tr s) :
    (∀ x ∈ s.taskResults, ∀ v, x.output = .value v → ∃ e ∈ s.executions, e.id = x.execution ∧
      ∃ c spec id t, s.concurrencyOf p e = .ok c ∧ c.tasks.find? (·.name == x.task) = some spec ∧
        spec.output = some id ∧ p.transform? id = some t ∧ t.output = c.element ∧
        p.bodyElement p.depth spec.body = some t.input ∧ τ.HasType x.value t.input ∧ τ.HasType v c.element) ∧
    (∀ r ∈ s.results, ∀ w pl c, s.workflow? p r.run = some w → w.placement? r.placement = some pl →
      pl.control = .concurrency c →
        τ.HasType r.value (match c.output with | .list => .list c.element | .stream => c.element)) := by
  have hr := h.reachable
  have ht := Conforming.typed valid lists typed h
  refine ⟨fun x hx v hxv => ?_, fun r hrm w pl c hw hpl hctl => ?_⟩
  · obtain ⟨e, he, heid, c, spec, T, hc, hspec, hT, hv, hout⟩ := ht.taskResults x hx
    -- A transformed output belongs to a task in the output.
    obtain ⟨e', he', he'id, spec', hspec', hso, -⟩ := CoversViewAux.reachable_taskResultShape valid hr x hx
    obtain rfl : e' = e := hr.wellKeyed.execution_eq_of_id he' he (he'id.trans heid.symm)
    obtain ⟨c', hc', hfind'⟩ := State.taskSpec_eq_ok.mp hspec'
    obtain rfl : c' = c := by rw [hc] at hc'; exact (Except.ok.inj hc').symm
    obtain rfl : spec' = spec := by rw [hspec] at hfind'; exact (Option.some.inj hfind').symm
    obtain ⟨id, hid⟩ := Option.isSome_iff_exists.mp (hso (by rw [hxv]; simp))
    obtain ⟨w, pl, hw, hpl, hctl⟩ := Delivery.concurrencyOf_iff.mp hc
    obtain ⟨run, -, hwf⟩ := Delivery.workflow?_iff.mp hw
    obtain ⟨-, -, -, -, -, -, htasks⟩ :=
      (((Definition.normal_of_validate valid).workflows w (Definition.workflow?_eq_some hwf).1).placements pl
        (Workflow.placement?_eq_some hpl).1).concurrency c' hctl
    obtain ⟨t, htid, hbody, htout⟩ := (htasks spec' (List.mem_of_find?_eq_some hspec)).output id hid
    rw [hbody] at hT
    cases hT
    exact ⟨e', he', heid, c', spec', id, t, hc, hspec, hid, htid, htout, hbody, hv, hout v hxv⟩
  · obtain ⟨-, -, -, -, -, hlist, hstream⟩ := typed_connection_result_controls valid lists typed h r hrm w pl hw hpl
    cases hout : c.output with
    | list => exact hlist c hctl hout
    | stream => exact hstream c hctl hout

end Suimon.Values
