import Suimon.Theorems.StaticLemmas

namespace Suimon

/-- Each connection's transform fits its source result and its target input (§4.2, §14). --/
def Definition.TypedConnections (p : Definition) : Prop :=
  ∀ w ∈ p.workflows, ∀ c ∈ w.connections, ∃ src dst,
    w.placement? c.source = some src ∧ w.placement? c.target = some dst ∧
    match c.transform with
    | .declared id => ∃ t, p.transform? id = some t ∧ p.resultType src.control = some t.input ∧
        p.inputType dst.control = some (some t.output)
    | .discard => (p.resultType src.control).isSome ∧ p.inputType dst.control = some none

theorem typedConnections_of_validate {p : Definition} (h : p.validate = .ok ()) : p.TypedConnections :=
  fun w hw c hc => Definition.validateConnection_ok (((Definition.validate_ok h).workflows w hw).connections c hc)

/-- Every task in the output maps its results to the output element type, and at least one task is
    in the output (§8.1, §8.3). --/
theorem concurrency_output_typed {p : Definition} (h : p.validate = .ok ()) :
    ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ c, pl.control = .concurrency c →
      c.tasks.any (·.output.isSome) ∧ ∀ task ∈ c.tasks, ∀ id, task.output = some id →
        ∃ t, p.transform? id = some t ∧ t.output = c.element ∧ p.bodyElement p.depth task.body = some t.input := by
  intro w hw pl hpl c hc
  obtain ⟨-, -, hany, htasks⟩ := (((Definition.validate_ok h).workflows w hw).placements pl hpl).concurrency c hc
  refine ⟨hany, fun task ht id hid => ?_⟩
  obtain ⟨at_, hv⟩ := htasks task ht
  exact Definition.validateTask_output hv hid

/-- Every placement has a derived kind; endpoints are Single; Merge takes only Single inputs;
    waitStream takes a Stream (§5.2, §9, §13.2). --/
theorem kinds_of_validate {p : Definition} (h : p.validate = .ok ()) :
    ∀ w ∈ p.workflows, ∀ pl ∈ w.placements,
      (w.outputKind? p pl.name).isSome ∧
      (w.isEndpoint pl.name = true → w.outputKind? p pl.name = some .single) ∧
      (∀ e, pl.control = .merge e → ∀ c ∈ w.incoming pl.name, w.outputKind? p c.source = some .single) ∧
      (∀ e, pl.control = .waitStream e → w.inputKind? p pl.name = some (some .stream)) := by
  intro w hw pl hpl
  have hwc := (Definition.validate_ok h).workflows w hw
  have hplc := hwc.placements pl hpl
  exact ⟨hplc.kind, hwc.endpoints pl hpl, hplc.merge, hplc.waitStream⟩

/-- The derived kind of a placement is the §5.2 rule applied to the derived kind of its input. --/
theorem kind_rule {p : Definition} (h : p.validate = .ok ()) :
    ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ input, w.inputKind? p pl.name = some input →
      w.outputKind? p pl.name = p.outputKind pl.control input := by
  intro w hw pl hpl input hin
  have hwc := (Definition.validate_ok h).workflows w hw
  rw [Workflow.outputKind?_eq_bind hwc.names hwc.acyclic hpl, hin]
  rfl

/-- A normal node takes at most one input, and the entry counts as one (§3.2). --/
theorem inputs_of_validate {p : Definition} (h : p.validate = .ok ()) :
    ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, (∀ e, pl.control ≠ .merge e) →
      (w.incoming pl.name).length + (if w.isEntry pl.name then 1 else 0) ≤ 1 :=
  fun w hw pl hpl => (((Definition.validate_ok h).workflows w hw).placements pl hpl).inputs

/-- Task names are distinct within a concurrency, and its limit is positive (§8.2). --/
theorem concurrency_settings {p : Definition} (h : p.validate = .ok ()) :
    ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ c, pl.control = .concurrency c →
      (c.tasks.map (·.name)).Nodup ∧ 0 < c.limit := by
  intro w hw pl hpl c hc
  obtain ⟨hlimit, hnodup, -⟩ := (((Definition.validate_ok h).workflows w hw).placements pl hpl).concurrency c hc
  exact ⟨hnodup, hlimit⟩

/-- The external input goes to the root run as one value, and only if the main workflow takes one;
    nothing else happens at the start (§3.1). --/
theorem start_boundary {p : Definition} {s : State} {input : Option Value}
    (h : step p {} (.start input) = .ok s) :
    s = { started := true, runs := [{ path := [], workflow := p.main, input }] } ∧
    ((p.workflow? p.main).bind (·.input)).isSome = input.isSome := by
  simp only [step, Step.start] at h
  rcases hw : p.workflow? p.main with _ | w
  · simp [hw, need, require, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  · cases hi : (w.input.isSome == input.isSome)
    · simp [hw, hi, need, require, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at h
    · simp only [hw, hi, need, require, bind, Except.bind, pure, Except.pure, Bool.not_false,
        beq_self_eq_true, Bool.and_self, ↓reduceIte, Except.ok.injEq] at h
      exact ⟨h.symm, by simpa using hi⟩

end Suimon
