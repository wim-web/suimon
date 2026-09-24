import Suimon.Theorems.Trace
import Suimon.Theorems.Normal

/-! Execution records and crash recovery for the records `suimon check` reads (§12.1, §15.2): the
    theorems of `Theorems/Trace.lean` for the text codec `Trace.wireCodec` and the loader
    `Header.load` that the CLI uses, with no hypothesis on the loader. A recorder of `p` writes the
    header `Header.of p validated`, whose definition is the canonical form of `p`, which repeats no
    key (`Codec.definitionWire_distinctKeys`), and whose flag says whether the execution was started
    with validation of `p` (run) or without it (runUnchecked).

    The loader reads the definition by the flag. A header that says the execution was started with
    validation loads as `p` for every `p` that validation accepts (`Header.load_of_validate`); a
    record with such a header checks and resumes only with a definition that validation accepts
    (`check_validated`, `resume_validated`), and is refused at line 1 otherwise
    (`check_validated_invalid`). A header that says it was started without validation loads as `p`
    for every `p` that the definition file can express, valid or not (`Header.load_unchecked`), so
    such a record is checked and resumed without validation. The theorems come in two families:
    `_of_validate` for the records of executions started with validation, and `_unchecked` for the
    others.

    Resuming compares the canonical forms of the recorded and the resuming definition. For an
    expressible `p`, the header then holds `p` itself, whatever its flag
    (`resume_eq_ok_of_expressible`), so `Trace.resume`, which replays against the definition of the
    header, replays against `p`, as Go's `Resume` does. -/

namespace Suimon.Trace

variable {p : Definition} {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}

/-! ## The loader -/

theorem Header.of_distinctKeys (p : Definition) (validated : Bool) :
    (Header.of p validated).definition.DistinctKeys :=
  Codec.definitionWire_distinctKeys p

/-- The header of an execution of a valid definition started with validation loads back to the
    definition. --/
theorem Header.load_of_validate (hp : p.validate = .ok ()) : Header.load (.of p true) = .ok p := by
  simp [Header.load, Header.of, Codec.load_definitionWire hp]

/-- The header of an execution of an expressible definition started without validation loads back to
    the definition, valid or not. --/
theorem Header.load_unchecked (hp : p.Expressible) : Header.load (.of p false) = .ok p := by
  simp [Header.load, Header.of, Codec.loadUnchecked_definitionWire hp]

/-- The definition of a header that says its execution was started with validation is loaded only if
    validation accepts it. --/
theorem Header.validate_of_load {header : Header} {q : Definition} (h : Header.load header = .ok q)
    (hv : header.validated = true) : q.validate = .ok () := by
  simp only [Header.load, hv, ↓reduceIte] at h
  exact Codec.validate_of_load h

/-- Every definition `Header.load` reads is expressible, whatever the flag of the header. --/
theorem Header.expressible_of_load {header : Header} {q : Definition} (h : Header.load header = .ok q) :
    q.Expressible := by
  cases hv : header.validated
  · simp only [Header.load, hv, Bool.false_eq_true, ↓reduceIte] at h
    exact Codec.expressible_of_loadUnchecked h
  · exact (Definition.normal_of_validate (Header.validate_of_load h hv)).expressible

/-- A header that `Header.load` reads with the canonical form of an expressible `p` holds `p` itself,
    whatever its flag. --/
theorem Header.load_eq_of_definitionWire (hp : p.Expressible) {header : Header} {q : Definition}
    (h : Header.load header = .ok q) (hw : Codec.definitionWire q = Codec.definitionWire p) : q = p :=
  (Codec.definitionWire_inj_of_expressible (Header.expressible_of_load h) hp).1 hw

/-! ## Records of executions started with validation

The theorems below are about every definition `p` that validation accepts and the header
`Header.of p true`. -/

/-- Replaying a whole record of a valid definition reproduces the state of the run that wrote it and
    the payloads of its transitions. --/
theorem check_text_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) :
    check wireCodec Header.load (recording wireCodec (.of p true) rs) =
      .ok { definition := some p, validated := some true, state := t, committed := steps.length,
            uncommitted := false, values := steps.flatMap (·.2) } :=
  check_text wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h

theorem recover_text_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) :
    recover wireCodec Header.load (recording wireCodec (.of p true) rs) = .ok t :=
  recover_text wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h

/-- A crash after the header leaves the header, the first `k` records and possibly a partial line;
    the text checks to exactly the first `k / 2` transitions, the committed ones. --/
theorem check_torn_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      check wireCodec Header.load (recording wireCodec (.of p true) (rs.take k) ++ tail) =
        .ok { definition := some p, validated := some true, state := u, committed := k / 2,
              uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } :=
  check_torn wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h hk htail

theorem recover_torn_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      recover wireCodec Header.load (recording wireCodec (.of p true) (rs.take k) ++ tail) = .ok u :=
  recover_torn wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h hk htail

/-- A crash anywhere in a record of a valid definition, the header included: a text cut inside the
    header checks to nothing, and one that holds the header and the first `k` records checks to the
    first `k / 2` transitions, those whose commit records are complete. --/
theorem check_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p true) rs).toList) :
    ('\n' ∉ pre.toList ∧
      check wireCodec Header.load pre =
        .ok { definition := none, validated := none, state := {}, committed := 0, uncommitted := decide (pre ≠ ""),
              values := [] }) ∨
    ∃ k ≤ rs.length, ∃ tail : String, '\n' ∉ tail.toList ∧
      pre = recording wireCodec (.of p true) (rs.take k) ++ tail ∧
      ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
        check wireCodec Header.load pre =
          .ok { definition := some p, validated := some true, state := u, committed := k / 2,
                uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } :=
  check_prefix wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h hpre

/-- After a crash anywhere in a record of a valid definition, the header included, recovery gives the
    state after the committed transitions, the first `n`. --/
theorem recover_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p true) rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover wireCodec Header.load pre = .ok u :=
  recover_prefix wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h hpre

/-- After a crash that left the header, the runtime keeps the header as it was written and the
    committed lines, resumes from the recovered state with the committed payloads and appends the
    records of new transactions; the result checks like an uninterrupted record. --/
theorem check_resume_of_validate (hp : p.validate = .ok ()) {more : List (Op × List (Value × String))}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) {u t' : State} {rs' : List Record}
    (hu : recover wireCodec Header.load (recording wireCodec (.of p true) (rs.take k) ++ tail) = .ok u)
    (hmore : record p u more ((steps.take (k / 2)).flatMap (·.2)) (2 * (k / 2) + 1) = .ok (t', rs')) :
    check wireCodec Header.load (recording wireCodec (.of p true) (rs.take (2 * (k / 2))) ++ text wireCodec rs') =
      .ok { definition := some p, validated := some true, state := t', committed := k / 2 + more.length,
            uncommitted := false, values := (steps.take (k / 2) ++ more).flatMap (·.2) } :=
  check_resume wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h hk htail hu hmore

/-- After a crash anywhere in a record of a valid definition, the runtime keeps the header as it was
    written, writing it again if the crash cut it, and the committed lines; it resumes from the
    recovered state with the committed payloads and appends the records of new transactions. The
    result checks like an uninterrupted record, and `p` resumes it. --/
theorem check_resume_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p true) rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover wireCodec Header.load pre = .ok u ∧
      ∀ {more : List (Op × List (Value × String))} {t' : State} {rs' : List Record},
        record p u more ((steps.take n).flatMap (·.2)) (2 * n + 1) = .ok (t', rs') →
        check wireCodec Header.load (recording wireCodec (.of p true) (rs.take (2 * n)) ++ text wireCodec rs') =
          .ok { definition := some p, validated := some true, state := t', committed := n + more.length,
                uncommitted := false, values := (steps.take n ++ more).flatMap (·.2) } ∧
        resume wireCodec Header.load p
            (recording wireCodec (.of p true) (rs.take (2 * n)) ++ text wireCodec rs') = .ok t' := by
  obtain ⟨n, hn, u, hu, hrecover, hcheck⟩ :=
    check_resume_prefix wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h hpre
  refine ⟨n, hn, u, hu, hrecover, fun {more t' rs'} hmore => ⟨hcheck hmore, ?_⟩⟩
  have htake : (steps.take n).length = n := by simp; omega
  have hall : record p {} (steps.take n ++ more) [] 1 = .ok (t', rs.take (2 * n) ++ rs') :=
    record_append hu (by rw [htake, Nat.add_comm]; simpa using hmore)
  rw [recording_append]
  exact resume_text wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) hall

/-- A valid definition resumes a whole record of its own, from the state of the run that wrote it. --/
theorem resume_text_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) :
    resume wireCodec Header.load p (recording wireCodec (.of p true) rs) = .ok t :=
  resume_text wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h

/-- After a crash that left the header, a valid definition resumes a record of its own from the state
    of the committed transitions. --/
theorem resume_torn_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      resume wireCodec Header.load p (recording wireCodec (.of p true) (rs.take k) ++ tail) = .ok u :=
  resume_torn wireCodec_lawful (Header.of_distinctKeys p true) (Header.load_of_validate hp) h hk htail

/-- After a crash anywhere in a record of a valid definition, the definition resumes it from the state
    of the committed transitions, unless the crash cut the header. --/
theorem resume_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p true) rs).toList) :
    ('\n' ∉ pre.toList ∧ resume wireCodec Header.load p pre = .error "the record has no header") ∨
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      resume wireCodec Header.load p pre = .ok u := by
  rcases prefix_recording wireCodec_lawful _ rs hpre with hnl | ⟨k, hk, tail, htail, rfl⟩
  · exact Or.inl ⟨hnl, resume_torn_header wireCodec Header.load p hnl⟩
  · obtain ⟨u, hu, hresume⟩ := resume_torn_of_validate hp h hk htail
    have hlen := record_length h
    exact Or.inr ⟨k / 2, by omega, u, hu, hresume⟩

/-- A record whose header says that its execution was started with validation, and that
    `suimon check` accepts, holds a definition that validation accepts. --/
theorem check_validated {text : String} {checked : Checked} (h : check wireCodec Header.load text = .ok checked)
    (hv : checked.validated = some true) : ∃ q, checked.definition = some q ∧ q.validate = .ok () := by
  have hsome := check_validated_isSome h
  rw [hv, Option.isSome_some] at hsome
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome.symm
  obtain ⟨header, hload, hflag⟩ := check_definition h hq
  rw [hv, Option.some.injEq] at hflag
  exact ⟨q, hq, Header.validate_of_load hload hflag.symm⟩

/-- A record whose header says that its execution was started with validation, and holds a
    definition that decodes but that validation rejects, is refused at line 1 with the error of
    validation, whatever follows the header: `suimon check` does not check it, and no definition
    resumes it (§12.1). --/
theorem check_validated_invalid {w : Wire} (hw : w.DistinctKeys) {q : Definition}
    (hq : Codec.loadUnchecked w = .ok q) {e : String} (he : q.validate = .error e) (rest : String) :
    check wireCodec Header.load (wireCodec.encodeHeader ⟨w, true⟩ ++ "\n" ++ rest) = .error s!"line 1: {e}" ∧
      ∀ p, resume wireCodec Header.load p (wireCodec.encodeHeader ⟨w, true⟩ ++ "\n" ++ rest) =
        .error s!"line 1: {e}" := by
  have hload : Header.load ⟨w, true⟩ = .error e := by
    simp only [Codec.loadUnchecked] at hq
    simp [Header.load, Codec.load, Codec.loadJson, hq, he, bind, Except.bind]
  exact ⟨check_load_error wireCodec_lawful hw hload rest, fun p => resume_load_error wireCodec_lawful hw hload p rest⟩

/-- A record that says its execution was started with validation, of a definition that validation
    rejects, is refused at line 1 with the error of validation however it goes on, and no definition
    resumes it: its header is what a recorder writes for an execution started with validation, which
    no such definition has, and it holds a definition that the definition file can express. --/
theorem check_invalid_of_validated (hp : p.Expressible) {e : String} (he : p.validate = .error e)
    (rs : List Record) :
    check wireCodec Header.load (recording wireCodec (.of p true) rs) = .error s!"line 1: {e}" ∧
      ∀ q, resume wireCodec Header.load q (recording wireCodec (.of p true) rs) = .error s!"line 1: {e}" :=
  check_validated_invalid (Codec.definitionWire_distinctKeys p) (Codec.loadUnchecked_definitionWire hp) he
    (text wireCodec rs)

/-! ## Records of executions started without validation

The theorems below are about every definition `p` that the definition file can express, which
validation need not accept, and the header `Header.of p false`: such a record replays without
validation. -/

/-- Replaying a whole record of an execution started without validation reproduces the state of the
    run that wrote it and the payloads of its transitions, whether validation accepts the definition
    or not. --/
theorem check_text_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs)) :
    check wireCodec Header.load (recording wireCodec (.of p false) rs) =
      .ok { definition := some p, validated := some false, state := t, committed := steps.length,
            uncommitted := false, values := steps.flatMap (·.2) } :=
  check_text wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h

theorem recover_text_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs)) :
    recover wireCodec Header.load (recording wireCodec (.of p false) rs) = .ok t :=
  recover_text wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h

/-- A crash after the header of a record of an execution started without validation leaves the
    header, the first `k` records and possibly a partial line; the text checks to exactly the first
    `k / 2` transitions, the committed ones. --/
theorem check_torn_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      check wireCodec Header.load (recording wireCodec (.of p false) (rs.take k) ++ tail) =
        .ok { definition := some p, validated := some false, state := u, committed := k / 2,
              uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } :=
  check_torn wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h hk htail

theorem recover_torn_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      recover wireCodec Header.load (recording wireCodec (.of p false) (rs.take k) ++ tail) = .ok u :=
  recover_torn wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h hk htail

/-- A crash anywhere in a record of an execution started without validation, the header included: a
    text cut inside the header checks to nothing, and one that holds the header and the first `k`
    records checks to the first `k / 2` transitions, those whose commit records are complete. --/
theorem check_prefix_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p false) rs).toList) :
    ('\n' ∉ pre.toList ∧
      check wireCodec Header.load pre =
        .ok { definition := none, validated := none, state := {}, committed := 0, uncommitted := decide (pre ≠ ""),
              values := [] }) ∨
    ∃ k ≤ rs.length, ∃ tail : String, '\n' ∉ tail.toList ∧
      pre = recording wireCodec (.of p false) (rs.take k) ++ tail ∧
      ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
        check wireCodec Header.load pre =
          .ok { definition := some p, validated := some false, state := u, committed := k / 2,
                uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } :=
  check_prefix wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h hpre

/-- After a crash anywhere in a record of an execution started without validation, the header
    included, recovery gives the state after the committed transitions, the first `n`. --/
theorem recover_prefix_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p false) rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover wireCodec Header.load pre = .ok u :=
  recover_prefix wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h hpre

/-- After a crash that left the header of a record of an execution started without validation, the
    runtime keeps the header as it was written, with its flag, and the committed lines, resumes from
    the recovered state with the committed payloads and appends the records of new transactions; the
    result checks like an uninterrupted record. --/
theorem check_resume_unchecked (hp : p.Expressible) {more : List (Op × List (Value × String))}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) {u t' : State} {rs' : List Record}
    (hu : recover wireCodec Header.load (recording wireCodec (.of p false) (rs.take k) ++ tail) = .ok u)
    (hmore : record p u more ((steps.take (k / 2)).flatMap (·.2)) (2 * (k / 2) + 1) = .ok (t', rs')) :
    check wireCodec Header.load (recording wireCodec (.of p false) (rs.take (2 * (k / 2))) ++ text wireCodec rs') =
      .ok { definition := some p, validated := some false, state := t', committed := k / 2 + more.length,
            uncommitted := false, values := (steps.take (k / 2) ++ more).flatMap (·.2) } :=
  check_resume wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h hk htail hu hmore

/-- After a crash anywhere in a record of an execution started without validation, the runtime keeps
    the header as it was written, writing it again if the crash cut it, and the committed lines; it
    resumes from the recovered state with the committed payloads and appends the records of new
    transactions. The result checks like an uninterrupted record, and `p` resumes it, without
    validation. --/
theorem check_resume_prefix_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p false) rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover wireCodec Header.load pre = .ok u ∧
      ∀ {more : List (Op × List (Value × String))} {t' : State} {rs' : List Record},
        record p u more ((steps.take n).flatMap (·.2)) (2 * n + 1) = .ok (t', rs') →
        check wireCodec Header.load (recording wireCodec (.of p false) (rs.take (2 * n)) ++ text wireCodec rs') =
          .ok { definition := some p, validated := some false, state := t', committed := n + more.length,
                uncommitted := false, values := (steps.take n ++ more).flatMap (·.2) } ∧
        resume wireCodec Header.load p
            (recording wireCodec (.of p false) (rs.take (2 * n)) ++ text wireCodec rs') = .ok t' := by
  obtain ⟨n, hn, u, hu, hrecover, hcheck⟩ :=
    check_resume_prefix wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h hpre
  refine ⟨n, hn, u, hu, hrecover, fun {more t' rs'} hmore => ⟨hcheck hmore, ?_⟩⟩
  have htake : (steps.take n).length = n := by simp; omega
  have hall : record p {} (steps.take n ++ more) [] 1 = .ok (t', rs.take (2 * n) ++ rs') :=
    record_append hu (by rw [htake, Nat.add_comm]; simpa using hmore)
  rw [recording_append]
  exact resume_text wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) hall

/-- An expressible definition resumes a whole record of its own execution started without validation,
    from the state of the run that wrote it, whether validation accepts it or not. --/
theorem resume_text_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs)) :
    resume wireCodec Header.load p (recording wireCodec (.of p false) rs) = .ok t :=
  resume_text wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h

/-- After a crash that left the header, an expressible definition resumes a record of its own
    execution started without validation from the state of the committed transitions. --/
theorem resume_torn_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      resume wireCodec Header.load p (recording wireCodec (.of p false) (rs.take k) ++ tail) = .ok u :=
  resume_torn wireCodec_lawful (Header.of_distinctKeys p false) (Header.load_unchecked hp) h hk htail

/-- After a crash anywhere in a record of an execution started without validation, the definition
    resumes it from the state of the committed transitions, unless the crash cut the header. --/
theorem resume_prefix_unchecked (hp : p.Expressible) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (.of p false) rs).toList) :
    ('\n' ∉ pre.toList ∧ resume wireCodec Header.load p pre = .error "the record has no header") ∨
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      resume wireCodec Header.load p pre = .ok u := by
  rcases prefix_recording wireCodec_lawful _ rs hpre with hnl | ⟨k, hk, tail, htail, rfl⟩
  · exact Or.inl ⟨hnl, resume_torn_header wireCodec Header.load p hnl⟩
  · obtain ⟨u, hu, hresume⟩ := resume_torn_unchecked hp h hk htail
    have hlen := record_length h
    exact Or.inr ⟨k / 2, by omega, u, hu, hresume⟩

/-! ## Resuming -/

/-- The definition that `resume` replays a record against, the one its header holds, is the resuming
    definition itself when the definition file can express it, valid or not, whatever the flag of the
    header. Every valid definition is expressible (`Definition.Normal.expressible`). --/
theorem agreeing_load_eq_ok (hp : p.Expressible) {header : Header} {q : Definition}
    (h : agreeing Header.load p header = .ok q) : q = p := by
  obtain ⟨hq, hw⟩ := agreeing_eq_ok.1 h
  exact Header.load_eq_of_definitionWire hp hq hw

/-- An expressible definition `p` resumes a record exactly when the record checks with the loader of
    the CLI and its header holds `p` itself, not only a definition of the same canonical form,
    whatever the flag of the header; it resumes from the checked state. Replaying against the
    definition of the header is then replaying against `p`, as Go's `Resume` does. --/
theorem resume_eq_ok_of_expressible (hp : p.Expressible) {text : String} {s : State} :
    resume wireCodec Header.load p text = .ok s ↔
      ∃ checked, check wireCodec Header.load text = .ok checked ∧ checked.definition = some p ∧
        checked.state = s := by
  rw [resume_eq_ok]
  constructor
  · rintro ⟨checked, q, hcheck, hq, hw, rfl⟩
    obtain ⟨header, hload, -⟩ := check_definition hcheck hq
    obtain rfl := Header.load_eq_of_definitionWire hp hload hw
    exact ⟨checked, hcheck, hq, rfl⟩
  · rintro ⟨checked, hcheck, hq, rfl⟩
    exact ⟨checked, p, hcheck, hq, rfl, rfl⟩

/-- A valid definition `p` resumes a record exactly when the record checks with the loader of the CLI
    and its header holds `p` itself; it resumes from the checked state. --/
theorem resume_eq_ok_of_validate (hp : p.validate = .ok ()) {text : String} {s : State} :
    resume wireCodec Header.load p text = .ok s ↔
      ∃ checked, check wireCodec Header.load text = .ok checked ∧ checked.definition = some p ∧
        checked.state = s :=
  resume_eq_ok_of_expressible (Definition.normal_of_validate hp).expressible

/-- An expressible definition resumes a record whose header says that its execution was started with
    validation only if validation accepts the definition (§12.1). --/
theorem resume_validated (hp : p.Expressible) {text : String} {s : State} {checked : Checked}
    (h : resume wireCodec Header.load p text = .ok s) (hcheck : check wireCodec Header.load text = .ok checked)
    (hv : checked.validated = some true) : p.validate = .ok () := by
  obtain ⟨checked', hcheck', hp', -⟩ := (resume_eq_ok_of_expressible hp).1 h
  rw [hcheck, Except.ok.injEq] at hcheck'
  subst hcheck'
  obtain ⟨q, hq, hvalid⟩ := check_validated hcheck hv
  rw [hp', Option.some.injEq] at hq
  exact hq ▸ hvalid

/-- Canonical forms of valid definitions that render alike, as `resume` compares them, belong to the
    same definition. --/
theorem eq_of_render (hp : p.validate = .ok ()) {q : Definition} (hq : q.validate = .ok ())
    (h : (Codec.definitionWire q).render = (Codec.definitionWire p).render) : q = p :=
  (Codec.definitionWire_inj hq hp).1 (definitionWire_eq_of_render h)

/-- Canonical forms of expressible definitions that render alike belong to the same definition. --/
theorem eq_of_render_of_expressible (hp : p.Expressible) {q : Definition} (hq : q.Expressible)
    (h : (Codec.definitionWire q).render = (Codec.definitionWire p).render) : q = p :=
  (Codec.definitionWire_inj_of_expressible hq hp).1 (definitionWire_eq_of_render h)

end Suimon.Trace
