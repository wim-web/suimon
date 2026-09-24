import Suimon.Theorems.Trace
import Suimon.Theorems.Normal

/-! Execution records and crash recovery for the records `suimon check` reads (§12.1, §15.2): the
    theorems of `Theorems/Trace.lean` for the text codec `Trace.wireCodec` and the loader
    `Codec.load` that the CLI uses, with no hypothesis on the loader, for every definition `p` that
    validation accepts. A recorder of `p` writes the header `Codec.definitionWire p`, which repeats no
    key (`Codec.definitionWire_distinctKeys`) and loads as `p` (`Codec.load_definitionWire`). -/

namespace Suimon.Trace

variable {p : Definition} {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}

/-! ## Replay and crash recovery -/

/-- Replaying a whole record of a valid definition reproduces the state of the run that wrote it and
    the payloads of its transitions. --/
theorem check_text_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) :
    check wireCodec Codec.load (recording wireCodec (Codec.definitionWire p) rs) =
      .ok { definition := some p, state := t, committed := steps.length, uncommitted := false,
            values := steps.flatMap (·.2) } :=
  check_text wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h

theorem recover_text_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) :
    recover wireCodec Codec.load (recording wireCodec (Codec.definitionWire p) rs) = .ok t :=
  recover_text wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h

/-- A crash after the header leaves the header, the first `k` records and possibly a partial line;
    the text checks to exactly the first `k / 2` transitions, the committed ones. --/
theorem check_torn_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      check wireCodec Codec.load (recording wireCodec (Codec.definitionWire p) (rs.take k) ++ tail) =
        .ok { definition := some p, state := u, committed := k / 2,
              uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } :=
  check_torn wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h hk htail

theorem recover_torn_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      recover wireCodec Codec.load (recording wireCodec (Codec.definitionWire p) (rs.take k) ++ tail) = .ok u :=
  recover_torn wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h hk htail

/-- A crash anywhere in a record of a valid definition, the header included: a text cut inside the
    header checks to nothing, and one that holds the header and the first `k` records checks to the
    first `k / 2` transitions, those whose commit records are complete. --/
theorem check_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (Codec.definitionWire p) rs).toList) :
    ('\n' ∉ pre.toList ∧
      check wireCodec Codec.load pre =
        .ok { definition := none, state := {}, committed := 0, uncommitted := decide (pre ≠ ""), values := [] }) ∨
    ∃ k ≤ rs.length, ∃ tail : String, '\n' ∉ tail.toList ∧
      pre = recording wireCodec (Codec.definitionWire p) (rs.take k) ++ tail ∧
      ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
        check wireCodec Codec.load pre =
          .ok { definition := some p, state := u, committed := k / 2,
                uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } :=
  check_prefix wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h hpre

/-- After a crash anywhere in a record of a valid definition, the header included, recovery gives the
    state after the committed transitions, the first `n`. --/
theorem recover_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (Codec.definitionWire p) rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover wireCodec Codec.load pre = .ok u :=
  recover_prefix wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h hpre

/-- After a crash that left the header, the runtime keeps the committed lines, resumes from the
    recovered state with the committed payloads and appends the records of new transactions; the
    result checks like an uninterrupted record. --/
theorem check_resume_of_validate (hp : p.validate = .ok ()) {more : List (Op × List (Value × String))}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) {u t' : State} {rs' : List Record}
    (hu : recover wireCodec Codec.load (recording wireCodec (Codec.definitionWire p) (rs.take k) ++ tail) = .ok u)
    (hmore : record p u more ((steps.take (k / 2)).flatMap (·.2)) (2 * (k / 2) + 1) = .ok (t', rs')) :
    check wireCodec Codec.load
        (recording wireCodec (Codec.definitionWire p) (rs.take (2 * (k / 2))) ++ text wireCodec rs') =
      .ok { definition := some p, state := t', committed := k / 2 + more.length, uncommitted := false,
            values := (steps.take (k / 2) ++ more).flatMap (·.2) } :=
  check_resume wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h hk htail hu
    hmore

/-- After a crash anywhere in a record of a valid definition, the runtime keeps the header, writing it
    again if the crash cut it, and the committed lines; it resumes from the recovered state with the
    committed payloads and appends the records of new transactions. The result checks like an
    uninterrupted record, and `p` resumes it. --/
theorem check_resume_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (Codec.definitionWire p) rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover wireCodec Codec.load pre = .ok u ∧
      ∀ {more : List (Op × List (Value × String))} {t' : State} {rs' : List Record},
        record p u more ((steps.take n).flatMap (·.2)) (2 * n + 1) = .ok (t', rs') →
        check wireCodec Codec.load
            (recording wireCodec (Codec.definitionWire p) (rs.take (2 * n)) ++ text wireCodec rs') =
          .ok { definition := some p, state := t', committed := n + more.length, uncommitted := false,
                values := (steps.take n ++ more).flatMap (·.2) } ∧
        resume wireCodec Codec.load p
            (recording wireCodec (Codec.definitionWire p) (rs.take (2 * n)) ++ text wireCodec rs') = .ok t' := by
  obtain ⟨n, hn, u, hu, hrecover, hcheck⟩ :=
    check_resume_prefix wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h hpre
  refine ⟨n, hn, u, hu, hrecover, fun {more t' rs'} hmore => ⟨hcheck hmore, ?_⟩⟩
  have htake : (steps.take n).length = n := by simp; omega
  have hall : record p {} (steps.take n ++ more) [] 1 = .ok (t', rs.take (2 * n) ++ rs') :=
    record_append hu (by rw [htake, Nat.add_comm]; simpa using hmore)
  rw [recording_append]
  exact resume_text wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) hall

/-! ## Resuming -/

/-- A valid definition resumes a whole record of its own, from the state of the run that wrote it. --/
theorem resume_text_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) :
    resume wireCodec Codec.load p (recording wireCodec (Codec.definitionWire p) rs) = .ok t :=
  resume_text wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h

/-- After a crash that left the header, a valid definition resumes a record of its own from the state
    of the committed transitions. --/
theorem resume_torn_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat}
    (hk : k ≤ rs.length) {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      resume wireCodec Codec.load p (recording wireCodec (Codec.definitionWire p) (rs.take k) ++ tail) = .ok u :=
  resume_torn wireCodec_lawful (Codec.definitionWire_distinctKeys p) (Codec.load_definitionWire hp) h hk htail

/-- After a crash anywhere in a record of a valid definition, the definition resumes it from the state
    of the committed transitions, unless the crash cut the header. --/
theorem resume_prefix_of_validate (hp : p.validate = .ok ()) (h : record p {} steps [] 1 = .ok (t, rs))
    {pre : String} (hpre : pre.toList <+: (recording wireCodec (Codec.definitionWire p) rs).toList) :
    ('\n' ∉ pre.toList ∧ resume wireCodec Codec.load p pre = .error "the record has no header") ∨
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      resume wireCodec Codec.load p pre = .ok u := by
  rcases prefix_recording wireCodec_lawful _ rs hpre with hnl | ⟨k, hk, tail, htail, rfl⟩
  · exact Or.inl ⟨hnl, resume_torn_header wireCodec Codec.load p hnl⟩
  · obtain ⟨u, hu, hresume⟩ := resume_torn_of_validate hp h hk htail
    have hlen := record_length h
    exact Or.inr ⟨k / 2, by omega, u, hu, hresume⟩

end Suimon.Trace
