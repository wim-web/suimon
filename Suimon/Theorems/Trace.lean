import Suimon.Trace
import Suimon.Theorems.WireText

namespace Suimon.Trace

/-! ## Encoding and decoding do not change a record -/

private theorem ok_bind {α β ε : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

private theorem map_ok {α β ε : Type} (x : α) (f : α → β) : (f <$> Except.ok x : Except ε β) = .ok (f x) :=
  rfl

private theorem pure_ok {α ε : Type} (x : α) : (pure x : Except ε α) = .ok x := rfl

private theorem error_bind {α β ε : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e :=
  rfl

private theorem throw_error {α ε : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

private theorem map_error {α β ε : Type} (e : ε) (f : α → β) : (f <$> Except.error e : Except ε β) = .error e :=
  rfl

theorem strings_map_str (at_ : String) (items : List String) : strings at_ (items.map .str) = .ok items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [strings, ih]; rfl

theorem opOfWire_opWire (o : Op) : opOfWire (opWire o) = .ok o := by
  cases o
  case start input => cases input <;> rfl
  case invoke run placement trigger =>
    cases trigger <;> simp [opWire, opOfWire, pathWire, optional, getText, getText?, getPath, strict,
      List.lookup, List.find?, strings_map_str, ok_bind, pure_ok]
  case deliver run connection source value =>
    cases value <;> simp [opWire, opOfWire, pathWire, optional, getText, getText?, getNat, getPath, strict,
      List.lookup, List.find?, strings_map_str, ok_bind, pure_ok]
  case taskInput execution task value => cases value <;> rfl
  all_goals simp [opWire, opOfWire, pathWire, getText, getNat, getBool, getPath, strict,
      List.lookup, List.find?, strings_map_str, ok_bind, pure_ok]

theorem payloads_valuesWire (values : List (Value × String)) :
    payloads (values.map fun entry => (entry.1, .str entry.2)) = .ok values := by
  induction values with
  | nil => rfl
  | cons entry rest ih => simp [payloads, ih]; rfl

theorem recordOfWire_recordWire (r : Record) : recordOfWire (recordWire r) = .ok r := by
  cases r with
  | commit seq => rfl
  | op seq o values =>
    by_cases h : values = []
    · subst h
      simp [recordWire, recordOfWire, optional, getNat, strict, List.lookup, List.find?, opOfWire_opWire,
        map_ok]
    · have hne : values.isEmpty = false := by simpa using h
      simp [recordWire, recordOfWire, optional, valuesWire, hne, getNat, strict, List.lookup, List.find?,
        opOfWire_opWire, payloads_valuesWire, ok_bind, map_ok]

/-- A text form of `Wire` values that reads back what it renders, on one line, gives a lawful codec. --/
theorem Codec.ofWire_lawful {render : Wire → String} {parse : String → Except String Wire}
    (hparse : ∀ r, parse (render (recordWire r)) = .ok (recordWire r))
    (hline : ∀ r, '\n' ∉ (render (recordWire r)).toList) : (Codec.ofWire render parse).Lawful :=
  ⟨fun r => by simp [Codec.ofWire, hparse, ok_bind, recordOfWire_recordWire], hline⟩

/-- Records are written and read back through the verified text form of `Wire` values. --/
theorem wireCodec_lawful : wireCodec.Lawful :=
  Codec.ofWire_lawful (fun r => Wire.parse_render (recordWire r)) (fun r => Wire.newline_not_mem_render (recordWire r))

/-! ## Lines -/

theorem splitLines_of_not_mem {xs : List Char} (h : '\n' ∉ xs) (current : List Char) :
    splitLines xs current = ([], current.reverse ++ xs) := by
  induction xs generalizing current with
  | nil => simp [splitLines]
  | cons x xs ih =>
    have hx : x ≠ '\n' := fun e => h (e ▸ List.mem_cons_self)
    have hxs : '\n' ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitLines, hx, ih hxs]

theorem splitLines_append_of_not_mem {xs : List Char} (h : '\n' ∉ xs) (rest current : List Char) :
    splitLines (xs ++ rest) current = splitLines rest (xs.reverse ++ current) := by
  induction xs generalizing current with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ '\n' := fun e => h (e ▸ List.mem_cons_self)
    have hxs : '\n' ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitLines, hx, ih hxs]

/-- Lines without newlines, each ended by one, followed by a tail without a newline, split back
    into the same lines and tail. --/
theorem splitLines_lines {lines : List (List Char)} {tail : List Char}
    (hlines : ∀ l ∈ lines, '\n' ∉ l) (htail : '\n' ∉ tail) :
    splitLines (lines.flatMap (· ++ ['\n']) ++ tail) [] = (lines, tail) := by
  induction lines with
  | nil => simp [splitLines_of_not_mem htail]
  | cons l ls ih =>
    have hl : '\n' ∉ l := hlines l List.mem_cons_self
    have hls : ∀ l ∈ ls, '\n' ∉ l := fun l' m => hlines l' (List.mem_cons_of_mem _ m)
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append]
    rw [splitLines_append_of_not_mem hl]
    simp [splitLines, ih hls]

theorem text_toList (c : Codec) (rs : List Record) :
    (text c rs).toList = (rs.map fun r => (c.encode r).toList).flatMap (· ++ ['\n']) := by
  simp [text, String.toList_join, List.flatMap_map]

/-! ## Recording -/

theorem transaction_eq_ok {p : Program} {s : State} {o : Op} {values known : List (Value × String)} {seq : Nat}
    {next : State} {records : List Record} :
    transaction p s o values known seq = .ok (next, records) ↔
      step p s o = .ok next ∧ missing s next values known = [] ∧
        records = [.op seq o values, .commit (seq + 1)] := by
  unfold transaction
  cases hs : step p s o with
  | error e => simp [error_bind]
  | ok n =>
    cases hm : (missing s n values known).isEmpty <;> simp_all [ok_bind, pure_ok, error_bind, throw_error] <;>
      rintro rfl
    · exact fun h => absurd h hm
    · simp only [hm, true_and]
      exact eq_comm

theorem record_cons_ok {p : Program} {s t : State} {o : Op} {values known : List (Value × String)}
    {rest : List (Op × List (Value × String))} {seq : Nat} {rs : List Record}
    (h : record p s ((o, values) :: rest) known seq = .ok (t, rs)) :
    ∃ next later, step p s o = .ok next ∧ missing s next values known = [] ∧
      record p next rest (known ++ values) (seq + 2) = .ok (t, later) ∧
      rs = .op seq o values :: .commit (seq + 1) :: later := by
  simp only [record] at h
  cases ht : transaction p s o values known seq with
  | error e => simp [ht, error_bind] at h
  | ok x =>
    obtain ⟨next, records⟩ := x
    obtain ⟨hs, hm, rfl⟩ := transaction_eq_ok.1 ht
    cases hr : record p next rest (known ++ values) (seq + 2) with
    | error e => simp [ht, hr, ok_bind, map_error] at h
    | ok y =>
      obtain ⟨final, later⟩ := y
      simp [ht, hr, ok_bind, pure_ok] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨next, later, hs, hm, hr, rfl⟩

theorem record_cons_of {p : Program} {s next t : State} {o : Op} {values known : List (Value × String)}
    {rest : List (Op × List (Value × String))} {seq : Nat} {later : List Record}
    (hs : step p s o = .ok next) (hm : missing s next values known = [])
    (hr : record p next rest (known ++ values) (seq + 2) = .ok (t, later)) :
    record p s ((o, values) :: rest) known seq = .ok (t, .op seq o values :: .commit (seq + 1) :: later) := by
  have ht : transaction p s o values known seq = .ok (next, [.op seq o values, .commit (seq + 1)]) :=
    transaction_eq_ok.2 ⟨hs, hm, rfl⟩
  simp [record, ht, hr, ok_bind, pure_ok]

theorem record_length {p : Program} :
    ∀ {steps : List (Op × List (Value × String))} {s t : State} {known : List (Value × String)} {seq : Nat}
      {rs : List Record}, record p s steps known seq = .ok (t, rs) → rs.length = 2 * steps.length := by
  intro steps
  induction steps with
  | nil =>
    intro s t known seq rs h
    simp only [record, pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons step rest ih =>
    obtain ⟨o, values⟩ := step
    intro s t known seq rs h
    obtain ⟨next, later, -, -, hr, rfl⟩ := record_cons_ok h
    simp [ih hr]
    omega

/-- Recording two lists of transactions one after the other records their concatenation; the
    second recording knows the payloads of the first. --/
theorem record_append {p : Program} :
    ∀ {xs ys : List (Op × List (Value × String))} {s u t : State} {known : List (Value × String)} {seq : Nat}
      {rs₁ rs₂ : List Record},
      record p s xs known seq = .ok (u, rs₁) →
      record p u ys (known ++ xs.flatMap (·.2)) (seq + 2 * xs.length) = .ok (t, rs₂) →
      record p s (xs ++ ys) known seq = .ok (t, rs₁ ++ rs₂) := by
  intro xs
  induction xs with
  | nil =>
    intro ys s u t known seq rs₁ rs₂ h₁ h₂
    simp only [record, pure_ok, Except.ok.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simpa using h₂
  | cons step rest ih =>
    obtain ⟨o, values⟩ := step
    intro ys s u t known seq rs₁ rs₂ h₁ h₂
    obtain ⟨next, later, hs, hm, hr, rfl⟩ := record_cons_ok h₁
    have h₂' : record p u ys (known ++ values ++ rest.flatMap (·.2)) (seq + 2 + 2 * rest.length) =
        .ok (t, rs₂) := by
      rw [show seq + 2 + 2 * rest.length = seq + 2 * (rest.length + 1) by omega]
      simpa using h₂
    exact record_cons_of hs hm (ih hr h₂')

theorem text_append (c : Codec) (rs₁ rs₂ : List Record) : text c (rs₁ ++ rs₂) = text c rs₁ ++ text c rs₂ := by
  simp [text, String.join_append]

/-! ## Replay -/

/-- Payloads of earlier records only help. --/
theorem missing_known {before after : State} {values : List (Value × String)}
    (h : missing before after values [] = []) (known : List (Value × String)) :
    missing before after values known = [] := by
  simp only [missing, List.filter_eq_nil_iff] at h ⊢
  intro v hv
  have := h v hv
  cases hb : values.any (·.1 == v)
  · rw [hb] at this
    simp at this
  · simp

theorem replayLine_op {c : Codec} (hc : c.Lawful) (p : Program) (r : Replay) (index seq : Nat) (o : Op)
    (values : List (Value × String)) (hpending : r.pending = none) (hnext : r.next = seq) :
    replayLine c p r index (String.ofList (c.encode (.op seq o values)).toList) =
      .ok { r with pending := some (o, values), next := seq + 1 } := by
  obtain ⟨state, committed, known, pending, next⟩ := r
  simp only at hpending hnext
  subst hpending hnext
  simp [replayLine, hc.1, Record.seq, pure_ok]

theorem replayLine_commit {c : Codec} (hc : c.Lawful) (p : Program) (r : Replay) (index seq : Nat) (o : Op)
    (values : List (Value × String)) (next : State) (hpending : r.pending = some (o, values))
    (hnext : r.next = seq) (hs : step p r.state o = .ok next) (hm : missing r.state next values r.values = []) :
    replayLine c p r index (String.ofList (c.encode (.commit seq)).toList) =
      .ok { state := next, committed := r.committed + 1, values := r.values ++ values, pending := none,
            next := seq + 1 } := by
  obtain ⟨state, committed, known, pending, n⟩ := r
  simp only at hpending hnext hs hm
  subst hpending hnext
  simp [replayLine, hc.1, Record.seq, hs, hm, pure_ok]

theorem replayLines_append (c : Codec) (p : Program) (xs ys : List (List Char)) :
    ∀ (r : Replay) (index : Nat), replayLines c p r index (xs ++ ys) =
      replayLines c p r index xs >>= fun r' => replayLines c p r' (index + xs.length) ys := by
  induction xs with
  | nil => intro r index; simp [replayLines, pure_ok, ok_bind]
  | cons x xs ih =>
    intro r index
    simp only [List.cons_append, replayLines]
    cases h : replayLine c p r index (String.ofList x) with
    | error e => rfl
    | ok r' =>
      simp only [ok_bind, ih, List.length_cons]
      rw [show index + 1 + xs.length = index + (xs.length + 1) by omega]

/-- Replaying the first `k` lines of a recording commits `k / 2` transitions and holds the op of the
    next one when `k` is odd. The replay starts where the recording did, knowing the same payloads. --/
theorem replayLines_take {c : Codec} (hc : c.Lawful) {p : Program} :
    ∀ {steps : List (Op × List (Value × String))} {s t : State} {known : List (Value × String)} {seq : Nat}
      {rs : List Record},
      record p s steps known seq = .ok (t, rs) →
      ∀ (r : Replay) (index k : Nat), r.state = s → r.values = known → r.pending = none → r.next = seq →
        k ≤ rs.length →
      ∃ u, record p s (steps.take (k / 2)) known seq = .ok (u, rs.take (2 * (k / 2))) ∧
        replayLines c p r index ((rs.take k).map fun x => (c.encode x).toList) =
          .ok { state := u, committed := r.committed + k / 2,
                values := r.values ++ (steps.take (k / 2)).flatMap (·.2),
                pending := if k % 2 = 1 then steps[k / 2]? else none, next := seq + k } := by
  intro steps
  induction steps with
  | nil =>
    intro s t known seq rs h r index k hstate hvalues hpending hnext hk
    simp only [record, pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    refine ⟨s, by simp [record, pure_ok], ?_⟩
    obtain ⟨state, committed, vals, pending, next⟩ := r
    simp only at hstate hpending hnext
    subst hstate hpending hnext
    simp [replayLines, pure_ok]
  | cons step rest ih =>
    obtain ⟨o, values⟩ := step
    intro s t known seq rs h r index k hstate hvalues hpending hnext hk
    obtain ⟨next, later, hs, hm, hr, rfl⟩ := record_cons_ok h
    have hop := replayLine_op hc p r index seq o values hpending hnext
    match k with
    | 0 =>
      refine ⟨s, by simp [record, pure_ok], ?_⟩
      obtain ⟨state, committed, vals, pending, n⟩ := r
      simp only at hstate hpending hnext
      subst hstate hpending hnext
      simp [replayLines, pure_ok]
    | 1 =>
      refine ⟨s, by simp [record, pure_ok], ?_⟩
      simp only [List.take, List.map, replayLines]
      rw [hop]
      obtain ⟨state, committed, vals, pending, n⟩ := r
      simp only at hstate hpending hnext
      subst hstate hpending hnext
      simp [ok_bind, pure_ok]
    | k + 2 =>
      have hk' : k ≤ later.length := by simp at hk; omega
      have hcommit := replayLine_commit hc p { r with pending := some (o, values), next := seq + 1 }
        (index + 1) (seq + 1) o values next rfl rfl (by simpa [hstate] using hs)
        (by simpa [hstate, hvalues] using hm)
      obtain ⟨u, hu, hreplay⟩ := ih hr
        { state := next, committed := r.committed + 1, values := r.values ++ values, pending := none,
          next := seq + 1 + 1 } (index + 1 + 1) k rfl (by simp [hvalues]) rfl rfl hk'
      refine ⟨u, ?_, ?_⟩
      · have hhalf : (k + 2) / 2 = k / 2 + 1 := by omega
        have htwice : 2 * (k / 2 + 1) = 2 * (k / 2) + 1 + 1 := by omega
        rw [hhalf, List.take_succ_cons, htwice, List.take_succ_cons, List.take_succ_cons]
        exact record_cons_of hs hm hu
      · simp only [List.take_succ_cons, List.map_cons, replayLines]
        rw [hop]
        simp only [ok_bind]
        rw [hcommit]
        simp only [ok_bind]
        rw [hreplay]
        have hhalf : (k + 2) / 2 = k / 2 + 1 := by omega
        have hmod : (k + 2) % 2 = k % 2 := by omega
        simp only [hhalf, hmod, List.take_succ_cons, List.flatMap_cons, List.append_assoc,
          List.getElem?_cons_succ, Except.ok.injEq, Replay.mk.injEq]
        refine ⟨trivial, by omega, trivial, trivial, by omega⟩

/-! ## Replay and crash recovery (§12.1, §15.2) -/

/-- A crash leaves the first `k` lines a recorder wrote and possibly the start of the next line.
    Checking such a text replays exactly the committed transitions, the first `k / 2`, and reports
    the rest as uncommitted. --/
theorem check_torn {c : Codec} (hc : c.Lawful) {p : Program} {steps : List (Op × List (Value × String))}
    {t : State} {rs : List Record} (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length)
    {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      check c p (text c (rs.take k) ++ tail) =
        .ok { state := u, committed := k / 2, uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""),
              values := (steps.take (k / 2)).flatMap (·.2) } := by
  obtain ⟨u, hu, hreplay⟩ := replayLines_take hc h {} 0 k rfl rfl rfl rfl hk
  refine ⟨u, hu, ?_⟩
  have hlines : ∀ l ∈ (rs.take k).map (fun x => (c.encode x).toList), '\n' ∉ l := by
    intro l hl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
    exact hc.2 x
  have hsplit : splitLines (text c (rs.take k) ++ tail).toList [] =
      ((rs.take k).map fun x => (c.encode x).toList, tail.toList) := by
    rw [String.toList_append, text_toList]
    exact splitLines_lines hlines htail
  have hlen := record_length h
  have hpending : (if k % 2 = 1 then steps[k / 2]? else none).isSome = decide (k % 2 = 1) := by
    by_cases hodd : k % 2 = 1
    · have : k / 2 < steps.length := by omega
      simp [hodd, this]
    · simp [hodd]
  have htailEmpty : tail.toList.isEmpty = decide (tail = "") := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, String.toList_eq_nil_iff, decide_eq_true_iff]
  simp only [check, hsplit, hreplay, ok_bind, pure_ok, hpending, htailEmpty]
  simp

/-- Replaying a whole record reproduces the state of the run that wrote it. --/
theorem check_text {c : Codec} (hc : c.Lawful) {p : Program} {steps : List (Op × List (Value × String))}
    {t : State} {rs : List Record} (h : record p {} steps [] 1 = .ok (t, rs)) :
    check c p (text c rs) =
      .ok { state := t, committed := steps.length, uncommitted := false, values := steps.flatMap (·.2) } := by
  have hlen := record_length h
  obtain ⟨u, hu, hcheck⟩ := check_torn hc h (Nat.le_refl rs.length) (tail := "") (by simp)
  have hhalf : rs.length / 2 = steps.length := by omega
  have hmod : rs.length % 2 = 0 := by omega
  rw [hhalf, List.take_length, h] at hu
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hu)
  rw [List.take_length, String.append_empty, hhalf, hmod, List.take_length] at hcheck
  simpa using hcheck

theorem recover_text {c : Codec} (hc : c.Lawful) {p : Program} {steps : List (Op × List (Value × String))}
    {t : State} {rs : List Record} (h : record p {} steps [] 1 = .ok (t, rs)) :
    recover c p (text c rs) = .ok t := by
  simp [recover, check_text hc h, Except.map]

/-- After a crash, recovery resumes from the state of the committed transitions. --/
theorem recover_torn {c : Codec} (hc : c.Lawful) {p : Program} {steps : List (Op × List (Value × String))}
    {t : State} {rs : List Record} (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length)
    {tail : String} (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      recover c p (text c (rs.take k) ++ tail) = .ok u := by
  obtain ⟨u, hu, hcheck⟩ := check_torn hc h hk htail
  exact ⟨u, hu, by simp [recover, hcheck, Except.map]⟩

/-- After a crash the runtime keeps the committed lines, resumes from the recovered state with the
    committed payloads, and appends the records of new transactions; the result replays like an
    uninterrupted record. --/
theorem check_resume {c : Codec} (hc : c.Lawful) {p : Program}
    {steps more : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) {u t' : State} {rs' : List Record}
    (hu : recover c p (text c (rs.take k) ++ tail) = .ok u)
    (hmore : record p u more ((steps.take (k / 2)).flatMap (·.2)) (2 * (k / 2) + 1) = .ok (t', rs')) :
    check c p (text c (rs.take (2 * (k / 2))) ++ text c rs') =
      .ok { state := t', committed := k / 2 + more.length, uncommitted := false,
            values := (steps.take (k / 2) ++ more).flatMap (·.2) } := by
  obtain ⟨u₀, hu₀, hrecover⟩ := recover_torn hc h hk htail
  rw [hu] at hrecover
  obtain rfl := (Except.ok.inj hrecover).symm
  have hlen := record_length h
  have htake : (steps.take (k / 2)).length = k / 2 := by simp; omega
  have hall : record p {} (steps.take (k / 2) ++ more) [] 1 = .ok (t', rs.take (2 * (k / 2)) ++ rs') :=
    record_append hu₀ (by rw [htake, Nat.add_comm]; simpa using hmore)
  rw [← text_append, check_text hc hall, List.length_append, htake]

/-! ## Payloads of a recovered state (§12.1) -/

/-- Each value of `after` is a value of `before` or one the transition introduces. --/
theorem mem_introduced {before after : State} {v : Value} (hafter : v ∈ after.values)
    (hbefore : v ∉ before.values) : v ∈ introduced before after := by
  simp [introduced, List.mem_eraseDups, hafter, hbefore]

/-- A transition whose introduced values all have payloads keeps every value covered. --/
theorem covered_of_missing {before after : State} {values known : List (Value × String)}
    (hm : missing before after values known = [])
    (hbefore : ∀ v ∈ before.values, known.any (·.1 == v) = true) :
    ∀ v ∈ after.values, (known ++ values).any (·.1 == v) = true := by
  intro v hv
  rw [List.any_append]
  by_cases hb : v ∈ before.values
  · rw [hbefore v hb, Bool.true_or]
  · have hnot := (List.filter_eq_nil_iff.1 hm) v (mem_introduced hv hb)
    revert hnot
    cases known.any (·.1 == v) <;> cases values.any (·.1 == v) <;> simp

/-- The payloads read so far cover every value the replayed state mentions. --/
def Replay.Covered (r : Replay) : Prop := ∀ v ∈ r.state.values, r.values.any (·.1 == v) = true

theorem replayLine_covered {c : Codec} {p : Program} {r r' : Replay} {index : Nat} {line : String}
    (hr : r.Covered) (h : replayLine c p r index line = .ok r') : r'.Covered := by
  simp only [replayLine] at h
  split at h
  · simp [throw_error] at h
  · split at h
    · simp [throw_error] at h
    · split at h
      · simp only [pure_ok, Except.ok.injEq] at h
        subst h
        exact hr
      · split at h
        · split at h
          · rename_i hm
            simp only [pure_ok, Except.ok.injEq] at h
            subst h
            exact covered_of_missing (by simpa using hm) hr
          · simp [throw_error] at h
        · simp [throw_error] at h
      · simp [throw_error] at h
      · simp [throw_error] at h

theorem replayLines_covered {c : Codec} {p : Program} :
    ∀ {lines : List (List Char)} {r r' : Replay} {index : Nat}, r.Covered →
      replayLines c p r index lines = .ok r' → r'.Covered := by
  intro lines
  induction lines with
  | nil =>
    intro r r' index hr h
    simp only [replayLines, pure_ok, Except.ok.injEq] at h
    exact h ▸ hr
  | cons line rest ih =>
    intro r r' index hr h
    simp only [replayLines] at h
    cases hl : replayLine c p r index (String.ofList line) with
    | error e => simp [hl, error_bind] at h
    | ok r₁ =>
      rw [hl, ok_bind] at h
      exact ih (replayLine_covered hr hl) h

/-- Every value a checked state mentions has its payload among the committed ones, so a recovered
    state never names a lost value (§12.1). --/
theorem check_payloads {c : Codec} {p : Program} {text : String} {checked : Checked}
    (h : check c p text = .ok checked) : ∀ v ∈ checked.state.values, checked.values.any (·.1 == v) = true := by
  simp only [check] at h
  cases hr : replayLines c p {} 0 (splitLines text.toList []).1 with
  | error e => simp only [hr, error_bind, reduceCtorEq] at h
  | ok r =>
    simp only [hr, ok_bind, pure_ok, Except.ok.injEq] at h
    subst h
    exact replayLines_covered (fun v hv => by simp [State.values] at hv) hr

end Suimon.Trace
