import Suimon.Trace
import Suimon.Theorems.WireText
import Suimon.Theorems.Json

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

private theorem mapError_ok {α ε ε' : Type} (x : α) (f : ε → ε') :
    (Except.ok x : Except ε α).mapError f = .ok x :=
  rfl

private theorem mapError_error {α ε ε' : Type} (e : ε) (f : ε → ε') :
    (Except.error e : Except ε α).mapError f = .error (f e) :=
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

theorem headerOfWire_headerWire (header : Header) : headerOfWire (headerWire header) = .ok header := by
  obtain ⟨definition, validated⟩ := header
  simp [headerWire, headerOfWire, strict, getBool, List.lookup, List.find?, ok_bind, pure_ok]

/-! ## Keys -/

theorem pathWire_distinctKeys (path : Path) : (pathWire path).DistinctKeys :=
  .arr fun w hw => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hw
    exact .str s

/-- Each op has fixed, distinct keys, and its fields are strings, numbers, booleans and paths. --/
theorem opWire_distinctKeys (o : Op) : (opWire o).DistinctKeys := by
  cases o
  case start input => cases input <;> simp [opWire, optional, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.str]
  case invoke run placement trigger =>
    cases trigger <;> simp [opWire, optional, Wire.distinctKeys_obj_iff, pathWire_distinctKeys, Wire.DistinctKeys.str]
  case deliver run connection source value =>
    cases value <;> simp [opWire, optional, Wire.distinctKeys_obj_iff, pathWire_distinctKeys, Wire.DistinctKeys.str,
      Wire.DistinctKeys.nat]
  case taskInput execution task value =>
    cases value <;> simp [opWire, optional, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.str]
  all_goals simp [opWire, Wire.distinctKeys_obj_iff, pathWire_distinctKeys, Wire.DistinctKeys.str,
    Wire.DistinctKeys.nat, Wire.DistinctKeys.bool]

/-- A record whose payloads have distinct keys has no repeated key. --/
theorem recordWire_distinctKeys {r : Record} (hr : r.DistinctKeys) : (recordWire r).DistinctKeys := by
  cases r with
  | commit seq => simp [recordWire, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.nat, Wire.DistinctKeys.bool]
  | op seq o values =>
    simp only [Record.DistinctKeys] at hr
    have hvalues : (valuesWire values).DistinctKeys :=
      .obj (by simpa [valuesWire, Function.comp_def] using hr) fun f hf => by
        obtain ⟨⟨_, payload⟩, -, rfl⟩ := List.mem_map.1 hf
        exact .str payload
    by_cases hv : values = [] <;>
      simp [recordWire, optional, hv, Wire.distinctKeys_obj_iff, Wire.DistinctKeys.nat, opWire_distinctKeys, hvalues]

theorem headerWire_distinctKeys {header : Header} (hw : header.definition.DistinctKeys) :
    (headerWire header).DistinctKeys := by
  simp [headerWire, Wire.distinctKeys_obj_iff, hw, Wire.DistinctKeys.bool]

/-- A text form of `Wire` values that reads back what it renders, when no key repeats, on one line,
    gives a lawful codec. --/
theorem Codec.ofWire_lawful {render : Wire → String} {parse : String → Except String Wire}
    (hparse : ∀ w, w.DistinctKeys → parse (render w) = .ok w) (hline : ∀ w, '\n' ∉ (render w).toList) :
    (Codec.ofWire render parse).Lawful where
  decode_encode r hr := by
    simp [Codec.ofWire, hparse _ (recordWire_distinctKeys hr), ok_bind, recordOfWire_recordWire]
  newline_not_mem_encode r := hline (recordWire r)
  decodeHeader_encodeHeader header hw := by
    simp [Codec.ofWire, hparse _ (headerWire_distinctKeys hw), ok_bind, headerOfWire_headerWire]
  newline_not_mem_encodeHeader header := hline (headerWire header)

/-- The header and the records are written and read back through the verified text form of `Wire`
    values, whose one side condition, that no key repeats, `Codec.Lawful` carries. --/
theorem wireCodec_lawful : wireCodec.Lawful :=
  Codec.ofWire_lawful Wire.parse_render Wire.newline_not_mem_render

/-- The payloads read from the fields of an object have the keys of the fields. --/
theorem payloads_keys : ∀ {entries : Fields} {values : List (Value × String)},
    payloads entries = .ok values → values.map (·.1) = entries.map (·.1)
  | [], values, h => by
    simp only [payloads, pure_ok, Except.ok.injEq] at h
    subst h
    rfl
  | (key, w) :: rest, values, h => by
    cases w with
    | str payload =>
      simp only [payloads] at h
      cases hr : payloads rest with
      | error e => simp only [hr, error_bind, reduceCtorEq] at h
      | ok vs =>
        simp only [hr, ok_bind, pure_ok, Except.ok.injEq] at h
        subst h
        simp [payloads_keys hr]
    | _ => simp [payloads, throw_error] at h

theorem mem_of_lookup {α : Type} : ∀ {fields : List (String × α)} {k : String} {v : α},
    fields.lookup k = some v → (k, v) ∈ fields
  | [], _, _, h => by simp at h
  | (k', v') :: rest, k, v, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      cases h
      simp only [beq_iff_eq] at heq
      simp [heq]
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- A record read from a value without repeated keys has payloads with distinct keys. --/
theorem recordOfWire_distinctKeys {w : Wire} {r : Record} (hw : w.DistinctKeys) (h : recordOfWire w = .ok r) :
    r.DistinctKeys := by
  cases r with
  | commit seq => trivial
  | op seq o values =>
    simp only [Record.DistinctKeys]
    unfold recordOfWire at h
    split at h
    · rename_i fields
      obtain ⟨-, hfields⟩ := Wire.distinctKeys_obj_iff.1 hw
      cases hseq : getNat fields "seq" "record" with
      | error e => simp [hseq, error_bind] at h
      | ok s =>
        simp only [hseq, ok_bind] at h
        split at h
        · cases hs : strict fields ["seq", "commit"] "record" <;> simp [hs, error_bind, ok_bind, pure_ok] at h
        · rename_i o' _ _
          cases hs : strict fields ["seq", "op", "values"] "record" with
          | error e => simp [hs, error_bind] at h
          | ok u =>
            simp only [hs, ok_bind] at h
            split at h
            · cases ho : opOfWire o' <;> simp [ho, pure_ok, ok_bind, error_bind] at h
              obtain ⟨-, -, rfl⟩ := h
              simp
            · rename_i entries hvals
              cases hp : payloads entries with
              | error e => simp [hp, error_bind] at h
              | ok vs =>
                cases ho : opOfWire o' <;> simp [hp, ho, pure_ok, ok_bind, error_bind] at h
                obtain ⟨-, -, rfl⟩ := h
                rw [payloads_keys hp]
                exact (Wire.distinctKeys_obj_iff.1 (hfields _ (mem_of_lookup hvals))).1
            · simp [throw_error, error_bind] at h
        · simp [throw_error] at h
    · simp [throw_error] at h

/-- The codec reads only records whose payloads have distinct keys. --/
def Codec.DecodesDistinct (c : Codec) : Prop := ∀ line r, c.decode line = .ok r → r.DistinctKeys

/-- The text form reads only records whose payloads have distinct keys, since no object of a line may
    repeat a key (`Wire.distinctKeys_of_parse`). --/
theorem wireCodec_decodesDistinct : wireCodec.DecodesDistinct := by
  intro line r h
  simp only [wireCodec, Codec.ofWire] at h
  cases hp : Wire.parse line with
  | error e => simp [hp, error_bind] at h
  | ok w =>
    simp only [hp, ok_bind] at h
    exact recordOfWire_distinctKeys (Wire.distinctKeys_of_parse hp) h

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

/-- A recording is the lines of the header and the records, each ended by a newline. --/
theorem recording_toList (c : Codec) (header : Header) (rs : List Record) :
    (recording c header rs).toList =
      ((c.encodeHeader header).toList :: rs.map fun r => (c.encode r).toList).flatMap (· ++ ['\n']) := by
  simp [recording, text_toList]

/-- The lines of a recording have no newline of their own. --/
theorem newline_not_mem_lines {c : Codec} (hc : c.Lawful) (header : Header) (rs : List Record) :
    ∀ l ∈ (c.encodeHeader header).toList :: rs.map fun r => (c.encode r).toList, '\n' ∉ l := by
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · exact hc.newline_not_mem_encodeHeader header
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hl
    exact hc.newline_not_mem_encode r

/-! ## Recording -/

theorem transaction_eq_ok {p : Definition} {s : State} {o : Op} {values known : List (Value × String)} {seq : Nat}
    {next : State} {records : List Record} :
    transaction p s o values known seq = .ok (next, records) ↔
      (values.map (·.1)).Nodup ∧ step p s o = .ok next ∧ unexpected s next values = [] ∧
        missing s next values known = [] ∧ records = [.op seq o values, .commit (seq + 1)] := by
  unfold transaction
  by_cases hk : (values.map (·.1)).Nodup
  · simp only [hk, ↓reduceIte, pure_ok, true_and]
    cases hs : step p s o with
    | error e => simp [error_bind]
    | ok n =>
      by_cases hu : unexpected s n values = []
      · by_cases hm : missing s n values known = []
        · simp only [hu, hm, List.isEmpty_nil, ok_bind]
          constructor
          · intro h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
            exact ⟨rfl, hu, hm, rfl⟩
          · rintro ⟨h1, -, -, rfl⟩
            rw [Except.ok.inj h1]
            rfl
        · have hm' : (missing s n values known).isEmpty = false := by simpa using hm
          simp only [hu, List.isEmpty_nil, ok_bind, hm', throw_error]
          constructor
          · intro h; cases h
          · rintro ⟨h1, -, hm'', -⟩
            rw [← Except.ok.inj h1] at hm''
            exact absurd hm'' hm
      · have hu' : (unexpected s n values).isEmpty = false := by simpa using hu
        simp only [ok_bind, hu', throw_error]
        constructor
        · intro h; cases h
        · rintro ⟨h1, hu'', -⟩
          rw [← Except.ok.inj h1] at hu''
          exact absurd hu'' hu
  · simp [hk, throw_error, error_bind]

theorem record_cons_ok {p : Definition} {s t : State} {o : Op} {values known : List (Value × String)}
    {rest : List (Op × List (Value × String))} {seq : Nat} {rs : List Record}
    (h : record p s ((o, values) :: rest) known seq = .ok (t, rs)) :
    ∃ next later, (values.map (·.1)).Nodup ∧ step p s o = .ok next ∧ unexpected s next values = [] ∧
      missing s next values known = [] ∧ record p next rest (known ++ values) (seq + 2) = .ok (t, later) ∧
      rs = .op seq o values :: .commit (seq + 1) :: later := by
  simp only [record] at h
  cases ht : transaction p s o values known seq with
  | error e => simp [ht, error_bind] at h
  | ok x =>
    obtain ⟨next, records⟩ := x
    obtain ⟨hk, hs, hu, hm, rfl⟩ := transaction_eq_ok.1 ht
    cases hr : record p next rest (known ++ values) (seq + 2) with
    | error e => simp [ht, hr, ok_bind, map_error] at h
    | ok y =>
      obtain ⟨final, later⟩ := y
      simp [ht, hr, ok_bind, pure_ok] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨next, later, hk, hs, hu, hm, hr, rfl⟩

theorem record_cons_of {p : Definition} {s next t : State} {o : Op} {values known : List (Value × String)}
    {rest : List (Op × List (Value × String))} {seq : Nat} {later : List Record}
    (hk : (values.map (·.1)).Nodup) (hs : step p s o = .ok next) (hu : unexpected s next values = [])
    (hm : missing s next values known = [])
    (hr : record p next rest (known ++ values) (seq + 2) = .ok (t, later)) :
    record p s ((o, values) :: rest) known seq = .ok (t, .op seq o values :: .commit (seq + 1) :: later) := by
  have ht : transaction p s o values known seq = .ok (next, [.op seq o values, .commit (seq + 1)]) :=
    transaction_eq_ok.2 ⟨hk, hs, hu, hm, rfl⟩
  simp [record, ht, hr, ok_bind, pure_ok]

theorem record_length {p : Definition} :
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
    obtain ⟨next, later, -, -, -, -, hr, rfl⟩ := record_cons_ok h
    simp [ih hr]
    omega

/-- The recorder repeats no payload key, so every record it writes reads back (`Codec.Lawful`). --/
theorem record_distinctKeys {p : Definition} :
    ∀ {steps : List (Op × List (Value × String))} {s t : State} {known : List (Value × String)} {seq : Nat}
      {rs : List Record}, record p s steps known seq = .ok (t, rs) → ∀ r ∈ rs, r.DistinctKeys := by
  intro steps
  induction steps with
  | nil =>
    intro s t known seq rs h
    simp only [record, pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons step rest ih =>
    obtain ⟨o, values⟩ := step
    intro s t known seq rs h r hr
    obtain ⟨next, later, hk, -, -, -, hlater, rfl⟩ := record_cons_ok h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hk
    rcases List.mem_cons.1 hr with rfl | hr
    · trivial
    · exact ih hlater r hr

/-- Recording two lists of transactions one after the other records their concatenation; the
    second recording knows the payloads of the first. --/
theorem record_append {p : Definition} :
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
    obtain ⟨next, later, hk, hs, hu, hm, hr, rfl⟩ := record_cons_ok h₁
    have h₂' : record p u ys (known ++ values ++ rest.flatMap (·.2)) (seq + 2 + 2 * rest.length) =
        .ok (t, rs₂) := by
      rw [show seq + 2 + 2 * rest.length = seq + 2 * (rest.length + 1) by omega]
      simpa using h₂
    exact record_cons_of hk hs hu hm (ih hr h₂')

theorem text_append (c : Codec) (rs₁ rs₂ : List Record) : text c (rs₁ ++ rs₂) = text c rs₁ ++ text c rs₂ := by
  simp [text, String.join_append]

theorem recording_append (c : Codec) (header : Header) (rs₁ rs₂ : List Record) :
    recording c header rs₁ ++ text c rs₂ = recording c header (rs₁ ++ rs₂) := by
  simp [recording, text_append, String.append_assoc]

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

theorem replayLine_op {c : Codec} (hc : c.Lawful) (p : Definition) (r : Replay) (index seq : Nat) (o : Op)
    (values : List (Value × String)) (hkeys : (values.map (·.1)).Nodup) (hpending : r.pending = none)
    (hnext : r.next = seq) :
    replayLine c p r index (String.ofList (c.encode (.op seq o values)).toList) =
      .ok { r with pending := some (o, values), next := seq + 1 } := by
  have hdecode := hc.decode_encode (.op seq o values) hkeys
  obtain ⟨state, committed, known, pending, next⟩ := r
  simp only at hpending hnext
  subst hpending hnext
  simp [replayLine, hdecode, Record.seq, pure_ok]

theorem replayLine_commit {c : Codec} (hc : c.Lawful) (p : Definition) (r : Replay) (index seq : Nat) (o : Op)
    (values : List (Value × String)) (next : State) (hpending : r.pending = some (o, values))
    (hnext : r.next = seq) (hs : step p r.state o = .ok next) (hu : unexpected r.state next values = [])
    (hm : missing r.state next values r.values = []) :
    replayLine c p r index (String.ofList (c.encode (.commit seq)).toList) =
      .ok { state := next, committed := r.committed + 1, values := r.values ++ values, pending := none,
            next := seq + 1 } := by
  have hdecode := hc.decode_encode (.commit seq) trivial
  obtain ⟨state, committed, known, pending, n⟩ := r
  simp only at hpending hnext hs hu hm
  subst hpending hnext
  simp [replayLine, hdecode, Record.seq, hs, hu, hm, pure_ok]

theorem replayLines_append (c : Codec) (p : Definition) (xs ys : List (List Char)) :
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
theorem replayLines_take {c : Codec} (hc : c.Lawful) {p : Definition} :
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
    obtain ⟨next, later, hkeys, hs, hu, hm, hr, rfl⟩ := record_cons_ok h
    have hop := replayLine_op hc p r index seq o values hkeys hpending hnext
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
        (index + 1) (seq + 1) o values next rfl rfl (by simpa [hstate] using hs) (by simpa [hstate] using hu)
        (by simpa [hstate, hvalues] using hm)
      obtain ⟨u, hu', hreplay⟩ := ih hr
        { state := next, committed := r.committed + 1, values := r.values ++ values, pending := none,
          next := seq + 1 + 1 } (index + 1 + 1) k rfl (by simp [hvalues]) rfl rfl hk'
      refine ⟨u, ?_, ?_⟩
      · have hhalf : (k + 2) / 2 = k / 2 + 1 := by omega
        have htwice : 2 * (k / 2 + 1) = 2 * (k / 2) + 1 + 1 := by omega
        rw [hhalf, List.take_succ_cons, htwice, List.take_succ_cons, List.take_succ_cons]
        exact record_cons_of hkeys hs hu hm hu'
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

/-- The header line of a recording reads back to its header. --/
theorem decodeHeader_line {c : Codec} (hc : c.Lawful) {header : Header} (hw : header.definition.DistinctKeys) :
    (c.decodeHeader (String.ofList (c.encodeHeader header).toList)).mapError (s!"line 1: {·}") = .ok header := by
  simp [hc.decodeHeader_encodeHeader header hw, mapError_ok]

/-- A crash inside the header, the first line, leaves no complete line: nothing is committed, and the
    record names no definition yet. --/
theorem check_torn_header (c : Codec) (load : Header → Except String Definition) {tail : String}
    (htail : '\n' ∉ tail.toList) :
    check c load tail =
      .ok { definition := none, validated := none, state := {}, committed := 0, uncommitted := decide (tail ≠ ""),
            values := [] } := by
  have hsplit : splitLines tail.toList [] = ([], tail.toList) := by simpa using splitLines_of_not_mem htail []
  have htailEmpty : tail.toList.isEmpty = decide (tail = "") := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, String.toList_eq_nil_iff, decide_eq_true_iff]
  simp only [check, hsplit, pure_ok, htailEmpty]
  simp

/-- A crash after the header leaves it, the first `k` records a recorder wrote, and possibly the start
    of the next line. Checking such a text loads the definition of the header, replays exactly the
    committed transitions, the first `k / 2`, and reports the rest as uncommitted, and the flag of the
    header. With `check_torn_header`, this covers a crash anywhere in a recording. The definition of
    the header repeats no key; a recorder writes the canonical form of its definition, which has none
    (`Codec.definitionWire_distinctKeys`). --/
theorem check_torn {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      check c load (recording c header (rs.take k) ++ tail) =
        .ok { definition := some p, validated := some header.validated, state := u, committed := k / 2,
              uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } := by
  obtain ⟨u, hu, hreplay⟩ := replayLines_take hc h {} 1 k rfl rfl rfl rfl hk
  refine ⟨u, hu, ?_⟩
  have hsplit : splitLines (recording c header (rs.take k) ++ tail).toList [] =
      ((c.encodeHeader header).toList :: (rs.take k).map fun x => (c.encode x).toList, tail.toList) := by
    rw [String.toList_append, recording_toList]
    exact splitLines_lines (newline_not_mem_lines hc header (rs.take k)) htail
  have hlen := record_length h
  have hpending : (if k % 2 = 1 then steps[k / 2]? else none).isSome = decide (k % 2 = 1) := by
    by_cases hodd : k % 2 = 1
    · have : k / 2 < steps.length := by omega
      simp [hodd, this]
    · simp [hodd]
  have htailEmpty : tail.toList.isEmpty = decide (tail = "") := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, String.toList_eq_nil_iff, decide_eq_true_iff]
  simp only [check, hsplit, decodeHeader_line hc hw, hload, mapError_ok, hreplay, ok_bind, pure_ok, hpending,
    htailEmpty]
  simp

/-- Replaying a whole record reproduces the state of the run that wrote it. --/
theorem check_text {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) :
    check c load (recording c header rs) =
      .ok { definition := some p, validated := some header.validated, state := t, committed := steps.length,
            uncommitted := false, values := steps.flatMap (·.2) } := by
  have hlen := record_length h
  obtain ⟨u, hu, hcheck⟩ := check_torn hc hw hload h (Nat.le_refl rs.length) (tail := "") (by simp)
  have hhalf : rs.length / 2 = steps.length := by omega
  have hmod : rs.length % 2 = 0 := by omega
  rw [hhalf, List.take_length, h] at hu
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hu)
  rw [List.take_length, String.append_empty, hhalf, hmod, List.take_length] at hcheck
  simpa using hcheck

theorem recover_text {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) :
    recover c load (recording c header rs) = .ok t := by
  simp [recover, check_text hc hw hload h, Except.map]

/-- After a crash, recovery resumes from the state of the committed transitions. --/
theorem recover_torn {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      recover c load (recording c header (rs.take k) ++ tail) = .ok u := by
  obtain ⟨u, hu, hcheck⟩ := check_torn hc hw hload h hk htail
  exact ⟨u, hu, by simp [recover, hcheck, Except.map]⟩

/-- After a crash the runtime keeps the header as it was written and the committed lines, resumes from
    the recovered state with the committed payloads, and appends the records of new transactions; the
    result replays like an uninterrupted record. --/
theorem check_resume {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps more : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) {u t' : State} {rs' : List Record}
    (hu : recover c load (recording c header (rs.take k) ++ tail) = .ok u)
    (hmore : record p u more ((steps.take (k / 2)).flatMap (·.2)) (2 * (k / 2) + 1) = .ok (t', rs')) :
    check c load (recording c header (rs.take (2 * (k / 2))) ++ text c rs') =
      .ok { definition := some p, validated := some header.validated, state := t', committed := k / 2 + more.length,
            uncommitted := false, values := (steps.take (k / 2) ++ more).flatMap (·.2) } := by
  obtain ⟨u₀, hu₀, hrecover⟩ := recover_torn hc hw hload h hk htail
  rw [hu] at hrecover
  obtain rfl := (Except.ok.inj hrecover).symm
  have hlen := record_length h
  have htake : (steps.take (k / 2)).length = k / 2 := by simp; omega
  have hall : record p {} (steps.take (k / 2) ++ more) [] 1 = .ok (t', rs.take (2 * (k / 2)) ++ rs') :=
    record_append hu₀ (by rw [htake, Nat.add_comm]; simpa using hmore)
  rw [recording_append, check_text hc hw hload hall, List.length_append, htake]

/-! ### A crash anywhere

A crash may cut a recording at any character. What is left is a part of the header, or the header,
some records and a part of the next line (`prefix_recording`); `check_torn_header` and `check_torn`
cover both. -/

/-- A prefix of lines, each ended by a newline, is some of the lines and then a part of the next one,
    without a newline. --/
theorem prefix_lines : ∀ {lines : List (List Char)}, (∀ l ∈ lines, '\n' ∉ l) → ∀ {pre : List Char},
    pre <+: lines.flatMap (· ++ ['\n']) →
    ∃ k ≤ lines.length, ∃ tail, '\n' ∉ tail ∧ pre = (lines.take k).flatMap (· ++ ['\n']) ++ tail
  | [], _, pre, h => by
    obtain rfl := List.prefix_nil.1 h
    exact ⟨0, Nat.le_refl _, [], by simp, by simp⟩
  | l :: ls, hlines, pre, h => by
    have hl : '\n' ∉ l := hlines l List.mem_cons_self
    have hls : ∀ l' ∈ ls, '\n' ∉ l' := fun l' m => hlines l' (List.mem_cons_of_mem _ m)
    rw [List.flatMap_cons, List.append_assoc] at h
    rcases List.prefix_or_prefix_of_prefix h (List.prefix_append l _) with hpl | hlp
    · exact ⟨0, Nat.zero_le _, pre, fun m => hl (hpl.subset m), by simp⟩
    · obtain ⟨r, rfl⟩ := hlp
      have hr := (List.prefix_append_right_inj l).1 h
      cases r with
      | nil => exact ⟨0, Nat.zero_le _, l, hl, by simp⟩
      | cons x r =>
        rw [List.singleton_append, List.cons_prefix_cons] at hr
        obtain ⟨rfl, hr⟩ := hr
        obtain ⟨k, hk, tail, htail, rfl⟩ := prefix_lines hls hr
        exact ⟨k + 1, by simp; omega, tail, htail, by simp⟩

/-- What a crash leaves of a recording: a part of the header, without a newline, or the header, the
    first `k` records and a part of the next line. --/
theorem prefix_recording {c : Codec} (hc : c.Lawful) (header : Header) (rs : List Record) {pre : String}
    (h : pre.toList <+: (recording c header rs).toList) :
    '\n' ∉ pre.toList ∨
      ∃ k ≤ rs.length, ∃ tail : String, '\n' ∉ tail.toList ∧ pre = recording c header (rs.take k) ++ tail := by
  rw [recording_toList] at h
  obtain ⟨k, hk, tail, htail, hpre⟩ := prefix_lines (newline_not_mem_lines hc header rs) h
  cases k with
  | zero => exact Or.inl (by simpa [hpre] using htail)
  | succ k =>
    refine Or.inr ⟨k, by simp at hk; omega, String.ofList tail, by simpa using htail, String.ext ?_⟩
    rw [String.toList_append, recording_toList, hpre, String.toList_ofList]
    simp [List.map_take]

/-- A crash anywhere in a recording, the header included, leaves a text that checks: before the header
    is complete, to nothing; after it, to exactly the transitions whose commit records are complete,
    which are the first `k / 2` when the text holds the first `k` records. --/
theorem check_prefix {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {pre : String} (hpre : pre.toList <+: (recording c header rs).toList) :
    ('\n' ∉ pre.toList ∧
      check c load pre =
        .ok { definition := none, validated := none, state := {}, committed := 0, uncommitted := decide (pre ≠ ""),
              values := [] }) ∨
    ∃ k ≤ rs.length, ∃ tail : String, '\n' ∉ tail.toList ∧ pre = recording c header (rs.take k) ++ tail ∧
      ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
        check c load pre =
          .ok { definition := some p, validated := some header.validated, state := u, committed := k / 2,
                uncommitted := decide (k % 2 = 1 ∨ tail ≠ ""), values := (steps.take (k / 2)).flatMap (·.2) } := by
  rcases prefix_recording hc header rs hpre with hnl | ⟨k, hk, tail, htail, rfl⟩
  · exact Or.inl ⟨hnl, check_torn_header c load hnl⟩
  · obtain ⟨u, hu, hcheck⟩ := check_torn hc hw hload h hk htail
    exact Or.inr ⟨k, hk, tail, htail, rfl, u, hu, hcheck⟩

/-- After a crash anywhere in a recording, recovery gives the state after the first `n` transitions,
    those whose commit records survived (`check_prefix`). --/
theorem recover_prefix {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {pre : String} (hpre : pre.toList <+: (recording c header rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover c load pre = .ok u := by
  rcases check_prefix hc hw hload h hpre with ⟨-, hcheck⟩ | ⟨k, hk, tail, -, -, u, hu, hcheck⟩
  · exact ⟨0, Nat.zero_le _, {}, by simp [record, pure_ok], by simp [recover, hcheck, Except.map]⟩
  · have hlen := record_length h
    exact ⟨k / 2, by omega, u, hu, by simp [recover, hcheck, Except.map]⟩

/-- After a crash anywhere in a recording, the runtime keeps the header as it was written (writing it
    again if the crash cut it) and the committed lines, resumes from the recovered state with the
    committed payloads, and appends the records of new transactions; the result replays like an
    uninterrupted record. --/
theorem check_resume_prefix {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition}
    {header : Header} (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {pre : String} (hpre : pre.toList <+: (recording c header rs).toList) :
    ∃ n ≤ steps.length, ∃ u, record p {} (steps.take n) [] 1 = .ok (u, rs.take (2 * n)) ∧
      recover c load pre = .ok u ∧
      ∀ {more : List (Op × List (Value × String))} {t' : State} {rs' : List Record},
        record p u more ((steps.take n).flatMap (·.2)) (2 * n + 1) = .ok (t', rs') →
        check c load (recording c header (rs.take (2 * n)) ++ text c rs') =
          .ok { definition := some p, validated := some header.validated, state := t', committed := n + more.length,
                uncommitted := false, values := (steps.take n ++ more).flatMap (·.2) } := by
  obtain ⟨n, hn, u, hu, hrecover⟩ := recover_prefix hc hw hload h hpre
  refine ⟨n, hn, u, hu, hrecover, fun {more t' rs'} hmore => ?_⟩
  have htake : (steps.take n).length = n := by simp; omega
  have hall : record p {} (steps.take n ++ more) [] 1 = .ok (t', rs.take (2 * n) ++ rs') :=
    record_append hu (by rw [htake, Nat.add_comm]; simpa using hmore)
  rw [recording_append, check_text hc hw hload hall, List.length_append, htake]

/-- The lines of a text that starts with a header line are that line and the lines after it. --/
theorem splitLines_header (c : Codec) (hc : c.Lawful) (header : Header) (rest : String) :
    (splitLines (c.encodeHeader header ++ "\n" ++ rest).toList []).1 =
      (c.encodeHeader header).toList :: (splitLines rest.toList []).1 := by
  rw [String.toList_append, String.toList_append, List.append_assoc,
    splitLines_append_of_not_mem (hc.newline_not_mem_encodeHeader header)]
  simp [splitLines]

/-- A record whose header holds a definition that `load` refuses is refused at line 1, with the error
    of `load`, whatever follows the header. --/
theorem check_load_error {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {e : String} (hload : load header = .error e) (rest : String) :
    check c load (c.encodeHeader header ++ "\n" ++ rest) = .error s!"line 1: {e}" := by
  simp only [check, splitLines_header c hc header rest]
  simp only [decodeHeader_line hc hw, hload, mapError_error, ok_bind, error_bind]

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

theorem replayLine_covered {c : Codec} {p : Definition} {r r' : Replay} {index : Nat} {line : String}
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
          · simp [throw_error] at h
          · split at h
            · rename_i hm
              simp only [pure_ok, Except.ok.injEq] at h
              subst h
              exact covered_of_missing (by simpa using hm) hr
            · simp [throw_error] at h
        · simp [throw_error] at h
      · simp [throw_error] at h
      · simp [throw_error] at h

theorem replayLines_covered {c : Codec} {p : Definition} :
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

/-- A record that checks has a header that `load` read, unless it has no complete line; the checked
    record replays its other lines against the definition that `load` gave. --/
theorem check_eq_ok {c : Codec} {load : Header → Except String Definition} {text : String} {checked : Checked}
    (h : check c load text = .ok checked) :
    (checked.definition = none ∧ checked.validated = none ∧ checked.state = {} ∧ checked.values = []) ∨
      ∃ header p lines r, load header = .ok p ∧ replayLines c p {} 1 lines = .ok r ∧ checked.definition = some p ∧
        checked.validated = some header.validated ∧ checked.state = r.state ∧ checked.values = r.values := by
  simp only [check] at h
  split at h
  · simp only [pure_ok, Except.ok.injEq] at h
    subst h
    exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · rename_i line lines _
    cases hd : c.decodeHeader (String.ofList line) with
    | error e => simp [hd, mapError_error, error_bind] at h
    | ok header =>
      cases hl : load header with
      | error e => simp [hd, hl, mapError_ok, mapError_error, ok_bind, error_bind] at h
      | ok p =>
        cases hr : replayLines c p {} 1 lines with
        | error e => simp [hd, hl, hr, mapError_ok, ok_bind, map_error] at h
        | ok r =>
          simp only [hd, hl, hr, mapError_ok, ok_bind, pure_ok, Except.ok.injEq] at h
          subst h
          exact Or.inr ⟨header, p, lines, r, hl, hr, rfl, rfl, rfl, rfl⟩

/-- Every value a checked state mentions has its payload among the committed ones, so a recovered
    state never names a lost value (§12.1). --/
theorem check_payloads {c : Codec} {load : Header → Except String Definition} {text : String}
    {checked : Checked} (h : check c load text = .ok checked) :
    ∀ v ∈ checked.state.values, checked.values.any (·.1 == v) = true := by
  have hempty : Replay.Covered {} := fun v hv => by simp [State.values] at hv
  rcases check_eq_ok h with ⟨-, -, hstate, hvalues⟩ | ⟨header, p, lines, r, -, hr, -, -, hstate, hvalues⟩
  · rw [hstate, hvalues]
    exact hempty
  · rw [hstate, hvalues]
    exact replayLines_covered hempty hr

/-- The definition a checked record names is one that `load` read from its header, and the record
    reports the flag of that header. --/
theorem check_definition {c : Codec} {load : Header → Except String Definition} {text : String} {checked : Checked}
    {q : Definition} (h : check c load text = .ok checked) (hq : checked.definition = some q) :
    ∃ header, load header = .ok q ∧ checked.validated = some header.validated := by
  rcases check_eq_ok h with ⟨hnone, -⟩ | ⟨header, p, lines, r, hl, -, hp, hv, -⟩
  · rw [hnone] at hq
    cases hq
  · rw [hp, Option.some.injEq] at hq
    exact ⟨header, hq ▸ hl, hv⟩

/-- A checked record names a definition exactly when it reports the flag of a header. --/
theorem check_validated_isSome {c : Codec} {load : Header → Except String Definition} {text : String}
    {checked : Checked} (h : check c load text = .ok checked) :
    checked.validated.isSome = checked.definition.isSome := by
  rcases check_eq_ok h with ⟨hd, hv, -⟩ | ⟨header, p, lines, r, -, -, hp, hv, -⟩
  · rw [hd, hv]
    rfl
  · rw [hp, hv]
    rfl

/-! ## Resuming under a definition (§12.1)

A run resumes only under the definition its record holds: `resume` compares the canonical forms,
which repeat no key, so forms that render alike are equal. -/

/-- Canonical forms that render alike are equal: they repeat no key, and a rendered value parses back
    to itself. --/
theorem definitionWire_eq_of_render {p q : Definition}
    (h : (Codec.definitionWire q).render = (Codec.definitionWire p).render) :
    Codec.definitionWire q = Codec.definitionWire p := by
  have hq := Wire.parse_render _ (Codec.definitionWire_distinctKeys q)
  rw [h, Wire.parse_render _ (Codec.definitionWire_distinctKeys p)] at hq
  exact (Except.ok.inj hq).symm

/-- The definition `agreeing load p` reads is the one `load` reads, when it has the canonical form
    of `p`. --/
theorem agreeing_eq_ok {load : Header → Except String Definition} {p q : Definition} {header : Header} :
    agreeing load p header = .ok q ↔ load header = .ok q ∧ Codec.definitionWire q = Codec.definitionWire p := by
  simp only [agreeing]
  cases hl : load header with
  | error e => simp [error_bind]
  | ok q' =>
    simp only [ok_bind, Except.ok.injEq]
    by_cases hr : (Codec.definitionWire q').render = (Codec.definitionWire p).render
    · simp only [hr, beq_self_eq_true, ↓reduceIte, pure_ok, Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨rfl, definitionWire_eq_of_render hr⟩
      · exact fun h => h.1
    · have hne : ((Codec.definitionWire q').render == (Codec.definitionWire p).render) = false := by
        simpa using hr
      simp only [hne, Bool.false_eq_true, ↓reduceIte, throw_error, error_bind, reduceCtorEq, false_iff,
        not_and]
      rintro rfl hw
      exact hr (congrArg Wire.render hw)

/-- `agreeing load p` refuses what `load` refuses, with the same error. --/
theorem agreeing_of_error {load : Header → Except String Definition} {p : Definition} {header : Header} {e : String}
    (h : load header = .error e) : agreeing load p header = .error e := by
  simp [agreeing, h, error_bind]

/-- A record checks with `agreeing load p` exactly when it checks with `load` and the definition of
    its header, once complete, has the canonical form of `p`; both checks then agree. --/
theorem check_agreeing {c : Codec} {load : Header → Except String Definition} {p : Definition} {text : String}
    {checked : Checked} :
    check c (agreeing load p) text = .ok checked ↔
      check c load text = .ok checked ∧
        ∀ q, checked.definition = some q → Codec.definitionWire q = Codec.definitionWire p := by
  simp only [check]
  split
  · refine ⟨fun h => ⟨h, fun q hq => ?_⟩, fun h => h.1⟩
    simp only [pure_ok, Except.ok.injEq] at h
    subst h
    simp at hq
  · rename_i line lines _
    cases hd : c.decodeHeader (String.ofList line) with
    | error e => simp [mapError_error, error_bind]
    | ok header =>
      simp only [mapError_ok, ok_bind]
      cases hl : load header with
      | error e => simp [agreeing_of_error hl, error_bind, mapError_error]
      | ok q =>
        by_cases hr : Codec.definitionWire q = Codec.definitionWire p
        · simp only [agreeing_eq_ok.2 ⟨hl, hr⟩]
          refine ⟨fun h => ⟨h, fun q' hq' => ?_⟩, fun h => h.1⟩
          cases hrep : replayLines c q {} 1 lines with
          | error e => simp only [mapError_ok, ok_bind, hrep, error_bind, reduceCtorEq] at h
          | ok r =>
            simp only [mapError_ok, ok_bind, hrep, pure_ok, Except.ok.injEq] at h
            subst h
            simp only [Option.some.injEq] at hq'
            exact hq' ▸ hr
        · have hag : ∀ q', agreeing load p header ≠ .ok q' := fun q' h => by
            obtain ⟨hq', hw⟩ := agreeing_eq_ok.1 h
            rw [hl, Except.ok.injEq] at hq'
            exact hr (hq' ▸ hw)
          cases ha : agreeing load p header with
          | ok q' => exact absurd ha (hag q')
          | error e =>
            simp only [mapError_error, mapError_ok, error_bind, ok_bind, reduceCtorEq, false_iff, not_and]
            intro h
            cases hrep : replayLines c q {} 1 lines with
            | error e => simp only [hrep, error_bind, reduceCtorEq] at h
            | ok r =>
              simp only [hrep, ok_bind, pure_ok, Except.ok.injEq] at h
              subst h
              exact fun hall => hr (hall q rfl)

/-- A record resumes under `p` exactly when it checks, its header is complete, and the definition
    the header holds has the canonical form of `p`; it resumes from the checked state. --/
theorem resume_eq_ok {c : Codec} {load : Header → Except String Definition} {p : Definition} {text : String}
    {s : State} :
    resume c load p text = .ok s ↔
      ∃ checked q, check c load text = .ok checked ∧ checked.definition = some q ∧
        Codec.definitionWire q = Codec.definitionWire p ∧ checked.state = s := by
  simp only [resume]
  cases hc : check c (agreeing load p) text with
  | error e =>
    simp only [error_bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro checked q hcheck hq hw _
    have := check_agreeing.2 ⟨hcheck, fun q' hq' => by rw [hq, Option.some.injEq] at hq'; exact hq' ▸ hw⟩
    rw [hc] at this
    cases this
  | ok checked =>
    obtain ⟨hcheck, hq⟩ := check_agreeing.1 hc
    simp only [ok_bind]
    cases hd : checked.definition with
    | none =>
      simp only [throw_error, reduceCtorEq, false_iff, not_exists, not_and]
      intro checked' q hcheck' hq' _ _
      rw [hcheck, Except.ok.injEq] at hcheck'
      subst hcheck'
      rw [hd] at hq'
      cases hq'
    | some q =>
      simp only [pure_ok, Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨checked, q, hcheck, hd, hq q hd, rfl⟩
      · rintro ⟨checked', q', hcheck', -, -, rfl⟩
        rw [hcheck, Except.ok.injEq] at hcheck'
        rw [hcheck']

/-- A record resumes only under a definition of the canonical form of the one its header holds
    (§12.1). --/
theorem resume_definitionWire {c : Codec} {load : Header → Except String Definition} {p : Definition}
    {text : String} {s : State} (h : resume c load p text = .ok s) :
    ∃ checked q, check c load text = .ok checked ∧ checked.definition = some q ∧
      Codec.definitionWire q = Codec.definitionWire p := by
  obtain ⟨checked, q, hcheck, hq, hw, -⟩ := resume_eq_ok.1 h
  exact ⟨checked, q, hcheck, hq, hw⟩

/-- A resumed run continues from the state `recover` gives. --/
theorem resume_recover {c : Codec} {load : Header → Except String Definition} {p : Definition} {text : String}
    {s : State} (h : resume c load p text = .ok s) : recover c load text = .ok s := by
  obtain ⟨checked, q, hcheck, -, -, rfl⟩ := resume_eq_ok.1 h
  simp [recover, hcheck, Except.map]

/-- A record without a complete line, which a crash inside the header leaves, does not resume. --/
theorem resume_torn_header (c : Codec) (load : Header → Except String Definition) (p : Definition) {tail : String}
    (htail : '\n' ∉ tail.toList) : resume c load p tail = .error "the record has no header" := by
  simp [resume, check_torn_header c (agreeing load p) htail, ok_bind, throw_error]

/-- A record whose header holds a definition that `load` refuses resumes under no definition: it is
    refused at line 1, with the error of `load`. --/
theorem resume_load_error {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {e : String} (hload : load header = .error e) (p : Definition)
    (rest : String) : resume c load p (c.encodeHeader header ++ "\n" ++ rest) = .error s!"line 1: {e}" := by
  simp [resume, check_load_error hc hw (agreeing_of_error (p := p) hload) rest, error_bind]

/-- A header whose definition `load` reads as `p` agrees with `p`. --/
theorem agreeing_of_load {load : Header → Except String Definition} {p : Definition} {header : Header}
    (hload : load header = .ok p) : agreeing load p header = .ok p :=
  agreeing_eq_ok.2 ⟨hload, rfl⟩

/-- A definition resumes a whole recording whose header it loads from, from the state of the run that
    wrote it. --/
theorem resume_text {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) :
    resume c load p (recording c header rs) = .ok t := by
  simp [resume, check_text hc hw (agreeing_of_load hload) h, ok_bind, pure_ok]

/-- After a crash that left the header complete, the definition resumes from the state of the
    committed transitions. --/
theorem resume_torn {c : Codec} (hc : c.Lawful) {load : Header → Except String Definition} {header : Header}
    (hw : header.definition.DistinctKeys) {p : Definition} (hload : load header = .ok p)
    {steps : List (Op × List (Value × String))} {t : State} {rs : List Record}
    (h : record p {} steps [] 1 = .ok (t, rs)) {k : Nat} (hk : k ≤ rs.length) {tail : String}
    (htail : '\n' ∉ tail.toList) :
    ∃ u, record p {} (steps.take (k / 2)) [] 1 = .ok (u, rs.take (2 * (k / 2))) ∧
      resume c load p (recording c header (rs.take k) ++ tail) = .ok u := by
  obtain ⟨u, hu, hcheck⟩ := check_torn hc hw (agreeing_of_load hload) h hk htail
  exact ⟨u, hu, by simp [resume, hcheck, ok_bind, pure_ok]⟩

end Suimon.Trace
