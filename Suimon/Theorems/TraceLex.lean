import Suimon.Theorems.TraceText

namespace Suimon.Trace.Text

private theorem digit_ne (c other : Char) (digit : c.isDigit = true) (notDigit : other.isDigit = false) : c ≠ other := by
  intro eq
  rw [eq, notDigit] at digit
  contradiction

theorem readAtom_digit (c : Char) (rest : Chars) (digit : c.isDigit = true) :
    readAtom (c :: rest) = readNumber false (c :: rest) := by
  simp [readAtom, digit_ne c _ digit (show '{'.isDigit = false by decide),
    digit_ne c _ digit (show '}'.isDigit = false by decide), digit_ne c _ digit (show '['.isDigit = false by decide),
    digit_ne c _ digit (show ']'.isDigit = false by decide), digit_ne c _ digit (show '"'.isDigit = false by decide),
    digit_ne c _ digit (show 't'.isDigit = false by decide), digit_ne c _ digit (show 'f'.isDigit = false by decide),
    digit_ne c _ digit (show 'n'.isDigit = false by decide), digit_ne c _ digit (show '-'.isDigit = false by decide)]

theorem readAtom_nat_prefix (n : Nat) (rest : Chars) :
    readAtom (n.repr.toList ++ rest) = readNumber false (n.repr.toList ++ rest) := by
  have nonempty : n.repr.toList ≠ [] := by rw [Nat.toList_repr]; exact Nat.toDigits_ne_nil
  cases chars : n.repr.toList with
  | nil => exact False.elim (nonempty chars)
  | cons c cs =>
    apply readAtom_digit
    apply Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by decide) (by decide)
    rw [← Nat.toList_repr, chars]
    simp

theorem readNumber_roundtrip (negative : Bool) (n exponent : Nat) (rest : Chars)
    (stops : rest.head?.all (fun c => !c.isDigit) = true) :
    readNumber negative (n.repr.toList ++ ['e', '-'] ++ exponent.repr.toList ++ rest) =
      some (.number (if negative then -(n : Int) else (n : Int)) exponent, rest) := by
  simp only [readNumber, List.append_assoc]
  rw [readNat_roundtrip n _ rfl]
  simp only [bind, Option.bind, List.cons_append, List.nil_append]
  rw [readNat_roundtrip exponent rest stops]
  rfl

theorem readAtom_render (atom : JsonAtom) (sep : Char) (rest : Chars) (allowed : sep = ' ' ∨ sep = ',') :
    readAtom (renderAtom atom ++ sep :: rest) = some (atom, sep :: rest) := by
  have stops : (sep :: rest).head?.all (fun c => !c.isDigit) = true := by rcases allowed with rfl | rfl <;> rfl
  have notColon : sep ≠ ':' := by rcases allowed with rfl | rfl <;> decide
  cases atom with
  | null => rfl
  | boolean value => cases value <;> rfl
  | arrayStart => rfl
  | arrayEnd => rfl
  | objectStart => rfl
  | objectEnd => rfl
  | string value =>
    change (do
      let (value, after) ← readString (quoted value ++ sep :: rest)
      match after with
      | ':' :: tail => pure (JsonAtom.field value, tail)
      | _ => pure (JsonAtom.string value, after)) = _
    rw [readString_roundtrip]
    simp [bind, Option.bind, notColon, pure]
  | field name =>
    change (do
      let (value, after) ← readString ((quoted name ++ [':']) ++ sep :: rest)
      match after with
      | ':' :: tail => pure (JsonAtom.field value, tail)
      | _ => pure (JsonAtom.string value, after)) = _
    rw [List.append_assoc, readString_roundtrip]
    rfl
  | number value exponent =>
    cases value with
    | ofNat n =>
      change readAtom (n.repr.toList ++ ['e', '-'] ++ exponent.repr.toList ++ sep :: rest) = _
      rw [List.append_assoc, List.append_assoc, readAtom_nat_prefix]
      simpa [List.append_assoc] using readNumber_roundtrip false n exponent (sep :: rest) stops
    | negSucc n =>
      simp only [renderAtom, Int.repr, String.toList_append]
      change readAtom (('-' :: (n + 1).repr.toList) ++ ['e', '-'] ++ exponent.repr.toList ++ sep :: rest) = _
      simp only [List.cons_append, readAtom, ↓reduceIte]
      simpa [List.append_assoc, Int.negSucc_eq] using readNumber_roundtrip true (n + 1) exponent (sep :: rest) stops


theorem readAtom_separator (c : Char) (rest : Chars) (isSeparator : separator c = true) : readAtom (c :: rest) = none := by
  simp only [separator, Bool.or_eq_true, beq_iff_eq] at isSeparator
  rcases isSeparator with (((rfl | rfl) | rfl) | rfl) | rfl <;>
    simp [readAtom, readNumber, readNat, String.toNat?_eq_none (s := "") (by apply Bool.eq_false_iff.mpr; simp [String.isNat_iff]), bind, Option.bind]

theorem renderAtom_head (atom : JsonAtom) : ∃ c rest, renderAtom atom = c :: rest ∧ separator c = false := by
  have parsed := readAtom_render atom ' ' [] (.inl rfl)
  cases encoded : renderAtom atom with
  | nil =>
    rw [encoded] at parsed
    have invalid := readAtom_separator ' ' [] (show separator ' ' = true from rfl)
    simp only [List.nil_append, invalid] at parsed
    contradiction
  | cons c rest =>
    refine ⟨c, rest, rfl, ?_⟩
    cases sep : separator c with
    | false => rfl
    | true =>
      rw [encoded, List.cons_append, readAtom_separator c (rest ++ [' ']) sep] at parsed
      contradiction

theorem dropSeparators_renderAtom (atom : JsonAtom) (rest : Chars) :
    (renderAtom atom ++ rest).dropWhile separator = renderAtom atom ++ rest := by
  obtain ⟨c, cs, encoded, head⟩ := renderAtom_head atom
  simp [encoded, head]

theorem readAtom_gap (atom : JsonAtom) (atoms : List JsonAtom) (rest : Chars) :
    readAtom (renderAtom atom ++ atomGap atom atoms ++ rest) = some (atom, atomGap atom atoms ++ rest) := by
  cases atoms with
  | nil => simpa [atomGap, List.append_assoc] using readAtom_render atom ' ' rest (.inl rfl)
  | cons next tail =>
    cases gap : endsValue atom && startsSibling next
    · simpa [atomGap, gap, List.append_assoc] using readAtom_render atom ' ' rest (.inl rfl)
    · simpa [atomGap, gap, List.append_assoc] using readAtom_render atom ',' (' ' :: rest) (.inr rfl)

theorem atomGap_drop (atom : JsonAtom) (atoms : List JsonAtom) (rest : Chars) :
    (atomGap atom atoms ++ rest).dropWhile separator = rest.dropWhile separator := by
  cases atoms with
  | nil => rfl
  | cons next tail => cases gap : endsValue atom && startsSibling next <;> simp [atomGap, gap, separator]

theorem lexAtoms_gap (fuel : Nat) (atom : JsonAtom) (atoms : List JsonAtom) (rest : Chars) :
    lexAtoms fuel (atomGap atom atoms ++ rest) = lexAtoms fuel rest := by
  cases fuel <;> simp only [lexAtoms, atomGap_drop]

theorem lexAtoms_step (fuel : Nat) (input rest : Chars) (atom : JsonAtom)
    (clean : input.dropWhile separator = input) (parsed : readAtom input = some (atom, rest)) :
    lexAtoms (fuel + 1) input = (lexAtoms fuel rest).map (atom :: ·) := by
  cases input with
  | nil => simp [readAtom] at parsed
  | cons c cs =>
    simp only [lexAtoms, clean, parsed, bind, Option.bind, pure]
    cases lexAtoms fuel rest <;> rfl

theorem lexAtoms_render (atoms : List JsonAtom) (fuel : Nat) (enough : atoms.length ≤ fuel) :
    lexAtoms fuel (renderAtoms atoms) = some atoms := by
  induction atoms generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons atom atoms ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have restEnough : atoms.length ≤ fuel := Nat.le_of_succ_le_succ enough
      rw [renderAtoms, lexAtoms_step fuel _ _ atom
        (by simpa only [List.append_assoc] using dropSeparators_renderAtom atom (atomGap atom atoms ++ renderAtoms atoms))
        (readAtom_gap atom atoms (renderAtoms atoms)), lexAtoms_gap, ih fuel restEnough]
      rfl

theorem atomGap_length (atom : JsonAtom) (atoms : List JsonAtom) : 1 ≤ (atomGap atom atoms).length := by
  cases atoms with
  | nil => simp [atomGap]
  | cons next tail => cases gap : endsValue atom && startsSibling next <;> simp [atomGap, gap]

theorem renderAtoms_length (atoms : List JsonAtom) : atoms.length ≤ (renderAtoms atoms).length := by
  induction atoms with
  | nil => exact Nat.le_refl _
  | cons atom atoms ih =>
    have gap := atomGap_length atom atoms
    simp only [renderAtoms, List.length_append, List.length_cons]
    omega

theorem roundtrip (atoms : List JsonAtom) : decode (encode atoms) = some atoms := by
  simp only [decode, encode, String.toList_ofList]
  exact lexAtoms_render atoms _ (renderAtoms_length atoms)

theorem lexAtoms_render_suffix (atoms : List JsonAtom) (rest : Chars) (fuel : Nat)
    (enough : atoms.length ≤ fuel) (whitespace : rest.dropWhile separator = []) :
    lexAtoms fuel (renderAtoms atoms ++ rest) = some atoms := by
  induction atoms generalizing fuel with
  | nil => cases fuel <;> simp [renderAtoms, lexAtoms, whitespace]
  | cons atom atoms ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have restEnough : atoms.length ≤ fuel := Nat.le_of_succ_le_succ enough
      have clean := dropSeparators_renderAtom atom (atomGap atom atoms ++ (renderAtoms atoms ++ rest))
      have parsed := readAtom_gap atom atoms (renderAtoms atoms ++ rest)
      simp only [List.append_assoc] at parsed
      simp only [renderAtoms, List.append_assoc]
      rw [lexAtoms_step fuel _ _ atom clean parsed, lexAtoms_gap, ih fuel restEnough]
      rfl

theorem roundtrip_suffix (atoms : List JsonAtom) (rest : String)
    (whitespace : rest.toList.dropWhile separator = []) :
    decode (encode atoms ++ rest) = some atoms := by
  simp only [decode, encode, String.toList_append, String.toList_ofList]
  apply lexAtoms_render_suffix atoms rest.toList
  · have bound := renderAtoms_length atoms
    simp only [List.length_append]
    omega
  · exact whitespace

end Suimon.Trace.Text
