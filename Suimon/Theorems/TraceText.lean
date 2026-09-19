import Suimon.Trace.Text

namespace Suimon.Trace.Text

theorem hex_roundtrip (n : Nat) (bound : n < 16) : hexValue (hexDigit n) = some n := by
  have checked : ∀ n : Fin 16, hexValue (hexDigit n.val) = some n.val := by decide
  exact checked ⟨n, bound⟩

theorem readStringBody_escape (c : Char) (rest : Chars) :
    readStringBody (escapeChar c ++ rest) = (readStringBody rest).map (fun (cs, tail) => (c :: cs, tail)) := by
  by_cases quote : c = '"'
  · subst c
    simp [escapeChar, readStringBody, bind, Option.bind, pure]
    cases readStringBody rest <;> rfl
  by_cases slash : c = '\\'
  · subst c
    simp [escapeChar, readStringBody, bind, Option.bind, pure]
    cases readStringBody rest <;> rfl
  by_cases control : c.toNat < 32
  · have high : c.toNat / 16 < 16 := by omega
    have low : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have number : c.toNat / 16 * 16 + c.toNat % 16 = c.toNat := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod c.toNat 16
    simp [escapeChar, quote, slash, control, readStringBody, hex_roundtrip _ high, hex_roundtrip _ low,
      number, bind, Option.bind, pure]
    cases readStringBody rest <;> rfl
  · simp [escapeChar, quote, slash, control, readStringBody, bind, Option.bind, pure]
    cases readStringBody rest <;> rfl

theorem readStringBody_roundtrip (chars rest : Chars) :
    readStringBody (chars.flatMap escapeChar ++ '"' :: rest) = some (chars, rest) := by
  induction chars with
  | nil => rfl
  | cons c chars ih =>
    simp only [List.flatMap_cons, List.append_assoc, readStringBody_escape, ih, Option.map_some]

theorem readString_roundtrip (s : String) (rest : Chars) : readString (quoted s ++ rest) = some (s, rest) := by
  simp [quoted, List.append_assoc, readString, readStringBody_roundtrip, bind, Option.bind, pure]

theorem digit_split (digits rest : Chars) (digitsOK : ∀ c ∈ digits, c.isDigit = true)
    (stops : rest.head?.all (fun c => !c.isDigit) = true) :
    (digits ++ rest).takeWhile Char.isDigit = digits ∧ (digits ++ rest).dropWhile Char.isDigit = rest := by
  induction digits with
  | nil =>
    cases rest with
    | nil => simp
    | cons c rest =>
      have stop : c.isDigit = false := by simpa using stops
      simp [stop]
  | cons c digits ih =>
    have first := digitsOK c (by simp)
    have remaining := ih (fun c h => digitsOK c (by simp [h]))
    simp [first, remaining.1, remaining.2]

theorem readNat_roundtrip (n : Nat) (rest : Chars) (stops : rest.head?.all (fun c => !c.isDigit) = true) :
    readNat ((Nat.repr n).toList ++ rest) = some (n, rest) := by
  have split := digit_split (Nat.toDigits 10 n) rest
    (fun c member => Nat.isDigit_of_mem_toDigits (by decide) (by decide) member) stops
  simp only [readNat, Nat.toList_repr, split.1, split.2]
  rw [← Nat.repr_eq_ofList_toDigits, Nat.toNat?_repr]
  rfl

end Suimon.Trace.Text
