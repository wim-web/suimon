import Suimon.WireText

namespace Suimon

namespace WireText

/-- The characters `pushEscaped` appends for `c`. --/
def escChars (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat < 32 then
    ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

/-- The characters of `s` as a quoted JSON string. --/
def strChars (s : String) : List Char :=
  '"' :: (s.toList.flatMap escChars ++ ['"'])

end WireText

open WireText in
mutual

/-- The rendering of a value as a character list, the specification of `Wire.renderTo`. --/
def Wire.textChars : Wire → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool true => ['t', 'r', 'u', 'e']
  | .bool false => ['f', 'a', 'l', 's', 'e']
  | .nat n => natDigits n []
  | .str s => strChars s
  | .arr items => '[' :: (Wire.itemsChars items true ++ [']'])
  | .obj fields => '{' :: (Wire.fieldsChars fields true ++ ['}'])

def Wire.itemsChars : List Wire → Bool → List Char
  | [], _ => []
  | w :: ws, first => (if first then [] else [',']) ++ (w.textChars ++ Wire.itemsChars ws false)

def Wire.fieldsChars : List (String × Wire) → Bool → List Char
  | [], _ => []
  | (k, v) :: fs, first =>
    (if first then [] else [',']) ++ (strChars k ++ ':' :: (v.textChars ++ Wire.fieldsChars fs false))

end

/-- Induction over `Wire` with hypotheses for every member of an array or object. --/
theorem Wire.induction {P : Wire → Prop} (null : P .null) (bool : ∀ b, P (.bool b))
    (nat : ∀ n, P (.nat n)) (str : ∀ s, P (.str s))
    (arr : ∀ items, (∀ w ∈ items, P w) → P (.arr items))
    (obj : ∀ fields, (∀ f ∈ fields, P f.2) → P (.obj fields)) (w : Wire) : P w :=
  Wire.rec (motive_1 := P) (motive_2 := fun items => ∀ w ∈ items, P w)
    (motive_3 := fun fields => ∀ f ∈ fields, P f.2) (motive_4 := fun f => P f.2)
    null bool nat str arr obj (by simp)
    (fun _ _ hh ht x hx => (List.mem_cons.1 hx).elim (fun h => h ▸ hh) (ht x))
    (by simp)
    (fun _ _ hh ht x hx => (List.mem_cons.1 hx).elim (fun h => h ▸ hh) (ht x))
    (fun _ _ h => h) w

theorem Wire.distinctKeys_arr_iff {items : List Wire} :
    (Wire.arr items).DistinctKeys ↔ ∀ w ∈ items, w.DistinctKeys :=
  ⟨fun | .arr h => h, .arr⟩

theorem Wire.distinctKeys_obj_iff {fields : List (String × Wire)} :
    (Wire.obj fields).DistinctKeys ↔ (fields.map (·.1)).Nodup ∧ ∀ f ∈ fields, f.2.DistinctKeys :=
  ⟨fun | .obj hk hf => ⟨hk, hf⟩, fun ⟨hk, hf⟩ => .obj hk hf⟩

namespace WireText

theorem toNat_ofNat (n : Nat) : (Char.ofNat n).toNat = if n.isValidChar then n else 0 := by
  unfold Char.ofNat
  split <;> rfl

theorem toNat_ofNat_of_lt (n : Nat) (h : n < 0xD800) : (Char.ofNat n).toNat = n := by
  simp only [toNat_ofNat, Nat.isValidChar]
  split <;> omega

theorem toNat_hexDigit (d : Nat) (h : d < 16) :
    (hexDigit d).toNat = if d < 10 then 48 + d else 87 + d := by
  unfold hexDigit
  split <;> rw [toNat_ofNat_of_lt _ (by omega)]

/-! ## Rendering matches the character specification -/

theorem pushEscaped_toList (acc : String) (c : Char) :
    (pushEscaped acc c).toList = acc.toList ++ escChars c := by
  unfold pushEscaped escChars
  split
  · simp
  split
  · simp
  split <;> simp

theorem foldl_pushEscaped_toList (l : List Char) (acc : String) :
    (l.foldl pushEscaped acc).toList = acc.toList ++ l.flatMap escChars := by
  induction l generalizing acc with
  | nil => simp
  | cons c l ih => simp [ih, pushEscaped_toList]

theorem pushString_toList (acc s : String) :
    (pushString acc s).toList = acc.toList ++ strChars s := by
  simp [pushString, strChars, String.foldl_eq_foldl_toList, foldl_pushEscaped_toList]

end WireText

open WireText

theorem Wire.renderTo_toList (w : Wire) :
    ∀ acc, (w.renderTo acc).toList = acc.toList ++ w.textChars := by
  induction w using Wire.induction with
  | null => intro acc; simp [Wire.renderTo, Wire.textChars]
  | bool b => intro acc; cases b <;> simp [Wire.renderTo, Wire.textChars]
  | nat n => intro acc; simp [Wire.renderTo, Wire.textChars]
  | str s => intro acc; simp [Wire.renderTo, Wire.textChars, pushString_toList]
  | arr items ih =>
    intro acc
    have key : ∀ acc first, (Wire.renderItems items acc first).toList =
        acc.toList ++ Wire.itemsChars items first := by
      induction items with
      | nil => intro acc first; simp [Wire.renderItems, Wire.itemsChars]
      | cons w ws ihl =>
        intro acc first
        simp only [List.mem_cons, forall_eq_or_imp] at ih
        simp only [Wire.renderItems, Wire.itemsChars, ihl ih.2, ih.1]
        cases first <;> simp
    simp [Wire.renderTo, Wire.textChars, key]
  | obj fields ih =>
    intro acc
    have key : ∀ acc first, (Wire.renderFields fields acc first).toList =
        acc.toList ++ Wire.fieldsChars fields first := by
      induction fields with
      | nil => intro acc first; simp [Wire.renderFields, Wire.fieldsChars]
      | cons f fs ihl =>
        intro acc first
        obtain ⟨k, v⟩ := f
        simp only [List.mem_cons, forall_eq_or_imp] at ih
        simp only [Wire.renderFields, Wire.fieldsChars, ihl ih.2, ih.1, String.toList_push,
          pushString_toList]
        cases first <;> simp
    simp [Wire.renderTo, Wire.textChars, key]

theorem Wire.render_toList (w : Wire) : w.render.toList = w.textChars := by
  simp [Wire.render, Wire.renderTo_toList]

namespace WireText

/-! ## Parsing the specification back -/

/-- The value of decimal digits read onto `a`. --/
def digitsVal (a : Nat) (l : List Char) : Nat :=
  l.foldl (fun a c => 10 * a + (c.toNat - 48)) a

/-- What may follow a value inside the rendering of a value, or at its end. --/
def Delim (rest : List Char) : Prop :=
  ∀ c r, rest = c :: r → c = ',' ∨ c = ']' ∨ c = '}'

theorem string_push_append_ofList (acc : String) (c : Char) (l : List Char) :
    acc.push c ++ String.ofList l = acc ++ String.ofList (c :: l) := by
  apply String.ext
  simp

theorem hexVal_hexDigit (d : Nat) (h : d < 16) : hexVal (hexDigit d) = some d := by
  by_cases hd : d < 10 <;> simp [hexVal, toNat_hexDigit d h, hd] <;> (try intro) <;>
    (repeat' split) <;> first | rfl | omega

theorem hex4_control (n : Nat) (h : n < 32) :
    hex4 '0' '0' (hexDigit (n / 16)) (hexDigit (n % 16)) = some n := by
  have h1 := hexVal_hexDigit (n / 16) (by omega)
  have h2 := hexVal_hexDigit (n % 16) (by omega)
  have h0 : hexVal '0' = some 0 := by simp [hexVal]
  simp only [hex4, h0, h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq]
  omega

theorem parseStringBody_escChars (c : Char) (rest : List Char) (acc : String) :
    parseStringBody (escChars c ++ rest) acc = parseStringBody rest (acc.push c) := by
  unfold escChars
  split
  · subst_vars; rw [parseStringBody.eq_def]; simp [simpleEscape]
  split
  · subst_vars; rw [parseStringBody.eq_def]; simp [simpleEscape]
  split
  · rename_i h1 h2 h3
    have hv := hex4_control c.toNat h3
    rw [parseStringBody.eq_def]
    simp [simpleEscape, hv]
    omega
  · rename_i h1 h2 h3
    rw [parseStringBody.eq_def]
    simp [h1, h2, h3]

theorem parseStringBody_escaped (l : List Char) :
    ∀ acc rest, parseStringBody (l.flatMap escChars ++ '"' :: rest) acc =
      .ok (acc ++ String.ofList l, rest) := by
  induction l with
  | nil => intro acc rest; rw [parseStringBody.eq_def]; simp
  | cons c l ih =>
    intro acc rest
    rw [← string_push_append_ofList, ← ih, List.flatMap_cons, List.append_assoc,
      parseStringBody_escChars]

theorem isDigit_ofNat (k : Nat) (h : k < 10) : isDigit (Char.ofNat (48 + k)) := by
  unfold isDigit; rw [toNat_ofNat_of_lt _ (by omega)]; omega

theorem natDigits_spec (n : Nat) (acc : List Char) :
    ∃ d ds, natDigits n acc = d :: (ds ++ acc) ∧ isDigit d ∧ (∀ c ∈ ds, isDigit c) ∧
      digitsVal 0 (d :: ds) = n ∧ (n = 0 → d = '0' ∧ ds = []) ∧ (0 < n → d ≠ '0') := by
  fun_induction natDigits n acc with
  | case1 n acc h =>
    refine ⟨_, [], rfl, isDigit_ofNat n h, by simp, ?_, ?_, ?_⟩
    · simp [digitsVal, toNat_ofNat_of_lt _ (show 48 + n < 0xD800 by omega)]
    · rintro rfl; exact ⟨rfl, rfl⟩
    · intro hn heq
      have := congrArg Char.toNat heq
      rw [toNat_ofNat_of_lt _ (by omega)] at this
      simp at this; omega
  | case2 n acc h ih =>
    obtain ⟨d, ds, heq, hd, hds, hval, _, hpos⟩ := ih
    refine ⟨d, ds ++ [Char.ofNat (48 + n % 10)], by simp [heq], hd, ?_, ?_, by omega, fun _ => hpos (by omega)⟩
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hds c hc
      · exact isDigit_ofNat _ (by omega)
    · simp only [digitsVal, List.foldl_cons, List.foldl_append, List.foldl_nil] at hval ⊢
      rw [hval, toNat_ofNat_of_lt _ (by omega)]
      omega

theorem spanDigits_append (ds rest : List Char) (hds : ∀ c ∈ ds, isDigit c)
    (hrest : ∀ c r, rest = c :: r → ¬ isDigit c) (a : Nat) :
    spanDigits (ds ++ rest) a = (digitsVal a ds, rest) := by
  induction ds generalizing a with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c r => simp [spanDigits, hrest c r rfl, digitsVal]
  | cons c ds ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hds
    simp [spanDigits, hds.1, ih hds.2, digitsVal]

theorem skipWs_delim {rest : List Char} (h : Delim rest) : skipWs rest = rest := by
  cases rest with
  | nil => rfl
  | cons c r => rcases h c r rfl with rfl | rfl | rfl <;> simp [skipWs, isWs]

theorem skipWs_cons_of {c : Char} (t : List Char) (h : isWs c = false) :
    skipWs (c :: t) = c :: t := by
  simp [skipWs, h]

theorem not_isDigit_of_delim {rest : List Char} (h : Delim rest) :
    ∀ c r, rest = c :: r → ¬ isDigit c := by
  intro c r hr
  rcases h c r hr with rfl | rfl | rfl <;> simp [isDigit]

theorem delim_nil : Delim [] := by
  intro c r h; cases h

theorem ne_of_isDigit {d : Char} (hd : isDigit d) (c : Char) (hc : ¬ isDigit c) : d ≠ c := by
  rintro rfl; exact hc hd

theorem isWs_of_isDigit {d : Char} (hd : isDigit d) : isWs d = false := by
  have h1 := ne_of_isDigit hd ' ' (by simp [isDigit])
  have h2 := ne_of_isDigit hd '\t' (by simp [isDigit])
  have h3 := ne_of_isDigit hd '\n' (by simp [isDigit])
  have h4 := ne_of_isDigit hd '\r' (by simp [isDigit])
  simp [isWs, h1, h2, h3, h4]

theorem textChars_head (w : Wire) :
    ∃ c t, w.textChars = c :: t ∧ isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases w with
  | null => exact ⟨_, _, rfl, by simp [isWs], by decide, by decide⟩
  | bool b => cases b <;> exact ⟨_, _, rfl, by simp [isWs], by decide, by decide⟩
  | nat n =>
    obtain ⟨d, ds, h, hd, -⟩ := natDigits_spec n []
    exact ⟨d, ds ++ [], h, isWs_of_isDigit hd, ne_of_isDigit hd _ (by simp [isDigit]),
      ne_of_isDigit hd _ (by simp [isDigit])⟩
  | str s => exact ⟨_, _, rfl, by simp [isWs], by decide, by decide⟩
  | arr items => exact ⟨_, _, rfl, by simp [isWs], by decide, by decide⟩
  | obj fields => exact ⟨_, _, rfl, by simp [isWs], by decide, by decide⟩

/-- A value parses back from its rendering followed by anything that may follow it. --/
def ValueOK (w : Wire) : Prop :=
  ∀ fuel rest, w.textChars.length ≤ fuel → Delim rest →
    parseValue fuel (w.textChars ++ rest) = .ok (w, rest)

theorem delim_itemsTail (xs : List Wire) (rest : List Char) :
    Delim (Wire.itemsChars xs false ++ ']' :: rest) := by
  cases xs <;> simp [Wire.itemsChars, Delim]

theorem delim_fieldsTail (fs : List (String × Wire)) (rest : List Char) :
    Delim (Wire.fieldsChars fs false ++ '}' :: rest) := by
  cases fs with
  | nil => simp [Wire.fieldsChars, Delim]
  | cons f fs => obtain ⟨k, v⟩ := f; simp [Wire.fieldsChars, Delim]

theorem parseItems_itemsChars (xs : List Wire) (hxs : ∀ w ∈ xs, ValueOK w) :
    ∀ x, ValueOK x → ∀ fuel rest acc,
      (x.textChars ++ Wire.itemsChars xs false).length + 1 ≤ fuel →
      parseItems fuel (x.textChars ++ (Wire.itemsChars xs false ++ ']' :: rest)) acc =
        .ok (.arr (acc.toList ++ x :: xs), rest) := by
  induction xs with
  | nil =>
    intro x hx fuel rest acc hf
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    have hv := hx g (Wire.itemsChars [] false ++ ']' :: rest) (by simp at hf; omega)
      (delim_itemsTail [] rest)
    simp only [Wire.itemsChars, List.nil_append] at hv
    simp [parseItems, Wire.itemsChars, hv, skipWs, isWs]
  | cons y ys ih =>
    intro x hx fuel rest acc hf
    simp only [List.mem_cons, forall_eq_or_imp] at hxs
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    have hv := hx g (Wire.itemsChars (y :: ys) false ++ ']' :: rest)
      (by simp at hf; omega) (delim_itemsTail _ rest)
    have hrec := ih hxs.2 y hxs.1 g rest (acc.push x)
      (by simp [Wire.itemsChars] at hf ⊢; omega)
    simp only [Wire.itemsChars, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append, List.append_assoc] at hv hrec ⊢
    simp [parseItems, hv, skipWs, isWs, hrec]

theorem parseStringBody_strChars (k : String) (rest : List Char) :
    parseStringBody (k.toList.flatMap escChars ++ '"' :: rest) "" = .ok (k, rest) := by
  simp [parseStringBody_escaped]

/-- A key that comes after the fields read so far, in fields without repeated keys, is new. --/
theorem any_key_eq_false {acc : Array (String × Wire)} {k : String} {v : Wire} {fs : List (String × Wire)}
    (h : ((acc.toList ++ (k, v) :: fs).map (·.1)).Nodup) : acc.any (·.1 == k) = false := by
  rw [← Array.any_toList, List.any_eq_false]
  intro f hf heq
  simp only [List.map_append, List.map_cons, List.nodup_append] at h
  exact h.2.2 f.1 (List.mem_map_of_mem hf) k List.mem_cons_self (by simpa using heq)

theorem parseFields_fieldsChars (fs : List (String × Wire)) (hfs : ∀ f ∈ fs, ValueOK f.2) :
    ∀ k v, ValueOK v → ∀ fuel rest acc,
      ((acc.toList ++ (k, v) :: fs).map (·.1)).Nodup →
      (strChars k ++ ':' :: (v.textChars ++ Wire.fieldsChars fs false)).length + 1 ≤ fuel →
      parseFields fuel (strChars k ++ ':' :: (v.textChars ++ (Wire.fieldsChars fs false ++ '}' :: rest)))
        acc = .ok (.obj (acc.toList ++ (k, v) :: fs), rest) := by
  induction fs with
  | nil =>
    intro k v hv fuel rest acc hkeys hf
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    have hval := hv g (Wire.fieldsChars [] false ++ '}' :: rest) (by simp at hf; omega)
      (delim_fieldsTail [] rest)
    have hnew := any_key_eq_false hkeys
    simp only [Wire.fieldsChars, List.nil_append] at hval
    simp [parseFields, strChars, Wire.fieldsChars, parseStringBody_strChars, hnew, hval, skipWs, isWs]
  | cons f fs ih =>
    intro k v hv fuel rest acc hkeys hf
    obtain ⟨k', v'⟩ := f
    simp only [List.mem_cons, forall_eq_or_imp] at hfs
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    have hval := hv g (Wire.fieldsChars ((k', v') :: fs) false ++ '}' :: rest)
      (by simp at hf; omega) (delim_fieldsTail _ rest)
    have hnew := any_key_eq_false hkeys
    have hrec := ih hfs.2 k' v' hfs.1 g rest (acc.push (k, v)) (by simpa using hkeys)
      (by simp [Wire.fieldsChars] at hf ⊢; omega)
    simp only [Wire.fieldsChars, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append, List.append_assoc, strChars] at hval hrec ⊢
    simp [parseFields, parseStringBody_strChars, hnew, hval, skipWs, isWs, hrec]

theorem parseValue_textChars (w : Wire) (hw : w.DistinctKeys) : ValueOK w := by
  induction w using Wire.induction with
  | null =>
    intro fuel rest hf hd
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [Wire.textChars] at hf; omega⟩
    simp [parseValue, Wire.textChars, skipWs, isWs, literal, expectWord]
  | bool b =>
    intro fuel rest hf hd
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by cases b <;> simp [Wire.textChars] at hf <;> omega⟩
    cases b <;> simp [parseValue, Wire.textChars, skipWs, isWs, literal, expectWord]
  | nat n =>
    intro fuel rest hf hd
    obtain ⟨d, ds, h, hdig, hds, hval, hzero, hpos⟩ := natDigits_spec n []
    simp only [Wire.textChars, h, List.append_nil] at hf ⊢
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have h1 := ne_of_isDigit hdig '{' (by simp [isDigit])
    have h2 := ne_of_isDigit hdig '[' (by simp [isDigit])
    have h3 := ne_of_isDigit hdig '"' (by simp [isDigit])
    have h4 := ne_of_isDigit hdig 't' (by simp [isDigit])
    have h5 := ne_of_isDigit hdig 'f' (by simp [isDigit])
    have h6 := ne_of_isDigit hdig 'n' (by simp [isDigit])
    have hnd := not_isDigit_of_delim hd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨rfl, rfl⟩ := hzero rfl
      cases rest with
      | nil => simp [parseValue, skipWs, isWs]
      | cons c r => simp [parseValue, skipWs, isWs, hnd c r rfl]
    · have hspan := spanDigits_append (d :: ds) rest (by simpa [hdig] using hds) hnd 0
      rw [hval] at hspan
      simp only [List.cons_append] at hspan
      simp [parseValue, skipWs, isWs_of_isDigit hdig, h1, h2, h3, h4, h5, h6, hpos hn, hdig, hspan]
  | str s =>
    intro fuel rest hf hd
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [Wire.textChars, strChars] at hf; omega⟩
    simp [parseValue, Wire.textChars, strChars, skipWs, isWs, parseStringBody_strChars]
  | arr items ih =>
    replace ih : ∀ w ∈ items, ValueOK w := fun w m => ih w m (Wire.distinctKeys_arr_iff.1 hw w m)
    intro fuel rest hf hd
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [Wire.textChars] at hf; omega⟩
    cases items with
    | nil => simp [parseValue, Wire.textChars, Wire.itemsChars, skipWs, isWs]
    | cons x xs =>
      simp only [List.mem_cons, forall_eq_or_imp] at ih
      have hitems := parseItems_itemsChars xs ih.2 x ih.1 g rest #[]
        (by simp [Wire.textChars, Wire.itemsChars] at hf ⊢; omega)
      obtain ⟨c, t, hct, hws, hne, -⟩ := textChars_head x
      rw [hct] at hitems
      simp only [Wire.textChars, Wire.itemsChars, ↓reduceIte, List.nil_append, hct,
        List.cons_append, List.append_assoc] at hitems ⊢
      simp only [parseValue]
      rw [skipWs_cons_of (c := '[') _ (by simp [isWs])]
      simp only [↓reduceIte]
      rw [skipWs_cons_of _ hws]
      simp [hne, hitems]
  | obj fields ih =>
    obtain ⟨hkeys, hall⟩ := Wire.distinctKeys_obj_iff.1 hw
    replace ih : ∀ f ∈ fields, ValueOK f.2 := fun f m => ih f m (hall f m)
    intro fuel rest hf hd
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [Wire.textChars] at hf; omega⟩
    cases fields with
    | nil => simp [parseValue, Wire.textChars, Wire.fieldsChars, skipWs, isWs]
    | cons f fs =>
      obtain ⟨k, v⟩ := f
      simp only [List.mem_cons, forall_eq_or_imp] at ih
      have hfields := parseFields_fieldsChars fs ih.2 k v ih.1 g rest #[] (by simpa using hkeys)
        (by simp [Wire.textChars, Wire.fieldsChars] at hf ⊢; omega)
      simp only [Wire.textChars, Wire.fieldsChars, ↓reduceIte, List.nil_append, strChars,
        List.cons_append, List.append_assoc] at hfields ⊢
      simp [parseValue, skipWs, isWs, hfields]

/-! ## No raw newline -/

theorem hexDigit_ne_newline (d : Nat) (h : d < 16) : hexDigit d ≠ '\n' := by
  intro he
  have := congrArg Char.toNat he
  rw [toNat_hexDigit d h] at this
  simp at this
  split at this <;> omega

theorem newline_not_mem_escChars (c : Char) : '\n' ∉ escChars c := by
  unfold escChars
  split
  · simp
  split
  · simp
  split
  · rename_i h
    simp [(hexDigit_ne_newline (c.toNat / 16) (by omega)).symm,
      (hexDigit_ne_newline (c.toNat % 16) (by omega)).symm]
  · rename_i h
    simp only [List.mem_singleton]
    rintro rfl
    simp at h

theorem newline_not_mem_strChars (s : String) : '\n' ∉ strChars s := by
  simp [strChars, newline_not_mem_escChars]

theorem newline_not_mem_natDigits (n : Nat) : '\n' ∉ natDigits n [] := by
  obtain ⟨d, ds, h, hd, hds, -⟩ := natDigits_spec n []
  rw [h, List.append_nil]
  intro hmem
  rcases List.mem_cons.1 hmem with he | he
  · exact ne_of_isDigit hd '\n' (by simp [isDigit]) he.symm
  · exact ne_of_isDigit (hds _ he) '\n' (by simp [isDigit]) rfl

theorem newline_not_mem_textChars (w : Wire) : '\n' ∉ w.textChars := by
  induction w using Wire.induction with
  | null => simp [Wire.textChars]
  | bool b => cases b <;> simp [Wire.textChars]
  | nat n => simpa [Wire.textChars] using newline_not_mem_natDigits n
  | str s => simpa [Wire.textChars] using newline_not_mem_strChars s
  | arr items ih =>
    have key : ∀ first, '\n' ∉ Wire.itemsChars items first := by
      induction items with
      | nil => simp [Wire.itemsChars]
      | cons w ws ihl =>
        intro first
        simp only [List.mem_cons, forall_eq_or_imp] at ih
        have := ihl ih.2 false
        cases first <;> simp_all [Wire.itemsChars]
    simpa [Wire.textChars] using key true
  | obj fields ih =>
    have key : ∀ first, '\n' ∉ Wire.fieldsChars fields first := by
      induction fields with
      | nil => simp [Wire.fieldsChars]
      | cons f fs ihl =>
        intro first
        obtain ⟨k, v⟩ := f
        simp only [List.mem_cons, forall_eq_or_imp] at ih
        have := ihl ih.2 false
        have hk := newline_not_mem_strChars k
        cases first <;> simp_all [Wire.fieldsChars]
    simpa [Wire.textChars] using key true

end WireText

open WireText

/-- A rendering contains no raw newline, so rendered values can be written as JSON lines. --/
theorem Wire.newline_not_mem_render (w : Wire) : '\n' ∉ (Wire.render w).toList := by
  rw [Wire.render_toList]
  exact newline_not_mem_textChars w

/-- Parsing inverts rendering for a value without repeated keys (the parser rejects a repeated key). --/
theorem Wire.parse_render (w : Wire) (hw : w.DistinctKeys) : Wire.parse (Wire.render w) = .ok w := by
  have h := parseValue_textChars w hw (w.textChars.length + 1) [] (by omega) delim_nil
  rw [List.append_nil] at h
  simp [Wire.parse, Wire.render_toList, h, skipWs]

/-! ## No repeated key -/

namespace WireText

theorem literal_eq_ok {word : List Char} {value w : Wire} {cs rest : List Char}
    (h : literal word value cs = .ok (w, rest)) : w = value := by
  unfold literal at h
  split at h
  · cases h; rfl
  · simp [fail] at h

/-- Every value the parser reads repeats no key, since `parseFields` rejects a key it has read. --/
theorem parsed_distinctKeys : ∀ fuel,
    (∀ cs w rest, parseValue fuel cs = .ok (w, rest) → w.DistinctKeys) ∧
    (∀ cs (acc : Array Wire) w rest, (∀ x ∈ acc.toList, x.DistinctKeys) →
      parseItems fuel cs acc = .ok (w, rest) → w.DistinctKeys) ∧
    (∀ cs (acc : Array (String × Wire)) w rest, (acc.toList.map (·.1)).Nodup →
      (∀ f ∈ acc.toList, f.2.DistinctKeys) → parseFields fuel cs acc = .ok (w, rest) → w.DistinctKeys)
  | 0 => ⟨fun _ _ _ h => by simp [parseValue, fail] at h, fun _ _ _ _ _ h => by simp [parseItems, fail] at h,
      fun _ _ _ _ _ _ h => by simp [parseFields, fail] at h⟩
  | fuel + 1 => by
    obtain ⟨ihv, ihi, ihf⟩ := parsed_distinctKeys fuel
    refine ⟨fun cs w rest h => ?_, fun cs acc w rest hacc h => ?_, fun cs acc w rest hkeys hacc h => ?_⟩
    · simp only [parseValue] at h
      split at h
      · simp [fail] at h
      · split at h
        · split at h
          · simp [fail] at h
          · split at h
            · cases h; exact .obj (by simp) (by simp)
            · exact ihf _ _ _ _ (by simp) (by simp) h
        · split at h
          · split at h
            · simp [fail] at h
            · split at h
              · cases h; exact .arr (by simp)
              · exact ihi _ _ _ _ (by simp) h
          · split at h
            · split at h
              · cases h; exact .str _
              · simp at h
            · split at h
              · rw [literal_eq_ok h]; exact .bool _
              · split at h
                · rw [literal_eq_ok h]; exact .bool _
                · split at h
                  · rw [literal_eq_ok h]; exact .null
                  · split at h
                    · split at h
                      · split at h
                        · simp [fail] at h
                        · cases h; exact .nat _
                      · cases h; exact .nat _
                    · split at h
                      · cases h; exact .nat _
                      · simp [fail] at h
    · simp only [parseItems] at h
      split at h
      · simp at h
      · rename_i x rest' hx
        have hxd := ihv _ _ _ hx
        have hacc' : ∀ y ∈ (acc.push x).toList, y.DistinctKeys := by
          intro y hy
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact hacc y hy
          · exact hxd
        split at h
        · simp [fail] at h
        · split at h
          · exact ihi _ _ _ _ hacc' h
          · split at h
            · cases h; exact .arr hacc'
            · simp [fail] at h
    · simp only [parseFields] at h
      split at h
      · simp [fail] at h
      · split at h
        · split at h
          · simp at h
          · rename_i k rest' hk
            split at h
            · simp [fail] at h
            · rename_i hnew
              split at h
              · simp [fail] at h
              · split at h
                · split at h
                  · simp at h
                  · rename_i v rest'' hv
                    have hvd := ihv _ _ _ hv
                    have hkeys' : ((acc.push (k, v)).toList.map (·.1)).Nodup := by
                      rw [Array.toList_push, List.map_append, List.nodup_append]
                      refine ⟨hkeys, by simp, ?_⟩
                      intro a ha b hb heq
                      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
                      subst hb heq
                      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
                      have : acc.any (·.1 == f.1) = true := by
                        rw [← Array.any_toList, List.any_eq_true]
                        exact ⟨f, hf, by simp⟩
                      simp [this] at hnew
                    have hacc' : ∀ f ∈ (acc.push (k, v)).toList, f.2.DistinctKeys := by
                      intro f hf
                      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hf
                      rcases hf with hf | rfl
                      · exact hacc f hf
                      · exact hvd
                    split at h
                    · simp [fail] at h
                    · split at h
                      · exact ihf _ _ _ _ hkeys' hacc' h
                      · split at h
                        · cases h; exact .obj hkeys' hacc'
                        · simp [fail] at h
                · simp [fail] at h
        · simp [fail] at h

end WireText

/-- The parser rejects a repeated key: no object of a value it reads repeats one, at any depth. --/
theorem Wire.distinctKeys_of_parse {s : String} {w : Wire} (h : Wire.parse s = .ok w) : w.DistinctKeys := by
  simp only [Wire.parse] at h
  split at h
  · simp at h
  · rename_i w' rest hw
    split at h
    · cases h
      exact (parsed_distinctKeys _).1 _ _ _ hw
    · simp at h

end Suimon
