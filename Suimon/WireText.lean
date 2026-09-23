import Suimon.Wire

/-! The text encoding of `Wire` values: compact JSON with a fixed rendering and a parser that
    accepts at least every rendering. Records are written one per line, so a rendering never
    contains a raw newline. -/

namespace Suimon

namespace WireText

/-- The lowercase hexadecimal digit for `d < 16`. --/
def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- The decimal digits of `n`, without leading zeros, in front of `acc`. --/
def natDigits (n : Nat) (acc : List Char) : List Char :=
  if n < 10 then Char.ofNat (48 + n) :: acc
  else natDigits (n / 10) (Char.ofNat (48 + n % 10) :: acc)
termination_by n
decreasing_by omega

/-- Appends `c` escaped for a JSON string: quote, backslash and control characters. --/
def pushEscaped (acc : String) (c : Char) : String :=
  if c = '"' then (acc.push '\\').push '"'
  else if c = '\\' then (acc.push '\\').push '\\'
  else if c.toNat < 32 then
    (((((acc.push '\\').push 'u').push '0').push '0').push (hexDigit (c.toNat / 16))).push
      (hexDigit (c.toNat % 16))
  else acc.push c

/-- Appends `s` as a quoted JSON string. --/
def pushString (acc : String) (s : String) : String :=
  (s.foldl pushEscaped (acc.push '"')).push '"'

end WireText

open WireText in
mutual

/-- Appends the rendering of `w` to `acc`. --/
def Wire.renderTo : Wire → String → String
  | .null, acc => acc ++ "null"
  | .bool true, acc => acc ++ "true"
  | .bool false, acc => acc ++ "false"
  | .nat n, acc => acc ++ String.ofList (natDigits n [])
  | .str s, acc => pushString acc s
  | .arr items, acc => (Wire.renderItems items (acc.push '[') true).push ']'
  | .obj fields, acc => (Wire.renderFields fields (acc.push '{') true).push '}'

/-- Appends array items separated by commas; `first` says no comma precedes the next item. --/
def Wire.renderItems : List Wire → String → Bool → String
  | [], acc, _ => acc
  | w :: ws, acc, first => Wire.renderItems ws (Wire.renderTo w (if first then acc else acc.push ',')) false

/-- Appends object fields `"k":v` separated by commas, in list order. --/
def Wire.renderFields : List (String × Wire) → String → Bool → String
  | [], acc, _ => acc
  | (k, v) :: fs, acc, first =>
    Wire.renderFields fs
      (Wire.renderTo v ((pushString (if first then acc else acc.push ',') k).push ':')) false

end

/-- The compact JSON text of `w`: no whitespace, fields in list order, strings escaped with
    `\"`, `\\` and `\u00xx` for control characters. --/
def Wire.render (w : Wire) : String :=
  w.renderTo ""

namespace WireText

/-- Parse errors carry the length of the unread input, so the caller can report an offset. --/
abbrev Parsed (α : Type) := Except (String × Nat) (α × List Char)

def fail (msg : String) (cs : List Char) : Except (String × Nat) α :=
  .error (msg, cs.length)

def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if isWs c then skipWs cs else c :: cs

def isDigit (c : Char) : Prop :=
  48 ≤ c.toNat ∧ c.toNat ≤ 57

instance (c : Char) : Decidable (isDigit c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Reads decimal digits as far as they go, accumulating onto `n`. --/
def spanDigits : List Char → Nat → Nat × List Char
  | [], n => (n, [])
  | c :: cs, n => if isDigit c then spanDigits cs (10 * n + (c.toNat - 48)) else (n, c :: cs)

def hexVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55)
  else none

def hex4 (a b c d : Char) : Option Nat := do
  let a ← hexVal a
  let b ← hexVal b
  let c ← hexVal c
  let d ← hexVal d
  pure (((a * 16 + b) * 16 + c) * 16 + d)

/-- The character a one-letter escape stands for. --/
def simpleEscape (e : Char) : Option Char :=
  if e = '"' then some '"'
  else if e = '\\' then some '\\'
  else if e = '/' then some '/'
  else if e = 'b' then some (Char.ofNat 8)
  else if e = 'f' then some (Char.ofNat 12)
  else if e = 'n' then some '\n'
  else if e = 'r' then some '\r'
  else if e = 't' then some '\t'
  else none

/-- Reads a string body after the opening quote, up to and including the closing quote. --/
def parseStringBody : List Char → String → Parsed String
  | [], _ => fail "unterminated string" []
  | c :: cs, acc =>
    if c = '"' then .ok (acc, cs)
    else if c = '\\' then
      match cs with
      | [] => fail "unterminated escape" cs
      | e :: cs =>
        match simpleEscape e with
        | some d => parseStringBody cs (acc.push d)
        | none =>
          if e = 'u' then
            match cs with
            | a :: b :: c :: d :: cs =>
              match hex4 a b c d with
              | none => fail "invalid \\u escape" cs
              | some v =>
                if v < 0xD800 ∨ 0xDFFF < v then parseStringBody cs (acc.push (Char.ofNat v))
                else if v < 0xDC00 then
                  match cs with
                  | b1 :: b2 :: a :: b :: c :: d :: cs =>
                    if b1 = '\\' ∧ b2 = 'u' then
                      match hex4 a b c d with
                      | some lo =>
                        if 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF then
                          parseStringBody cs
                            (acc.push (Char.ofNat (0x10000 + (v - 0xD800) * 0x400 + (lo - 0xDC00))))
                        else fail "invalid low surrogate" cs
                      | none => fail "invalid \\u escape" cs
                    else fail "unpaired high surrogate" cs
                  | _ => fail "unpaired high surrogate" cs
                else fail "unpaired low surrogate" cs
            | _ => fail "truncated \\u escape" cs
          else fail s!"invalid escape {repr e}" cs
    else if c.toNat < 32 then fail "control character in string" (c :: cs)
    else parseStringBody cs (acc.push c)

/-- Consumes the exact characters `word`. --/
def expectWord : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | w :: ws, c :: cs => if w = c then expectWord ws cs else none
  | _ :: _, [] => none

def literal (word : List Char) (value : Wire) (cs : List Char) : Parsed Wire :=
  match expectWord word cs with
  | some rest => .ok (value, rest)
  | none => fail "invalid literal" cs

/- `fuel` bounds the call depth; `Wire.parse` passes the input length plus one, which is enough
   because every call either consumes input or is followed by one that does. -/
mutual

/-- Reads one value after optional whitespace. --/
def parseValue : Nat → List Char → Parsed Wire
  | 0, cs => fail "input too deeply nested" cs
  | fuel + 1, cs =>
    match skipWs cs with
    | [] => fail "unexpected end of input" []
    | c :: cs =>
      if c = '{' then
        match skipWs cs with
        | [] => fail "unterminated object" []
        | d :: ds => if d = '}' then .ok (.obj [], ds) else parseFields fuel (d :: ds) #[]
      else if c = '[' then
        match skipWs cs with
        | [] => fail "unterminated array" []
        | d :: ds => if d = ']' then .ok (.arr [], ds) else parseItems fuel (d :: ds) #[]
      else if c = '"' then
        match parseStringBody cs "" with
        | .ok (s, rest) => .ok (.str s, rest)
        | .error e => .error e
      else if c = 't' then literal ['r', 'u', 'e'] (.bool true) cs
      else if c = 'f' then literal ['a', 'l', 's', 'e'] (.bool false) cs
      else if c = 'n' then literal ['u', 'l', 'l'] .null cs
      else if c = '0' then
        match cs with
        | d :: _ => if isDigit d then fail "leading zero in number" cs else .ok (.nat 0, cs)
        | [] => .ok (.nat 0, [])
      else if isDigit c then
        let (n, rest) := spanDigits (c :: cs) 0
        .ok (.nat n, rest)
      else fail s!"unexpected character {repr c}" (c :: cs)

/-- Reads array items from the first item on, through the closing bracket. --/
def parseItems : Nat → List Char → Array Wire → Parsed Wire
  | 0, cs, _ => fail "input too deeply nested" cs
  | fuel + 1, cs, acc =>
    match parseValue fuel cs with
    | .error e => .error e
    | .ok (w, rest) =>
      match skipWs rest with
      | [] => fail "unterminated array" []
      | c :: cs =>
        if c = ',' then parseItems fuel cs (acc.push w)
        else if c = ']' then .ok (.arr (acc.push w).toList, cs)
        else fail "expected ',' or ']'" (c :: cs)

/-- Reads object fields from the first key on, through the closing brace. --/
def parseFields : Nat → List Char → Array (String × Wire) → Parsed Wire
  | 0, cs, _ => fail "input too deeply nested" cs
  | fuel + 1, cs, acc =>
    match skipWs cs with
    | [] => fail "unterminated object" []
    | c :: cs =>
      if c = '"' then
        match parseStringBody cs "" with
        | .error e => .error e
        | .ok (k, rest) =>
          match skipWs rest with
          | [] => fail "unterminated object" []
          | c :: cs =>
            if c = ':' then
              match parseValue fuel cs with
              | .error e => .error e
              | .ok (v, rest) =>
                match skipWs rest with
                | [] => fail "unterminated object" []
                | c :: cs =>
                  if c = ',' then parseFields fuel cs (acc.push (k, v))
                  else if c = '}' then .ok (.obj (acc.push (k, v)).toList, cs)
                  else fail "expected ',' or '}'" (c :: cs)
            else fail "expected ':'" (c :: cs)
      else fail "expected a string key" (c :: cs)

end

end WireText

open WireText in
/-- Parses JSON text into a `Wire`: whitespace between tokens and the standard escapes are
    accepted, numbers must be natural numbers, and nothing may follow the value. --/
def Wire.parse (s : String) : Except String Wire :=
  let cs := s.toList
  let err (e : String × Nat) : Except String Wire :=
    .error s!"{e.1} at offset {cs.length - e.2}"
  match parseValue (cs.length + 1) cs with
  | .error e => err e
  | .ok (w, rest) =>
    match skipWs rest with
    | [] => .ok w
    | c :: more => err (s!"unexpected trailing character {repr c}", (c :: more).length)

end Suimon
