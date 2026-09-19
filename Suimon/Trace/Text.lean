import Suimon.Trace.JsonEquality
import Std.Data.String.ToNat

namespace Suimon.Trace.Text
open Lean

abbrev Chars := List Char
abbrev Reader (α : Type) := Chars → Option (α × Chars)

def hexDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e' | 15 => 'f'
  | _ => '0'

def hexValue : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | _ => none

def escapeChar (c : Char) : Chars :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat < 32 then ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

def quoted (s : String) : Chars := '"' :: s.toList.flatMap escapeChar ++ ['"']

def readStringBody : Reader (List Char)
  | '"' :: rest => some ([], rest)
  | '\\' :: '"' :: rest => do
    let (chars, tail) ← readStringBody rest
    return ('"' :: chars, tail)
  | '\\' :: '\\' :: rest => do
    let (chars, tail) ← readStringBody rest
    return ('\\' :: chars, tail)
  | '\\' :: 'u' :: '0' :: '0' :: high :: low :: rest => do
    let h ← hexValue high
    let l ← hexValue low
    let (chars, tail) ← readStringBody rest
    return (Char.ofNat (h * 16 + l) :: chars, tail)
  | '\\' :: _ => none
  | c :: rest => do
    if c.toNat < 32 then none else
      let (chars, tail) ← readStringBody rest
      return (c :: chars, tail)
  | [] => none

def readString : Reader String
  | '"' :: rest => do
    let (chars, tail) ← readStringBody rest
    return (String.ofList chars, tail)
  | _ => none

def readNat (chars : Chars) : Option (Nat × Chars) := do
  let n ← (String.ofList (chars.takeWhile Char.isDigit)).toNat?
  return (n, chars.dropWhile Char.isDigit)


def separator (c : Char) : Bool := c == ' ' || c == ',' || c == '\n' || c == '\r' || c == '\t'

def readNumber (negative : Bool) (chars : Chars) : Option (JsonAtom × Chars) := do
  let (n, tail) ← readNat chars
  match tail with
  | 'e' :: '-' :: rest =>
    let (exponent, after) ← readNat rest
    return (.number (if negative then -(n : Int) else (n : Int)) exponent, after)
  | _ => none

def readAtom (chars : Chars) : Option (JsonAtom × Chars) :=
  match chars with
  | [] => none
  | c :: rest =>
    if c = '{' then some (.objectStart, rest)
    else if c = '}' then some (.objectEnd, rest)
    else if c = '[' then some (.arrayStart, rest)
    else if c = ']' then some (.arrayEnd, rest)
    else if c = '"' then do
      let (value, after) ← readString chars
      match after with
      | ':' :: tail => return (.field value, tail)
      | _ => return (.string value, after)
    else if c = 't' then match rest with
      | 'r' :: 'u' :: 'e' :: tail => some (.boolean true, tail)
      | _ => none
    else if c = 'f' then match rest with
      | 'a' :: 'l' :: 's' :: 'e' :: tail => some (.boolean false, tail)
      | _ => none
    else if c = 'n' then match rest with
      | 'u' :: 'l' :: 'l' :: tail => some (.null, tail)
      | _ => none
    else if c = '-' then readNumber true rest
    else readNumber false chars

def renderAtom : JsonAtom → Chars
  | .null => "null".toList
  | .boolean true => "true".toList
  | .boolean false => "false".toList
  | .number n exponent => n.repr.toList ++ ['e', '-'] ++ exponent.repr.toList
  | .string value => quoted value
  | .arrayStart => ['[']
  | .arrayEnd => [']']
  | .objectStart => ['{']
  | .objectEnd => ['}']
  | .field name => quoted name ++ [':']

def endsValue : JsonAtom → Bool
  | .field _ | .arrayStart | .objectStart => false
  | _ => true

def startsSibling : JsonAtom → Bool
  | .arrayEnd | .objectEnd => false
  | _ => true

def atomGap (atom : JsonAtom) : List JsonAtom → Chars
  | [] => [' ']
  | next :: _ => if endsValue atom && startsSibling next then [',', ' '] else [' ']

def renderAtoms : List JsonAtom → Chars
  | [] => []
  | atom :: rest => renderAtom atom ++ atomGap atom rest ++ renderAtoms rest

def lexAtoms : Nat → Chars → Option (List JsonAtom)
  | 0, chars => if (chars.dropWhile separator).isEmpty then some [] else none
  | fuel + 1, chars =>
    match chars.dropWhile separator with
    | [] => some []
    | clean => do
      let (atom, rest) ← readAtom clean
      let tail ← lexAtoms fuel rest
      return atom :: tail

def encode (atoms : List JsonAtom) : String := String.ofList (renderAtoms atoms)

def decode (text : String) : Option (List JsonAtom) :=
  lexAtoms text.toList.length text.toList

end Suimon.Trace.Text
