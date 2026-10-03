import Lean.Data.Json
import Suimon.Wire

namespace Suimon

def defaultMaxInputBytes : Nat := 1024 * 1024

/-- The number of open arrays and objects, including empty containers. --/
def maxInputDepth : Nat := 64

/-- A per-definition or per-record-line byte budget; zero selects the default.
    Nesting has a fixed ceiling independent of this configurable budget. --/
structure InputLimits where
  maxBytes : Nat := defaultMaxInputBytes
  deriving Inhabited

namespace InputLimits

def byteLimit (limits : InputLimits) : Nat :=
  if limits.maxBytes = 0 then defaultMaxInputBytes else limits.maxBytes

def sizeError (limits : InputLimits) : String :=
  s!"input exceeds maximum size of {limits.byteLimit} bytes"

def depthError : String := s!"input exceeds maximum nesting depth of {maxInputDepth}"

def checkSize (limits : InputLimits) (size : Nat) : Except String Unit :=
  if size > limits.byteLimit then .error limits.sizeError else .ok ()

/-- A constant-space scan before allocating a syntax tree or character list.
    Brackets inside strings (including escaped quotes) do not count. The parser
    still checks syntax and supplies its usual diagnostics. --/
def check (limits : InputLimits) (text : String) : Except String Unit := do
  limits.checkSize text.utf8ByteSize
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  for c in text do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == '[' || c == '{' then
      depth := depth + 1
      if depth > maxInputDepth then throw depthError
    else if c == ']' || c == '}' then depth := depth - 1

private def spend (limits : InputLimits) (n remaining : Nat) : Except String Nat :=
  if n > remaining then .error limits.sizeError else .ok (remaining - n)

/-- Prebuilt trees must be checked before recursive decoding too. The budget
    counts nodes and raw string/key bytes, a lower bound on their JSON size.
    Traversal stops at the fixed depth or budget; it never renders the tree. --/
def checkJsonAt (limits : InputLimits) (depth remaining : Nat) (json : Lean.Json) : Except String Nat := do
  let remaining ← limits.spend 1 remaining
  match json with
  | .str s => limits.spend s.utf8ByteSize remaining
  | .arr items =>
    match depth with
    | 0 => throw depthError
    | depth + 1 =>
      let mut left := remaining
      for item in items do
        left ← limits.checkJsonAt depth left item
      return left
  | .obj fields =>
    match depth with
    | 0 => throw depthError
    | depth + 1 =>
      -- Refuse a wide prebuilt object before materializing its field list.
      limits.checkSize fields.size
      let mut left := remaining
      for (key, value) in fields.toList do
        left ← limits.spend key.utf8ByteSize left
        left ← limits.checkJsonAt depth left value
      return left
  | _ => return remaining
termination_by depth

def checkJson (limits : InputLimits) (json : Lean.Json) : Except String Unit := do
  let _ ← limits.checkJsonAt maxInputDepth limits.byteLimit json

/-- Size of a string in the canonical Wire rendering, without allocating that rendering. --/
private def stringSize (s : String) : Nat := Id.run do
  let mut size := s.utf8ByteSize + 2
  for c in s do
    if c == '"' || c == '\\' then size := size + 1
    else if c.toNat < 32 then size := size + 5
  return size

/-- Check a header's tree before `Wire.toJson` can recurse into it. Count canonical
    bytes, as Go passes the canonical definition text to its header loader. --/
def checkWireAt (limits : InputLimits) (depth remaining : Nat) (wire : Wire) : Except String Nat := do
  match wire with
  | .null => limits.spend 4 remaining
  | .bool b => limits.spend (if b then 4 else 5) remaining
  | .nat n =>
    -- Bound conversion work even for a number built by an alternate decoder.
    if n.log2 >= 4 * remaining then throw limits.sizeError
    limits.spend (toString n).utf8ByteSize remaining
  | .str s =>
    limits.checkSize s.utf8ByteSize
    limits.spend (stringSize s) remaining
  | .arr items =>
    match depth with
    | 0 => throw depthError
    | depth + 1 =>
      let mut left ← limits.spend 2 remaining
      let mut first := true
      for item in items do
        unless first do left ← limits.spend 1 left
        first := false
        left ← limits.checkWireAt depth left item
      return left
  | .obj fields =>
    match depth with
    | 0 => throw depthError
    | depth + 1 =>
      let mut left ← limits.spend 2 remaining
      let mut first := true
      for (key, value) in fields do
        unless first do left ← limits.spend 1 left
        first := false
        limits.checkSize key.utf8ByteSize
        left ← limits.spend (stringSize key + 1) left
        left ← limits.checkWireAt depth left value
      return left
termination_by depth

def checkWire (limits : InputLimits) (wire : Wire) : Except String Unit := do
  let _ ← limits.checkWireAt maxInputDepth limits.byteLimit wire

end InputLimits
end Suimon
