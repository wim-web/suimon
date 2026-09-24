import Lean.Data.Json
import Suimon.WireText

namespace Suimon.Test.WireText
open Suimon

def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

/-- Rendering is injective on values without repeated keys (`Wire.parse_render`), so equal renderings
    mean equal values. --/
def roundTrip (label : String) (w : Wire) : IO Unit := do
  let text := w.render
  check (!text.toList.contains '\n') s!"{label}: raw newline in {text}"
  match Wire.parse text with
  | .ok back => check (back.render == text) s!"{label}: round trip changed {text} to {back.render}"
  | .error e => throw (IO.userError s!"{label}: {text} did not parse: {e}")

def renders (label : String) (w : Wire) (expected : String) : IO Unit :=
  check (w.render == expected) s!"{label}: rendered {w.render}, expected {expected}"

def parses (label text : String) (expected : Wire) : IO Unit :=
  match Wire.parse text with
  | .ok w => check (w.render == expected.render) s!"{label}: parsed {w.render}, expected {expected.render}"
  | .error e => throw (IO.userError s!"{label}: {e}")

def rejects (label text : String) : IO Unit :=
  match Wire.parse text with
  | .ok w => throw (IO.userError s!"{label}: accepted {text} as {w.render}")
  | .error _ => pure ()

def rejectsWith (label text expected : String) : IO Unit :=
  match Wire.parse text with
  | .ok w => throw (IO.userError s!"{label}: accepted {text} as {w.render}")
  | .error e => check (e == expected) s!"{label}: expected '{expected}', got '{e}'"

def sample : Wire :=
  .obj [
    ("name", .str "suimon"),
    ("quote", .str "say \"hi\" \\ back\\slash"),
    ("control", .str "a\nb\tc\r\x00\x1f"),
    ("unicode", .str "日本語 é 😀 \u007f"),
    ("nums", .arr [.nat 0, .nat 7, .nat 10, .nat 1234567890123456789012345678901234567890]),
    ("flags", .arr [.bool true, .bool false, .null]),
    ("nested", .arr [.arr [], .obj [], .arr [.arr [.obj [("", .arr [])]]]]),
    ("same key, other objects", .arr [.obj [("a", .obj [("a", .nat 1)])], .obj [("a", .nat 2)]])]

def run : IO Unit := do
  renders "scalars" (.arr [.null, .bool true, .bool false, .nat 0, .nat 42]) "[null,true,false,0,42]"
  renders "empty" (.obj [("a", .arr []), ("b", .obj [])]) "{\"a\":[],\"b\":{}}"
  renders "escapes" (.str "\"\\\n\x1f/é") "\"\\\"\\\\\\u000a\\u001f/é\""
  renders "field order" (.obj [("z", .nat 1), ("a", .nat 2), ("z", .nat 3)]) "{\"z\":1,\"a\":2,\"z\":3}"
  for (label, w) in [("null", Wire.null), ("empty string", .str ""), ("empty array", .arr []),
      ("empty object", .obj []), ("sample", sample), ("deep", (List.range 200).foldl (fun w _ => .arr [w]) .null)] do
    roundTrip label w
  parses "whitespace" " { \"a\" :\n[ 1 ,\t2 ] ,\r\"b\" : { } } " (.obj [("a", .arr [.nat 1, .nat 2]), ("b", .obj [])])
  parses "standard escapes" "\"\\n\\t\\r\\b\\f\\/\\u00e9\\u00C9\"" (.str "\n\t\r\x08\x0c/éÉ")
  parses "surrogate pair" "\"\\ud83d\\ude00\"" (.str "😀")
  rejects "trailing content" "{} {}"
  rejects "leading zero" "01"
  rejects "negative" "-1"
  rejects "fraction" "1.5"
  rejects "trailing comma" "[1,]"
  rejects "raw control character" "\"a\nb\""
  rejects "lone surrogate" "\"\\ude00\""
  rejects "unterminated" "[\"a\""
  rejects "empty" ""
  -- An object may not repeat a key, compared after its escapes are decoded; the error is right after
  -- the repeated key.
  rejectsWith "repeated key" "{\"a\":1,\"a\":2}" "duplicate key \"a\" at offset 10"
  rejectsWith "repeated key in field order" (Wire.obj [("z", .nat 1), ("a", .nat 2), ("z", .nat 3)]).render
    "duplicate key \"z\" at offset 16"
  rejectsWith "repeated nested key" "[{\"x\":{\"b\":[],\"b\":{}}}]" "duplicate key \"b\" at offset 17"
  rejectsWith "repeated escaped key" "{\"a\":1,\"\\u0061\":2}" "duplicate key \"a\" at offset 15"
  rejectsWith "quoted key" "{\"\\n\\\"\":1, \"\\n\\\"\" :2}" "duplicate key \"\\n\\\"\" at offset 17"
  rejectsWith "repeated key before a syntax error" "{\"a\":1,\"a\"" "duplicate key \"a\" at offset 10"
  match Lean.Json.parse sample.render with
  | .ok j =>
    check ((j.getObjValD "unicode").getStr?.toOption == some "日本語 é 😀 \u007f")
      "Lean's Json reads a different string"
    check ((j.getObjValD "control").getStr?.toOption == some "a\nb\tc\r\x00\x1f")
      "Lean's Json reads a different control string"
  | .error e => throw (IO.userError s!"Lean's Json.parse rejected the sample: {e}")
  IO.println "wire text: ok"

end Suimon.Test.WireText
