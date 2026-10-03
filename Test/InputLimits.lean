import Suimon.Trace
import Test.Validate

namespace Suimon.Test.InputLimits
open Lean

private def nested (left right leaf : String) (depth : Nat) : String :=
  String.join (List.replicate depth left) ++ leaf ++ String.join (List.replicate depth right)

private def succeeds {α : Type} (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"{label}: {e}")

private def rejects {α : Type} (label expected : String) (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"{label}: accepted excessive input")
  | .error e => Validate.ensure (e == expected) s!"{label}: {e}, expected {expected}"

def run : IO Unit := do
  let depthError := Suimon.InputLimits.depthError
  let sizeError := ({} : Suimon.InputLimits).sizeError
  for (left, right) in [("[", "]"), ("{\"x\":", "}")] do
    for leaf in ["null", "[]", "{}"] do
      let depth := maxInputDepth - (if leaf == "null" then 0 else 1)
      let text := nested left right leaf depth
      succeeds "definition at depth limit" (Codec.parse text)
      succeeds "record at depth limit" (Wire.parse text)
      let tooDeep := nested left right leaf (depth + 1)
      rejects "definition past limit" depthError (Codec.parse tooDeep)
      rejects "record past limit" depthError (Wire.parse tooDeep)
  -- Siblings do not consume nesting depth; escapes and brackets in strings do not either.
  for text in ["[" ++ String.join (List.replicate 10000 "0,") ++ "0]",
      "\"" ++ String.join (List.replicate 100 "\\\"\\\\[{}]\\u005b") ++ "\""] do
    succeeds "shallow definition" (Codec.parse text)
    succeeds "shallow record" (Wire.parse text)
  let atSize := "\"" ++ String.ofList (List.replicate (defaultMaxInputBytes - 2) 'x') ++ "\""
  succeeds "definition at byte limit" (Codec.parse atSize)
  succeeds "record at byte limit" (Wire.parse atSize)
  succeeds "raised definition budget" (Codec.parse (atSize ++ " ") { maxBytes := defaultMaxInputBytes + 1 })
  succeeds "raised record budget" (Wire.parse (atSize ++ " ") { maxBytes := defaultMaxInputBytes + 1 })
  rejects "raised bytes preserve depth" depthError
    (Wire.parse (nested "[" "]" "0" 65) { maxBytes := 2 * defaultMaxInputBytes })
  for text in [atSize ++ " ", "\"" ++ String.join (List.replicate (defaultMaxInputBytes / 3) "界") ++ "\""] do
    rejects "large definition" sizeError (Codec.parse text)
    rejects "large record" sizeError (Wire.parse text)
  let unicode := "\"界\""
  succeeds "UTF-8 byte limit" (Wire.parse unicode { maxBytes := 5 })
  rejects "UTF-8 past byte limit" "input exceeds maximum size of 4 bytes"
    (Wire.parse unicode { maxBytes := 4 })
  succeeds "configured definition bytes" (Codec.parse unicode { maxBytes := 5 })
  rejects "configured definition bytes" "input exceeds maximum size of 4 bytes"
    (Codec.parse unicode { maxBytes := 4 })
  let hugeDepth := nested "[" "]" "0" 20000
  rejects "hostile definition" depthError (Codec.parse hugeDepth)
  rejects "hostile record" depthError (Wire.parse hugeDepth)
  rejects "record codec" depthError (Trace.wireCodec.decode hugeDepth)
  rejects "header codec" depthError (Trace.wireCodec.decodeHeader hugeDepth)
  rejects "check header" ("line 1: " ++ depthError)
    (Trace.check Trace.wireCodec Trace.Header.load (hugeDepth ++ "\n"))
  let header := "{\"definition\":{\"main\":\"w\"},\"validated\":false}\n"
  rejects "check record" ("line 2: " ++ depthError)
    (Trace.check Trace.wireCodec Trace.Header.load (header ++ hugeDepth ++ "\n"))
  -- Alternate JSON and Wire decoders cannot send deep trees into ValueType decoding or toJson.
  let typeJson := (List.range maxInputDepth).foldl
    (fun j _ => Json.mkObj [("list", j)]) (.str "T")
  succeeds "prebuilt type at limit" (Codec.valueType typeJson "type")
  let tooDeep := Json.mkObj [("list", typeJson)]
  rejects "prebuilt type past limit" depthError (Codec.valueType tooDeep "type")
  for json in [tooDeep, Json.mkObj [("unknown", tooDeep)]] do
    rejects "prebuilt definition" depthError (Codec.definition json)
    rejects "prebuilt validated definition" depthError (Codec.loadJson json)
    rejects "FromJson definition" depthError (fromJson? json : Except String Definition)
  let wire := (List.range (maxInputDepth + 1)).foldl
    (fun w _ => Wire.obj [("list", w)]) (.str "T")
  rejects "wire definition" depthError (Codec.load wire)
  rejects "unchecked wire definition" depthError (Codec.loadUnchecked wire)
  for validated in [true, false] do
    rejects "prebuilt header" depthError (Trace.Header.load ⟨wire, validated⟩)
  let shallow := Json.arr (Array.replicate 100 (.str "T"))
  rejects "prebuilt structural budget" "input exceeds maximum size of 20 bytes"
    (Codec.definition shallow { maxBytes := 20 })
  rejects "wire structural budget" "input exceeds maximum size of 20 bytes"
    (Codec.loadUnchecked (.arr (List.replicate 100 (.str "T"))) { maxBytes := 20 })
  IO.println "input limits: ok"

end Suimon.Test.InputLimits
