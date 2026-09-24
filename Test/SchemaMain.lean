import Test.Schema
import Test.Validate
import Test.Trace

open Lean Suimon Suimon.Test

private def liftError (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError s!"{label}: {e}")

/-- The examples are read without repeated keys, which suimon rejects and JSON Schema cannot express. --/
private def rejected (schema : Schema.Validator) (label text : String) : IO Unit := do
  let value ← liftError label (Codec.parse text)
  Validate.ensure (schema.validate value).toOption.isNone s!"schema accepted {label}"

/-- The schema and the decoder accept the same examples, including what the encoder writes. --/
def main : IO Unit := do
  let definitionSchema ← liftError "definition.schema.json"
    (Json.parse (← IO.FS.readFile "schema/definition.schema.json"))
  let schema ← liftError "definition.schema.json" (Schema.compile definitionSchema)
  for name in ["users", "branch", "merge"] do
    let json ← liftError name (Codec.parse (← IO.FS.readFile s!"Test/definitions/{name}.json"))
    liftError name (schema.validate json)
    liftError s!"{name} (encoded)" (schema.validate (Codec.definitionJson (← Validate.load name)))
  let placement := fun (fields : String) =>
    "{\"main\":\"w\",\"workflows\":[{\"id\":\"w\",\"placements\":[{\"name\":\"a\"," ++ fields ++ "}]}]}"
  let merge := "\"node\":{\"type\":\"merge\",\"element\":\"T\"}"
  rejected schema "missing policy" (placement merge)
  rejected schema "unknown field" (placement (merge ++ ",\"policy\":\"stop\",\"retries\":1"))
  rejected schema "unknown policy" (placement (merge ++ ",\"policy\":\"retry\""))
  rejected schema "zero timeout" (placement (merge ++ ",\"policy\":\"stop\",\"timeout\":{\"callMs\":0}"))
  rejected schema "null input type"
    "{\"main\":\"w\",\"functions\":[{\"id\":\"f\",\"input\":null,\"output\":{\"single\":\"T\"}}],\"workflows\":[]}"
  rejected schema "empty arms"
    (placement "\"node\":{\"type\":\"branch\",\"judge\":\"j\",\"arms\":[]},\"policy\":\"stop\"")
  -- An integer is a number with a zero fractional part in any notation, as the decoder reads it.
  let limit := fun (text : String) => placement ("\"node\":{\"type\":\"concurrency\",\"limit\":" ++ text ++
    ",\"tasks\":[{\"name\":\"t\",\"body\":{\"type\":\"function\",\"function\":\"f\"},\"outputTransform\":\"o\"," ++
    "\"policy\":\"stop\"}],\"output\":\"list\",\"element\":\"T\"},\"policy\":\"stop\"")
  for text in ["1", "2", "2.0", "20e-1", "0.2e1", "1e1", "1000e-3"] do
    liftError s!"limit {text}" (Codec.parse (limit text) >>= schema.validate)
  for text in ["2.5", "1e-1", "1e-1000000000"] do
    rejected schema s!"limit {text}" (limit text)
  -- Below the minimum; the rest of the example is valid, so the minimum is what rejects it.
  for text in ["0", "-0", "0.0", "0e-1000000000", "-1", "-10e-1"] do
    rejected schema s!"limit {text}" (limit text)
  -- Up to the maximum, 2^64 - 1, which implementations hold in 64 bits.
  liftError "limit 2^64-1" (Codec.parse (limit "18446744073709551615") >>= schema.validate)
  for text in ["18446744073709551616", "1e20", "1e1000000000"] do
    rejected schema s!"limit {text}" (limit text)
  let timed := merge ++ ",\"policy\":\"stop\",\"timeout\":{\"callMs\":1.5e3,\"elementMs\":2.50e1}"
  liftError "timeout" (Codec.parse (placement timed) >>= schema.validate)
  -- Numbers compare by value, whatever their exponents, and zero is above every negative number. A
  -- number is a mantissa over a power of ten.
  let n := fun (mantissa : Int) (exponent : Nat) => (⟨mantissa, exponent⟩ : JsonNumber)
  for (a, b, less) in [(n (-1) 0, n 0 0, true), (n 0 0, n (-1) 0, false), (n (-5) 0, n (-3) 0, true),
      (n (-3) 0, n (-5) 0, false), (n 1 1000000000, n 1 0, true), (n 1 0, n 1 1000000000, false),
      (n (-1) 1000000000, n 0 0, true), (n 0 0, n 1 1000000000, true), (n 20 1, n 2 0, false),
      (n 2 0, n 20 1, false), (n 25 2, n 5 1, true), (n 5 1, n 25 2, false), (n 99 0, n 100 0, true),
      (n 100 1, n 99 0, true), (n (-100) 1, n (-99) 0, false), (n 0 5, n 0 0, false)] do
    Validate.ensure (Schema.numberLt a b == less) s!"{a} < {b} should be {less}"
  -- The header of a record refers to the definition schema.
  let trace ← liftError "trace.schema.json" (Json.parse (← IO.FS.readFile "schema/trace.schema.json") >>=
    (Schema.compile · [("definition.schema.json", definitionSchema)]))
  for name in ["users", "branch", "merge"] do
    let p ← Validate.load name
    for validated in [true, false] do
      liftError s!"{name} header {validated}"
        (Codec.parse (Trace.wireCodec.encodeHeader (.of p validated)) >>= trace.validate)
    for seed in List.range 10 do
      let recorded ← Test.Trace.recorded p (seed + 1)
      for record in recorded.records do
        liftError s!"{name} seed {seed + 1}" (Codec.parse (Trace.wireCodec.encode record) >>= trace.validate)
  -- The header of an execution started without validation may hold a definition that validation
  -- rejects.
  for (name, invalid, _) in ← Test.Trace.invalidDefinitions do
    liftError s!"{name} header" (Codec.parse (Trace.wireCodec.encodeHeader (.of invalid false)) >>= trace.validate)
  -- The order the Wire form fixes is accepted too.
  liftError "ordered fields"
    (Codec.parse "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":\"x\"}}" >>=
      trace.validate)
  rejected trace "unknown op" "{\"seq\":1,\"op\":{\"type\":\"retry\",\"call\":\"c\"}}"
  rejected trace "op with commit" "{\"seq\":1,\"op\":{\"type\":\"cancel\"},\"commit\":true}"
  rejected trace "zero seq" "{\"seq\":0,\"commit\":true}"
  rejected trace "values not an object" "{\"seq\":1,\"op\":{\"type\":\"cancel\"},\"values\":[]}"
  rejected trace "payload not a string"
    "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":1}}"
  rejected trace "null optional field" "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":null}}"
  -- An index is at least 0.
  let deliver := fun (connection : String) =>
    "{\"seq\":1,\"op\":{\"type\":\"deliver\",\"run\":[],\"connection\":" ++ connection ++ ",\"source\":\"s\"}}"
  for text in ["0", "3"] do
    liftError s!"connection {text}" (Codec.parse (deliver text) >>= trace.validate)
  for text in ["-1", "-3e0"] do
    rejected trace s!"connection {text}" (deliver text)
  let definition := "{\"main\":\"w\",\"workflows\":[]}"
  for validated in ["true", "false"] do
    liftError s!"header {validated}"
      (Codec.parse ("{\"definition\":" ++ definition ++ s!",\"validated\":{validated}}") >>= trace.validate)
  rejected trace "header with seq" ("{\"seq\":1,\"definition\":" ++ definition ++ ",\"validated\":true}")
  rejected trace "header field" ("{\"definition\":" ++ definition ++ ",\"validated\":true,\"version\":1}")
  rejected trace "header without definition" "{\"validated\":true}"
  rejected trace "header without validated" ("{\"definition\":" ++ definition ++ "}")
  for value in ["\"true\"", "null", "1"] do
    rejected trace s!"header with validated {value}" ("{\"definition\":" ++ definition ++ s!",\"validated\":{value}}")
  rejected trace "header with an invalid definition" "{\"definition\":{\"main\":\"w\"},\"validated\":true}"
  -- Only a record marked validated holds a definition that definition.schema.json accepts; an unchecked
  -- one may hold any definition, such as one without placements, which the decoder still reads.
  let noPlacements := "{\"main\":\"w\",\"workflows\":[{\"id\":\"w\",\"placements\":[]}]}"
  liftError "unchecked header without placements"
    (Codec.parse ("{\"definition\":" ++ noPlacements ++ ",\"validated\":false}") >>= trace.validate)
  rejected trace "validated header without placements" ("{\"definition\":" ++ noPlacements ++ ",\"validated\":true}")
  IO.println "schema: ok"
