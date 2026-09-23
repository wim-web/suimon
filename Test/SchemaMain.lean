import Test.Schema
import Test.Validate
import Test.Trace

open Lean Suimon Suimon.Test

private def liftError (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError s!"{label}: {e}")

private def rejected (schema : Schema.Validator) (label text : String) : IO Unit := do
  let value ← liftError label (Json.parse text)
  Validate.ensure (schema.validate value).toOption.isNone s!"schema accepted {label}"

/-- The schema and the decoder accept the same examples, including what the encoder writes. --/
def main : IO Unit := do
  let schema ← liftError "program.schema.json"
    (Json.parse (← IO.FS.readFile "schema/program.schema.json") >>= Schema.compile)
  for name in ["users", "branch", "merge"] do
    let json ← liftError name (Json.parse (← IO.FS.readFile s!"Test/programs/{name}.json"))
    liftError name (schema.validate json)
    liftError s!"{name} (encoded)" (schema.validate (Codec.programJson (← Validate.load name)))
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
  rejected schema "zero limit" (placement
    "\"node\":{\"type\":\"concurrency\",\"limit\":0,\"tasks\":[],\"output\":\"list\",\"element\":\"T\"},\"policy\":\"stop\"")
  let trace ← liftError "trace.schema.json"
    (Json.parse (← IO.FS.readFile "schema/trace.schema.json") >>= Schema.compile)
  for name in ["users", "branch", "merge"] do
    for seed in List.range 10 do
      let recorded ← Test.Trace.recorded (← Validate.load name) (seed + 1)
      for record in recorded.records do
        liftError s!"{name} seed {seed + 1}" (Json.parse (Trace.wireCodec.encode record) >>= trace.validate)
  -- The order the Wire form fixes is accepted too.
  liftError "ordered fields"
    (Json.parse "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":\"x\"}}" >>=
      trace.validate)
  rejected trace "unknown op" "{\"seq\":1,\"op\":{\"type\":\"retry\",\"call\":\"c\"}}"
  rejected trace "op with commit" "{\"seq\":1,\"op\":{\"type\":\"cancel\"},\"commit\":true}"
  rejected trace "zero seq" "{\"seq\":0,\"commit\":true}"
  rejected trace "values not an object" "{\"seq\":1,\"op\":{\"type\":\"cancel\"},\"values\":[]}"
  rejected trace "payload not a string"
    "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"},\"values\":{\"t\":1}}"
  rejected trace "null optional field" "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":null}}"
  IO.println "schema: ok"
