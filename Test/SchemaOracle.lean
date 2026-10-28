import Test.Schema
import Suimon.Json

namespace Suimon.Test.SchemaOracle
open Lean

/-- Check the corpus classified independently by python-jsonschema. Raw JSON text
    preserves large integers and exponent notation across the process boundary. -/
def run (path : String) : IO Unit := do
  let groups ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let mut count := 0
  for group in groups do
    let rule ← IO.ofExcept (group.getObjVal? "schema")
    let documents ← IO.ofExcept ((← IO.ofExcept (group.getObjVal? "documents" >>= Json.getArr?)).toList.mapM
      fun document => do
        return (← document.getObjVal? "name" >>= Json.getStr?, ← document.getObjVal? "schema"))
    let validator ← IO.ofExcept (Schema.compile rule documents)
    let cases ← IO.ofExcept (group.getObjVal? "cases" >>= Json.getArr?)
    for test in cases do
      let label ← IO.ofExcept (test.getObjVal? "label" >>= Json.getStr?)
      let text ← IO.ofExcept (test.getObjVal? "text" >>= Json.getStr?)
      let expected ← IO.ofExcept (test.getObjVal? "valid" >>= Json.getBool?)
      let value ← IO.ofExcept (Codec.parse text)
      let actual := (validator.validate value).toOption.isSome
      unless actual == expected do
        throw (IO.userError s!"schema oracle: {label}: expected {expected}, got {actual}")
      count := count + 1
  unless count > 100 do throw (IO.userError s!"schema oracle corpus unexpectedly small: {count}")
  IO.println s!"schema oracle: {count} cases agree"

end Suimon.Test.SchemaOracle
