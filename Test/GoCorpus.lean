import Suimon.Trace.Event

namespace Suimon.Test.GoCorpus
open Lean

/-- Optional export of the existing regression cases for independent Go replay. -/
def record (s : State) (op : Op) (result : Result State) : IO Unit := do
  if let some path ← IO.getEnv "SUIMON_GO_CORPUS" then
    let fields := [("before", toJson s), ("op", toJson op)] ++ match result with
      | .error r => [("reject", toJson r)]
      | .ok next => [("reject", .null), ("after", toJson next),
          ("facts", toJson (Trace.effects s next op))]
    let file ← IO.FS.Handle.mk path .append
    file.putStrLn (Json.mkObj fields).compress

end Suimon.Test.GoCorpus
