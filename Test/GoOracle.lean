import Suimon
open Lean Suimon

/- A persistent, test-only JSON-lines oracle. All expected states, rejections,
   candidates and facts are computed by the original Lean definitions. -/
private def respond (s : State) (request : Json) : Except String (State × Json) := do
  let action : String ← request.getObjValAs? _ "action"
  match action with
  | "reset" =>
    let g ← graphFromJson (← request.getObjVal? "graph")
    g.validate
    let state := State.initial g
    return (state, Json.mkObj [("state", toJson state)])
  | "validate" =>
    let g ← graphFromJson (← request.getObjVal? "graph")
    let body := (request.getObjValAs? Bool "body").toOption.getD false
    return (s, match g.validate body with
      | .ok _ => Json.mkObj [("error", .null)]
      | .error e => Json.mkObj [("error", toJson e)])
  | "inspect" =>
    let cfg : Explore.Config ← request.getObjValAs? _ "config"
    return (s, Json.mkObj [("state", toJson s), ("candidates", toJson (Explore.candidates cfg s)),
      ("hasWork", toJson s.hasWork)])
  | "conforms" =>
    let state : State ← request.getObjValAs? _ "state"
    let op : Op ← request.getObjValAs? _ "op"
    let leaf : List Output ← request.getObjValAs? _ "leaf"
    let arm : String ← request.getObjValAs? _ "arm"
    let keep : Bool ← request.getObjValAs? _ "keep"
    let done : Bool ← request.getObjValAs? _ "done"
    let oracle : ScopedOracle := fun _ => {
      leaf := fun _ _ => leaf
      branch := fun _ _ => arm
      filter := fun _ _ => keep
      loop := fun _ _ _ => done }
    return (s, toJson (oracleConforms oracle state op))
  | "step" =>
    let op : Op ← request.getObjValAs? _ "op"
    match step s op with
    | .error r => return (s, Json.mkObj [("state", toJson s), ("reject", toJson r)])
    | .ok next => return (next, Json.mkObj [("state", toJson next), ("reject", .null),
        ("facts", toJson (Trace.effects s next op))])
  | "probe" =>
    let ops : List Op ← request.getObjValAs? _ "ops"
    let results := ops.map fun op => match step s op with
      | .error r => Json.mkObj [("reject", toJson r)]
      | .ok next => Json.mkObj [("state", toJson next), ("reject", .null),
          ("facts", toJson (Trace.effects s next op))]
    return (s, toJson results)
  | "generate" =>
    let g ← graphFromJson (← request.getObjVal? "graph")
    let cfg : Explore.Config ← request.getObjValAs? _ "config"
    let seed : Nat ← request.getObjValAs? _ "seed"
    let count : Nat ← request.getObjValAs? _ "count"
    match Explore.generate g cfg seed count with
    | .error r => return (s, Json.mkObj [("reject", toJson r)])
    | .ok (state, events) => return (s, Json.mkObj [("state", toJson state),
        ("events", toJson events), ("reject", .null)])
  | "search" =>
    let g ← graphFromJson (← request.getObjVal? "graph")
    let cfg : Explore.Config ← request.getObjValAs? _ "config"
    return (s, toJson (Explore.search g cfg))
  | "check" | "recover" =>
    let g ← graphFromJson (← request.getObjVal? "graph")
    let lines : List String ← request.getObjValAs? _ "lines"
    let result := if action == "check" then Trace.checkText g lines else Trace.recoverText g lines
    return (s, match result with
      | .error d => Json.mkObj [("diagnostic", toJson d)]
      | .ok state => Json.mkObj [("state", toJson state), ("diagnostic", .null),
          ("bags", toJson (channelBags state)), ("drained", toJson (succeededDrained state))])
  | _ => throw s!"unknown oracle action: {action}"

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut state : State := {}
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    match Json.parse line >>= respond state with
    | .error e => output.putStrLn (Json.mkObj [("oracle_error", toJson e)]).compress
    | .ok (next, result) =>
      state := next
      output.putStrLn result.compress
    output.flush
