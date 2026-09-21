import Suimon.Explore
import Suimon.Trace.Wire
import Test.Examples
open Lean Suimon

private def usage : String :=
  "suimon check <trace.jsonl> --graph <graph.json>\n" ++
  "suimon explore --graph <graph.json> [--depth N] [--workers N] [--tick N] [--max-states N]\n" ++
  "suimon gen [--graph <graph.json>] --seed S --count N [--workers N] [--tick N]\n"

private def options (args : List String) (allowed : List String) : Except String (List (String × String)) := do
  let rec go : List String → List (String × String) → Except String (List (String × String))
    | [], acc => .ok acc
    | key :: value :: rest, acc => do
      unless allowed.contains key && !(acc.map (·.1)).contains key do throw s!"unknown or repeated option: {key}"
      go rest (acc ++ [(key, value)])
    | _, _ => .error "option requires a value"
  go args []

private def natOpt (opts : List (String × String)) (name : String) (default : Nat) : Except String Nat :=
  match opts.lookup name with
  | none => .ok default
  | some value => value.toNat?.toExcept s!"invalid nonnegative integer for {name}"

private def loadGraph (path : String) : IO Graph := do
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"invalid graph JSON: {e}")
  let g ← match graphFromJson json with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"invalid graph JSON: {e}")
  unless toJson g == json do throw (IO.userError "graph fields do not match the canonical schema")
  match g.validate with
  | .ok _ => pure g
  | .error e => throw (IO.userError s!"invalid graph: {e}")

private def getGraph (opts : List (String × String)) (default : Option Graph := none) : IO Graph :=
  match opts.lookup "--graph", default with
  | some path, _ => loadGraph path
  | none, some g => pure g
  | none, none => throw (IO.userError "--graph is required")

private def liftError (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)

private def config (opts : List (String × String)) : IO Explore.Config := do
  let depth ← liftError (natOpt opts "--depth" 8)
  let workers ← liftError (natOpt opts "--workers" 1)
  let tick ← liftError (natOpt opts "--tick" 1)
  let maxStates ← liftError (natOpt opts "--max-states" 100000)
  if workers == 0 || tick == 0 || maxStates == 0 then throw (IO.userError "workers, tick and max-states must be positive")
  return { depth, workers, tick, maxStates }

private def checkFile (g : Graph) (file : String) : IO UInt32 := do
  let stream ← IO.FS.Handle.mk file .read
  let initial := State.initial g
  let mut cursor : Trace.Cursor := { state := initial, boundary := initial }
  repeat
    let line ← stream.getLine
    if line.isEmpty then break
    match Trace.checkTextLine cursor line with
    | .error d => IO.eprintln (toJson d).compress; return 1
    | .ok next => cursor := next
  match Trace.finish cursor with
  | .error d => IO.eprintln (toJson d).compress; return 1
  | .ok s =>
    IO.println (Json.mkObj [("valid", toJson true), ("events", toJson (cursor.sequence - 1)), ("status", toJson s.status), ("transactions", toJson cursor.completed.length)]).compress
    return 0

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--help"] | ["help"] => IO.println usage; return 0
    | "check" :: file :: rest =>
      let opts ← liftError (options rest ["--graph"])
      checkFile (← getGraph opts) file
    | "explore" :: rest =>
      let opts ← liftError (options rest ["--graph", "--depth", "--workers", "--tick", "--max-states"])
      let g ← getGraph opts
      let report := Explore.search g (← config opts)
      IO.println (toJson report).compress
      return if report.failure.isSome || !report.complete then 1 else 0
    | "gen" :: rest =>
      let opts ← liftError (options rest ["--graph", "--seed", "--count", "--workers", "--tick"])
      let g ← getGraph opts (some Test.minimal)
      let seed ← liftError (natOpt opts "--seed" 1)
      let count ← liftError (natOpt opts "--count" 20)
      match Explore.generate g (← config opts) seed count with
      | .error r => IO.eprintln (toJson r).compress; return 1
      | .ok (_, events) =>
        for event in events do IO.println (Trace.encodeEvent event)
        return 0
    | _ => IO.eprintln usage; return 2
  catch e =>
    IO.eprintln e.toString
    return 2
