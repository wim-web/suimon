import Suimon
import Suimon.Trace

open Lean Suimon

private def usage : String :=
  "suimon validate <definition.json>\n" ++
  "suimon check <trace.jsonl> [--state]\n" ++
  "suimon explore <definition.json> [--seeds N] [--steps N]\n" ++
  "suimon gen <definition.json> [--seed N] [--steps N]\n"

/-- Options with a value, and `flags` without one, which map to `""`. --/
private def options (args : List String) (allowed : List String) (flags : List String := []) :
    Except String (List (String × String)) :=
  match args with
  | [] => pure []
  | key :: rest =>
    if flags.contains key then return (key, "") :: (← options rest allowed flags)
    else match rest with
      | value :: rest => do
        unless allowed.contains key do throw s!"unknown option {key}"
        return (key, value) :: (← options rest allowed flags)
      | [] => throw s!"missing value for {key}"

private def natOption (opts : List (String × String)) (key : String) (default : Nat) : Except String Nat :=
  match opts.lookup key with
  | none => pure default
  | some text => match text.toNat? with
    | some n => pure n
    | none => throw s!"{key} expects a natural number"

/-- Reads a definition file: JSON text without repeated keys (`Codec.parse`), decoded and validated
    (`Codec.loadJson`). --/
private def readDefinition (path : String) : IO Definition := do
  match Codec.parse (← IO.FS.readFile path) >>= Codec.loadJson with
  | .ok p => pure p
  | .error e => throw (IO.userError e)

private def statusName (s : Status) : String :=
  match toJson s with
  | .str name => name
  | other => other.compress

private def run (action : IO UInt32) : IO UInt32 := do
  try action catch e => IO.eprintln e; return 1

private def validateFile (path : String) : IO UInt32 := run do
  let _ ← readDefinition path
  IO.println "ok"
  return 0

/-- The complete lines of a record, and whether anything follows the last newline. A crash may cut
    the last line inside a character, so only the complete lines must be UTF-8 (§12.1). --/
private def readRecord (path : String) : IO (String × Bool) := do
  let bytes ← IO.FS.readBinFile path
  let cut := (bytes.toList.reverse.dropWhile (· != 10)).length
  match String.fromUTF8? (bytes.extract 0 cut) with
  | some text => return (text, cut < bytes.size)
  | none => throw (IO.userError s!"Tried to read file '{path}' containing non UTF-8 data.")

/-- Replays a record against the definition of its header, which is read by the header's flag
    (`Trace.Header.load`): decoded and validated like a definition file when the execution was started
    with validation, decoded only when it was started without. --/
private def checkFile (trace : String) (opts : List (String × String)) : IO UInt32 := run do
  let (text, torn) ← readRecord trace
  match (Trace.check Trace.wireCodec Trace.Header.load text).map fun c =>
      { c with uncommitted := c.uncommitted || torn } with
  | .ok checked =>
    -- `--state` prints the whole state, for comparing another implementation's state with this one.
    if (opts.lookup "--state").isSome then IO.println (toJson checked.state).compress
    else
      IO.println (Json.mkObj [("status", statusName checked.state.status), ("committed", checked.committed),
        ("uncommitted", checked.uncommitted), ("validated", toJson checked.validated)]).compress
    return 0
  | .error e => IO.eprintln e; return 1

private def explore (path : String) (opts : List (String × String)) : IO UInt32 := run do
  let definition ← readDefinition path
  let seeds ← IO.ofExcept (natOption opts "--seeds" 100)
  let steps ← IO.ofExcept (natOption opts "--steps" 10000)
  let mut counts : List (String × Nat) := []
  for seed in List.range seeds do
    let (s, _) := Explore.walk definition {} (seed + 1) steps
    unless s.status.terminal do
      IO.eprintln s!"seed {seed + 1}: no accepted operation in status {statusName s.status}"
      return 1
    let name := statusName s.status
    counts := (name, (counts.lookup name).getD 0 + 1) :: counts.filter (·.1 != name)
  IO.println (Json.mkObj (counts.map fun (name, n) => (name, toJson n))).compress
  return 0

/-- A random walk written as an execution record: the header, then the records. The definition is
    validated before the walk, as run validates it, so the header says so. Each op record carries the
    payloads of the values its transition introduces, and a payload repeats its value identity. --/
private def gen (path : String) (opts : List (String × String)) : IO UInt32 := run do
  let definition ← readDefinition path
  let seed ← IO.ofExcept (natOption opts "--seed" 1)
  let steps ← IO.ofExcept (natOption opts "--steps" 10000)
  let (_, ops) := Explore.walk definition {} seed steps
  let mut state : State := {}
  let mut transactions := #[]
  for o in ops do
    let next ← IO.ofExcept (step definition state o)
    transactions := transactions.push (o, (Trace.introduced state next).map fun v => (v, v))
    state := next
  let (_, records) ← IO.ofExcept (Trace.record definition {} transactions.toList [] 1)
  IO.print (Trace.recording Trace.wireCodec (.of definition true) records)
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["help"] => IO.print usage; return 0
  | ["validate", path] => validateFile path
  | "check" :: trace :: rest => match options rest [] ["--state"] with
    | .ok opts => checkFile trace opts
    | .error e => IO.eprintln e; return 2
  | "explore" :: path :: rest => match options rest ["--seeds", "--steps"] with
    | .ok opts => explore path opts
    | .error e => IO.eprintln e; return 2
  | "gen" :: path :: rest => match options rest ["--seed", "--steps"] with
    | .ok opts => gen path opts
    | .error e => IO.eprintln e; return 2
  | _ => IO.eprint usage; return 2
