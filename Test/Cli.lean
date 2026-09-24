import Suimon.Trace
import Test.Validate
import Test.Trace

namespace Suimon.Test.Cli
open Lean

private def cli (args : List String) (code : UInt32) : IO IO.Process.Output := do
  let result ← IO.Process.output { cmd := ".lake/build/bin/suimon", args := args.toArray }
  Validate.ensure (result.exitCode == code)
    s!"CLI {args}: expected exit {code}, got {result.exitCode}\n{result.stdout}\n{result.stderr}"
  return result

private def statusName (s : Status) : String :=
  match toJson s with
  | .str name => name
  | other => other.compress

def run : IO Unit := do
  for name in ["users", "branch", "merge"] do
    let result ← cli ["validate", s!"Test/definitions/{name}.json"] 0
    Validate.ensure (result.stdout == "ok\n") s!"validate {name}: unexpected output {result.stdout}"
  IO.FS.withTempFile fun handle path => do
    handle.putStr "{\"main\":\"w\",\"workflows\":[]}"
    handle.flush
    let result ← cli ["validate", path.toString] 1
    Validate.ensure (Validate.contains result.stderr "unknown main workflow w") s!"invalid definition: {result.stderr}"
  for name in ["users", "branch", "merge"] do
    let definition := s!"Test/definitions/{name}.json"
    let generated ← cli ["gen", definition, "--seed", "3"] 0
    -- The record starts with the header, which holds the definition, validated before the walk.
    let lines := (generated.stdout.splitOn "\n").dropLast
    let headerLine := Trace.wireCodec.encodeHeader (.of (← Validate.load name) true)
    Validate.ensure (lines.head? == some headerLine) s!"gen {name}: the first line is not the header"
    IO.FS.withTempFile fun handle path => do
      handle.putStr generated.stdout
      handle.flush
      let result ← cli ["check", path.toString] 0
      Validate.ensure (Validate.contains result.stdout "\"uncommitted\":false") s!"check {name}: {result.stdout}"
      -- `--state` prints the checked state as the derived JSON, which reads back to the same state.
      let expected ← IO.ofExcept (Trace.check Trace.wireCodec Trace.Header.load generated.stdout)
      let printed ← cli ["check", path.toString, "--state"] 0
      Validate.ensure (printed.stdout == (toJson expected.state).compress ++ "\n") s!"check --state {name}"
      match Json.parse printed.stdout >>= fromJson? with
      | .ok (state : State) => Validate.ensure (state == expected.state) s!"check --state {name}: another state"
      | .error e => throw (IO.userError s!"check --state {name}: {e}")
    -- A record cut in the middle of its last line is recovered, and the cut is reported.
    IO.FS.withTempFile fun handle path => do
      handle.putStr (String.join ((lines.dropLast).map (· ++ "\n")) ++ "{\"seq\"")
      handle.flush
      let result ← cli ["check", path.toString] 0
      Validate.ensure (Validate.contains result.stdout s!"\"committed\":{(lines.length - 2) / 2}," &&
        Validate.contains result.stdout "\"uncommitted\":true") s!"check torn {name}: {result.stdout}"
    -- A record cut inside its header has committed nothing; a header alone neither.
    -- The flag is null until the header line is complete.
    for (text, torn, validated) in
        [((headerLine.take 20).toString, true, "null"), (headerLine ++ "\n", false, "true")] do
      IO.FS.withTempFile fun handle path => do
        handle.putStr text
        handle.flush
        let result ← cli ["check", path.toString] 0
        Validate.ensure (result.stdout ==
            s!"\{\"committed\":0,\"status\":\"running\",\"uncommitted\":{torn},\"validated\":{validated}}\n")
          s!"check header {name}: {result.stdout}"
    let explored ← cli ["explore", definition, "--seeds", "20"] 0
    Validate.ensure (explored.stdout.startsWith "{") s!"explore {name}: {explored.stdout}"
  let _ ← cli ["check", "Test/definitions/users.json"] 1
  let _ ← cli ["check", "Test/definitions/users.json", "--states"] 2
  let _ ← cli ["check", "x.jsonl", "--definition", "Test/definitions/users.json"] 2
  let _ ← cli ["explore", "Test/definitions/users.json", "--seeds"] 2
  -- The definition of a header marked as validated is read like a definition file: decoded, then
  -- validated. That of a header marked as unchecked is only decoded.
  IO.FS.withTempFile fun handle path => do
    handle.putStr "{\"definition\":{\"main\":\"w\",\"workflows\":[]},\"validated\":true}\n"
    handle.flush
    let result ← cli ["check", path.toString] 1
    Validate.ensure (result.stderr == "line 1: unknown main workflow w\n") s!"invalid header: {result.stderr}"
  IO.FS.withTempFile fun handle path => do
    handle.putStr "{\"definition\":{\"main\":\"w\",\"workflows\":[]},\"validated\":false}\n"
    handle.flush
    let result ← cli ["check", path.toString] 0
    Validate.ensure
        (result.stdout == "{\"committed\":0,\"status\":\"running\",\"uncommitted\":false,\"validated\":false}\n")
      s!"unchecked invalid header: {result.stdout}"
  -- The flag is required, and a boolean.
  for (flag, message) in [("", "line 1: header: missing field validated\n"),
      (",\"validated\":\"false\"", "line 1: header.validated: expected a boolean\n")] do
    IO.FS.withTempFile fun handle path => do
      handle.putStr s!"\{\"definition\":\{\"main\":\"w\",\"workflows\":[]}{flag}}\n"
      handle.flush
      let result ← cli ["check", path.toString] 1
      Validate.ensure (result.stderr == message) s!"header flag {flag}: {result.stderr}"
  -- A number in the header's definition is bounded as in a definition file, whatever the flag.
  for validated in ["true", "false"] do
    IO.FS.withTempFile fun handle path => do
      handle.putStr ("{\"definition\":{\"main\":\"w\",\"workflows\":[{\"id\":\"w\",\"placements\":[{\"name\":\"c\"," ++
        "\"node\":{\"type\":\"concurrency\",\"limit\":18446744073709551616,\"tasks\":[],\"output\":\"list\"," ++
        s!"\"element\":\"T\"},\"policy\":\"stop\"}]}]},\"validated\":{validated}}\n")
      handle.flush
      let result ← cli ["check", path.toString] 1
      Validate.ensure (result.stderr ==
          "line 1: workflows.w.placements.c.node.limit: must be at most 18446744073709551615\n")
        s!"large header number: {result.stderr}"
  -- The record of an execution started without validation checks without validation, and `--state`
  -- prints the state it replays to; marked as validated, the same record is refused with the error of
  -- validation.
  for (name, invalid, error) in ← Trace.invalidDefinitions do
    for seed in [1, 2, 3] do
      for validated in [false, true] do
        let recorded ← Trace.recorded invalid seed validated
        IO.FS.withTempFile fun handle path => do
          handle.putStr recorded.text
          handle.flush
          if validated then
            let result ← cli ["check", path.toString] 1
            Validate.ensure (result.stderr == s!"line 1: {error}\n") s!"{name} validated record: {result.stderr}"
          else
            let final := recorded.states.getLast!
            let result ← cli ["check", path.toString] 0
            Validate.ensure (result.stdout == s!"\{\"committed\":{recorded.states.length - 1},\"status\":" ++
              s!"\"{statusName final.status}\",\"uncommitted\":false,\"validated\":false}\n")
              s!"{name} unchecked record: {result.stdout}"
            let printed ← cli ["check", path.toString, "--state"] 0
            Validate.ensure (printed.stdout == (toJson final).compress ++ "\n") s!"{name} unchecked record --state"
  -- No object may repeat a key, in a definition file or in any line of a record.
  IO.FS.withTempFile fun handle path => do
    handle.putStr "{\"main\":\"w\",\"main\":\"w\",\"workflows\":[]}"
    handle.flush
    let result ← cli ["validate", path.toString] 1
    Validate.ensure (result.stderr == "offset 18: duplicate key \"main\"\n") s!"repeated key: {result.stderr}"
  IO.FS.withTempFile fun handle path => do
    handle.putStr "{\"definition\":{\"main\":\"w\",\"main\":\"w\",\"workflows\":[]}}\n"
    handle.flush
    let result ← cli ["check", path.toString] 1
    Validate.ensure (result.stderr == "line 1: duplicate key \"main\" at offset 32\n")
      s!"repeated header key: {result.stderr}"
  -- A crash may cut the last line inside a character; only the complete lines must be UTF-8.
  let generated ← cli ["gen", "Test/definitions/users.json", "--seed", "3"] 0
  let complete := String.join ((generated.stdout.splitOn "\n").take 5 |>.map (· ++ "\n"))
  IO.FS.withTempFile fun handle path => do
    handle.write (complete.toUTF8 ++ ByteArray.mk #[0xe3, 0x81])
    handle.flush
    let result ← cli ["check", path.toString] 0
    Validate.ensure (Validate.contains result.stdout "\"committed\":2" && Validate.contains result.stdout "\"uncommitted\":true")
      s!"torn character: {result.stdout}"
  IO.FS.withTempFile fun handle path => do
    handle.write (ByteArray.mk #[0xff, 0x0a])
    handle.flush
    let result ← cli ["check", path.toString] 1
    Validate.ensure (Validate.contains result.stderr "non UTF-8") s!"invalid complete line: {result.stderr}"
  let _ ← cli ["validate", "Test/definitions/missing.json"] 1
  let _ ← cli [] 2
  let _ ← cli ["--help"] 0
  IO.println "cli: ok"

end Suimon.Test.Cli
