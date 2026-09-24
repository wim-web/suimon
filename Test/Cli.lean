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
    -- The record starts with the header, which holds the definition.
    let lines := (generated.stdout.splitOn "\n").dropLast
    let headerLine := Trace.wireCodec.encodeHeader (Codec.definitionWire (← Validate.load name))
    Validate.ensure (lines.head? == some headerLine) s!"gen {name}: the first line is not the header"
    IO.FS.withTempFile fun handle path => do
      handle.putStr generated.stdout
      handle.flush
      let result ← cli ["check", path.toString] 0
      Validate.ensure (Validate.contains result.stdout "\"uncommitted\":false") s!"check {name}: {result.stdout}"
      -- `--state` prints the checked state as the derived JSON, which reads back to the same state.
      let expected ← IO.ofExcept (Trace.check Trace.wireCodec Test.Trace.loadHeader generated.stdout)
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
    for (text, torn) in [((headerLine.take 20).toString, true), (headerLine ++ "\n", false)] do
      IO.FS.withTempFile fun handle path => do
        handle.putStr text
        handle.flush
        let result ← cli ["check", path.toString] 0
        Validate.ensure (result.stdout == s!"\{\"committed\":0,\"status\":\"running\",\"uncommitted\":{torn}}\n")
          s!"check header {name}: {result.stdout}"
    let explored ← cli ["explore", definition, "--seeds", "20"] 0
    Validate.ensure (explored.stdout.startsWith "{") s!"explore {name}: {explored.stdout}"
  let _ ← cli ["check", "Test/definitions/users.json"] 1
  let _ ← cli ["check", "Test/definitions/users.json", "--states"] 2
  let _ ← cli ["check", "x.jsonl", "--definition", "Test/definitions/users.json"] 2
  let _ ← cli ["explore", "Test/definitions/users.json", "--seeds"] 2
  -- The definition of the header is read like a definition file: decoded, then validated.
  IO.FS.withTempFile fun handle path => do
    handle.putStr "{\"definition\":{\"main\":\"w\",\"workflows\":[]}}\n"
    handle.flush
    let result ← cli ["check", path.toString] 1
    Validate.ensure (result.stderr == "line 1: unknown main workflow w\n") s!"invalid header: {result.stderr}"
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
