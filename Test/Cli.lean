import Suimon.Trace
import Test.Validate

namespace Suimon.Test.Cli
open Lean

private def cli (args : List String) (code : UInt32) : IO IO.Process.Output := do
  let result ← IO.Process.output { cmd := ".lake/build/bin/suimon", args := args.toArray }
  Validate.ensure (result.exitCode == code)
    s!"CLI {args}: expected exit {code}, got {result.exitCode}\n{result.stdout}\n{result.stderr}"
  return result

def run : IO Unit := do
  for name in ["users", "branch", "merge"] do
    let result ← cli ["validate", s!"Test/programs/{name}.json"] 0
    Validate.ensure (result.stdout == "ok\n") s!"validate {name}: unexpected output {result.stdout}"
  IO.FS.withTempFile fun handle path => do
    handle.putStr "{\"main\":\"w\",\"workflows\":[]}"
    handle.flush
    let result ← cli ["validate", path.toString] 1
    Validate.ensure (Validate.contains result.stderr "unknown main workflow w") s!"invalid program: {result.stderr}"
  for name in ["users", "branch", "merge"] do
    let program := s!"Test/programs/{name}.json"
    let generated ← cli ["gen", program, "--seed", "3"] 0
    IO.FS.withTempFile fun handle path => do
      handle.putStr generated.stdout
      handle.flush
      let result ← cli ["check", path.toString, "--program", program] 0
      Validate.ensure (Validate.contains result.stdout "\"uncommitted\":false") s!"check {name}: {result.stdout}"
      -- `--state` prints the checked state as the derived JSON, which reads back to the same state.
      let expected ← IO.ofExcept (Trace.check Trace.wireCodec (← Validate.load name) generated.stdout)
      for args in [["--program", program, "--state"], ["--state", "--program", program]] do
        let printed ← cli (["check", path.toString] ++ args) 0
        Validate.ensure (printed.stdout == (toJson expected.state).compress ++ "\n") s!"check --state {name}"
        match Json.parse printed.stdout >>= fromJson? with
        | .ok (state : State) => Validate.ensure (state == expected.state) s!"check --state {name}: another state"
        | .error e => throw (IO.userError s!"check --state {name}: {e}")
    -- A record cut in the middle of its last line is recovered, and the cut is reported.
    let lines := (generated.stdout.splitOn "\n").dropLast
    IO.FS.withTempFile fun handle path => do
      handle.putStr (String.join ((lines.dropLast).map (· ++ "\n")) ++ "{\"seq\"")
      handle.flush
      let result ← cli ["check", path.toString, "--program", program] 0
      Validate.ensure (Validate.contains result.stdout s!"\"committed\":{(lines.length - 1) / 2}," &&
        Validate.contains result.stdout "\"uncommitted\":true") s!"check torn {name}: {result.stdout}"
    let explored ← cli ["explore", program, "--seeds", "20"] 0
    Validate.ensure (explored.stdout.startsWith "{") s!"explore {name}: {explored.stdout}"
  let _ ← cli ["check", "Test/programs/users.json"] 1
  let _ ← cli ["check", "Test/programs/users.json", "--program", "Test/programs/users.json", "--states"] 2
  let _ ← cli ["explore", "Test/programs/users.json", "--seeds"] 2
  -- A crash may cut the last line inside a character; only the complete lines must be UTF-8.
  let generated ← cli ["gen", "Test/programs/users.json", "--seed", "3"] 0
  let complete := String.join ((generated.stdout.splitOn "\n").take 4 |>.map (· ++ "\n"))
  IO.FS.withTempFile fun handle path => do
    handle.write (complete.toUTF8 ++ ByteArray.mk #[0xe3, 0x81])
    handle.flush
    let result ← cli ["check", path.toString, "--program", "Test/programs/users.json"] 0
    Validate.ensure (Validate.contains result.stdout "\"committed\":2" && Validate.contains result.stdout "\"uncommitted\":true")
      s!"torn character: {result.stdout}"
  IO.FS.withTempFile fun handle path => do
    handle.write (ByteArray.mk #[0xff, 0x0a])
    handle.flush
    let result ← cli ["check", path.toString, "--program", "Test/programs/users.json"] 1
    Validate.ensure (Validate.contains result.stderr "non UTF-8") s!"invalid complete line: {result.stderr}"
  let _ ← cli ["validate", "Test/programs/missing.json"] 1
  let _ ← cli [] 2
  let _ ← cli ["--help"] 0
  IO.println "cli: ok"

end Suimon.Test.Cli
