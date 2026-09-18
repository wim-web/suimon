import Test.Schema
import Test.Examples

namespace Suimon.Test.Artifacts
open Lean

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def liftError (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def readJson (path : System.FilePath) : IO Json := do
  liftError (Json.parse (← IO.FS.readFile path))

private def jsonLines (text : String) : IO (List Json) :=
  ((text.splitOn "\n").filter (! ·.isEmpty)).mapM (fun line => liftError (Json.parse line))

private def writeLines (path : System.FilePath) (events : List Json) : IO Unit :=
  IO.FS.writeFile path (String.intercalate "\n" (events.map Json.compress) ++ "\n")

private def cli (args : List String) (code : UInt32 := 0) : IO IO.Process.Output := do
  let result ← IO.Process.output { cmd := ".lake/build/bin/suimon", args := args.toArray }
  ensure (result.exitCode == code)
    s!"CLI {args}: expected exit {code}, got {result.exitCode}\n{result.stdout}\n{result.stderr}"
  return result

private def graphPath (name : String) : String := s!"Test/graphs/{name}.json"
private def tracePath (name : String) : String := s!"Test/traces/{name}.jsonl"

private def validate (schema : Schema.Validator) (value : Json) : IO Unit :=
  liftError (schema.validate value)

private def rejected (schema : Schema.Validator) (value : Json) : IO Unit :=
  ensure ((schema.validate value).toOption.isNone) s!"schema accepted {value.compress}"

private def checkTrace (path : System.FilePath) (graph : String) (code : UInt32 := 0) : IO Json := do
  let result ← cli ["check", path.toString, "--graph", graph] code
  liftError (Json.parse (if code == 0 then result.stdout else result.stderr))

private def schemaTests (graphs events : Schema.Validator) (original : List Json) : IO Unit := do
  -- Exercise constraints independently of the workflow parser and trace checker.
  let graph ← readJson (graphPath "minimal")
  let nodes ← liftError (graph.getObjValAs? (Array Json) "nodes")
  let node ← liftError (graph.getObjVal? "nodes" >>= (·.getArrVal? 0))
  rejected graphs (graph.setObjVal! "nodes" (.arr (nodes.set! 0 (node.setObjVal! "id" (.str "")))))
  rejected graphs (graph.setObjVal! "nodes" (.arr (nodes.set! 0 (node.setObjVal! "unexpected" (.bool true)))))
  let kind ← liftError (node.getObjVal? "kind")
  rejected graphs (graph.setObjVal! "nodes" (.arr (nodes.set! 0
    (node.setObjVal! "kind" (kind.setObjVal! "concurrency" (toJson (0 : Nat)))))))
  let branch ← readJson (graphPath "branch")
  let branchNodes ← liftError (branch.getObjValAs? (Array Json) "nodes")
  let first ← liftError (branch.getObjVal? "nodes" >>= (·.getArrVal? 0))
  let kind ← liftError (first.getObjVal? "kind")
  rejected graphs (branch.setObjVal! "nodes" (.arr (branchNodes.set! 0
    (first.setObjVal! "kind" (kind.setObjVal! "arms" (toJson ["left", "left"]))))))
  for event in original.take 1 do
    for wrong in [toJson (0 : Nat), toJson (-1 : Int), .bool true, .str "1"] do
      rejected events (event.setObjVal! "sequence" wrong)
    rejected events (event.setObjVal! "txn" (.str ""))
    rejected events (event.setObjVal! "op" (.str "unknown"))
    rejected events (event.setObjVal! "extra" (.bool true))
  let oneOf ← liftError (Json.parse "{\"oneOf\":[{},{}]}")
  rejected (← liftError (Schema.compile oneOf)) .null
  for text in ["{\"pattern\":\".*\"}", "{\"$ref\":\"#/$defs/missing\"}",
      "{\"type\":\"unknown\"}", "{\"required\":\"id\"}"] do
    let schema ← liftError (Json.parse text)
    ensure ((Schema.compile schema).toOption.isNone) "unsupported or broken schema silently accepted"

private def mutationTests (temp : System.FilePath) (graphs : Schema.Validator)
    (original : List Json) : IO Unit := do
  let invalid := temp / "independent-coalesce.json"
  IO.FS.writeFile invalid (toJson independentCoalesce).compress
  let _ ← cli ["explore", "--graph", invalid.toString] 2
  let firstTxn := ((original.head?.getD .null).getObjValD "txn")
  let lastTxn := ((original.getLast?.getD .null).getObjValD "txn")
  let removedCommit := (original.filter fun event => event.getObjValD "sequence" != toJson (4 : Nat)).zipIdx.map
    (fun (event, idx) => event.setObjVal! "sequence" (toJson (idx + 1)))
  let wrongExpiry := original.map fun event =>
    if event.getObjValD "type" == .str "attempt.started" && (event.getObjValD "op").isNull then
      event.setObjVal! "data" ((event.getObjValD "data").setObjVal! "lease_until" (toJson (999 : Nat)))
    else event
  let mutations : List (String × List Json) := [
    ("truncated", original.dropLast),
    ("sequence-gap", original.zipIdx.map fun (event, idx) =>
      if idx == 0 then event.setObjVal! "sequence" (toJson (2 : Nat)) else event),
    ("transaction-reuse", original.map fun event =>
      if event.getObjValD "txn" == lastTxn then event.setObjVal! "txn" firstTxn else event),
    ("unknown-field", original.zipIdx.map fun (event, idx) =>
      if idx == 0 then event.setObjVal! "unexpected" (.bool true) else event),
    ("wrong-expiry", wrongExpiry),
    ("missing-commit", removedCommit)]
  for (name, trace) in mutations do
    let path := temp / s!"{name}.jsonl"
    writeLines path trace
    let diagnostic ← checkTrace path (graphPath "minimal") 1
    let code ← liftError ((diagnostic.getObjValD "reason").getObjValAs? String "code")
    ensure (!code.isEmpty) s!"missing diagnostic for {name}"
    if name == "wrong-expiry" then
      ensure ((diagnostic.getObjValD "boundary").getObjValD "attempts" == .arr #[])
        "uncommitted attempt leaked into diagnostic"
  let malformed := temp / "malformed.jsonl"
  IO.FS.writeFile malformed "{broken\n"
  let diagnostic ← checkTrace malformed (graphPath "minimal") 1
  ensure ((diagnostic.getObjValD "reason").getObjValD "code" == .str "INVALID_JSON") "malformed JSON diagnostic"
  let graph ← readJson (graphPath "minimal")
  let nodes ← liftError (graph.getObjValAs? (Array Json) "nodes")
  let node ← liftError (graph.getObjVal? "nodes" >>= (·.getArrVal? 0))
  let bad := graph.setObjVal! "nodes" (.arr (nodes.set! 0 (node.setObjVal! "unexpected" (.bool true))))
  rejected graphs bad
  let path := temp / "unknown-graph-field.json"
  IO.FS.writeFile path bad.compress
  let _ ← cli ["explore", "--graph", path.toString] 2

def run : IO Unit := do
  let graphs ← liftError (Schema.compile (← readJson "schema/graph.schema.json"))
  let events ← liftError (Schema.compile (← readJson "schema/events.schema.json"))
  for entry in ← System.FilePath.readDir "Test/graphs" do
    if entry.path.extension == some "json" then validate graphs (← readJson entry.path)
  for entry in ← System.FilePath.readDir "Test/traces" do
    if entry.path.extension == some "jsonl" then
      for event in ← jsonLines (← IO.FS.readFile entry.path) do validate events event
  let original ← jsonLines (← IO.FS.readFile (tracePath "minimal"))
  schemaTests graphs events original
  let good ← checkTrace (tracePath "minimal") (graphPath "minimal")
  ensure (good.getObjValD "valid" == .bool true && good.getObjValD "status" == .str "succeeded") "minimal trace failed"
  for (trace, graph) in [("coalesce", "coalesce"), ("loop-retry", "loop")] do
    let result ← checkTrace (tracePath trace) (graphPath graph)
    ensure (result.getObjValD "status" == .str "succeeded") s!"{trace} trace failed"
  for name in ["missing-attempt", "after-eos"] do
    let diagnostic ← checkTrace (tracePath name) (graphPath "minimal") 1
    let sequence ← liftError (diagnostic.getObjValAs? Nat "sequence")
    ensure (sequence > 0 && !(diagnostic.getObjValD "boundary").isNull) "incomplete rejection diagnostic"
  for options in [["--depth", "-1"], ["--workers", "0"], ["--typo", "8"]] do
    let _ ← cli (["explore", "--graph", graphPath "minimal"] ++ options) 2
  let limited ← cli ["explore", "--graph", graphPath "minimal", "--max-states", "1"] 1
  let report ← liftError (Json.parse limited.stdout)
  ensure (report.getObjValD "complete" == .bool false) "truncated exploration reported success"
  IO.FS.withTempDir fun temp => do
    mutationTests temp graphs original
    for (name, _) in examples do
      for seed in [1, 3, 17] do
        let args := ["gen", "--graph", graphPath name, "--seed", toString seed, "--count", "30"]
        let generated ← cli args
        ensure (generated.stdout == (← cli args).stdout) "generation is not reproducible"
        for event in ← jsonLines generated.stdout do validate events event
        let path := temp / "generated.jsonl"
        IO.FS.writeFile path generated.stdout
        let _ ← checkTrace path (graphPath name)
  IO.println "ok: JSON schemas, CLI diagnostics, corrupted traces, reproducible generation"

end Suimon.Test.Artifacts
