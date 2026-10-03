import Test.Trace

namespace Suimon.Test.TraceBounded
open Suimon.Trace Suimon.Test.Validate

private def check (text : String) (limits : Limits := {}) : Except String Checked :=
  Suimon.Trace.check wireCodec Header.load text limits

private def rejected (label expected text : String) (limits : Limits) : IO Unit := do
  match check text limits with
  | .ok _ => throw (IO.userError s!"{label}: accepted")
  | .error e => ensure (e == expected) s!"{label}: expected {expected}, got {e}"

/-- Build a valid sustained stream without using the reference recorder's history scans. --/
def stream (p : Definition) (count : Nat) : String := Id.run do
  let call := Key.invocation [] "fetchAllUsers" none
  let mut records : Array Record := #[.op 1 (.start (some "tenant")) [("tenant", "payload")],
    .commit 2, .op 3 (.invoke [] "fetchAllUsers" none) [], .commit 4]
  for i in [:count] do
    let seq := 4 * i + 5
    let v := s!"v{i}"
    records := records.push (.op seq (.fetch call) [])
    records := records.push (.commit (seq + 1))
    records := records.push (.op (seq + 2) (.yielded call v) [(v, v)])
    records := records.push (.commit (seq + 3))
  return recording wireCodec (.of p true) records.toList

/-- Allocation counts avoid wall-clock noise while catching copies of the growing payload history.
    Transition replay itself still uses the list-based model and is separately work-bounded. --/
private def payloadCost (n : Nat) : IO Nat := do
  let start ← IO.getNumHeartbeats
  let mut payloads : Bounded.Payloads := {}
  for i in [:n] do
    let v := toString i
    payloads ← IO.ofExcept (payloads.commit (some v) [(v, v)] n "benchmark")
  ensure (payloads.known.size == n && payloads.reversed.length == n) "payload benchmark lost values"
  let finish ← IO.getNumHeartbeats
  return finish - start

def run : IO Unit := do
  let p ← load "users"
  let text := stream p 2
  let bytes := text.utf8ByteSize
  let exact : Limits := { maxBytes := bytes, maxRecords := 12, maxValues := 3 }
  let c ← IO.ofExcept (check text exact)
  ensure (c.committed == 6 && c.values == [("tenant", "payload"), ("v0", "v0"), ("v1", "v1")])
    "exact limits or payload order"
  rejected "byte limit" s!"record-byte limit exceeded (max {bytes - 1})" text
    { exact with maxBytes := bytes - 1 }
  rejected "record limit" "record-count limit exceeded (max 11)" text { exact with maxRecords := 11 }
  ensure ((recover wireCodec Header.load text { maxRecords := 0 }).toOption.isNone)
    "recover bypassed the record limit"
  ensure ((resume wireCodec Header.load p text { maxBytes := 0 }).toOption.isNone)
    "resume bypassed the byte limit"
  rejected "value limit" "line 13: introduced-value limit exceeded (max 2)" text
    { exact with maxValues := 2 }
  -- Work rejects before decoding (even a codec that always fails) or executing the next step.
  rejected "work before parse" "record: replay-work limit exceeded (max 0)" text { maxWork := 0 }
  let header := Suimon.Test.Trace.header p
  let first := wireCodec.encode (.op 1 (.start (some "tenant")) [("tenant", "payload")])
  let commit := wireCodec.encode (.commit 2)
  let short := header ++ first ++ "\n" ++ commit ++ "\n"
  let parsing := short.utf8ByteSize + header.utf8ByteSize + first.utf8ByteSize + 1 + commit.utf8ByteSize + 1
  let exactWork := parsing + header.utf8ByteSize
  let _ ← IO.ofExcept (check short { maxWork := exactWork })
  rejected "work before step" s!"line 3: replay-work limit exceeded (max {exactWork - 1})" short
    { maxWork := exactWork - 1 }
  -- Complete uncommitted ops consume a record slot; a torn tail consumes bytes only.
  let pending := header ++ first ++ "\n"
  let pc ← IO.ofExcept (check pending { maxRecords := 1, maxValues := 0 })
  ensure (pc.uncommitted && pc.values.isEmpty) "uncommitted payloads entered the index"
  rejected "pending record limit" "record-count limit exceeded (max 0)" pending { maxRecords := 0 }
  let _ ← IO.ofExcept (check header { maxRecords := 0, maxValues := 0 })
  let _ ← IO.ofExcept (check "" { maxBytes := 0, maxRecords := 0, maxValues := 0, maxWork := 0 })
  rejected "UTF-8 bytes" "record-byte limit exceeded (max 2)" "猫" { maxBytes := 2 }
  let torn ← IO.ofExcept (check "猫" { maxBytes := 3 })
  ensure torn.uncommitted "torn UTF-8 header"
  rejected "tail bytes" s!"record-byte limit exceeded (max {bytes})" (text ++ "x") exact
  -- Duplicate keys remain rejected by the wire parser, even with matching payloads.
  let duplicate := header ++ "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"tenant\"}," ++
    "\"values\":{\"tenant\":\"a\",\"tenant\":\"a\"}}\n{\"seq\":2,\"commit\":true}\n"
  let _ ← Suimon.Test.Trace.checkBoth "bounded duplicate" duplicate
  -- A value may recur in state, but its payload must not recur, even if identical.
  let repeated := text ++ Suimon.Test.Trace.written [(.fetch (Key.invocation [] "fetchAllUsers" none), [])]
  -- This also checks deterministic sequence validation after a long committed prefix.
  let _ ← Suimon.Test.Trace.checkBoth "bounded sequence" repeated
  let call := Key.invocation [] "fetchAllUsers" none
  let same := text ++ Suimon.Trace.text wireCodec [.op 13 (.fetch call) [], .commit 14,
    .op 15 (.yielded call "v0") [], .commit 16]
  let _ ← Suimon.Test.Trace.checkBoth "reused identity without payload" same
  let extra := text ++ Suimon.Trace.text wireCodec [.op 13 (.fetch call) [], .commit 14,
    .op 15 (.yielded call "v0") [("v0", "different")], .commit 16]
  let _ ← Suimon.Test.Trace.checkBoth "reused identity with payload" extra
  for n in [64, 128, 256] do
    let _ ← Suimon.Test.Trace.checkBoth s!"stream {n}" (stream p n)
  for n in [512, 1024] do
    let start ← IO.monoMsNow
    let c ← IO.ofExcept (check (stream p n) { maxWork := 100000000000 })
    ensure (c.committed == 2 + 2 * n && c.values.length == n + 1) s!"stream {n}: lost transitions"
    IO.println s!"bounded stream {n}: {(← IO.monoMsNow) - start}ms"
  let small ← payloadCost 10000
  let large ← payloadCost 20000
  ensure (large < 3 * small) s!"payload bookkeeping grew faster than linearly: {small}, {large}"
  IO.println s!"bounded payload allocations: {small}, {large}"
  IO.println "bounded trace: ok"

end Suimon.Test.TraceBounded
