import Suimon
import Test.Examples
import Test.Schema

namespace Suimon.Test.TraceText
open Lean

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def ops (s : String) : List Op :=
  let auth : Credentials := ⟨s, s, s, 10 ^ 40⟩
  [.start [⟨⟨s, s⟩, [s, ""]⟩], .activate [s] s, .spawn [s] s s,
    .claim auth s, .renew auth, .expireLease s (10 ^ 40), .promoteRetry s 0,
    .emit auth s s, .complete auth [⟨s, [s, ""]⟩], .fail auth s true,
    .fireWaitAll [s] s, .fireBranch [s] s s, .fireCoalesce [s] s s s,
    .fireCollect [s] s, .fireFilter [s] s s false, .fireMerge [s] s s s,
    .propagateEos [s] s, .finishSubworkflow s, .loopIterate s true,
    .skip [s] s, .idle, .cancel, .manualRetry s]

/-- Interoperability with Lean's independent standard JSON parser and the old
    v2 event reader; this does not merely call the proved codec twice. --/
private def interoperability : IO Unit := do
  let text := "日本語🔁\"\\" ++ String.ofList ((List.range 32).map Char.ofNat)
  let values : List Json := [.null, .bool true, .str text,
    .num ⟨-(10 ^ 45 : Int), 12⟩, .num ⟨0, 7⟩,
    Json.mkObj [("z", .arr #[.str text, .num ⟨123, 2⟩]), ("a", Json.mkObj [])]]
  for data in values do
    for op in none :: (ops text).map some do
      let e : Trace.Event := {
        sequence := 10 ^ 40, txn := text, recorded_at := 10 ^ 30
        type := text, op, data }
      let encoded := Trace.encodeEvent e
      let standard ← match Trace.parseEvent encoded with
        | .ok event => pure event
        | .error message => throw (IO.userError s!"canonical JSON is not standard v2: {message}")
      ensure (Trace.sameJson (toJson e) (toJson standard)) "standard JSON changed an event value"
      for suffix in ["", "\n", "\r\n"] do
        match Trace.decodeWire (encoded ++ suffix) with
        | some wire =>
          ensure (wire.data == Trace.jsonAtoms data && wire.op == op && wire.txn == text && wire.sequence == e.sequence)
            "canonical decoder changed an event value"
        | none => throw (IO.userError "canonical reader unexpectedly used compatibility fallback")
      -- The standard printer normalizes decimal representations; compare its
      -- parsed value, not the original mantissa/exponent pair.
      let legacy := (toJson e).compress
      let legacyExpected ← match Trace.parseEvent legacy with
        | .ok event => pure event
        | .error message => throw (IO.userError message)
      match Trace.parseWireEvent legacy with
      | .ok wire =>
        ensure (wire.data == Trace.jsonAtoms legacyExpected.data && wire.op == legacyExpected.op)
          "compatibility reader changed values"
      | .error message => throw (IO.userError message)
  for value in values do
    ensure (Trace.sameJson value value) "structural JSON equality is not reflexive"
    for other in values do
      ensure (Trace.sameJson value other == (value == other)) "structural equality differs from standard JSON"
  let left := Json.mkObj [("b", .str text), ("a", .num ⟨1, 0⟩)]
  let right := Json.mkObj [("a", .num ⟨1, 0⟩), ("b", .str text)]
  ensure (Trace.sameJson left right) "object insertion order leaked into equality"

private def protocol : IO Unit := do
  let auth : Credentials := ⟨instanceId [] "work", "attempt", "token", 0⟩
  let commands : List Op := [.start (Explore.inputValues minimal), .activate [] "work",
    .claim auth "worker", .complete auth [⟨"out", ["result"]⟩], .idle]
  let (state, events) ← match Trace.recordTransaction (.initial minimal) commands 1 "text" 0 with
    | .ok result => pure result
    | .error error => throw (IO.userError error.code)
  match Trace.checkText minimal (events.map Trace.encodeEvent) with
  | .ok replayed => ensure (replayed == state) "JSONL replay changed state"
  | .error d => throw (IO.userError (toJson d).compress)
  for cut in List.range events.length do
    match Trace.recoverText minimal ((events.take cut).map Trace.encodeEvent) with
    | .ok recovered => ensure (recovered == State.initial minimal) "torn JSONL exposed uncommitted changes"
    | .error d => throw (IO.userError (toJson d).compress)
  let some first := events.head? | throw (IO.userError "missing recorded events")
  let sample := Trace.encodeEvent first
  for malformed in [sample.replace ", " " ", sample.replace "{ " "{ , ", sample ++ "null",
      sample.replace "\"data\": { }" "\"data\": { \"bad\": }",
      sample.replace "\"schema_version\": 2e-0" "\"schema_version\": 1e-0"] do
    ensure ((Trace.parseWireEvent malformed) matches .error _) "canonical parser accepted malformed/old JSON"
  let schema ← match Json.parse (← IO.FS.readFile "schema/events.schema.json") >>= Schema.compile with
    | .ok schema => pure schema
    | .error message => throw (IO.userError message)
  for e in events do
    let json ← match Json.parse (Trace.encodeEvent e) with
      | .ok json => pure json
      | .error message => throw (IO.userError message)
    ensure ((schema.validate json) matches .ok _) "canonical encoding violates schema v2"

def run : IO Unit := do
  interoperability
  protocol
  IO.println "ok: proved JSONL codec, standard JSON interoperability, every torn transaction prefix"

end Suimon.Test.TraceText
