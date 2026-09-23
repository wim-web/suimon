import Suimon.Trace
import Suimon.Explore
import Test.Validate

namespace Suimon.Test.Trace
open Lean Suimon Suimon.Test.Validate

/-- Payloads repeat the identities of the values a transition introduces, as `suimon gen` writes them. --/
def withPayloads (before after : State) : List (Value × String) :=
  (Suimon.Trace.introduced before after).map fun v => (v, v)

structure Recorded where
  /-- The operations of the walk with the payloads of their op records. --/
  steps : List (Op × List (Value × String))
  records : List Suimon.Trace.Record
  text : String
  /-- The state before the first transition and after each committed one. --/
  states : List State

/-- The records of a random walk, with the states after each committed transition. --/
def recorded (p : Program) (seed : Nat) : IO Recorded := do
  let (_, ops) := Explore.walk p {} seed 10000
  let mut s : State := {}
  let mut states := [s]
  let mut steps := #[]
  for o in ops do
    let next ← IO.ofExcept (step p s o)
    steps := steps.push (o, withPayloads s next)
    states := states ++ [next]
    s := next
  let (final, records) ← IO.ofExcept (Suimon.Trace.record p {} steps.toList [] 1)
  ensure (final == s) "the recorder reached another state than the walk"
  return { steps := steps.toList, records, text := Suimon.Trace.text Suimon.Trace.wireCodec records, states }

def checked (label : String) (p : Program) (text : String) : IO Suimon.Trace.Checked :=
  match Suimon.Trace.check Suimon.Trace.wireCodec p text with
  | .ok c => pure c
  | .error e => throw (IO.userError s!"{label}: {e}")

def rejectedTrace (label fragment : String) (p : Program) (text : String) : IO Unit :=
  match Suimon.Trace.check Suimon.Trace.wireCodec p text with
  | .ok _ => throw (IO.userError s!"{label}: accepted, expected '{fragment}'")
  | .error e => ensure (contains e fragment) s!"{label}: expected '{fragment}', got {e}"

def rejectedSteps (label fragment : String) (p : Program) (steps : List (Op × List (Value × String))) :
    IO Unit :=
  match Suimon.Trace.record p {} steps [] 1 with
  | .ok _ => throw (IO.userError s!"{label}: recorded, expected '{fragment}'")
  | .error e => ensure (contains e fragment) s!"{label}: expected '{fragment}', got {e}"

/-- The text of records written from `steps`, which the recorder need not accept. --/
def written (steps : List (Op × List (Value × String))) : String :=
  Suimon.Trace.text Suimon.Trace.wireCodec <| (steps.zipIdx.map fun ((o, values), i) =>
    [Suimon.Trace.Record.op (2 * i + 1) o values, .commit (2 * i + 2)]).flatten

/-- A list the engine built, for a waitStream, a Merge or a concurrency List output. --/
def isList (v : Value) : Bool := ((decodeIdentity v).bind (·.head?)) == some "list"

def decodesTo (result : Except String Suimon.Trace.Record) (r : Suimon.Trace.Record) : Bool :=
  match result with
  | .ok decoded => decoded == r
  | .error _ => false

def keys : Wire → List String
  | .obj fields => fields.map (·.1)
  | _ => []

def run : IO Unit := do
  for name in ["users", "branch", "merge"] do
    let p ← load name
    for seed in List.range 20 do
      let label := s!"{name} seed {seed + 1}"
      let r ← recorded p (seed + 1)
      -- Replaying a whole record reproduces the state of the run that wrote it.
      let whole ← checked label p r.text
      ensure (whole.state == r.states.getLast! && whole.committed + 1 == r.states.length && !whole.uncommitted)
        s!"{label}: replay differs from the run"
      ensure (whole.state.values.all fun v => whole.values.any (·.1 == v)) s!"{label}: a value without payload"
      -- Encoding and decoding do not change a record, and an encoded record is one line.
      for record in r.records do
        ensure (decodesTo (Suimon.Trace.recordOfWire (Suimon.Trace.recordWire record)) record)
          s!"{label}: wire codec changed {repr record}"
        let line := Suimon.Trace.wireCodec.encode record
        ensure (decodesTo (Suimon.Trace.wireCodec.decode line) record) s!"{label}: text codec changed {line}"
        ensure (!line.contains '\n') s!"{label}: a newline in {line}"
      -- A commit needs the payload of each value its transition introduces, lists the engine builds
      -- included; an earlier committed record may hold it, a later one may not.
      if let some ((o, values), i) := r.steps.zipIdx.find? (·.1.2.any (isList ·.1)) then
        let lists := values.filter (isList ·.1)
        let stripped := r.steps.set i (o, values.filter (!isList ·.1))
        rejectedTrace s!"{label} list payload" s!"line {2 * i + 2}: missing payloads" p (written stripped)
        rejectedSteps s!"{label} recorder list payload" "missing payloads" p stripped
        let early := stripped.modify 0 fun (first, payloads) => (first, payloads ++ lists)
        let c ← checked s!"{label} early payload" p (written early)
        ensure (c.state == r.states.getLast! && !c.uncommitted) s!"{label}: early payload"
        match Suimon.Trace.record p {} early [] 1 with
        | .ok (final, _) => ensure (final == r.states.getLast!) s!"{label}: recorder with an early payload"
        | .error e => throw (IO.userError s!"{label}: recorder with an early payload: {e}")
        let later := stripped.modify (i + 1) fun (next, payloads) => (next, payloads ++ lists)
        rejectedTrace s!"{label} later payload" s!"line {2 * i + 2}: missing payloads" p (written later)
      -- A crash may cut the record anywhere; recovery keeps exactly the committed transitions.
      let lines := r.records.map Suimon.Trace.wireCodec.encode
      for cut in List.range (lines.length + 1) do
        let prefixText := Suimon.Trace.text Suimon.Trace.wireCodec (r.records.take cut)
        let half := match lines[cut]? with
          | some line => (line.take (line.length / 2)).toString
          | none => ""
        for torn in [prefixText, prefixText ++ half] do
          let c ← checked s!"{label} cut {cut}" p torn
          ensure (c.committed == cut / 2 && c.state == r.states[cut / 2]!) s!"{label} cut {cut}: wrong recovered state"
          ensure (c.uncommitted == (cut % 2 == 1 || torn.length > prefixText.length))
            s!"{label} cut {cut}: uncommitted flag"
          ensure ((Suimon.Trace.recover Suimon.Trace.wireCodec p torn).toOption == some r.states[cut / 2]!)
            s!"{label} cut {cut}: recover"
      -- Corruption before the last commit is an error, not a torn tail.
      if lines.length ≥ 4 then
        let corrupt := String.join ((lines.set 1 "{\"seq\":2").map (· ++ "\n"))
        rejectedTrace s!"{label} corrupt" "line 2" p corrupt
        let reordered := String.join (((lines.take 2).reverse ++ lines.drop 2).map (· ++ "\n"))
        rejectedTrace s!"{label} reordered" "expected sequence 1" p reordered
  -- Fields have a fixed order, and empty values are left out.
  ensure (Suimon.Trace.wireCodec.encode (.op 1 (.start (some "v")) [("v", "payload")]) ==
    "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"v\"},\"values\":{\"v\":\"payload\"}}") "op record text"
  ensure (Suimon.Trace.wireCodec.encode (.commit 2) == "{\"seq\":2,\"commit\":true}") "commit record text"
  ensure (keys (Suimon.Trace.recordWire (.op 1 (.start (some "v")) [("v", "payload")])) == ["seq", "op", "values"])
    "op record fields"
  ensure (keys (Suimon.Trace.recordWire (.op 1 (.start none) [])) == ["seq", "op"]) "empty values"
  ensure (keys (Suimon.Trace.recordWire (.commit 2)) == ["seq", "commit"]) "commit record fields"
  ensure (keys (Suimon.Trace.opWire (.invoke [] "a" none)) == ["type", "run", "placement"]) "absent trigger"
  let p ← load "merge"
  let start := "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
  rejectedTrace "commit twice" "a commit without an op" p (start ++ "{\"seq\":3,\"commit\":true}\n")
  let again := (start.replace "\"seq\":1" "\"seq\":3").replace "\"seq\":2" "\"seq\":4"
  rejectedTrace "rejected op" "rejected" p (start ++ again)
  rejectedTrace "op twice" "an op before the previous commit" p
    "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"op\":{\"type\":\"cancel\"}}\n"
  rejectedTrace "unknown op field" "unknown field trigger" p "{\"seq\":1,\"op\":{\"type\":\"start\",\"trigger\":\"x\"}}\n"
  rejectedTrace "unknown record field" "unknown field extra" p "{\"seq\":1,\"op\":{\"type\":\"start\"},\"extra\":1}\n"
  rejectedTrace "op and commit" "either an op or a commit" p "{\"seq\":1,\"op\":{\"type\":\"start\"},\"commit\":true}\n"
  rejectedTrace "unknown op" "unknown op type" p "{\"seq\":1,\"op\":{\"type\":\"retry\"}}\n"
  rejectedTrace "empty line" "line 1" p "\n"
  let torn ← checked "torn start" p "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"com"
  ensure (torn.committed == 0 && torn.uncommitted && torn.state == {}) "torn start"
  let users ← load "users"
  let startInput := "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}"
  let commit := "{\"seq\":2,\"commit\":true}\n"
  -- Payloads are checked when the transition commits, so an op without its commit needs none.
  rejectedTrace "missing payload" "line 2: missing payloads for [t]" users (startInput ++ "}\n" ++ commit)
  let uncommitted ← checked "uncommitted without payload" users (startInput ++ "}\n")
  ensure (uncommitted.committed == 0 && uncommitted.uncommitted) "uncommitted without payload"
  rejectedTrace "payload not a string" "expected a string" users (startInput ++ ",\"values\":{\"t\":1}}\n")
  let withPayload ← checked "payload" users (startInput ++ ",\"values\":{\"t\":\"x\"}}\n" ++ commit)
  ensure (withPayload.committed == 1 && !withPayload.uncommitted && withPayload.values == [("t", "x")]) "payload"
  -- The recorder refuses a transition without the payloads it introduces, and an op the rules reject.
  rejectedSteps "recorder missing payload" "missing payloads" users [(.start (some "t"), [])]
  rejectedSteps "recorder rejected op" "ALREADY_STARTED" p [(.start none, []), (.start none, [])]
  IO.println "trace: ok"

end Suimon.Test.Trace
