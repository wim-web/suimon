import Suimon.Trace
import Suimon.Explore
import Test.Validate

namespace Suimon.Test.Trace
open Lean Suimon Suimon.Test.Validate

/-- Payloads repeat the identities of the values a transition introduces, as `suimon gen` writes them. --/
def withPayloads (before after : State) : List (Value × String) :=
  (Suimon.Trace.introduced before after).map fun v => (v, v)

/-- The header line of a record of `p`, with its newline. --/
def header (p : Definition) : String :=
  Suimon.Trace.wireCodec.encodeHeader (Codec.definitionWire p) ++ "\n"

structure Recorded where
  /-- The operations of the walk with the payloads of their op records. --/
  steps : List (Op × List (Value × String))
  records : List Suimon.Trace.Record
  /-- The header, then the records. --/
  text : String
  /-- The state before the first transition and after each committed one. --/
  states : List State

/-- The records of a random walk, with the states after each committed transition. --/
def recorded (p : Definition) (seed : Nat) : IO Recorded := do
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
  let text := Suimon.Trace.recording Suimon.Trace.wireCodec (Codec.definitionWire p) records
  return { steps := steps.toList, records, text, states }

def checkedText (label : String) (text : String) : IO Suimon.Trace.Checked :=
  match Suimon.Trace.check Suimon.Trace.wireCodec Codec.load text with
  | .ok c => pure c
  | .error e => throw (IO.userError s!"{label}: {e}")

def rejectedText (label fragment : String) (text : String) : IO Unit :=
  match Suimon.Trace.check Suimon.Trace.wireCodec Codec.load text with
  | .ok _ => throw (IO.userError s!"{label}: accepted, expected '{fragment}'")
  | .error e => ensure (contains e fragment) s!"{label}: expected '{fragment}', got {e}"

def rejectedExactly (label expected : String) (text : String) : IO Unit :=
  match Suimon.Trace.check Suimon.Trace.wireCodec Codec.load text with
  | .ok _ => throw (IO.userError s!"{label}: accepted, expected '{expected}'")
  | .error e => ensure (e == expected) s!"{label}: expected '{expected}', got {e}"

/-- Resumes `text` under `q`, which must give `expected`, the state `recover` gives. --/
def resumedAs (label : String) (q : Definition) (text : String) (expected : State) : IO Unit :=
  match Suimon.Trace.resume Suimon.Trace.wireCodec Codec.load q text with
  | .ok s => ensure (s == expected && (Suimon.Trace.recover Suimon.Trace.wireCodec Codec.load text).toOption == some s)
      s!"{label}: resumed from another state"
  | .error e => throw (IO.userError s!"{label}: not resumed: {e}")

def resumeRejected (label expected : String) (q : Definition) (text : String) : IO Unit :=
  match Suimon.Trace.resume Suimon.Trace.wireCodec Codec.load q text with
  | .ok _ => throw (IO.userError s!"{label}: resumed, expected '{expected}'")
  | .error e => ensure (e == expected) s!"{label}: expected '{expected}', got {e}"

/-- `p` with the policy of placement `placement` of workflow `workflow` changed by `f`. --/
def withPolicy (workflow placement : String) (f : Policy → Policy) (p : Definition) : Definition :=
  { p with workflows := p.workflows.map fun w =>
      if w.id == workflow then
        { w with placements := w.placements.map fun pl =>
            if pl.name == placement then { pl with policy := f pl.policy } else pl }
      else w }

def flipPolicy : Policy → Policy
  | .stop => .«continue»
  | .«continue» => .stop

/-- Checks a record of `p` whose lines after the header are `text`. --/
def checked (label : String) (p : Definition) (text : String) : IO Suimon.Trace.Checked :=
  checkedText label (header p ++ text)

def rejectedTrace (label fragment : String) (p : Definition) (text : String) : IO Unit :=
  rejectedText label fragment (header p ++ text)

def rejectedSteps (label fragment : String) (p : Definition) (steps : List (Op × List (Value × String))) :
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

/-- The longest line in bytes, the header aside, of the record of a walk of `p` without failures or
    cancellation, which runs every level of a chain `depth` runs deep and succeeds. The record is the
    one `suimon gen` writes for the walk. --/
def longestLine (label : String) (p : Definition) (depth : Nat) : IO Nat := do
  accepted label p
  let (final, ops) := Explore.walk p { failures := false, cancel := false } 1 100000
  ensure (final.status == .succeeded && final.runs.any (·.path.length == depth))
    s!"{label}: the walk did not run all {depth} levels"
  let mut s : State := {}
  let mut steps := #[]
  for o in ops do
    let next ← IO.ofExcept (step p s o)
    steps := steps.push (o, withPayloads s next)
    s := next
  let (_, records) ← IO.ofExcept (Suimon.Trace.record p {} steps.toList [] 1)
  return (records.map fun r => (Suimon.Trace.wireCodec.encode r).utf8ByteSize).foldl max 0

def run : IO Unit := do
  for name in ["users", "branch", "merge"] do
    let p ← load name
    let headerLine := Suimon.Trace.wireCodec.encodeHeader (Codec.definitionWire p)
    -- The header reads back to the definition, on one line.
    let loaded := match Suimon.Trace.wireCodec.decodeHeader headerLine >>= Codec.load with
      | .ok q => q == p
      | .error _ => false
    ensure (!headerLine.contains '\n' && loaded) s!"{name}: header codec"
    -- Another definition, which differs from `p` by the policy of one placement.
    let other := match (p.workflow? p.main).bind (·.placements.head?) with
      | some pl => withPolicy p.main pl.name flipPolicy p
      | none => p
    ensure ((Codec.definitionWire other).render != (Codec.definitionWire p).render) s!"{name}: no other definition"
    for seed in List.range 20 do
      let label := s!"{name} seed {seed + 1}"
      let r ← recorded p (seed + 1)
      -- Replaying a whole record reproduces the state of the run that wrote it, with its definition.
      let whole ← checkedText label r.text
      ensure (whole.state == r.states.getLast! && whole.committed + 1 == r.states.length && !whole.uncommitted)
        s!"{label}: replay differs from the run"
      ensure (whole.definition == some p) s!"{label}: another definition"
      ensure (whole.state.values.all fun v => whole.values.any (·.1 == v)) s!"{label}: a value without payload"
      -- Encoding and decoding do not change a record, and an encoded record is one line.
      for record in r.records do
        ensure (decodesTo (Suimon.Trace.recordOfWire (Suimon.Trace.recordWire record)) record)
          s!"{label}: wire codec changed {repr record}"
        let line := Suimon.Trace.wireCodec.encode record
        ensure (decodesTo (Suimon.Trace.wireCodec.decode line) record) s!"{label}: text codec changed {line}"
        ensure (!line.contains '\n') s!"{label}: a newline in {line}"
      -- A commit needs the payload of each value its transition introduces, lists the engine builds
      -- included, and an op record carries payloads only for the values its transition introduces:
      -- neither an earlier record nor a later one may hold it. The header is line 1.
      if let some ((o, values), i) := r.steps.zipIdx.find? (·.1.2.any (isList ·.1)) then
        let lists := values.filter (isList ·.1)
        let stripped := r.steps.set i (o, values.filter (!isList ·.1))
        rejectedTrace s!"{label} list payload" s!"line {2 * i + 3}: missing payloads" p (written stripped)
        rejectedSteps s!"{label} recorder list payload" "missing payloads" p stripped
        let early := stripped.modify 0 fun (first, payloads) => (first, payloads ++ lists)
        let extra := s!"payloads for {lists.map (·.1)}, which the transition does not introduce"
        rejectedTrace s!"{label} early payload" s!"line 3: {extra}" p (written early)
        rejectedSteps s!"{label} recorder early payload" extra p early
        let later := stripped.modify (i + 1) fun (next, payloads) => (next, payloads ++ lists)
        rejectedTrace s!"{label} later payload" s!"line {2 * i + 3}: missing payloads" p (written later)
      -- A crash may cut the record anywhere, the header included; recovery keeps exactly the
      -- committed transitions, and knows the definition once the header is complete.
      let lines := headerLine :: r.records.map Suimon.Trace.wireCodec.encode
      for cut in List.range (lines.length + 1) do
        let prefixText := String.join ((lines.take cut).map (· ++ "\n"))
        let half := match lines[cut]? with
          | some line => (line.take (line.length / 2)).toString
          | none => ""
        let committed := (cut - 1) / 2
        for torn in [prefixText, prefixText ++ half] do
          let c ← checkedText s!"{label} cut {cut}" torn
          ensure (c.committed == committed && c.state == r.states[committed]!)
            s!"{label} cut {cut}: wrong recovered state"
          ensure (c.definition == if cut == 0 then none else some p) s!"{label} cut {cut}: definition"
          ensure (c.uncommitted == ((cut > 0 && (cut - 1) % 2 == 1) || torn.length > prefixText.length))
            s!"{label} cut {cut}: uncommitted flag"
          ensure ((Suimon.Trace.recover Suimon.Trace.wireCodec Codec.load torn).toOption == some r.states[committed]!)
            s!"{label} cut {cut}: recover"
          -- The definition of the record resumes it from the recovered state once the header is
          -- complete; another definition never does.
          if cut == 0 then
            resumeRejected s!"{label} cut {cut} resume" "the record has no header" p torn
            resumeRejected s!"{label} cut {cut} resume other" "the record has no header" other torn
          else
            resumedAs s!"{label} cut {cut} resume" p torn r.states[committed]!
            resumeRejected s!"{label} cut {cut} resume other" "line 1: the record holds another definition" other
              torn
      -- Corruption before the last commit is an error, not a torn tail.
      if lines.length ≥ 5 then
        let corrupt := String.join ((lines.set 2 "{\"seq\":2").map (· ++ "\n"))
        rejectedText s!"{label} corrupt" "line 3" corrupt
        let swapped := (lines.take 1) ++ (lines.drop 1 |>.take 2).reverse ++ lines.drop 3
        let reordered := String.join (swapped.map (· ++ "\n"))
        rejectedText s!"{label} reordered" "line 2: expected sequence 1" reordered
  -- Fields have a fixed order, and empty values are left out.
  ensure (Suimon.Trace.wireCodec.encode (.op 1 (.start (some "v")) [("v", "payload")]) ==
    "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"v\"},\"values\":{\"v\":\"payload\"}}") "op record text"
  ensure (Suimon.Trace.wireCodec.encode (.commit 2) == "{\"seq\":2,\"commit\":true}") "commit record text"
  ensure (Suimon.Trace.wireCodec.encodeHeader (.obj []) == "{\"definition\":{}}") "header text"
  ensure (keys (Suimon.Trace.recordWire (.op 1 (.start (some "v")) [("v", "payload")])) == ["seq", "op", "values"])
    "op record fields"
  ensure (keys (Suimon.Trace.recordWire (.op 1 (.start none) [])) == ["seq", "op"]) "empty values"
  ensure (keys (Suimon.Trace.recordWire (.commit 2)) == ["seq", "commit"]) "commit record fields"
  ensure (keys (Suimon.Trace.opWire (.invoke [] "a" none)) == ["type", "run", "placement"]) "absent trigger"
  let p ← load "merge"
  ensure (keys (Codec.definitionWire p) == ["main", "functions", "judges", "transforms", "workflows"])
    "definition fields"
  let start := "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
  rejectedTrace "commit twice" "a commit without an op" p (start ++ "{\"seq\":3,\"commit\":true}\n")
  let again := (start.replace "\"seq\":1" "\"seq\":3").replace "\"seq\":2" "\"seq\":4"
  rejectedTrace "rejected op" "line 5: rejected" p (start ++ again)
  rejectedTrace "op twice" "an op before the previous commit" p
    "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"op\":{\"type\":\"cancel\"}}\n"
  rejectedTrace "unknown op field" "unknown field trigger" p "{\"seq\":1,\"op\":{\"type\":\"start\",\"trigger\":\"x\"}}\n"
  rejectedTrace "unknown record field" "unknown field extra" p "{\"seq\":1,\"op\":{\"type\":\"start\"},\"extra\":1}\n"
  rejectedTrace "op and commit" "either an op or a commit" p "{\"seq\":1,\"op\":{\"type\":\"start\"},\"commit\":true}\n"
  rejectedTrace "unknown op" "unknown op type" p "{\"seq\":1,\"op\":{\"type\":\"retry\"}}\n"
  rejectedTrace "empty line" "line 2" p "\n"
  let torn ← checked "torn start" p "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"com"
  ensure (torn.committed == 0 && torn.uncommitted && torn.state == {}) "torn start"
  -- The header comes first and only there, and its definition must load.
  let headerOnly ← checkedText "header only" (header p)
  ensure (headerOnly.definition == some p && headerOnly.committed == 0 && !headerOnly.uncommitted &&
    headerOnly.state == {}) "header only"
  let tornHeader ← checkedText "torn header" ((header p).take 30).toString
  ensure (tornHeader.definition == none && tornHeader.committed == 0 && tornHeader.uncommitted &&
    tornHeader.state == {}) "torn header"
  let empty ← checkedText "empty" ""
  ensure (empty.definition == none && empty.committed == 0 && !empty.uncommitted) "empty"
  -- A record resumes only under a definition of the canonical form of the one its header holds, and
  -- from the state recover gives, which is the initial state while no transition is committed; a
  -- record without a complete header does not resume, and a definition that differs by one policy
  -- resumes no record of this one.
  let merged ← recorded p 1
  resumedAs "resume" p merged.text merged.states.getLast!
  resumedAs "resume header only" p (header p) {}
  resumedAs "resume torn start" p (header p ++ "{\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"com") {}
  resumeRejected "resume empty" "the record has no header" p ""
  resumeRejected "resume torn header" "the record has no header" p ((header p).take 30).toString
  resumeRejected "resume undecodable definition" "line 1: definition: missing field main" p "{\"definition\":{}}\n"
  let other := withPolicy "dashboard" "archive" (fun _ => .stop) p
  ensure ((Codec.definitionWire other).render != (Codec.definitionWire p).render) "the definitions are the same"
  for (label, text) in [("another definition", merged.text),
      ("cut inside a line", (merged.text.take (merged.text.length - 5)).toString),
      ("only the start", header p ++ start), ("only the header", header p)] do
    resumeRejected s!"resume {label}" "line 1: the record holds another definition" other text
  -- The same definition in another form is the same definition: the header is compared in its
  -- canonical form, whatever the white space and the fields the form leaves out.
  let file ← IO.FS.readFile "Test/definitions/merge.json"
  let reformatted := "{ \"definition\" : " ++ file.replace "\n" " " ++ " }\n"
  ensure (reformatted != header p) "the header was not reformatted"
  resumedAs "resume reformatted" p (reformatted ++ (merged.text.drop (header p).length).toString)
    merged.states.getLast!
  rejectedText "no header" "line 1: header: unknown field seq" start
  rejectedText "empty first line" "line 1: unexpected end of input" "\n"
  rejectedText "header not an object" "line 1: header: expected an object" "[]\n"
  rejectedText "header without definition" "line 1: header: missing field definition" "{}\n"
  rejectedText "unknown header field" "line 1: header: unknown field seq" "{\"definition\":{},\"seq\":0}\n"
  rejectedText "undecodable definition" "line 1: definition: missing field main" "{\"definition\":{}}\n"
  match Suimon.Trace.check Suimon.Trace.wireCodec Codec.load "{\"definition\":{\"main\":\"w\",\"workflows\":[]}}\n" with
  | .ok _ => throw (IO.userError "invalid definition: accepted")
  | .error e => ensure (e == "line 1: unknown main workflow w") s!"invalid definition: {e}"
  rejectedTrace "header twice" "line 2: record: missing field seq" p (header p)
  rejectedTrace "header after records" "line 4: record: missing field seq" p (start ++ header p)
  let users ← load "users"
  let startInput := "{\"seq\":1,\"op\":{\"type\":\"start\",\"input\":\"t\"}"
  let commit := "{\"seq\":2,\"commit\":true}\n"
  -- Payloads are checked when the transition commits, so an op without its commit needs none.
  rejectedTrace "missing payload" "line 3: missing payloads for [t]" users (startInput ++ "}\n" ++ commit)
  let uncommitted ← checked "uncommitted without payload" users (startInput ++ "}\n")
  ensure (uncommitted.committed == 0 && uncommitted.uncommitted) "uncommitted without payload"
  rejectedTrace "payload not a string" "expected a string" users (startInput ++ ",\"values\":{\"t\":1}}\n")
  let withPayload ← checked "payload" users (startInput ++ ",\"values\":{\"t\":\"x\"}}\n" ++ commit)
  ensure (withPayload.committed == 1 && !withPayload.uncommitted && withPayload.values == [("t", "x")]) "payload"
  -- No object of a line may repeat a key, at any depth, the header's definition included; the error is
  -- right after the repeated key. The recorder writes no repeated payload key.
  rejectedTrace "repeated record key" "line 2: duplicate key \"seq\" at offset 14" p
    "{\"seq\":1,\"seq\":1,\"op\":{\"type\":\"start\"}}\n{\"seq\":2,\"commit\":true}\n"
  rejectedTrace "repeated op key" "line 2: duplicate key \"type\" at offset 36" p
    "{\"seq\":1,\"op\":{\"type\":\"start\",\"type\":\"cancel\"}}\n{\"seq\":2,\"commit\":true}\n"
  rejectedTrace "repeated payload key" "line 2: duplicate key \"t\" at offset 64" users
    (startInput ++ ",\"values\":{\"t\":\"x\",\"t\":\"y\"}}\n" ++ commit)
  rejectedText "repeated header key" "line 1: duplicate key \"definition\" at offset 29"
    "{\"definition\":{},\"definition\":{}}\n"
  rejectedText "repeated definition key" "line 1: duplicate key \"main\" at offset 32"
    "{\"definition\":{\"main\":\"x\",\"main\":\"w\",\"workflows\":[]}}\n"
  rejectedSteps "recorder repeated payload" "duplicate payloads for [t]" users
    [(.start (some "t"), [("t", "x"), ("t", "y")])]
  -- An op record carries payloads only for values its transition introduces, so a committed payload is
  -- never given again, the same or another, and the state names no value it has no payload for.
  let invoke := "{\"seq\":3,\"op\":{\"type\":\"invoke\",\"run\":[],\"placement\":\"fetchAllUsers\"}"
  for payload in ["x", "y"] do
    rejectedExactly s!"known payload {payload}" "line 5: payloads for [t], which the transition does not introduce"
      (header users ++ startInput ++ ",\"values\":{\"t\":\"x\"}}\n" ++ commit ++ invoke ++
        s!",\"values\":\{\"t\":\"{payload}\"}}\n" ++ "{\"seq\":4,\"commit\":true}\n")
  rejectedExactly "stray payloads" "line 3: payloads for [z, y], which the transition does not introduce"
    (header users ++ startInput ++ ",\"values\":{\"z\":\"w\",\"t\":\"x\",\"y\":\"v\"}}\n" ++ commit)
  rejectedSteps "recorder stray payload" "payloads for [z], which the transition does not introduce" users
    [(.start (some "t"), [("t", "x"), ("z", "w")])]
  rejectedSteps "recorder known payload" "payloads for [t], which the transition does not introduce" users
    [(.start (some "t"), [("t", "before")]), (.invoke [] "fetchAllUsers" none, [("t", "after")])]
  ensure (Suimon.Trace.duplicates ["a", "b", "a", "c", "b", "a"] == ["a", "b"]) "duplicates"
  -- A record replays against the definition of its header: users records are rejected under merge.
  rejectedText "another definition" "line 3: rejected"
    (header p ++ startInput ++ ",\"values\":{\"t\":\"x\"}}\n" ++ commit)
  -- The recorder refuses a transition without the payloads it introduces, and an op the rules reject.
  rejectedSteps "recorder missing payload" "missing payloads" users [(.start (some "t"), [])]
  rejectedSteps "recorder rejected op" "ALREADY_STARTED" p [(.start none, []), (.start none, [])]
  -- Identities grow linearly with the nesting of runs: a run path holds one label per level, and an
  -- identity holds its run path once. Each chain nests 16 runs, sub-workflow calls or concurrency tasks
  -- and sub-workflow calls in turn, and each level starts from the result of a call; started at w8, it
  -- nests 8. Doubling the depth at most doubles the longest line, give or take the parts every line
  -- has, and keeps it under 8 KiB; identities that embed their run path at every level grow
  -- exponentially instead.
  for name in ["nested", "alternating"] do
    let deep ← load s!"chains/{name}"
    let longest16 ← longestLine s!"{name} 16" deep 16
    let longest8 ← longestLine s!"{name} 8" { deep with main := "w8" } 8
    ensure (2 * longest16 ≤ 5 * longest8 && longest16 ≤ 8192)
      s!"{name}: the longest line has {longest16} bytes at depth 16 and {longest8} at depth 8"
  IO.println "trace: ok"

end Suimon.Test.Trace
