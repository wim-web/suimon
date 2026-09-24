import Suimon.Step
import Suimon.WireText
import Suimon.Json

namespace Suimon.Trace

/-! An execution record is a sequence of lines. The first line is the header, which holds the
    definition of the execution. Each accepted transition is then one `op` record followed by one
    `commit` record; only committed transitions are part of the record (§12.1). A record is first
    written as a `Wire` value, and a `Codec` turns it into one line of text. -/

/-- Values the transition from `before` to `after` introduces: those `after` mentions and `before`
    does not, each once. This includes lists the engine builds. Their payloads are stored by the
    commit of the transition, so a recovered state never names a lost value (§12.1). --/
def introduced (before after : State) : List Value :=
  (after.values.filter fun v => !before.values.contains v).eraseDups

/-- Payloads of an op record for values its transition does not introduce. An op record may carry a
    payload only for a value its transition introduces, which the state before does not mention, so a
    committed payload is never repeated or contradicted by a later one (§12.1). --/
def unexpected (before after : State) (values : List (Value × String)) : List Value :=
  (values.map (·.1)).filter fun v => !(introduced before after).contains v

inductive Record where
  /-- `values` maps the identities of values the transition introduces to the payloads the runtime
      serialized. --/
  | op (seq : Nat) (op : Op) (values : List (Value × String))
  | commit (seq : Nat)
  deriving DecidableEq, Repr

def Record.seq : Record → Nat
  | .op seq .. | .commit seq => seq

/-- The payloads of an op record have distinct keys. A line may not repeat a key in any object
    (`Wire.parse`), so only such records read back, and the recorder writes no other
    (`transaction`). --/
def Record.DistinctKeys : Record → Prop
  | .op _ _ values => (values.map (·.1)).Nodup
  | .commit _ => True

/-! ## Wire form -/

def pathWire (path : Path) : Wire := .arr (path.map .str)

/-- An optional field is left out when it is absent. --/
def optional (key : String) : Option Wire → List (String × Wire)
  | some value => [(key, value)]
  | none => []

def opWire : Op → Wire
  | .start input => .obj ([("type", .str "start")] ++ optional "input" (input.map .str))
  | .invoke run placement trigger => .obj ([("type", .str "invoke"), ("run", pathWire run),
      ("placement", .str placement)] ++ optional "trigger" (trigger.map .str))
  | .fetch call => .obj [("type", .str "fetch"), ("call", .str call)]
  | .returned call value => .obj [("type", .str "returned"), ("call", .str call), ("value", .str value)]
  | .judged call arm => .obj [("type", .str "judged"), ("call", .str call), ("arm", .str arm)]
  | .yielded call value => .obj [("type", .str "yielded"), ("call", .str call), ("value", .str value)]
  | .ended call => .obj [("type", .str "ended"), ("call", .str call)]
  | .failed call => .obj [("type", .str "failed"), ("call", .str call)]
  | .timedOut call element => .obj [("type", .str "timedOut"), ("call", .str call),
      ("element", .bool element)]
  | .lost call => .obj [("type", .str "lost"), ("call", .str call)]
  | .terminated call => .obj [("type", .str "terminated"), ("call", .str call)]
  | .deliver run connection source value => .obj ([("type", .str "deliver"), ("run", pathWire run),
      ("connection", .nat connection), ("source", .str source)] ++ optional "value" (value.map .str))
  | .transformFailed run connection source => .obj [("type", .str "transformFailed"),
      ("run", pathWire run), ("connection", .nat connection), ("source", .str source)]
  | .taskInput execution task value => .obj ([("type", .str "taskInput"), ("execution", .str execution),
      ("task", .str task)] ++ optional "value" (value.map .str))
  | .taskInputFailed execution task => .obj [("type", .str "taskInputFailed"),
      ("execution", .str execution), ("task", .str task)]
  | .beginTask execution task => .obj [("type", .str "beginTask"), ("execution", .str execution),
      ("task", .str task)]
  | .taskOutput execution task index value => .obj [("type", .str "taskOutput"),
      ("execution", .str execution), ("task", .str task), ("index", .nat index), ("value", .str value)]
  | .taskOutputFailed execution task index => .obj [("type", .str "taskOutputFailed"),
      ("execution", .str execution), ("task", .str task), ("index", .nat index)]
  | .settle run placement => .obj [("type", .str "settle"), ("run", pathWire run),
      ("placement", .str placement)]
  | .closeExecution execution => .obj [("type", .str "closeExecution"), ("execution", .str execution)]
  | .closeRun run => .obj [("type", .str "closeRun"), ("run", pathWire run)]
  | .cancel => .obj [("type", .str "cancel")]
  | .conclude => .obj [("type", .str "conclude")]

def valuesWire (values : List (Value × String)) : Wire :=
  .obj (values.map fun (value, payload) => (value, .str payload))

/-- Fields keep a fixed order: `seq, op, values` and `seq, commit`. --/
def recordWire : Record → Wire
  | .op seq o values => .obj ([("seq", .nat seq), ("op", opWire o)] ++
      optional "values" (if values.isEmpty then none else some (valuesWire values)))
  | .commit seq => .obj [("seq", .nat seq), ("commit", .bool true)]

/-! Decoding looks fields up by name. The text form rejects a repeated key, so a name has at most one
    field. -/

abbrev Fields := List (String × Wire)

/-- Unknown keys are rejected, so a misspelled optional field is not silently ignored. --/
def strict (fields : Fields) (allowed : List String) (at_ : String) : Except String Unit :=
  match fields.find? fun field => !allowed.contains field.1 with
  | some (key, _) => throw s!"{at_}: unknown field {key}"
  | none => pure ()

def getText (fields : Fields) (key at_ : String) : Except String String :=
  match fields.lookup key with
  | some (.str text) => pure text
  | some _ => throw s!"{at_}.{key}: expected a string"
  | none => throw s!"{at_}: missing field {key}"

/-- An absent key is the only way to omit an optional field; `null` is rejected. --/
def getText? (fields : Fields) (key at_ : String) : Except String (Option String) :=
  match fields.lookup key with
  | some (.str text) => pure (some text)
  | some _ => throw s!"{at_}.{key}: expected a string"
  | none => pure none

def getNat (fields : Fields) (key at_ : String) : Except String Nat :=
  match fields.lookup key with
  | some (.nat n) => pure n
  | some _ => throw s!"{at_}.{key}: expected a natural number"
  | none => throw s!"{at_}: missing field {key}"

def getBool (fields : Fields) (key at_ : String) : Except String Bool :=
  match fields.lookup key with
  | some (.bool b) => pure b
  | some _ => throw s!"{at_}.{key}: expected a boolean"
  | none => throw s!"{at_}: missing field {key}"

def strings (at_ : String) : List Wire → Except String (List String)
  | [] => pure []
  | .str text :: rest => return text :: (← strings at_ rest)
  | _ :: _ => throw s!"{at_}: expected an array of strings"

def getPath (fields : Fields) (key at_ : String) : Except String Path :=
  match fields.lookup key with
  | some (.arr items) => strings s!"{at_}.{key}" items
  | some _ => throw s!"{at_}.{key}: expected an array of strings"
  | none => throw s!"{at_}: missing field {key}"

def opOfWire (wire : Wire) : Except String Op := do
  let .obj fields := wire | throw "op: expected an object"
  let at_ := "op"
  let kind ← getText fields "type" at_
  let keys := fun (names : List String) => strict fields ("type" :: names) s!"{at_} {kind}"
  match kind with
  | "start" => keys ["input"]; return .start (← getText? fields "input" at_)
  | "invoke" =>
    keys ["run", "placement", "trigger"]
    return .invoke (← getPath fields "run" at_) (← getText fields "placement" at_)
      (← getText? fields "trigger" at_)
  | "fetch" => keys ["call"]; return .fetch (← getText fields "call" at_)
  | "returned" =>
    keys ["call", "value"]; return .returned (← getText fields "call" at_) (← getText fields "value" at_)
  | "judged" => keys ["call", "arm"]; return .judged (← getText fields "call" at_) (← getText fields "arm" at_)
  | "yielded" =>
    keys ["call", "value"]; return .yielded (← getText fields "call" at_) (← getText fields "value" at_)
  | "ended" => keys ["call"]; return .ended (← getText fields "call" at_)
  | "failed" => keys ["call"]; return .failed (← getText fields "call" at_)
  | "timedOut" =>
    keys ["call", "element"]; return .timedOut (← getText fields "call" at_) (← getBool fields "element" at_)
  | "lost" => keys ["call"]; return .lost (← getText fields "call" at_)
  | "terminated" => keys ["call"]; return .terminated (← getText fields "call" at_)
  | "deliver" =>
    keys ["run", "connection", "source", "value"]
    return .deliver (← getPath fields "run" at_) (← getNat fields "connection" at_)
      (← getText fields "source" at_) (← getText? fields "value" at_)
  | "transformFailed" =>
    keys ["run", "connection", "source"]
    return .transformFailed (← getPath fields "run" at_) (← getNat fields "connection" at_)
      (← getText fields "source" at_)
  | "taskInput" =>
    keys ["execution", "task", "value"]
    return .taskInput (← getText fields "execution" at_) (← getText fields "task" at_)
      (← getText? fields "value" at_)
  | "taskInputFailed" =>
    keys ["execution", "task"]
    return .taskInputFailed (← getText fields "execution" at_) (← getText fields "task" at_)
  | "beginTask" =>
    keys ["execution", "task"]
    return .beginTask (← getText fields "execution" at_) (← getText fields "task" at_)
  | "taskOutput" =>
    keys ["execution", "task", "index", "value"]
    return .taskOutput (← getText fields "execution" at_) (← getText fields "task" at_)
      (← getNat fields "index" at_) (← getText fields "value" at_)
  | "taskOutputFailed" =>
    keys ["execution", "task", "index"]
    return .taskOutputFailed (← getText fields "execution" at_) (← getText fields "task" at_)
      (← getNat fields "index" at_)
  | "settle" =>
    keys ["run", "placement"]; return .settle (← getPath fields "run" at_) (← getText fields "placement" at_)
  | "closeExecution" => keys ["execution"]; return .closeExecution (← getText fields "execution" at_)
  | "closeRun" => keys ["run"]; return .closeRun (← getPath fields "run" at_)
  | "cancel" => keys []; return .cancel
  | "conclude" => keys []; return .conclude
  | other => throw s!"unknown op type {other}"

def payloads : Fields → Except String (List (Value × String))
  | [] => pure []
  | (value, .str payload) :: rest => return (value, payload) :: (← payloads rest)
  | (value, _) :: _ => throw s!"record.values.{value}: expected a string"

def recordOfWire (wire : Wire) : Except String Record := do
  let .obj fields := wire | throw "record: expected an object"
  let seq ← getNat fields "seq" "record"
  match fields.lookup "commit", fields.lookup "op" with
  | some (.bool true), none =>
    strict fields ["seq", "commit"] "record"
    return .commit seq
  | none, some o =>
    strict fields ["seq", "op", "values"] "record"
    let values ← match fields.lookup "values" with
      | none => pure []
      | some (.obj entries) => payloads entries
      | some _ => throw "record.values: expected an object"
    return .op seq (← opOfWire o) values
  | _, _ => throw "record: either an op or a commit"

/-! The header holds the definition of the execution, which a recorder writes in the canonical form
    of the definition file (`Codec.definitionWire`). It has no sequence number, so no other line reads
    as a header, and it reads as no other line. -/

def headerWire (definition : Wire) : Wire := .obj [("definition", definition)]

def headerOfWire (wire : Wire) : Except String Wire := do
  let .obj fields := wire | throw "header: expected an object"
  strict fields ["definition"] "header"
  match fields.lookup "definition" with
  | some definition => pure definition
  | none => throw "header: missing field definition"

/-! ## Text form -/

/-- A text form of the header and the records, one line each. Recovery needs only that decoding
    inverts encoding, for the lines a recorder writes, and that an encoded line contains no newline
    (`Codec.Lawful`). --/
structure Codec where
  encode : Record → String
  decode : String → Except String Record
  /-- The header holds a definition as a `Wire` value; `check` leaves reading it to its caller. --/
  encodeHeader : Wire → String
  decodeHeader : String → Except String Wire

/-- Decoding inverts encoding for the records and headers without repeated keys, which are all a
    recorder writes (`transaction`, `Codec.definitionWire_distinctKeys`), and a line has no newline. --/
structure Codec.Lawful (c : Codec) : Prop where
  decode_encode : ∀ r, r.DistinctKeys → c.decode (c.encode r) = .ok r
  newline_not_mem_encode : ∀ r, '\n' ∉ (c.encode r).toList
  decodeHeader_encodeHeader : ∀ w, w.DistinctKeys → c.decodeHeader (c.encodeHeader w) = .ok w
  newline_not_mem_encodeHeader : ∀ w, '\n' ∉ (c.encodeHeader w).toList

/-- A codec from a text form of `Wire` values. --/
def Codec.ofWire (render : Wire → String) (parse : String → Except String Wire) : Codec where
  encode r := render (recordWire r)
  decode line := parse line >>= recordOfWire
  encodeHeader w := render (headerWire w)
  decodeHeader line := parse line >>= headerOfWire

/-- The text form of the header and the records: compact JSON with the fields in the order
    `headerWire` and `recordWire` give them, one per line (`wireCodec_lawful`). --/
def wireCodec : Codec := .ofWire Wire.render Wire.parse

/-! ## Replay -/

/-- The complete lines of a text, each without its newline, and the text after the last newline.
    `current` holds the line read so far, reversed. --/
def splitLines : List Char → List Char → List (List Char) × List Char
  | [], current => ([], current.reverse)
  | c :: rest, current =>
    if c = '\n' then
      let after := splitLines rest []
      (current.reverse :: after.1, after.2)
    else splitLines rest (c :: current)

structure Checked where
  /-- The definition of the header, which the record replays against; `none` while the record has
      no complete line. --/
  definition : Option Definition
  state : State
  /-- The number of committed transitions. --/
  committed : Nat
  /-- An operation or a partial line after the last commit, which recovery discards. --/
  uncommitted : Bool
  /-- The payloads of the committed transitions. --/
  values : List (Value × String)

/-- What the complete lines read so far establish. --/
structure Replay where
  state : State := {}
  committed : Nat := 0
  values : List (Value × String) := []
  /-- The op read since the last commit. --/
  pending : Option (Op × List (Value × String)) := none
  /-- The sequence number the next record must carry. --/
  next : Nat := 1

/-- Values the transition from `before` to `after` introduces whose payloads are neither in the op
    record (`values`) nor in an earlier committed record (`known`). --/
def missing (before after : State) (values known : List (Value × String)) : List Value :=
  (introduced before after).filter fun v => !(values.any (·.1 == v) || known.any (·.1 == v))

/-- Replay one complete line; the op of a transition is applied at its commit, which also checks
    the payloads: the op record carries payloads only for values the transition introduces, and each
    of them has one. --/
def replayLine (c : Codec) (p : Definition) (r : Replay) (index : Nat) (line : String) :
    Except String Replay :=
  let at_ := s!"line {index + 1}"
  match c.decode line with
  | .error e => throw s!"{at_}: {e}"
  | .ok record =>
    if record.seq ≠ r.next then throw s!"{at_}: expected sequence {r.next}, got {record.seq}"
    else match record, r.pending with
      | .op _ o values, none => pure { r with pending := some (o, values), next := r.next + 1 }
      | .commit _, some (o, values) =>
        match step p r.state o with
        | .ok next =>
          let extra := unexpected r.state next values
          let absent := missing r.state next values r.values
          if !extra.isEmpty then throw s!"{at_}: payloads for {extra}, which the transition does not introduce"
          else if absent.isEmpty then
            pure { state := next, committed := r.committed + 1, values := r.values ++ values,
                   pending := none, next := r.next + 1 }
          else throw s!"{at_}: missing payloads for {absent}"
        | .error e => throw s!"{at_}: rejected {(opWire o).render}: {e}"
      | .op .., some _ => throw s!"{at_}: an op before the previous commit"
      | .commit _, none => throw s!"{at_}: a commit without an op"

def replayLines (c : Codec) (p : Definition) : Replay → Nat → List (List Char) → Except String Replay
  | r, _, [] => pure r
  | r, index, line :: rest => do
    replayLines c p (← replayLine c p r index (String.ofList line)) (index + 1) rest

/-- Replay the committed transitions of a record. `load` reads the definition of the header, the first
    line, and the other lines replay against it; line numbers count the header. A crash may leave an
    op without its commit, and a partial last line, which may be the header; both are reported as
    uncommitted and ignored. --/
def check (c : Codec) (load : Wire → Except String Definition) (text : String) : Except String Checked := do
  let split := splitLines text.toList []
  match split.1 with
  | [] => return { definition := none, state := {}, committed := 0, uncommitted := !split.2.isEmpty, values := [] }
  | header :: lines =>
    let p ← (c.decodeHeader (String.ofList header) >>= load).mapError (s!"line 1: {·}")
    let r ← replayLines c p {} 1 lines
    return { definition := some p, state := r.state, committed := r.committed,
             uncommitted := r.pending.isSome || !split.2.isEmpty, values := r.values }

/-- The state a crashed run resumes from (§12.1). --/
def recover (c : Codec) (load : Wire → Except String Definition) (text : String) : Except String State :=
  (check c load text).map (·.state)

/-! ## Resumption -/

/-- Reads the definition of a header with `load`, and accepts it only when it has the canonical form
    of `p` (`Codec.definitionWire`). --/
def agreeing (load : Wire → Except String Definition) (p : Definition) (w : Wire) :
    Except String Definition := do
  let q ← load w
  unless (Codec.definitionWire q).render == (Codec.definitionWire p).render do
    throw "the record holds another definition"
  return q

/-- The state from which the definition `p` resumes a crashed run (§12.1): only a record whose header
    holds a definition with the canonical form of `p` resumes, from the state `recover` gives, and a
    record without a complete header does not. The implementations of user processes are not part
    of the definition, so they are not compared (§14). --/
def resume (c : Codec) (load : Wire → Except String Definition) (p : Definition) (text : String) :
    Except String State := do
  let checked ← check c (agreeing load p) text
  match checked.definition with
  | some _ => return checked.state
  | none => throw "the record has no header"

/-! ## Recording -/

/-- The keys that occur more than once, each once, in the order they first occur. --/
def duplicates (keys : List String) : List String :=
  (keys.filter fun k => keys.count k > 1).eraseDups

/-- The records of one accepted transition, starting at `seq`, under the rules `check` applies: the
    payloads of the op record have distinct keys and are only for values the transition introduces,
    and each value the transition introduces has its payload in the op record or in `known`, the
    payloads of the transitions recorded before. --/
def transaction (p : Definition) (s : State) (o : Op) (values known : List (Value × String)) (seq : Nat) :
    Except String (State × List Record) := do
  let keys := values.map (·.1)
  unless keys.Nodup do throw s!"duplicate payloads for {duplicates keys}"
  let next ← step p s o
  let extra := unexpected s next values
  unless extra.isEmpty do throw s!"payloads for {extra}, which the transition does not introduce"
  let absent := missing s next values known
  unless absent.isEmpty do throw s!"missing payloads for {absent}"
  return (next, [.op seq o values, .commit (seq + 1)])

/-- Consecutive transactions from sequence number `seq`, after transitions whose payloads are `known`. --/
def record (p : Definition) : State → List (Op × List (Value × String)) → List (Value × String) → Nat →
    Except String (State × List Record)
  | s, [], _, _ => pure (s, [])
  | s, (o, values) :: rest, known, seq => do
    let (next, records) ← transaction p s o values known seq
    let (final, later) ← record p next rest (known ++ values) (seq + 2)
    return (final, records ++ later)

def text (c : Codec) (rs : List Record) : String := String.join (rs.map (c.encode · ++ "\n"))

/-- The whole text a recorder writes: the header with the definition, then the records. --/
def recording (c : Codec) (header : Wire) (rs : List Record) : String :=
  c.encodeHeader header ++ "\n" ++ text c rs

end Suimon.Trace
