import Suimon.Validate
import Suimon.Wire

/-! A definition is read from Lean's `Json`, which the definition file and the header of an execution
    record give, and validated (`Codec.loadJson`, `Codec.load`). It is written as a `Wire` value,
    whose fields keep the order of the definition file (`Codec.definitionWire`); its `Json` is that
    value's. -/

namespace Suimon
open Lean

/-! ## Definition text

A definition file is read as Lean's `Json.parse` reads JSON text, except that an object may not
repeat a key, where `Json.parse` keeps the last field. The parser is `Lean.Json.Parser`'s, with one
check added to `objectCore`, and uses its lexers: text without a repeated key gives the same `Json`,
and any error the same message at the same offset. The one exception is a number whose exponent pads
its mantissa with more than 64 zeros: it keeps 64, because the exact power of ten can be
astronomically large (`1e1000000000`) and a non-zero mantissa exceeds `maxNat` either way. Keys are compared after their escapes are decoded,
and a repeated key fails right after its closing quote, as `duplicate key "k"` with the key quoted
by `String.quote`. -/

namespace Codec.Parser
open Std.Internal.Parsec Std.Internal.Parsec.String
open Lean.Json.Parser (str lookahead numWithDecimals natMaybeZero)

/-- `JsonNumber.shiftl`, padding the mantissa with at most 64 zeros. --/
def shiftl (n : JsonNumber) (s : Nat) : JsonNumber :=
  if n.mantissa = 0 then ⟨0, n.exponent - s⟩
  else ⟨n.mantissa * (10 ^ min (s - n.exponent) 64 : Nat), n.exponent - s⟩

/-- `Lean.Json.Parser.num`, with `shiftl` above. --/
def num : Parser JsonNumber := do
  let value ← numWithDecimals
  if ← isEof then
    return value
  else
    let c ← peek!
    if c == 'e' || c == 'E' then
      skip
      let c ← peek!
      if c == '-' then
        skip
        let n ← natMaybeZero
        return value.shiftr n
      else
        if c = '+' then skip
        let n ← natMaybeZero
        if n > USize.size then fail "exp too large"
        return shiftl value n
    else
      return value

mutual

partial def arrayCore (acc : Array Json) : Parser (Array Json) := do
  let hd ← anyCore
  let acc' := acc.push hd
  let c ← any
  if c == ']' then
    ws
    return acc'
  else if c == ',' then
    ws
    arrayCore acc'
  else
    fail "unexpected character in array"

partial def objectCore (kvs : Std.TreeMap.Raw String Json) : Parser (Std.TreeMap.Raw String Json) := do
  lookahead (fun c => c == '"') "\""; skip;
  let k ← str
  if kvs.contains k then fail s!"duplicate key {k.quote}"
  ws
  lookahead (fun c => c == ':') ":"; skip; ws
  let v ← anyCore
  let c ← any
  if c == '}' then
    ws
    return kvs.insert k v
  else if c == ',' then
    ws
    objectCore (kvs.insert k v)
  else
    fail "unexpected character in object"

partial def anyCore : Parser Json := do
  let c ← peek!
  if c == '[' then
    skip; ws
    let c ← peek!
    if c == ']' then
      skip; ws
      return Json.arr (Array.mkEmpty 0)
    else
      let a ← arrayCore (Array.mkEmpty 4)
      return Json.arr a
  else if c == '{' then
    skip; ws
    let c ← peek!
    if c == '}' then
      skip; ws
      return Json.obj ∅
    else
      let kvs ← objectCore ∅
      return Json.obj kvs
  else if c == '\"' then
    skip
    let s ← str
    ws
    return Json.str s
  else if c == 'f' then
    skipString "false"; ws
    return Json.bool false
  else if c == 't' then
    skipString "true"; ws
    return Json.bool true
  else if c == 'n' then
    skipString "null"; ws
    return Json.null
  else if c == '-' || ('0' <= c && c <= '9') then
    let n ← num
    ws
    return Json.num n
  else
    fail "unexpected input"

end

end Codec.Parser

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- Parses definition text like `Json.parse`, except that a key repeated in an object is an error. --/
def Codec.parse (text : String) : Except String Json :=
  Parser.run (do ws; let json ← Codec.Parser.anyCore; eof; return json) text

mutual

/-- The `Json` of a `Wire` value. An object keeps the last field of each key; a value read from a
    record repeats no key (`Wire.parse`), so none is lost. --/
def Wire.toJson : Wire → Json
  | .null => .null
  | .bool b => .bool b
  | .nat n => .num (.fromNat n)
  | .str s => .str s
  | .arr items => .arr (Wire.itemsToJson items).toArray
  | .obj fields => Json.mkObj (Wire.fieldsToJson fields)

def Wire.itemsToJson : List Wire → List Json
  | [] => []
  | w :: ws => w.toJson :: Wire.itemsToJson ws

def Wire.fieldsToJson : List (String × Wire) → List (String × Json)
  | [] => []
  | (k, v) :: fs => (k, v.toJson) :: Wire.fieldsToJson fs

end

namespace Codec

/-- Unknown keys are rejected, so a misspelled optional field is not silently ignored. --/
def strict (json : Json) (allowed : List String) (at_ : String) : Except String Unit := do
  let .obj fields := json | throw s!"{at_}: expected an object"
  for (key, _) in fields.toList do
    unless allowed.contains key do throw s!"{at_}: unknown field {key}"

/-- An absent key is the only way to omit an optional field; `null` is rejected by the field's parser. --/
def field? (json : Json) (key : String) : Option Json :=
  (json.getObjVal? key).toOption

def field (json : Json) (key : String) (at_ : String) : Except String Json :=
  match field? json key with
  | some value => pure value
  | none => throw s!"{at_}: missing field {key}"

def text (json : Json) (at_ : String) : Except String String :=
  match json with
  | .str value => if value.isEmpty then throw s!"{at_}: empty string" else pure value
  | _ => throw s!"{at_}: expected a string"

def textField (json : Json) (key : String) (at_ : String) : Except String String := do
  text (← field json key at_) s!"{at_}.{key}"

def textField? (json : Json) (key : String) (at_ : String) : Except String (Option String) :=
  (field? json key).mapM (text · s!"{at_}.{key}")

/-- The value of a number that is a natural number in any notation. The parser does not normalize
    numbers, so `2.0` and `20e-1` both have mantissa 20 and exponent 1. Stripping trailing zeros,
    rather than computing a power of ten, takes at most one step per digit of the mantissa whatever
    the exponent. --/
def nat? : Json → Option Nat
  | .num ⟨.ofNat m, e⟩ => if m = 0 then some 0 else strip m e
  | _ => none
where
  strip (m : Nat) : Nat → Option Nat
    | 0 => some m
    | e + 1 => if m % 10 = 0 then strip (m / 10) e else none

def natField? (json : Json) (key : String) (at_ : String) : Except String (Option Nat) :=
  (field? json key).mapM fun value => match nat? value with
    | some n => if n ≤ maxNat then pure n else throw s!"{at_}.{key}: must be at most {maxNat}"
    | none => throw s!"{at_}.{key}: expected a natural number"

def list (json : Json) (key : String) (at_ : String) : Except String (List Json) :=
  match field? json key with
  | none => pure []
  | some (.arr items) => pure items.toList
  | some _ => throw s!"{at_}.{key}: expected an array"

/-- The fields that are present, in order: an absent optional field is left out. --/
def obj (fields : List (String × Option Wire)) : Wire :=
  .obj (fields.filterMap fun (key, value) => value.map (key, ·))

theorem sizeOf_get?_lt_impl {k : String} {v : Json} :
    ∀ t : Std.DTreeMap.Internal.Impl String (fun _ => Json),
      (letI : Ord String := ⟨compare⟩; Std.DTreeMap.Internal.Impl.Const.get? t k) = some v → sizeOf v < sizeOf t
  | .leaf, h => by simp [Std.DTreeMap.Internal.Impl.Const.get?] at h
  | .inner _ _ _ l r, h => by
    simp only [Std.DTreeMap.Internal.Impl.Const.get?] at h
    simp only [Std.DTreeMap.Internal.Impl.inner.sizeOf_spec]
    split at h
    · have := sizeOf_get?_lt_impl l h; omega
    · have := sizeOf_get?_lt_impl r h; omega
    · cases h; omega

/-- The value an object holds for a key is smaller than the object, so decoding may recurse into it. --/
theorem sizeOf_get?_lt {fields : Std.TreeMap.Raw String Json} {k : String} {v : Json}
    (h : fields.get? k = some v) : sizeOf v < sizeOf (Json.obj fields) := by
  have := sizeOf_get?_lt_impl fields.inner.inner h
  rcases fields with ⟨⟨t⟩⟩
  simp only [Json.obj.sizeOf_spec, Std.TreeMap.Raw.mk.sizeOf_spec, Std.DTreeMap.Raw.mk.sizeOf_spec] at this ⊢
  omega

/-- A type: a name, or `{"list": type}`. The element of a list is looked up as `field` does, but in the
    object itself, whose values are smaller than it (`sizeOf_get?_lt`), so that the decoder is a total
    function that proofs can unfold. --/
def valueType (json : Json) (at_ : String) : Except String ValueType :=
  match json with
  | .str name => if name.isEmpty then throw s!"{at_}: empty type name" else pure (.named name)
  | .obj fields => do
    strict (.obj fields) ["list"] at_
    match _h : fields.get? "list" with
    | some element => return .list (← valueType element at_)
    | none => throw s!"{at_}: missing field list"
  | _ => throw s!"{at_}: a type is a name or \{\"list\": type}"
termination_by sizeOf json
decreasing_by exact sizeOf_get?_lt _h

def valueTypeWire : ValueType → Wire
  | .named name => .str name
  | .list element => .obj [("list", valueTypeWire element)]

def contract (json : Json) (at_ : String) : Except String Contract := do
  strict json ["single", "stream"] at_
  match field? json "single", field? json "stream" with
  | some value, none => return .single (← valueType value s!"{at_}.single")
  | none, some element => return .stream (← valueType element s!"{at_}.stream")
  | _, _ => throw s!"{at_}: an output contract is either single or stream"

def contractWire : Contract → Wire
  | .single value => .obj [("single", valueTypeWire value)]
  | .stream element => .obj [("stream", valueTypeWire element)]

def policy (json : Json) (at_ : String) : Except String Policy :=
  match json with
  | .str "stop" => pure .stop
  | .str "continue" => pure .«continue»
  | _ => throw s!"{at_}: policy is stop or continue"

def policyWire : Policy → Wire
  | .stop => .str "stop"
  | .«continue» => .str "continue"

def timeout (json : Json) (at_ : String) : Except String Timeout := do
  match field? json "timeout" with
  | none => pure {}
  | some value =>
    let at_ := s!"{at_}.timeout"
    strict value ["callMs", "elementMs"] at_
    return { callMs := ← natField? value "callMs" at_, elementMs := ← natField? value "elementMs" at_ }

def timeoutWire (t : Timeout) : Option Wire :=
  if t.isEmpty then none
  else some (obj [("callMs", t.callMs.map .nat), ("elementMs", t.elementMs.map .nat)])

def body (json : Json) (at_ : String) : Except String Body := do
  match ← textField json "type" at_ with
  | "function" =>
    strict json ["type", "function"] at_
    return .function (← textField json "function" at_)
  | "subworkflow" =>
    strict json ["type", "workflow", "output"] at_
    return .workflow (← textField json "workflow" at_) (← textField json "output" at_)
  | other => throw s!"{at_}: unknown body type {other}"

def bodyWire : Body → Wire
  | .function id => .obj [("type", .str "function"), ("function", .str id)]
  | .workflow id output => .obj [("type", .str "subworkflow"), ("workflow", .str id), ("output", .str output)]

def transformRef (id : String) : TransformRef :=
  if id == TransformRef.discardName then .discard else .declared id

def transformRefWire : TransformRef → Wire
  | .declared id => .str id
  | .discard => .str TransformRef.discardName

def task (json : Json) (at_ : String) : Except String TaskSpec := do
  strict json ["name", "body", "inputTransform", "outputTransform", "policy", "timeout"] at_
  let name ← textField json "name" at_
  let at_ := s!"{at_}.{name}"
  return {
    name
    body := ← body (← field json "body" at_) s!"{at_}.body"
    input := (← textField? json "inputTransform" at_).map transformRef
    output := ← textField? json "outputTransform" at_
    policy := ← policy (← field json "policy" at_) s!"{at_}.policy"
    timeout := ← timeout json at_ }

def taskWire (t : TaskSpec) : Wire :=
  obj [("name", some (.str t.name)), ("body", some (bodyWire t.body)),
    ("inputTransform", t.input.map transformRefWire), ("outputTransform", t.output.map .str),
    ("policy", some (policyWire t.policy)), ("timeout", timeoutWire t.timeout)]

def collect (json : Json) (at_ : String) : Except String Collect :=
  match json with
  | .str "list" => pure .list
  | .str "stream" => pure .stream
  | _ => throw s!"{at_}: output is list or stream"

def collectWire : Collect → Wire
  | .list => .str "list"
  | .stream => .str "stream"

def control (json : Json) (at_ : String) : Except String Control := do
  match ← textField json "type" at_ with
  | "function" | "subworkflow" => return .call (← body json at_)
  | "branch" =>
    strict json ["type", "judge", "arms"] at_
    let arms ← (← list json "arms" at_).mapM (text · s!"{at_}.arms")
    return .branch (← textField json "judge" at_) arms
  | "waitStream" =>
    strict json ["type", "element"] at_
    return .waitStream (← valueType (← field json "element" at_) s!"{at_}.element")
  | "merge" =>
    strict json ["type", "element"] at_
    return .merge (← valueType (← field json "element" at_) s!"{at_}.element")
  | "concurrency" =>
    strict json ["type", "input", "limit", "tasks", "output", "element"] at_
    let limit ← natField? json "limit" at_
    return .concurrency {
      input := ← (field? json "input").mapM (valueType · s!"{at_}.input")
      limit := ← match limit with
        | some n => pure n
        | none => throw s!"{at_}: missing field limit"
      tasks := ← (← list json "tasks" at_).mapM (task · s!"{at_}.tasks")
      output := ← collect (← field json "output" at_) s!"{at_}.output"
      element := ← valueType (← field json "element" at_) s!"{at_}.element" }
  | other => throw s!"{at_}: unknown node type {other}"

def controlWire : Control → Wire
  | .call b => bodyWire b
  | .branch judge arms => .obj [("type", .str "branch"), ("judge", .str judge), ("arms", .arr (arms.map .str))]
  | .waitStream element => .obj [("type", .str "waitStream"), ("element", valueTypeWire element)]
  | .merge element => .obj [("type", .str "merge"), ("element", valueTypeWire element)]
  | .concurrency c => obj [("type", some (.str "concurrency")), ("input", c.input.map valueTypeWire),
      ("limit", some (.nat c.limit)), ("tasks", some (.arr (c.tasks.map taskWire))),
      ("output", some (collectWire c.output)), ("element", some (valueTypeWire c.element))]

def placement (json : Json) (at_ : String) : Except String Placement := do
  strict json ["name", "node", "policy", "timeout"] at_
  let name ← textField json "name" at_
  let at_ := s!"{at_}.{name}"
  return {
    name
    control := ← control (← field json "node" at_) s!"{at_}.node"
    policy := ← policy (← field json "policy" at_) s!"{at_}.policy"
    timeout := ← timeout json at_ }

def placementWire (p : Placement) : Wire :=
  obj [("name", some (.str p.name)), ("node", some (controlWire p.control)),
    ("policy", some (policyWire p.policy)), ("timeout", timeoutWire p.timeout)]

def connection (json : Json) (at_ : String) : Except String Connection := do
  strict json ["source", "arm", "target", "transform"] at_
  return {
    source := ← textField json "source" at_
    arm := ← textField? json "arm" at_
    target := ← textField json "target" at_
    transform := transformRef (← textField json "transform" at_) }

def connectionWire (c : Connection) : Wire :=
  obj [("source", some (.str c.source)), ("arm", c.arm.map .str),
    ("target", some (.str c.target)), ("transform", some (transformRefWire c.transform))]

def workflow (json : Json) (at_ : String) : Except String Workflow := do
  strict json ["id", "input", "placements", "connections"] at_
  let id ← textField json "id" at_
  let at_ := s!"{at_}.{id}"
  let input ← (field? json "input").mapM fun entry => do
    strict entry ["type", "placement"] s!"{at_}.input"
    return { valueType := ← valueType (← field entry "type" s!"{at_}.input") s!"{at_}.input.type"
             placement := ← textField entry "placement" s!"{at_}.input" : Entry }
  return {
    id, input
    placements := ← (← list json "placements" at_).mapM (placement · s!"{at_}.placements")
    connections := ← (← list json "connections" at_).mapM (connection · s!"{at_}.connections") }

def entryWire (e : Entry) : Wire :=
  .obj [("type", valueTypeWire e.valueType), ("placement", .str e.placement)]

def workflowWire (w : Workflow) : Wire :=
  obj [("id", some (.str w.id)), ("input", w.input.map entryWire),
    ("placements", some (.arr (w.placements.map placementWire))),
    ("connections", some (.arr (w.connections.map connectionWire)))]

def functionDecl (json : Json) (at_ : String) : Except String FunctionDecl := do
  strict json ["id", "input", "output"] at_
  let id ← textField json "id" at_
  let at_ := s!"{at_}.{id}"
  return {
    id
    input := ← (field? json "input").mapM (valueType · s!"{at_}.input")
    output := ← contract (← field json "output" at_) s!"{at_}.output" }

def judgeDecl (json : Json) (at_ : String) : Except String JudgeDecl := do
  strict json ["id", "input"] at_
  let id ← textField json "id" at_
  return { id, input := ← valueType (← field json "input" at_) s!"{at_}.{id}.input" }

def transformDecl (json : Json) (at_ : String) : Except String TransformDecl := do
  strict json ["id", "input", "output"] at_
  let id ← textField json "id" at_
  return {
    id
    input := ← valueType (← field json "input" at_) s!"{at_}.{id}.input"
    output := ← valueType (← field json "output" at_) s!"{at_}.{id}.output" }

def definition (json : Json) : Except String Definition := do
  strict json ["main", "functions", "judges", "transforms", "workflows"] "definition"
  return {
    main := ← textField json "main" "definition"
    functions := ← (← list json "functions" "definition").mapM (functionDecl · "functions")
    judges := ← (← list json "judges" "definition").mapM (judgeDecl · "judges")
    transforms := ← (← list json "transforms" "definition").mapM (transformDecl · "transforms")
    workflows := ← (← list json "workflows" "definition").mapM (workflow · "workflows") }

def functionWire (f : FunctionDecl) : Wire :=
  obj [("id", some (.str f.id)), ("input", f.input.map valueTypeWire), ("output", some (contractWire f.output))]

def judgeWire (j : JudgeDecl) : Wire := .obj [("id", .str j.id), ("input", valueTypeWire j.input)]

def transformWire (t : TransformDecl) : Wire :=
  .obj [("id", .str t.id), ("input", valueTypeWire t.input), ("output", valueTypeWire t.output)]

/-- The canonical form of a definition: the definition file with its fields in a fixed order and the
    absent optional fields left out, as Go's `definitionWire` writes it. The header of an execution
    record carries it, so that equal definitions are recorded alike (§12.1). --/
def definitionWire (p : Definition) : Wire :=
  .obj [("main", .str p.main), ("functions", .arr (p.functions.map functionWire)),
    ("judges", .arr (p.judges.map judgeWire)), ("transforms", .arr (p.transforms.map transformWire)),
    ("workflows", .arr (p.workflows.map workflowWire))]

def definitionJson (p : Definition) : Json := (definitionWire p).toJson

/-- Reads a definition from the `Json` of a definition file (`Codec.parse`): decoded, then validated
    (§14). --/
def loadJson (json : Json) : Except String Definition := do
  let p ← definition json
  p.validate
  return p

/-- Reads the definition that the header of an execution record holds, as a definition file is read.
    `suimon check` replays a record against it. --/
def load (w : Wire) : Except String Definition :=
  loadJson w.toJson

end Codec

instance : Lean.ToJson Definition := ⟨Codec.definitionJson⟩
instance : Lean.FromJson Definition := ⟨Codec.definition⟩

end Suimon
