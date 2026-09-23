import Suimon.Workflow

namespace Suimon.Codec
open Lean

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

def natField? (json : Json) (key : String) (at_ : String) : Except String (Option Nat) :=
  (field? json key).mapM fun value => value.getNat?.mapError fun _ => s!"{at_}.{key}: expected a natural number"

def list (json : Json) (key : String) (at_ : String) : Except String (List Json) :=
  match field? json key with
  | none => pure []
  | some (.arr items) => pure items.toList
  | some _ => throw s!"{at_}.{key}: expected an array"

def obj (fields : List (String × Option Json)) : Json :=
  Json.mkObj (fields.filterMap fun (key, value) => value.map (key, ·))

partial def valueType (json : Json) (at_ : String) : Except String ValueType :=
  match json with
  | .str name => if name.isEmpty then throw s!"{at_}: empty type name" else pure (.named name)
  | .obj _ => do
    strict json ["list"] at_
    return .list (← valueType (← field json "list" at_) at_)
  | _ => throw s!"{at_}: a type is a name or \{\"list\": type}"

def valueTypeJson : ValueType → Json
  | .named name => .str name
  | .list element => Json.mkObj [("list", valueTypeJson element)]

def contract (json : Json) (at_ : String) : Except String Contract := do
  strict json ["single", "stream"] at_
  match field? json "single", field? json "stream" with
  | some value, none => return .single (← valueType value s!"{at_}.single")
  | none, some element => return .stream (← valueType element s!"{at_}.stream")
  | _, _ => throw s!"{at_}: an output contract is either single or stream"

def contractJson : Contract → Json
  | .single value => Json.mkObj [("single", valueTypeJson value)]
  | .stream element => Json.mkObj [("stream", valueTypeJson element)]

def policy (json : Json) (at_ : String) : Except String Policy :=
  match json with
  | .str "stop" => pure .stop
  | .str "continue" => pure .«continue»
  | _ => throw s!"{at_}: policy is stop or continue"

def policyJson : Policy → Json
  | .stop => "stop"
  | .«continue» => "continue"

def timeout (json : Json) (at_ : String) : Except String Timeout := do
  match field? json "timeout" with
  | none => pure {}
  | some value =>
    let at_ := s!"{at_}.timeout"
    strict value ["callMs", "elementMs"] at_
    return { callMs := ← natField? value "callMs" at_, elementMs := ← natField? value "elementMs" at_ }

def timeoutJson (t : Timeout) : Option Json :=
  if t.isEmpty then none
  else some (obj [("callMs", t.callMs.map toJson), ("elementMs", t.elementMs.map toJson)])

def body (json : Json) (at_ : String) : Except String Body := do
  match ← textField json "type" at_ with
  | "function" =>
    strict json ["type", "function"] at_
    return .function (← textField json "function" at_)
  | "subworkflow" =>
    strict json ["type", "workflow", "output"] at_
    return .workflow (← textField json "workflow" at_) (← textField json "output" at_)
  | other => throw s!"{at_}: unknown body type {other}"

def bodyJson : Body → Json
  | .function id => Json.mkObj [("type", "function"), ("function", id)]
  | .workflow id output => Json.mkObj [("type", "subworkflow"), ("workflow", id), ("output", output)]

def transformRef (id : String) : TransformRef :=
  if id == TransformRef.discardName then .discard else .declared id

def transformRefJson : TransformRef → Json
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

def taskJson (t : TaskSpec) : Json :=
  obj [("name", some (toJson t.name)), ("body", some (bodyJson t.body)),
    ("inputTransform", t.input.map transformRefJson), ("outputTransform", t.output.map toJson),
    ("policy", some (policyJson t.policy)), ("timeout", timeoutJson t.timeout)]

def collect (json : Json) (at_ : String) : Except String Collect :=
  match json with
  | .str "list" => pure .list
  | .str "stream" => pure .stream
  | _ => throw s!"{at_}: output is list or stream"

def collectJson : Collect → Json
  | .list => "list"
  | .stream => "stream"

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

def controlJson : Control → Json
  | .call b => bodyJson b
  | .branch judge arms => Json.mkObj [("type", "branch"), ("judge", judge), ("arms", toJson arms)]
  | .waitStream element => Json.mkObj [("type", "waitStream"), ("element", valueTypeJson element)]
  | .merge element => Json.mkObj [("type", "merge"), ("element", valueTypeJson element)]
  | .concurrency c => obj [("type", some "concurrency"), ("input", c.input.map valueTypeJson),
      ("limit", some (toJson c.limit)), ("tasks", some (Json.arr (c.tasks.map taskJson).toArray)),
      ("output", some (collectJson c.output)), ("element", some (valueTypeJson c.element))]

def placement (json : Json) (at_ : String) : Except String Placement := do
  strict json ["name", "node", "policy", "timeout"] at_
  let name ← textField json "name" at_
  let at_ := s!"{at_}.{name}"
  return {
    name
    control := ← control (← field json "node" at_) s!"{at_}.node"
    policy := ← policy (← field json "policy" at_) s!"{at_}.policy"
    timeout := ← timeout json at_ }

def placementJson (p : Placement) : Json :=
  obj [("name", some (toJson p.name)), ("node", some (controlJson p.control)),
    ("policy", some (policyJson p.policy)), ("timeout", timeoutJson p.timeout)]

def connection (json : Json) (at_ : String) : Except String Connection := do
  strict json ["source", "arm", "target", "transform"] at_
  return {
    source := ← textField json "source" at_
    arm := ← textField? json "arm" at_
    target := ← textField json "target" at_
    transform := transformRef (← textField json "transform" at_) }

def connectionJson (c : Connection) : Json :=
  obj [("source", some (toJson c.source)), ("arm", c.arm.map toJson),
    ("target", some (toJson c.target)), ("transform", some (transformRefJson c.transform))]

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

def workflowJson (w : Workflow) : Json :=
  obj [("id", some (toJson w.id)),
    ("input", w.input.map fun e => Json.mkObj [("type", valueTypeJson e.valueType), ("placement", e.placement)]),
    ("placements", some (Json.arr (w.placements.map placementJson).toArray)),
    ("connections", some (Json.arr (w.connections.map connectionJson).toArray))]

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

def program (json : Json) : Except String Program := do
  strict json ["main", "functions", "judges", "transforms", "workflows"] "program"
  return {
    main := ← textField json "main" "program"
    functions := ← (← list json "functions" "program").mapM (functionDecl · "functions")
    judges := ← (← list json "judges" "program").mapM (judgeDecl · "judges")
    transforms := ← (← list json "transforms" "program").mapM (transformDecl · "transforms")
    workflows := ← (← list json "workflows" "program").mapM (workflow · "workflows") }

def programJson (p : Program) : Json :=
  Json.mkObj [("main", p.main),
    ("functions", Json.arr (p.functions.map fun f => obj [("id", some (toJson f.id)),
      ("input", f.input.map valueTypeJson), ("output", some (contractJson f.output))]).toArray),
    ("judges", Json.arr (p.judges.map fun j =>
      Json.mkObj [("id", j.id), ("input", valueTypeJson j.input)]).toArray),
    ("transforms", Json.arr (p.transforms.map fun t => Json.mkObj [("id", t.id),
      ("input", valueTypeJson t.input), ("output", valueTypeJson t.output)]).toArray),
    ("workflows", Json.arr (p.workflows.map workflowJson).toArray)]

end Codec

instance : Lean.ToJson Program := ⟨Codec.programJson⟩
instance : Lean.FromJson Program := ⟨Codec.program⟩

end Suimon
