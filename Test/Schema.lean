import Lean

namespace Suimon.Test.Schema
open Lean

/- Test-only checker for the JSON Schema keywords used in schema/*.json.
   Unsupported keywords are errors, so extending a schema cannot silently weaken tests. -/

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def field (json : Json) (name : String) : Option Json :=
  (json.getObjVal? name).toOption

private def resolve (root : Json) (reference : String) : Except String Json := do
  let ["#", "$defs", name] := reference.splitOn "/"
    | throw s!"only local $defs references are supported: {reference}"
  let definitions ← root.getObjVal? "$defs"
  definitions.getObjVal? ((name.replace "~1" "/").replace "~0" "~")

private def types := ["object", "array", "string", "integer", "number", "boolean", "null"]

/-- Check the entire schema, including unused definitions and alternatives. --/
private def checkSchema (root : Json) : Nat → Json → Except String Unit
  | 0, _ => .error "schema nesting limit exceeded"
  | fuel + 1, rule => do
    if rule matches .bool _ then return ()
    for (key, value) in (← rule.getObj?).toList do
      match key with
      | "$schema" =>
        require ((← value.getStr?) == "https://json-schema.org/draft/2020-12/schema") "unsupported schema dialect"
      | "$id" | "title" | "description" => let _ ← value.getStr?; pure ()
      | "$ref" => let _ ← resolve root (← value.getStr?); pure ()
      | "type" => require (types.contains (← value.getStr?)) "unsupported schema type"
      | "properties" | "$defs" =>
        for (_, child) in (← value.getObj?).toList do checkSchema root fuel child
      | "items" | "additionalProperties" => checkSchema root fuel value
      | "prefixItems" | "oneOf" | "anyOf" =>
        let children ← value.getArr?
        require (!children.isEmpty) s!"{key} must not be empty"
        for child in children do checkSchema root fuel child
      | "uniqueItems" => let _ ← value.getBool?; pure ()
      | "minLength" | "minItems" | "maxItems" => let _ ← value.getNat?; pure ()
      | "minimum" => let _ ← value.getNum?; pure ()
      | "const" => pure ()
      | "enum" =>
        let values := (← value.getArr?).toList
        require (!values.isEmpty && values.eraseDups.length == values.length) "invalid enum"
      | "required" =>
        let names ← (← value.getArr?).toList.mapM Json.getStr?
        require (names.eraseDups.length == names.length) "duplicate required property"
      | _ => throw s!"unsupported schema keyword: {key}"

private def hasType (value : Json) : String → Bool
  | "object" => (value matches .obj _)
  | "array" => (value matches .arr _)
  | "string" => (value matches .str _)
  | "integer" => value.getInt?.toOption.isSome
  | "number" => (value matches .num _)
  | "boolean" => (value matches .bool _)
  | "null" => value.isNull
  | _ => false

private def checkValue (root : Json) : Nat → Json → Json → Except String Unit
  | 0, _, _ => .error "schema evaluation nesting limit exceeded"
  | fuel + 1, rule, value => do
    if let .bool accept := rule then
      require accept "false schema"
      return ()
    if let some reference := field rule "$ref" then
      checkValue root fuel (← resolve root (← reference.getStr?)) value
    if let some kind := field rule "type" then
      require (hasType value (← kind.getStr?)) s!"expected type {kind.compress}"
    if let some expected := field rule "const" then
      require (value == expected) s!"expected constant {expected.compress}"
    if let some choices := field rule "enum" then
      require ((← choices.getArr?).contains value) "value is outside enum"
    for keyword in ["oneOf", "anyOf"] do
      if let some choices := field rule keyword then
        let accepted := (← choices.getArr?).filter fun child =>
          (checkValue root fuel child value).toOption.isSome
        require (if keyword == "oneOf" then accepted.size == 1 else !accepted.isEmpty)
          s!"{keyword}: {accepted.size} matching alternatives"
    match value with
    | .obj values =>
      let properties := ((field rule "properties").getD (Json.mkObj [])).getObj?
      let properties ← properties
      if let some required := field rule "required" then
        for name in (← required.getArr?) do
          require ((values.get? (← name.getStr?)).isSome) s!"missing property {name.compress}"
      for (key, child) in values.toList do
        match properties.get? key with
        | some childRule =>
          (checkValue root fuel childRule child).mapError (fun e => s!"{key}: {e}")
        | none =>
          match field rule "additionalProperties" with
          | some (.bool accept) => require accept s!"unexpected property {key}"
          | some additional => (checkValue root fuel additional child).mapError (fun e => s!"{key}: {e}")
          | none => pure ()
    | .arr values =>
      if let some minimum := field rule "minItems" then
        require (values.size ≥ (← minimum.getNat?)) "array is too short"
      if let some maximum := field rule "maxItems" then
        require (values.size ≤ (← maximum.getNat?)) "array is too long"
      if field rule "uniqueItems" == some (.bool true) then
        require (values.toList.eraseDups.length == values.size) "array has duplicate items"
      let heads ← ((field rule "prefixItems").getD (.arr #[])).getArr?
      for (child, idx) in values.toList.zipIdx do
        if let some childRule := heads[idx]? then
          checkValue root fuel childRule child
        else if let some childRule := field rule "items" then
          checkValue root fuel childRule child
    | .str text =>
      if let some minimum := field rule "minLength" then
        require (text.length ≥ (← minimum.getNat?)) "string is too short"
    | .num number =>
      if let some minimum := field rule "minimum" then
        require (!(number < (← minimum.getNum?))) "number is below minimum"
    | _ => pure ()

/-- Keep compilation and per-value checking separate to inspect every schema branch once. --/
structure Validator where
  private root : Json

def compile (schema : Json) : Except String Validator := do
  checkSchema schema 256 schema
  return ⟨schema⟩

def Validator.validate (schema : Validator) (value : Json) : Except String Unit :=
  checkValue schema.root 1024 schema.root value

end Suimon.Test.Schema
