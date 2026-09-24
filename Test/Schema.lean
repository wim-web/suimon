import Lean

namespace Suimon.Test.Schema
open Lean

/- Test-only checker for the JSON Schema keywords used in schema/*.json.
   Unsupported keywords are errors, so extending a schema cannot silently weaken tests. -/

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def field (json : Json) (name : String) : Option Json :=
  (json.getObjVal? name).toOption

/-- The schema a reference names, with the document it is in: `#/$defs/name` in the document of the
    reference, or another document by its file name, whole or `file#/$defs/name`. --/
private def resolve (documents : List (String × Json)) (root : Json) (reference : String) :
    Except String (Json × Json) := do
  let (document, pointer) ← match reference.splitOn "#" with
    | ["", pointer] => pure (root, pointer)
    | [file] => pure (← find file, "")
    | [file, pointer] => pure (← find file, pointer)
    | _ => throw s!"invalid reference: {reference}"
  if pointer.isEmpty then return (document, document)
  let ["", "$defs", name] := pointer.splitOn "/"
    | throw s!"only $defs references are supported: {reference}"
  let definitions ← document.getObjVal? "$defs"
  return (document, ← definitions.getObjVal? ((name.replace "~1" "/").replace "~0" "~"))
where
  find (file : String) : Except String Json :=
    match documents.lookup file with
    | some document => pure document
    | none => throw s!"unknown schema document: {file}"

private def types := ["object", "array", "string", "integer", "number", "boolean", "null"]

/-- Check the entire schema, including unused definitions and alternatives. --/
private def checkSchema (documents : List (String × Json)) (root : Json) : Nat → Json → Except String Unit
  | 0, _ => .error "schema nesting limit exceeded"
  | fuel + 1, rule => do
    if rule matches .bool _ then return ()
    for (key, value) in (← rule.getObj?).toList do
      match key with
      | "$schema" =>
        require ((← value.getStr?) == "https://json-schema.org/draft/2020-12/schema") "unsupported schema dialect"
      | "$id" | "title" | "description" => let _ ← value.getStr?; pure ()
      | "$ref" => let _ ← resolve documents root (← value.getStr?); pure ()
      | "type" => require (types.contains (← value.getStr?)) "unsupported schema type"
      | "properties" | "$defs" =>
        for (_, child) in (← value.getObj?).toList do checkSchema documents root fuel child
      | "items" | "additionalProperties" => checkSchema documents root fuel value
      | "prefixItems" | "oneOf" | "anyOf" =>
        let children ← value.getArr?
        require (!children.isEmpty) s!"{key} must not be empty"
        for child in children do checkSchema documents root fuel child
      | "uniqueItems" => let _ ← value.getBool?; pure ()
      | "minLength" | "minItems" | "maxItems" => let _ ← value.getNat?; pure ()
      | "minimum" | "maximum" => let _ ← value.getNum?; pure ()
      | "const" => pure ()
      | "enum" =>
        let values := (← value.getArr?).toList
        require (!values.isEmpty && values.eraseDups.length == values.length) "invalid enum"
      | "required" =>
        let names ← (← value.getArr?).toList.mapM Json.getStr?
        require (names.eraseDups.length == names.length) "duplicate required property"
      | _ => throw s!"unsupported schema keyword: {key}"

/-- JSON Schema counts any number with a zero fractional part as an integer, so `2.0` and `20e-1`
    are integers. The parser does not normalize numbers: both have mantissa 20 and exponent 1.
    Stripping trailing zeros, rather than computing a power of ten, takes at most one step per digit
    of the mantissa whatever the exponent. --/
private def isInteger : Json → Bool
  | .num ⟨m, e⟩ => m == 0 || strip m.natAbs e
  | _ => false
where
  strip (m : Nat) : Nat → Bool
    | 0 => true
    | e + 1 => m % 10 == 0 && strip (m / 10) e

/-- `a < b`. Lean's `JsonNumber.lt` compares zero with a negative number wrongly: it says `-1 < 0` is
    false. A number is its mantissa over a power of ten; numbers of one sign compare by the position
    of their first digit, then by their digits, so no power of ten beyond the digits of the mantissas
    is computed, whatever the exponents. --/
def numberLt (a b : JsonNumber) : Bool :=
  if sign a != sign b then sign a < sign b
  else if sign a == 0 then false
  else if sign a > 0 then magnitudeLt a b
  else magnitudeLt b a
where
  sign (n : JsonNumber) : Int := if n.mantissa > 0 then 1 else if n.mantissa < 0 then -1 else 0
  digits (n : Nat) : Nat := (toString n).length
  /-- `|a| < |b|` for non-zero numbers, whose values lie in `[10^(k-1), 10^k)` for `k` the number of
      digits of the mantissa less the exponent. --/
  magnitudeLt (a b : JsonNumber) : Bool :=
    let am := a.mantissa.natAbs
    let bm := b.mantissa.natAbs
    let ak : Int := digits am - a.exponent
    let bk : Int := digits bm - b.exponent
    if ak != bk then ak < bk
    else if digits am < digits bm then am * 10 ^ (digits bm - digits am) < bm
    else am < bm * 10 ^ (digits am - digits bm)

private def hasType (value : Json) : String → Bool
  | "object" => (value matches .obj _)
  | "array" => (value matches .arr _)
  | "string" => (value matches .str _)
  | "integer" => isInteger value
  | "number" => (value matches .num _)
  | "boolean" => (value matches .bool _)
  | "null" => value.isNull
  | _ => false

private def checkValue (documents : List (String × Json)) (root : Json) : Nat → Json → Json → Except String Unit
  | 0, _, _ => .error "schema evaluation nesting limit exceeded"
  | fuel + 1, rule, value => do
    if let .bool accept := rule then
      require accept "false schema"
      return ()
    if let some reference := field rule "$ref" then
      let (document, target) ← resolve documents root (← reference.getStr?)
      checkValue documents document fuel target value
    if let some kind := field rule "type" then
      require (hasType value (← kind.getStr?)) s!"expected type {kind.compress}"
    if let some expected := field rule "const" then
      require (value == expected) s!"expected constant {expected.compress}"
    if let some choices := field rule "enum" then
      require ((← choices.getArr?).contains value) "value is outside enum"
    for keyword in ["oneOf", "anyOf"] do
      if let some choices := field rule keyword then
        let accepted := (← choices.getArr?).filter fun child =>
          (checkValue documents root fuel child value).toOption.isSome
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
          (checkValue documents root fuel childRule child).mapError (fun e => s!"{key}: {e}")
        | none =>
          match field rule "additionalProperties" with
          | some (.bool accept) => require accept s!"unexpected property {key}"
          | some additional => (checkValue documents root fuel additional child).mapError (fun e => s!"{key}: {e}")
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
          checkValue documents root fuel childRule child
        else if let some childRule := field rule "items" then
          checkValue documents root fuel childRule child
    | .str text =>
      if let some minimum := field rule "minLength" then
        require (text.length ≥ (← minimum.getNat?)) "string is too short"
    | .num number =>
      if let some minimum := field rule "minimum" then
        require (!numberLt number (← minimum.getNum?)) "number is below minimum"
      if let some maximum := field rule "maximum" then
        require (!numberLt (← maximum.getNum?) number) "number is above maximum"
    | _ => pure ()

/-- Keep compilation and per-value checking separate to inspect every schema branch once. The
    documents are the other schemas that references name by file name. --/
structure Validator where
  private root : Json
  private documents : List (String × Json)

def compile (schema : Json) (documents : List (String × Json) := []) : Except String Validator := do
  checkSchema documents schema 256 schema
  return ⟨schema, documents⟩

def Validator.validate (schema : Validator) (value : Json) : Except String Unit :=
  checkValue schema.documents schema.root 1024 schema.root value

end Suimon.Test.Schema
