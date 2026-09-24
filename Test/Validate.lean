import Suimon.Validate
import Suimon.Json

namespace Suimon.Test.Validate
open Lean Suimon

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

def load (name : String) : IO Definition := do
  match Codec.parse (← IO.FS.readFile s!"Test/definitions/{name}.json") >>= Codec.definition with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"{name}: {e}")

def accepted (label : String) (p : Definition) : IO Unit :=
  match p.validate with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"{label}: expected a valid definition, got: {e}")

def rejected (label : String) (fragment : String) (p : Definition) : IO Unit :=
  match p.validate with
  | .ok () => throw (IO.userError s!"{label}: accepted, expected an error with '{fragment}'")
  | .error e => ensure (contains e fragment) s!"{label}: expected '{fragment}', got: {e}"

def decodeRejected (label : String) (fragment : String) (text : String) : IO Unit :=
  match Codec.parse text >>= Codec.definition with
  | .ok _ => throw (IO.userError s!"{label}: decoded, expected an error with '{fragment}'")
  | .error e => ensure (contains e fragment) s!"{label}: expected '{fragment}', got: {e}"

/-- Definition text without a repeated key reads as `Json.parse` reads it: to the same value, or to
    the same message at the same offset. --/
def parsesLikeLean (label text : String) : IO Unit :=
  let render (result : Except String Json) : String := match result with
    | .ok json => s!"ok {json.compress}"
    | .error e => s!"error {e}"
  ensure (render (Codec.parse text) == render (Json.parse text))
    s!"{label}: {render (Codec.parse text)}, but Json.parse gives {render (Json.parse text)}"

def parseRejected (label expected text : String) : IO Unit :=
  match Codec.parse text with
  | .ok json => throw (IO.userError s!"{label}: parsed as {json.compress}, expected '{expected}'")
  | .error e => ensure (e == expected) s!"{label}: expected '{expected}', got: {e}"

def decoded (label : String) (text : String) : IO Definition :=
  match Codec.parse text >>= Codec.definition with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"{label}: {e}")

def limits (p : Definition) : List Nat :=
  p.workflows.flatMap fun w => w.placements.filterMap fun pl => match pl.control with
    | .concurrency c => some c.limit
    | _ => none

def mapWorkflow (id : String) (f : Workflow → Workflow) (p : Definition) : Definition :=
  { p with workflows := p.workflows.map fun w => if w.id == id then f w else w }

def mapPlacement (name : String) (f : Placement → Placement) (w : Workflow) : Workflow :=
  { w with placements := w.placements.map fun pl => if pl.name == name then f pl else pl }

def mapConnection (source target : String) (f : Connection → Connection) (w : Workflow) : Workflow :=
  { w with connections := w.connections.map fun c => if c.source == source && c.target == target then f c else c }

def dropConnection (source target : String) (w : Workflow) : Workflow :=
  { w with connections := w.connections.filter fun c => !(c.source == source && c.target == target) }

def mapConcurrency (f : Concurrency → Concurrency) (pl : Placement) : Placement :=
  match pl.control with
  | .concurrency c => { pl with control := .concurrency (f c) }
  | _ => pl

def mapTask (name : String) (f : TaskSpec → TaskSpec) (c : Concurrency) : Concurrency :=
  { c with tasks := c.tasks.map fun t => if t.name == name then f t else t }

def kinds (p : Definition) (id : String) : List (String × Option Kind) :=
  match p.workflow? id with
  | some w => w.placements.map fun pl => (pl.name, w.outputKind? p pl.name)
  | none => []

def cycle : Definition := {
  main := "loop"
  functions := [{ id := "step", input := some (.named "A"), output := .single (.named "A") }]
  transforms := [{ id := "a", input := .named "A", output := .named "A" }]
  workflows := [{
    id := "loop"
    placements := [
      { name := "x", control := .call (.function "step"), policy := .stop },
      { name := "y", control := .call (.function "step"), policy := .stop }]
    connections := [
      { source := "x", target := "y", transform := .declared "a" },
      { source := "y", target := "x", transform := .declared "a" }] }] }

/-- A concurrency without input, whose only task takes no input either. --/
def standalone (input : Option TransformRef) : Definition := {
  main := "w"
  functions := [{ id := "loadConfig", output := .single (.named "Config") }]
  transforms := [{ id := "config", input := .named "Config", output := .named "Config" }]
  workflows := [{
    id := "w"
    placements := [{
      name := "c"
      policy := .stop
      control := .concurrency {
        limit := 1
        output := .list
        element := .named "Config"
        tasks := [{
          name := "config"
          body := .function "loadConfig"
          input := input
          output := some "config"
          policy := .stop }] } }] }] }

def run : IO Unit := do
  let users ← load "users"
  let branch ← load "branch"
  let merge ← load "merge"
  for (label, p) in [("users", users), ("branch", branch), ("merge", merge)] do
    accepted label p
    match Codec.definition (Codec.definitionJson p) with
    | .ok q => ensure (q == p) s!"{label}: JSON round trip changed the definition"
    | .error e => throw (IO.userError s!"{label}: JSON round trip failed: {e}")

  ensure (kinds users "users" == [("fetchAllUsers", some .stream), ("perUser", some .stream), ("all", some .single)])
    "users: Stream input to a List concurrency is a Stream of lists"
  ensure (kinds branch "shipping" ==
    [("list", some .stream), ("paid", some .stream), ("ship", some .stream), ("receipts", some .single)])
    "branch: a branch keeps its input kind"
  ensure (kinds merge "dashboard" == [("sales", some .single), ("stock", some .single),
    ("widgets", some .single), ("page", some .single), ("archive", some .single), ("notify", some .single)])
    "merge: Merge of Singles is Single, and a discard connection from a Single is Single"
  ensure (users.resultType (.concurrency { limit := 1, tasks := [], output := .list, element := .named "T" })
    == some (.list (.named "T"))) "a List concurrency produces List<T>"

  -- Names and references
  rejected "duplicate placement" "duplicate placement name" <| merge |> mapWorkflow "dashboard" fun w =>
    { w with placements := w.placements ++ w.placements.take 1 }
  rejected "unknown main" "unknown main workflow nope" { merge with main := "nope" }
  rejected "unknown transform" "unknown transform nope" <| merge |> mapWorkflow "dashboard"
    (mapConnection "sales" "archive" fun c => { c with transform := .declared "nope" })
  rejected "unknown output endpoint" "fetch is not an endpoint of workflow profileFlow" <| users |>
    mapWorkflow "users" (mapPlacement "perUser" (mapConcurrency (mapTask "profile" fun t =>
      { t with body := .workflow "profileFlow" "fetch" })))

  -- Types
  rejected "transform input" "takes Stock, but sales produces Sales" <| merge |> mapWorkflow "dashboard"
    (mapConnection "sales" "archive" fun c => { c with transform := .declared "stockWidget" })
  rejected "transform output" "returns Widget, but archive takes Sales" <| merge |> mapWorkflow "dashboard"
    (mapConnection "sales" "archive" fun c => { c with transform := .declared "salesWidget" })
  rejected "entry type" "the input type Org does not match" <| users |> mapWorkflow "users" fun w =>
    { w with input := some { valueType := .named "Org", placement := "fetchAllUsers" } }
  rejected "task input transform" "an input transform is required" <| users |>
    mapWorkflow "users" (mapPlacement "perUser" (mapConcurrency (mapTask "orders" fun t => { t with input := none })))
  rejected "task output transform" "takes Profile, but the body produces Orders" <| users |>
    mapWorkflow "users" (mapPlacement "perUser" (mapConcurrency (mapTask "orders" fun t =>
      { t with output := some "profileSummary" })))

  -- Inputs
  rejected "two inputs" "archive: needs exactly one input" <| merge |> mapWorkflow "dashboard" fun w =>
    { w with connections := w.connections ++ w.connections.filter (·.target == "archive") }
  rejected "missing input" "archive: needs exactly one input" <| merge |>
    mapWorkflow "dashboard" (dropConnection "sales" "archive")
  rejected "input to a node without input" "stock takes no input" <| merge |> mapWorkflow "dashboard" fun w =>
    { w with connections := w.connections ++ [{ source := "sales", target := "stock", transform := .declared "sales" }] }
  rejected "Merge entry" "Merge cannot be the entry" <| merge |> mapWorkflow "dashboard" fun w =>
    { w with input := some { valueType := .named "Widget", placement := "widgets" } }

  -- discard: a target without input runs once per value it receives, without the value
  let ticks := branch |> mapWorkflow "shipping" fun w =>
    { w with
      placements := w.placements ++ [
        { name := "tick", control := .call (.function "tick"), policy := .«continue» },
        { name := "ticks", control := .waitStream (.named "Tick"), policy := .stop }]
      connections := w.connections ++ [
        { source := "ship", target := "tick", transform := .discard },
        { source := "tick", target := "ticks", transform := .declared "tick" }] }
  let ticks := { ticks with
    functions := ticks.functions ++ [{ id := "tick", output := .single (.named "Tick") }]
    transforms := ticks.transforms ++ [{ id := "tick", input := .named "Tick", output := .named "Tick" }] }
  accepted "discard from a Stream" ticks
  ensure ((kinds ticks "shipping").lookup "tick" == some (some .stream)) "discard keeps the Stream kind"
  rejected "discard to a node with input" "discard passes no value, but archive takes Sales" <| merge |>
    mapWorkflow "dashboard" (mapConnection "sales" "archive" fun c => { c with transform := .discard })
  rejected "two discard connections" "notify: accepts at most one connection" <| merge |> mapWorkflow "dashboard" fun w =>
    { w with connections := w.connections ++ [{ source := "stock", target := "notify", transform := .discard }] }
  let configTask := fun (input : Option TransformRef) => users |> mapWorkflow "users"
    (mapPlacement "perUser" (mapConcurrency fun c => { c with tasks := c.tasks ++ [{
      name := "config", body := .function "loadConfig", input, policy := .«continue» }] }))
  let withConfig := fun (p : Definition) =>
    { p with functions := p.functions ++ [{ id := "loadConfig", output := .single (.named "Config") }] }
  accepted "task without input discards the concurrency input" (withConfig (configTask (some .discard)))
  rejected "task without input and without discard" "the input transform must be discard"
    (withConfig (configTask none))
  accepted "task without input in a concurrency without input" (standalone none)
  rejected "discard without concurrency input" "the concurrency has no input to discard" (standalone (some .discard))
  rejected "declared discard" "discard is provided by the library and cannot be declared"
    { merge with transforms := merge.transforms ++ [{ id := "discard", input := .named "A", output := .named "A" }] }

  -- Graph structure and kinds
  rejected "cycle" "connections contain a cycle" cycle
  rejected "recursive call" "workflows call each other in a cycle" <| users |> mapWorkflow "profileFlow"
    (mapPlacement "format" fun pl => { pl with control := .call (.workflow "profileFlow" "format") })
  rejected "waitStream on Single" "waitStream needs a Stream input" <| merge |> mapWorkflow "dashboard"
    (mapPlacement "page" fun pl => { pl with control := .waitStream (.list (.named "Widget")) })
  rejected "Merge of Stream" "Merge accepts only Single inputs (ship)" <| branch |> mapWorkflow "shipping"
    (mapPlacement "receipts" fun pl => { pl with control := .merge (.named "Receipt") })
  rejected "Stream endpoint" "endpoint ship must be Single" <| branch |> mapWorkflow "shipping" fun w =>
    { dropConnection "ship" "receipts" w with placements := w.placements.filter (·.name != "receipts") }

  -- Branch arms
  rejected "no connected arm" "at least one arm needs a connection" <| branch |>
    mapWorkflow "shipping" (dropConnection "paid" "ship")
  rejected "unknown arm" "unknown arm refunded" <| branch |> mapWorkflow "shipping"
    (mapConnection "paid" "ship" fun c => { c with arm := some "refunded" })
  rejected "missing arm" "a connection from a branch needs an arm" <| branch |> mapWorkflow "shipping"
    (mapConnection "paid" "ship" fun c => { c with arm := none })
  rejected "arm outside a branch" "only a connection from a branch has an arm" <| merge |>
    mapWorkflow "dashboard" (mapConnection "sales" "archive" fun c => { c with arm := some "x" })
  -- A branch without connections, which is not the entry, reaches the check of its placement.
  rejected "unknown judge" "shipping.orphan: unknown judge nope" <| branch |> mapWorkflow "shipping" fun w =>
    { w with placements := w.placements ++ [{ name := "orphan", control := .branch "nope" ["a"], policy := .stop }] }

  -- Settings
  rejected "zero limit" "limit must be positive" <| users |>
    mapWorkflow "users" (mapPlacement "perUser" (mapConcurrency fun c => { c with limit := 0 }))
  rejected "no task in the output" "at least one task must be in the output" <| users |>
    mapWorkflow "users" (mapPlacement "perUser" (mapConcurrency fun c =>
      { c with tasks := c.tasks.map fun t => { t with output := none } }))
  accepted "Merge with one input" <| merge |> mapWorkflow "dashboard" fun w =>
    { w with
      placements := w.placements.filter (·.name != "stock")
      connections := w.connections.filter (·.source != "stock") }
  rejected "timeout on waitStream" "a timeout is only for a function call or a branch judge" <| users |>
    mapWorkflow "users" (mapPlacement "all" fun pl => { pl with timeout := { callMs := some 10 } })
  rejected "element timeout on Single" "an element timeout is only for a Stream function" <| merge |>
    mapWorkflow "dashboard" (mapPlacement "sales" fun pl => { pl with timeout := { elementMs := some 10 } })
  rejected "zero timeout" "a timeout must be positive" <| branch |>
    mapWorkflow "shipping" (mapPlacement "paid" fun pl => { pl with timeout := { callMs := some 0 } })

  -- Decoding
  let base := "{\"main\":\"w\",\"workflows\":[{\"id\":\"w\",\"placements\":[{\"name\":\"a\",\"node\":{\"type\":\"merge\",\"element\":\"T\"}"
  decodeRejected "unknown field" "unknown field retries" (base ++ ",\"policy\":\"stop\",\"retries\":1}]}]}")
  decodeRejected "missing policy" "missing field policy" (base ++ "}]}]}")
  decodeRejected "unknown policy" "policy is stop or continue" (base ++ ",\"policy\":\"retry\"}]}]}")
  -- A key may not repeat in an object, compared after its escapes are decoded; the error is right after
  -- the repeated key. Any other text reads as `Json.parse` reads it.
  parseRejected "repeated key" "offset 18: duplicate key \"main\"" "{\"main\":\"x\",\"main\":\"w\",\"workflows\":[]}"
  parseRejected "repeated nested key" "offset 104: duplicate key \"type\""
    ("{\"main\":\"w\",\"workflows\":[{\"id\":\"w\",\"placements\":[{\"name\":\"a\",\"node\":{\"type\":\"merge\"," ++
      "\"element\":\"T\",\"type\":\"merge\"},\"policy\":\"stop\"}]}]}")
  parseRejected "repeated escaped key" "offset 23: duplicate key \"main\"" "{\"main\":\"x\",\"\\u006dain\":\"w\"}"
  parseRejected "quoted key" "offset 14: duplicate key \"a\\n\"" "{\"a\\n\":1,\"a\\n\":2}"
  parseRejected "repeated key before a syntax error" "offset 10: duplicate key \"a\"" "{\"a\":1,\"a\":2,}"
  decodeRejected "repeated key in a definition" "duplicate key \"main\""
    "{\"main\":\"w\",\"main\":\"w\",\"workflows\":[]}"
  for name in ["users", "branch", "merge"] do
    parsesLikeLean name (← IO.FS.readFile s!"Test/definitions/{name}.json")
  for text in ["", " ", "{", "[", "{\"a\"", "{\"a\":", "{\"a\" 1}", "{\"a\":1 \"b\":2}", "{\"a\":1,}", "{1:2}",
      "[1 2]", "[1,]", "{\"main\":\"w\",}", "{} x", "tru", "nul", "-", "1.", "1e", "01", "-0", "1e99999999999999999999",
      "\"\\q\"", "\"\\u00zz\"", "\"a\u0001\"", "\"\\ud83d\"", "\"\\ud83d\\ude00\"", "\"\\ude00x\"",
      " { \"a\" : [ 1 , 2.5e-3 , -0 , true , false , null ] , \"b\" : { } } ",
      "{\"a\":{\"a\":1},\"b\":[{\"a\":1},{\"a\":2}],\"c\":{\"b\":{\"a\":[]}}}", base ++ ",\"policy\":\"stop\"}]}]}"] do
    parsesLikeLean text.quote text
  -- A number is read by its value, whatever the notation.
  let concurrency := fun (limit : String) =>
    "{\"main\":\"w\",\"workflows\":[{\"id\":\"w\",\"placements\":[{\"name\":\"c\",\"policy\":\"stop\"," ++
      "\"node\":{\"type\":\"concurrency\",\"limit\":" ++ limit ++ ",\"tasks\":[],\"output\":\"list\",\"element\":\"T\"}}]}]}"
  for (text, n) in [("2", 2), ("2.0", 2), ("20e-1", 2), ("0.2e1", 2), ("1e1", 10)] do
    let p ← decoded s!"limit {text}" (concurrency text)
    ensure (limits p == [n]) s!"limit {text}: expected {n}, got {limits p}"
  for text in ["2.5", "-1", "1e-1", "1e-1000000000"] do
    decodeRejected s!"limit {text}" "node.limit: expected a natural number" (concurrency text)
  rejected "limit 0.0" "limit must be positive" (← decoded "limit 0.0" (concurrency "0.0"))
  -- A number above `Codec.maxNat` is rejected, and a huge exponent is not expanded.
  let largest ← decoded "limit 2^64-1" (concurrency "18446744073709551615")
  ensure (limits largest == [Codec.maxNat]) s!"limit 2^64-1: got {limits largest}"
  for text in ["18446744073709551616", "1.8446744073709551616e19", "1e20", "7e100", "1e1000000000"] do
    decodeRejected s!"limit {text}" "node.limit: must be at most 18446744073709551615" (concurrency text)
  rejected "limit 0e1000000000" "limit must be positive"
    (← decoded "limit 0e1000000000" (concurrency "0e1000000000"))
  for text in ["1e64", "12.5e65", "-3e64"] do
    parsesLikeLean text text
  let timed ← decoded "timeout" (base ++ ",\"policy\":\"stop\",\"timeout\":{\"callMs\":1.5e3,\"elementMs\":2.50e1}}]}]}")
  ensure ((timed.workflows.flatMap (·.placements)).map (·.timeout) == [{ callMs := some 1500, elementMs := some 25 }])
    "timeout: numbers in any notation"
  IO.println "validate: ok"

end Suimon.Test.Validate
