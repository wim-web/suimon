import Suimon.Workflow

/-! Resource admission for executable validation. The structural specification and its
proofs remain independent of these operational ceilings. Keep these values and the
work estimate in sync with implementations/go/src/limits.go. -/

namespace Suimon.Limits

def maxBytes : Nat := 1048576
def maxJSONDepth : Nat := 64
def maxTypeDepth : Nat := 32
def maxNameBytes : Nat := 256
def maxWorkflows : Nat := 128
def maxDeclarations : Nat := 1024
def maxPlacements : Nat := 1024
def maxConnections : Nat := 4096
def maxTasks : Nat := 1024
def maxArms : Nat := 1024
def maxWork : Nat := 1000000000

def check (name : String) (count limit : Nat) : Except String Unit :=
  if count ≤ limit then pure ()
  else throw s!"definition: {name} limit exceeded (max {limit})"

/-- Count only up to the limit plus one, including on programmatically built lists. --/
def count : Nat → List α → Nat
  | _, [] => 0
  | 0, _ :: _ => 1
  | n + 1, _ :: rest => 1 + count n rest

def text (s : String) : Except String Unit := check "name byte" s.utf8ByteSize maxNameBytes

def typeAt : Nat → ValueType → Except String Unit
  | _, .named s => text s
  | 0, .list _ => check "type depth" (maxTypeDepth + 1) maxTypeDepth
  | n + 1, .list t => typeAt n t

def type (t : ValueType) : Except String Unit := typeAt maxTypeDepth t

def body : Body → Except String Unit
  | .function id => text id
  | .workflow id output => do text id; text output

def ref : TransformRef → Except String Unit
  | .discard => pure ()
  | .declared id => text id

/-- Run before recursive JSON parsing; quoted brackets and escaped quotes do not nest. --/
def checkTextWithin (bytes nesting : Nat) (s : String) : Except String Unit := do
  check "byte" s.utf8ByteSize bytes
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  for c in s do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == '{' || c == '[' then
      depth := depth + 1
      check "JSON depth" depth nesting
    else if c == '}' || c == ']' then depth := depth - 1

def checkText (s : String) : Except String Unit := checkTextWithin maxBytes maxJSONDepth s

end Suimon.Limits

namespace Suimon

/-- Reject oversized inputs before deriving kinds, comparing types, or scanning graphs.
The work estimate bounds the repeated list scans of the reference implementation;
it is an admission policy, not a duration in milliseconds. --/
def Definition.checkResources (p : Definition) : Except String Unit := do
  let wc := Limits.count Limits.maxWorkflows p.workflows
  let decls := Limits.count Limits.maxDeclarations p.functions +
    Limits.count Limits.maxDeclarations p.judges + Limits.count Limits.maxDeclarations p.transforms
  Limits.check "workflow" wc Limits.maxWorkflows
  Limits.check "declaration" decls Limits.maxDeclarations
  Limits.text p.main
  for f in p.functions do
    Limits.text f.id
    for t in f.input do Limits.type t
    Limits.type f.output.element
  for j in p.judges do Limits.text j.id; Limits.type j.input
  for t in p.transforms do Limits.text t.id; Limits.type t.input; Limits.type t.output
  let mut placements := 0
  let mut connections := 0
  let mut tasks := 0
  let mut arms := 0
  for w in p.workflows do
    placements := placements + Limits.count Limits.maxPlacements w.placements
    connections := connections + Limits.count Limits.maxConnections w.connections
    Limits.check "placement" placements Limits.maxPlacements
    Limits.check "connection" connections Limits.maxConnections
    Limits.text w.id
    for e in w.input do Limits.type e.valueType; Limits.text e.placement
    for pl in w.placements do
      Limits.text pl.name
      match pl.control with
      | .call b => Limits.body b
      | .branch judge names =>
        Limits.text judge
        arms := arms + Limits.count Limits.maxArms names
        Limits.check "arm" arms Limits.maxArms
        for a in names do Limits.text a
      | .waitStream t | .merge t => Limits.type t
      | .concurrency c =>
        for t in c.input do Limits.type t
        Limits.type c.element
        tasks := tasks + Limits.count Limits.maxTasks c.tasks
        Limits.check "task" tasks Limits.maxTasks
        for t in c.tasks do
          Limits.text t.name
          Limits.body t.body
          for r in t.input do Limits.ref r
          for o in t.output do Limits.text o
    for c in w.connections do
      Limits.text c.source
      Limits.text c.target
      Limits.ref c.transform
      for a in c.arm do Limits.text a
  let d := decls + wc
  let n := d + placements + connections + tasks + arms + 1
  let mut work := n*n + wc*wc*wc*(placements+tasks+1)
  for w in p.workflows do
    let v := w.placements.length
    let e := w.connections.length
    work := work + (2*v+2*e+1)*(v+1)*(v*(v+e+d+1)+e)
    work := work + v*v*(v*e+v)
    work := work + (e+tasks+v+1)*(wc+1)*(wc+placements+d+1)
  work := work + arms * connections
  Limits.check "validation work" work Limits.maxWork

end Suimon
