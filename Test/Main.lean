import Suimon
import Test.Examples
import Test.Artifacts
import Test.Work
import Test.TraceProjection
import Test.TraceText
import Test.Determinism
import Test.OracleConformance
open Lean Suimon Suimon.Test

-- Keep the unrestricted T9 theorem available through the public library.
example : ScheduleDeterminism := schedule_determinism

example (s next : State) (op : Op) (safe : Invariants s) (started : s.started = true)
    (work : op.countsAsWork = true) (accepted : step s op = .ok next) (changed : next ≠ s) : s.hasWork = true :=
  hasWork_complete s next op safe started work accepted changed

example (g : Graph) (ops : List Op) (txn : String) (time : Nat) (s : State) (events : List Trace.Event)
    (recorded : Trace.recordTransaction (.initial g) ops 1 txn time = .ok (s, events)) : Trace.check g events = .ok s :=
  Trace.recordTransaction_roundtrip g ops txn time s events recorded

example (g : Graph) (ops : List Op) (txn : String) (time : Nat) (s : State) (events : List Trace.Event)
    (recorded : Trace.recordTransaction (.initial g) ops 1 txn time = .ok (s, events)) :
    Trace.checkText g (events.map Trace.encodeEvent) = .ok s :=
  Trace.recordTransaction_jsonl_roundtrip g ops txn time s events recorded

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def applyOp (s : State) (op : Op) : IO State := do
  match step s op with
  | .error r => throw (IO.userError s!"{repr op}: {r.code}: {r.message}")
  | .ok next =>
    ensure (invariants next) s!"invariant failed after {repr op}"
    return next

private def reject (s : State) (op : Op) (code : String) : IO Unit :=
  match step s op with
  | .error r => ensure (r.code == code) s!"expected {code}, got {r.code}: {repr op}"
  | .ok _ => throw (IO.userError s!"unexpected acceptance: {repr op}")

private def start (g : Graph) : IO State := do
  match g.validate with
  | .ok _ => applyOp (.initial g) (.start (Explore.inputValues g))
  | .error e => throw (IO.userError s!"test attempted to execute an invalid graph: {e}")
private def auth (node : String) (no : Nat := 1) (now : Nat := 0) (path : Path := []) : Credentials :=
  { «instance» := instanceId path node, attempt := identity [node, identity path, toString no], token := identity ["token", node, identity path, toString no], now }

private def completeLeaf (s : State) (path : Path) (node : String) : IO State := do
  let s ← applyOp s (.activate path node)
  let c := auth node 1 s.now path
  let s ← applyOp s (.claim c "worker")
  let i := (s.instance? c.instance).getD { id := "", node := "", path := [], status := .failed }
  let n := (s.node? path node).getD (leaf "" [] [])
  applyOp s (.complete c (Explore.outputs i n))

private def getInst (s : State) (id : String) : IO Instance :=
  match s.instance? id with | some i => pure i | none => throw (IO.userError s!"missing instance {id}")

private def childPath (s : State) (id : String) : IO Path := do
  let i ← getInst s id
  match currentFrame s i with
  | .ok f => pure f.path
  | .error e => throw (IO.userError e.message)

private def traceOps (g : Graph) (ops : List Op) : IO (State × List Trace.Event) := do
  let mut s := State.initial g
  let mut events := []
  for (op, idx) in ops.zipIdx do
    match Trace.recordTransaction s [op] (events.length + 1) (s!"txn-{idx}") s.now with
    | .ok (next, records) => s := next; events := events ++ records
    | .error r => throw (IO.userError s!"trace generation: {r.code}")
  return (s, events)

private def renumber (events : List Trace.Event) : List Trace.Event :=
  events.zipIdx.map fun (e, idx) => { e with sequence := idx + 1 }

private def graphTests : IO Unit := do
  for (name, g) in examples do
    ensure (g.validate matches .ok _) s!"invalid example: {name}"
    ensure (invariants (.initial g)) s!"invalid initial state: {name}"
    match graphFromJson (toJson g) with
    | .ok decoded => ensure (decoded == g) s!"graph round trip: {name}"
    | .error e => throw (IO.userError e)
  ensure (!(({ body with nodes := body.nodes ++ body.nodes }).validate matches .ok _)) "duplicate nodes"
  ensure (!(({ body with edges := [edge "work" "out" "work" "in"], entries := [] }).validate matches .ok _)) "cycle"
  let bad : Graph := { streaming with edges := [edge "emit" "out" "collect" "in", edge "collect" "out" "each" "in"] }
  ensure (!(bad.validate matches .ok _)) "kind mismatch"
  ensure (!(({ body with entries := [] }).validate matches .ok _)) "unconnected input"
  ensure (branch.validate matches .ok _) "unmerged Branch is valid at root"
  ensure (branch.validate true matches .error _) "unmerged Branch accepted inside a body"
  let escaping := { coalescedBranch with exits := [ref "left" "out", ref "join" "out"] }
  ensure (escaping.validate true matches .error _) "body Branch can escape before Coalesce"
  let invalidSub := { nested with nodes := [{ id := "sub", kind := .subworkflow branch, inputs := [plain "in"], outputs := [plain "left", plain "right"] }] }
  ensure (invalidSub.validate matches .error _) "nested Branch was not checked"

private def leaseTests : IO Unit := do
  let s ← start body
  let s ← applyOp s (.activate [] "work")
  let c := auth "work"
  reject s (.emit c "out" "x") "INVALID_LEASE"
  let s ← applyOp s (.claim c "one")
  reject s (.claim (auth "work" 2) "two") "NOT_READY"
  for op in [.renew { c with now := 3 }, .fail { c with now := 3 } "x" true, .complete { c with now := 3 } [{ port := "out", items := ["x"] }], .emit { c with now := 3 } "out" "x"] do
    reject s op "INVALID_LEASE"
  let s ← applyOp s (.expireLease c.instance 3)
  ensure ((s.attempts.head?.map (·.status)) == some .abandoned) "attempt was not abandoned"
  reject s (.promoteRetry c.instance 3) "RETRY_NOT_DUE"
  let s ← applyOp s (.promoteRetry c.instance 4)
  let c2 := auth "work" 2 4
  let s ← applyOp s (.claim c2 "two")
  reject s (.complete { c with now := 4 } [{ port := "out", items := ["late"] }]) "INVALID_LEASE"
  reject s (.renew { c2 with token := "wrong" }) "INVALID_LEASE"
  reject s (.renew { c2 with now := 3 }) "INVALID_LEASE"
  let s ← applyOp s (.fail c2 "FAILED" true)
  ensure (s.status == .blocked) "retry exhaustion must block"
  let s ← applyOp s (.manualRetry c2.instance)
  let s ← applyOp s (.promoteRetry c2.instance 4)
  let c3 := auth "work" 3 4
  let s ← applyOp s (.claim c3 "three")
  let out := [{ port := "out", items := ["result"] }]
  let s ← applyOp s (.complete c3 out)
  ensure ((← applyOp s (.complete { c3 with now := 99 } out)) == s) "complete redelivery changed state"
  reject s (.complete c3 [{ port := "out", items := ["different"] }]) "INVALID_LEASE"
  reject s (.activate [] "work") "PRECONDITION"
  let s ← applyOp s .idle
  ensure (s.status == .succeeded) "minimal workflow did not succeed"
  for op in [.cancel, .manualRetry c.instance] do
    ensure ((← applyOp s op) == s) "terminal state changed"
  reject s (.emit c "out" "after") "INVALID_LEASE"
  let s ← start body
  let s ← applyOp s (.activate [] "work")
  let s ← applyOp s (.claim c "one")
  let cancelled ← applyOp s .cancel
  ensure (cancelled.status == .cancelled && cancelled.attempts.all (·.status != .running)) "cancel left live attempts"
  let s ← start body
  let s ← applyOp s (.activate [] "work")
  let running ← applyOp s .idle
  ensure (running.status == .running && running.hasWork) "idle blocked a ready instance"

private def idleTests : IO Unit := do
  let s ← start body
  ensure ((← applyOp s .idle).status == .running) "idle missed activation"
  let ready ← applyOp s (.activate [] "work")
  let c := auth "work"
  let claimed ← applyOp ready (.claim c "worker")
  let failed ← applyOp claimed (.fail c "TRANSIENT" true)
  ensure ((← applyOp failed .idle).status == .running) "idle missed future retry promotion"
  let expired ← applyOp claimed (.expireLease c.instance 3)
  ensure ((← applyOp expired .idle).status == .running) "idle blocked retryWait"
  let fatal ← applyOp claimed (.fail c "PERMANENT" false)
  ensure (!fatal.hasWork) "manualRetry or cancel counted as ordinary work"
  ensure ((← applyOp fatal .idle).reason == some "PERMANENT") "idle erased failure reason"
  let s ← start streaming
  let s ← applyOp s (.activate [] "emit")
  let c := auth "emit"
  let s ← applyOp s (.claim c "worker")
  let s ← applyOp s (.emit c "out" "item")
  let s ← applyOp s (.complete c [])
  let s ← applyOp s (.spawn [] "each" "item")
  let parent := instanceId [] "each" (some "item")
  let path ← childPath s parent
  let s ← completeLeaf s path "work"
  ensure ((← applyOp s .idle).status == .running) "idle missed frame collection"
  let s ← applyOp s (.finishSubworkflow parent)
  ensure ((← applyOp s .idle).status == .running) "idle missed EOS propagation"
  let s ← applyOp s (.propagateEos [] "each")
  ensure ((← applyOp s .idle).status == .running) "idle missed AllWait"
  let s ← applyOp s (.fireCollect [] "collect")
  ensure (!(s.hasWork) && (← applyOp s .idle).status == .succeeded) "idle did not finish drained workflow"
  -- A trace may already have used the ID that a naive count-based generator would pick.
  let independent : Graph := {
    nodes := [leaf "a" ["in"] [], leaf "b" ["in"] ["out"]]
    edges := []
    entries := [ref "a" "in", ref "b" "in"]
    exits := [ref "b" "out"] }
  let s ← start independent
  let s ← applyOp s (.activate [] "a")
  let first := { auth "a" with attempt := identity ["attempt", "1"], token := identity ["lease", "0"] }
  let s ← applyOp s (.claim first "worker")
  let s ← applyOp s (.complete first [])
  let s ← applyOp s (.activate [] "b")
  ensure (s.hasWork && (← applyOp s .idle).status == .running) "ID collision hid ready work"
  -- All of these states are reached through operations, not record updates.
  let s ← start independent
  let s ← applyOp s (.activate [] "a")
  let s ← applyOp s (.activate [] "b")
  let s ← applyOp s (.claim (auth "a") "worker")
  let s ← applyOp s (.claim (auth "b") "worker")
  let s ← applyOp s (.fail (auth "a") "A_FAILED" false)
  let s ← applyOp s (.fail (auth "b") "B_FAILED" false)
  let s ← applyOp s (.manualRetry (instanceId [] "a"))
  let s ← applyOp s (.promoteRetry (instanceId [] "a") 0)
  let s ← applyOp s (.claim (auth "a" 2) "worker")
  let s ← applyOp s (.complete (auth "a" 2) [])
  let stopped ← applyOp s .idle
  ensure (stopped.reason == some "DEPENDENCIES_UNRESOLVED" && !stopped.hasWork) "partial recovery did not stop"
  let s ← applyOp stopped (.manualRetry (instanceId [] "b"))
  ensure (s.status == .running) "dependency reason incorrectly prevented manualRetry"
  -- A user-supplied error code must not trigger a hidden resume path.
  let s ← start independent
  let s ← applyOp s (.activate [] "a")
  let s ← applyOp s (.activate [] "b")
  let s ← applyOp s (.claim (auth "a") "worker")
  let s ← applyOp s (.fail (auth "a") "DEPENDENCIES_UNRESOLVED" false)
  let s ← applyOp s (.claim (auth "b") "worker")
  ensure (s.status == .blocked) "failure code collision triggered automatic resume"
  let c := auth "work"
  let s ← start body
  let s ← applyOp s (.activate [] "work")
  let s ← applyOp s (.claim c "worker")
  let outputs := [{ port := "out", items := ["result"] }]
  let s ← applyOp s (.complete c outputs)
  ensure (!s.hasWork && (← applyOp s (.complete c outputs)) == s) "idempotent receipt counted as work"
  ensure ((← applyOp s .idle).status == .succeeded) "receipt prevented termination"

private def fireCoalesce (s : State) (path : Path) (arm : String) (node : String := "join") : IO State := do
  let some c := (s.incoming path node).find? (·.edge.dst.port == arm)
    | throw (IO.userError "missing Coalesce input")
  let some item := c.pendingItems.head? | throw (IO.userError "missing Coalesce item")
  reject s (.fireCoalesce path node c.id "wrong") "PRECONDITION"
  let s ← applyOp s (.fireCoalesce path node c.id item)
  ensure ((s.outgoing path node "out").all (fun c => c.items == [item] && c.closed)) "Coalesce changed the selected value"
  reject s (.fireCoalesce path node c.id item) "PRECONDITION"
  return s

private def coalesceTests : IO Unit := do
  for arm in ["left", "right"] do
    let other := if arm == "left" then "right" else "left"
    let s ← start coalescedBranch
    let s ← applyOp s (.fireBranch [] "choose" arm)
    let s ← applyOp s (.skip [] other)
    reject s (.skip [] "join") "NOT_SKIPPABLE"
    let s ← completeLeaf s [] arm
    let s ← fireCoalesce s [] arm
    ensure ((← applyOp s .idle).status == .succeeded) "Coalesce root did not finish"
    let s ← start coalesceLoop
    let s ← applyOp s (.activate [] "sub")
    let sub := instanceId [] "sub"
    let subPath ← childPath s sub
    let s ← applyOp s (.activate subPath "loop")
    let parent := instanceId subPath "loop"
    let path ← childPath s parent
    let s ← applyOp s (.fireBranch path "choose" arm)
    let s ← completeLeaf s path arm
    let s ← fireCoalesce s path arm
    reject s (.loopIterate parent true) "BODY_NOT_FINISHED"
    reject s (.finishSubworkflow sub) "BODY_NOT_FINISHED"
    let s ← applyOp s (.skip path other)
    ensure ((← applyOp s .idle).status == .running) "idle missed completed Loop body"
    let s ← applyOp s (.loopIterate parent true)
    let s ← applyOp s (.finishSubworkflow sub)
    ensure ((← applyOp s .idle).status == .succeeded) "Branch/Coalesce body was not recovered"
  -- These graphs must be rejected before execution, in root and body positions.
  let conflicting : Graph := {
    nodes := [{ id := "join", kind := .coalesce, inputs := [plain "left", plain "right"], outputs := [plain "out"] }]
    edges := []
    entries := [ref "join" "left", ref "join" "right"]
    exits := [ref "join" "out"] }
  let duplicateEdges := coalescedBranch.edges.map (fun e =>
    if e.src == (ref "choose" "right") then { e with src := ref "choose" "left" } else e)
  let duplicateArm : Graph := { coalescedBranch with edges := duplicateEdges }
  let mixed : Graph := {
    nodes := [{ id := "a", kind := .branch ["left", "right"], inputs := [plain "in"], outputs := [plain "left", plain "right"] },
      { id := "b", kind := .branch ["left", "right"], inputs := [plain "in"], outputs := [plain "left", plain "right"] },
      { id := "join", kind := .coalesce, inputs := [plain "a", plain "b"], outputs := [plain "out"] }]
    edges := [edge "a" "left" "join" "a", edge "b" "right" "join" "b"]
    entries := [ref "a" "in", ref "b" "in"]
    exits := [ref "join" "out"] }
  -- Each input requires incompatible selections from two independent Branches.
  let crossed : Graph := {
    nodes := mixed.nodes.take 2 ++ [leaf "left" ["a", "b"] ["out"], leaf "right" ["a", "b"] ["out"],
      { id := "join", kind := .coalesce, inputs := [plain "left", plain "right"], outputs := [plain "out"] }]
    edges := [edge "a" "left" "left" "a", edge "b" "left" "left" "b", edge "a" "right" "right" "a",
      edge "b" "right" "right" "b", edge "left" "out" "join" "left", edge "right" "out" "join" "right"]
    entries := mixed.entries
    exits := mixed.exits }
  -- AllWait produces a list even for a skipped stream, so these inputs are not exclusive.
  let collected : Graph := {
    nodes := branch.nodes.take 1 ++ [emitter "left", emitter "right",
      { id := "leftAll", kind := .collect, inputs := [stream "in"], outputs := [plain "out"] },
      { id := "rightAll", kind := .collect, inputs := [stream "in"], outputs := [plain "out"] },
      { id := "join", kind := .coalesce, inputs := [plain "left", plain "right"], outputs := [plain "out"] }]
    edges := [edge "choose" "left" "left" "in", edge "choose" "right" "right" "in",
      edge "left" "out" "leftAll" "in", edge "right" "out" "rightAll" "in",
      edge "leftAll" "out" "join" "left", edge "rightAll" "out" "join" "right"]
    entries := branch.entries
    exits := [ref "join" "out"] }
  for graph in [independentCoalesce, conflicting, duplicateArm, mixed, crossed, collected] do
    ensure (graph.validate matches .error _) "invalid Coalesce accepted at root"
    ensure (graph.validate true matches .error _) "invalid Coalesce accepted inside body"
  ensure (sharedCoalesce.validate true matches .ok _) "shared plain context rejected"
  ensure (nestedCoalesce.validate true matches .ok _) "nested exclusive branches rejected"
  let s ← start sharedCoalesce
  let s ← completeLeaf s [] "context"
  let s ← applyOp s (.fireBranch [] "choose" "left")
  let s ← completeLeaf s [] "left"
  let s ← fireCoalesce s [] "left"
  let s ← applyOp s (.skip [] "right")
  ensure ((← applyOp s .idle).status == .succeeded) "shared context did not finish"
  for arm in ["up", "down"] do
    let other := if arm == "up" then "down" else "up"
    let s ← start nestedCoalesce
    let s ← applyOp s (.fireBranch [] "choose" "left")
    let s ← applyOp s (.fireBranch [] "left" arm)
    let s ← completeLeaf s [] arm
    let some input := (s.incoming [] "innerJoin").find? (·.edge.dst.port == arm)
      | throw (IO.userError "missing nested join input")
    let some item := input.pendingItems.head? | throw (IO.userError "missing nested join item")
    let s ← applyOp s (.fireCoalesce [] "innerJoin" input.id item)
    let s ← fireCoalesce s [] "left"
    let s ← applyOp s (.skip [] other)
    let s ← applyOp s (.skip [] "right")
    ensure ((← applyOp s .idle).status == .succeeded) "nested exclusive branches did not finish"

private def stagedCoalesceTests : IO Unit := do
  ensure (stagedCoalesce.validate true matches .ok _) "sequential joins rejected inside body"
  let crossedEdges := stagedCoalesce.edges.map (fun e =>
    if e.src == (ref "secondChoice" "right") then { e with src := ref "firstChoice" "right" } else e)
  let crossed := { stagedCoalesce with edges := crossedEdges }
  ensure (crossed.validate matches .error _) "Coalesce accepted an arm from the previous stage"
  ensure (crossed.validate true matches .error _) "body Coalesce accepted an arm from the previous stage"
  let wrapped : Graph := {
    nodes := [{ id := "sub", kind := .subworkflow stagedCoalesce, inputs := [plain "in"], outputs := [plain "out"] }]
    edges := []
    entries := [ref "sub" "in"]
    exits := [ref "sub" "out"] }
  for inBody in [false, true] do
    for first in ["left", "right"] do
      for second in ["left", "right"] do
        let s ← start (if inBody then wrapped else stagedCoalesce)
        let (s, path) ← if inBody then do
          let s ← applyOp s (.activate [] "sub")
          pure (s, ← childPath s (instanceId [] "sub"))
        else pure (s, [])
        reject s (.fireBranch path "secondChoice" second) "PRECONDITION"
        let s ← applyOp s (.fireBranch path "firstChoice" first)
        reject s (.fireBranch path "secondChoice" second) "PRECONDITION"
        let s ← fireCoalesce s path first "firstJoin"
        let s ← applyOp s (.fireBranch path "secondChoice" second)
        let s ← fireCoalesce s path second "secondJoin"
        let s ← if inBody then applyOp s (.finishSubworkflow (instanceId [] "sub")) else pure s
        ensure ((← applyOp s .idle).status == .succeeded) s!"sequential joins failed: {inBody}/{first}/{second}"

private def plainTests : IO Unit := do
  let s ← start diamond
  reject s (.activate [] "b") "PRECONDITION"
  let s ← completeLeaf s [] "a"
  let s ← completeLeaf s [] "b"
  reject s (.fireWaitAll [] "join") "PRECONDITION"
  let s ← completeLeaf s [] "c"
  let s ← applyOp s (.fireWaitAll [] "join")
  reject s (.fireWaitAll [] "join") "PRECONDITION"
  ensure ((← applyOp s .idle).status == .succeeded) "diamond failed"
  let s ← start nShape
  let s ← completeLeaf s [] "a"
  reject s (.activate [] "c") "PRECONDITION"
  let s ← completeLeaf s [] "b"
  let s ← completeLeaf s [] "c"
  ensure ((← applyOp s .idle).status == .succeeded) "N shape failed"
  for arm in ["left", "right"] do
    let other := if arm == "left" then "right" else "left"
    let s ← start branch
    let s ← applyOp s (.fireBranch [] "choose" arm)
    ensure ((s.outgoing [] "choose" arm).all (·.items.length == 1)) "chosen branch has no item"
    ensure ((s.outgoing [] "choose" other).all (fun c => c.items.isEmpty && c.closed)) "unchosen branch received item"
    let s ← applyOp s (.skip [] other)
    let s ← completeLeaf s [] arm
    ensure ((← applyOp s .idle).status == .succeeded) "branch failed"

private def streamTests : IO Unit := do
  let s ← start streaming
  let s ← applyOp s (.activate [] "emit")
  let c := auth "emit"
  let s ← applyOp s (.claim c "emitter")
  let s ← applyOp s (.emit c "out" "item-1")
  ensure ((← applyOp s (.emit c "out" "item-1")) == s) "retry emit was not deduplicated"
  let s ← applyOp s (.spawn [] "each" "item-1")
  ensure ((s.incoming [] "each").all (! ·.closed)) "spawn waited for EOS"
  let parent := instanceId [] "each" (some "item-1")
  let path ← childPath s parent
  let s ← completeLeaf s path "work"
  let s ← applyOp s (.finishSubworkflow parent)
  reject s (.propagateEos [] "each") "INPUT_NOT_DRAINED"
  reject s (.fireCollect [] "collect") "COLLECT_NOT_READY"
  let s ← applyOp s (.complete c [])
  reject s (.emit c "out" "after-eos") "INVALID_LEASE"
  reject s (.spawn [] "each" "item-1") "PRECONDITION"
  let s ← applyOp s (.propagateEos [] "each")
  let s ← applyOp s (.fireCollect [] "collect")
  reject s (.fireCollect [] "collect") "COLLECT_NOT_READY"
  ensure ((← applyOp s .idle).status == .succeeded) "stream pipeline failed"
  -- ForEach closes correctly for an empty stream.
  let s ← start streaming
  let s ← applyOp s (.activate [] "emit")
  let s ← applyOp s (.claim c "emitter")
  let s ← applyOp s (.complete c [])
  let s ← applyOp s (.propagateEos [] "each")
  let s ← applyOp s (.fireCollect [] "collect")
  ensure ((← applyOp s .idle).status == .succeeded) "empty stream failed"

private def concurrencyTests : IO Unit := do
  let limitedBody : Graph := { body with nodes := [{ leaf "work" ["in"] ["out"] with
    kind := .leaf { maxAttempts := 2, leaseSeconds := 3, retrySeconds := 1 } 1 }] }
  let graph : Graph := { streaming with nodes := streaming.nodes.map fun n =>
    if n.id == "each" then { n with kind := .forEach limitedBody } else n }
  let s ← start graph
  let s ← applyOp s (.activate [] "emit")
  let emitterAuth := auth "emit"
  let s ← applyOp s (.claim emitterAuth "emitter")
  let s ← applyOp s (.emit emitterAuth "out" "one")
  let s ← applyOp s (.emit emitterAuth "out" "two")
  let s ← applyOp s (.spawn [] "each" "one")
  let s ← applyOp s (.spawn [] "each" "two")
  let one := instanceId [] "each" (some "one")
  let two := instanceId [] "each" (some "two")
  let path1 ← childPath s one
  let path2 ← childPath s two
  let s ← applyOp s (.activate path1 "work")
  let s ← applyOp s (.activate path2 "work")
  let c1 := auth "work" 1 0 path1
  let c2 := auth "work" 1 0 path2
  let s ← applyOp s (.claim c1 "one")
  reject s (.claim c2 "two") "CONCURRENCY_LIMIT"
  let s ← applyOp s (.complete c1 [{ port := "out", items := ["one-result"] }])
  let s ← applyOp s (.claim c2 "two")
  let s ← applyOp s (.complete c2 [{ port := "out", items := ["two-result"] }])
  let s ← applyOp s (.finishSubworkflow one)
  let s ← applyOp s (.finishSubworkflow two)
  -- A restarted yielding node redelivers the first item without spawning a second body.
  let s ← applyOp s (.expireLease emitterAuth.instance 3)
  let s ← applyOp s (.promoteRetry emitterAuth.instance 4)
  let retryAuth := auth "emit" 2 4
  let s ← applyOp s (.claim retryAuth "replacement")
  let repeated ← applyOp s (.emit retryAuth "out" "one")
  ensure (repeated == s) "repeated yield changed already consumed stream"
  let s ← applyOp s (.complete retryAuth [])
  let s ← applyOp s (.propagateEos [] "each")
  let s ← applyOp s (.fireCollect [] "collect")
  ensure ((← applyOp s .idle).status == .succeeded) "concurrent body/retry test failed"

private def mergeFilterTests : IO Unit := do
  let s ← start merging
  let mut s := s
  for n in ["a", "b"] do
    s ← applyOp s (.activate [] n)
    let c := auth n
    s ← applyOp s (.claim c "worker")
    s ← applyOp s (.emit c "out" "shared-id")
    s ← applyOp s (.complete c [])
  let channels := s.incoming [] "merge"
  for channel in channels do
    s ← applyOp s (.fireMerge [] "merge" channel.id "shared-id")
  s ← applyOp s (.propagateEos [] "merge")
  ensure ((s.incoming [] "collect").all (·.items.length == 2)) "merge lost an occurrence"
  s ← applyOp s (.fireCollect [] "collect")
  ensure ((← applyOp s .idle).status == .succeeded) "merge failed"
  s ← start filtering
  s ← applyOp s (.activate [] "emit")
  let c := auth "emit"
  s ← applyOp s (.claim c "worker")
  s ← applyOp s (.emit c "out" "drop")
  s ← applyOp s (.emit c "out" "keep")
  s ← applyOp s (.fireFilter [] "filter" "drop" false)
  s ← applyOp s (.fireFilter [] "filter" "keep" true)
  s ← applyOp s (.complete c [])
  s ← applyOp s (.propagateEos [] "filter")
  ensure ((s.incoming [] "collect").all (·.items == ["keep"])) "filter result mismatch"
  s ← applyOp s (.fireCollect [] "collect")
  ensure ((← applyOp s .idle).status == .succeeded) "filter failed"
  ensure (derivedItem "list" [] "collect" (sortedItems ["a", "b"]) ==
    derivedItem "list" [] "collect" (sortedItems ["b", "a"])) "AllWait depends on arrival order"

private def loopTests : IO Unit := do
  for done in [true, false] do
    let s ← start loop
    let s ← applyOp s (.activate [] "loop")
    let parent := instanceId [] "loop"
    let path ← childPath s parent
    let s ← completeLeaf s path "work"
    let s ← applyOp s (.loopIterate parent false)
    let path ← childPath s parent
    let s ← completeLeaf s path "work"
    let s ← applyOp s (.loopIterate parent done)
    let i ← getInst s parent
    ensure (i.iteration == 2) "loop counter exceeded limit"
    if done then
      ensure ((← applyOp s .idle).status == .succeeded) "bounded loop failed"
    else
      ensure (s.status == .blocked && s.reason == some "LOOP_LIMIT") "loop exhaustion did not block"
      reject s (.loopIterate parent true) "NOT_WAITING_BODY"
      ensure (!s.hasWork && (← applyOp s .idle).reason == some "LOOP_LIMIT") "idle erased loop limit"
      let s ← applyOp s (.manualRetry parent)
      let i ← getInst s parent
      ensure (i.iteration == 3 && i.extraIterations == 1 && s.status == .running) "loop retry did not increase the limit"
      ensure ((s.frames.filter (fun f => f.owner == some parent && f.closed)).length == 2) "loop retry reopened old iterations"
      reject s (.manualRetry parent) "NOT_FAILED"
      let path ← childPath s parent
      let s ← completeLeaf s path "work"
      let s ← applyOp s (.loopIterate parent false)
      ensure (s.status == .blocked && s.reason == some "LOOP_LIMIT") "extended loop failed to stop"
      let s ← applyOp s (.manualRetry parent)
      let path ← childPath s parent
      let s ← completeLeaf s path "work"
      let s ← applyOp s (.loopIterate parent true)
      let i ← getInst s parent
      ensure (i.iteration == 4 && i.extraIterations == 2) "repeated retry lost its limit"
      ensure ((← applyOp s .idle).status == .succeeded) "manually retried loop did not finish"
  let s ← start nested
  let s ← applyOp s (.activate [] "sub")
  let sub := instanceId [] "sub"
  let path ← childPath s sub
  let s ← applyOp s (.activate path "loop")
  let parent := instanceId path "loop"
  let inner ← childPath s parent
  let s ← completeLeaf s inner "work"
  let s ← applyOp s (.loopIterate parent true)
  let s ← applyOp s (.finishSubworkflow sub)
  ensure ((← applyOp s .idle).status == .succeeded) "nested Sub failed"

private def minimalOps : List Op := [
  .start (Explore.inputValues minimal), .activate [] "work", .claim (auth "work") "worker", .complete (auth "work") [{ port := "out", items := ["result"] }], .idle]

private def coalesceOps : List Op := [
  .start (Explore.inputValues coalescedBranch), .fireBranch [] "choose" "right",
  .activate [] "right", .claim (auth "right") "worker",
  .complete (auth "right") [{ port := "out", items := ["chosen"] }],
  .fireCoalesce [] "join" (identity ["edge", "3"]) "chosen", .skip [] "left", .idle]

private def loopRetryOps : List Op := Id.run do
  let parent := instanceId [] "loop"
  let mut ops := [.start (Explore.inputValues loop), .activate [] "loop"]
  for iteration in [1, 2, 3] do
    if iteration == 3 then ops := ops ++ [.manualRetry parent]
    let path := [identity [parent, toString iteration]]
    let c := auth "work" 1 0 path
    ops := ops ++ [.activate path "work", .claim c "worker",
      .complete c [{ port := "out", items := [s!"result-{iteration}"] }],
      .loopIterate parent (iteration == 3)]
  return ops ++ [.idle]

private def traceTests : IO Unit := do
  for (graph, ops) in [(coalescedBranch, coalesceOps), (loop, loopRetryOps)] do
    let (state, events) ← traceOps graph ops
    ensure (state.status == .succeeded) "new-operation trace did not succeed"
    let parsed ← events.mapM fun e =>
      match Trace.parseEvent (toJson e).compress with
      | .ok event => pure event
      | .error error => throw (IO.userError error)
    match Trace.check graph parsed with
    | .ok replayed => ensure (state == replayed) "Coalesce/Loop retry replay mismatch"
    | .error d => throw (IO.userError (toJson d).compress)
  let (state, events) ← traceOps minimal minimalOps
  match Trace.check minimal events with
  | .ok replayed => ensure (state == replayed) "replay differs from original"
  | .error d => throw (IO.userError (toJson d).compress)
  for e in events do
    match fromJson? (α := Trace.Event) (toJson e) with
    | .ok e' => ensure (e == e') "event roundtrip"
    | .error msg => throw (IO.userError msg)
  let missing := renumber (events.filter fun e => !(e.type == "attempt.started"))
  ensure ((Trace.check minimal missing) matches .error _) "missing claim accepted"
  let forged := events.map fun e => if e.type == "token.placed" && e.op.isNone then
    { e with data := Json.mkObj [("forged", toJson true)] } else e
  ensure ((Trace.check minimal forged) matches .error _) "forged token accepted"
  let torn := events.dropLast
  ensure ((Trace.check minimal torn) matches .error _) "torn transaction accepted"
  let (_, durable) ← traceOps minimal (minimalOps.take 4)
  match Trace.recover minimal torn, Trace.check minimal durable with
  | .ok a, .ok b => ensure (a == b) "recovery included uncommitted suffix"
  | _, _ => throw (IO.userError "recovery failed")
  let initial := State.initial minimal
  for (ops, txn, time, code) in [
      ([], "empty", 0, "EMPTY_TRANSACTION"),
      (minimalOps.take 1, "", 0, "EMPTY_TRANSACTION_ID"),
      (minimalOps.take 3, "old-clock", 1, "CLOCK_REGRESSION")] do
    match Trace.recordTransaction initial ops 1 txn time with
    | .error r => ensure (r.code == code) s!"unexpected recorder rejection: {r.code}"
    | .ok _ => throw (IO.userError s!"recorder accepted {code}")
  match Trace.recordTransaction initial (minimalOps.take 3) 1 "atomic" 0 with
  | .error r => throw (IO.userError r.code)
  | .ok (state, events) =>
    match Trace.check minimal events with
    | .ok s => ensure (s == state) "multi-command transaction failed"
    | .error d => throw (IO.userError (toJson d).compress)
  for seed in List.range 30 do
    match Explore.generate streaming { depth := 8 } seed 25 with
    | .error r => throw (IO.userError r.code)
    | .ok (s, trace) =>
      match Trace.check streaming trace with
      | .ok replayed => ensure (s == replayed) "generated replay mismatch"
      | .error d => throw (IO.userError (toJson d).compress)

private def fixtureTests : IO Unit := do
  for (name, graph) in examples do
    let text ← IO.FS.readFile s!"Test/graphs/{name}.json"
    match Json.parse text with
    | .error e => throw (IO.userError e)
    | .ok json => ensure (json == toJson graph) s!"stale graph fixture: {name}"
  let (_, events) ← traceOps minimal minimalOps
  let text ← IO.FS.readFile "Test/traces/minimal.jsonl"
  let expected := String.intercalate "\n" (events.map (fun e => (toJson e).compress)) ++ "\n"
  ensure (text == expected) "stale minimal trace fixture"

private def writeFixtures : IO Unit := do
  for (name, graph) in examples do IO.FS.writeFile s!"Test/graphs/{name}.json" ((toJson graph).pretty ++ "\n")
  let (_, events) ← traceOps minimal minimalOps
  IO.FS.writeFile "Test/traces/minimal.jsonl" (String.intercalate "\n" (events.map (fun e => (toJson e).compress)) ++ "\n")
  let broken := renumber (events.filter fun e => e.type != "attempt.started")
  IO.FS.writeFile "Test/traces/missing-attempt.jsonl" (String.intercalate "\n" (broken.map (fun e => (toJson e).compress)) ++ "\n")
  let (_, prefixEvents) ← traceOps minimal (minimalOps.take 4)
  let extra : Trace.Event := {
    sequence := prefixEvents.length + 1, txn := "illegal-emit", recorded_at := 0, type := "token.placed", op := some (.emit (auth "work") "out" "after-eos") }
  let broken := prefixEvents ++ [extra, Trace.commitEvent (prefixEvents.length + 2) "illegal-emit" 0]
  IO.FS.writeFile "Test/traces/after-eos.jsonl" (String.intercalate "\n" (broken.map (fun e => (toJson e).compress)) ++ "\n")
  for (name, graph, ops) in [("coalesce", coalescedBranch, coalesceOps), ("loop-retry", loop, loopRetryOps)] do
    let (_, events) ← traceOps graph ops
    IO.FS.writeFile s!"Test/traces/{name}.jsonl" (String.intercalate "\n" (events.map (fun e => (toJson e).compress)) ++ "\n")

def main (args : List String) : IO Unit := do
  for (name, test) in [("graph", graphTests), ("lease/retry/cancel", leaseTests), ("idle / reachable recovery", idleTests), ("Branch / Coalesce / body", coalesceTests), ("Coalesce / Branch / Coalesce stages", stagedCoalesceTests), ("逐次 / Concurrency / Branch", plainTests), ("yield / ForEach / AllWait", streamTests), ("ノード種別ごとの全体上限 / yield 再送", concurrencyTests), ("Merge / Filter / AllWait", mergeFilterTests), ("Loop / Sub / manualRetry", loopTests), ("trace/recovery/generation", traceTests)] do
    test
    IO.println s!"ok: {name}"
  if args == ["--write-fixtures"] then writeFixtures else fixtureTests
  Artifacts.run
  Work.run
  TraceProjection.run
  TraceText.run
  Determinism.run
  OracleConformance.run
