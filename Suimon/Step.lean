import Suimon.Invariants
import Suimon.Candidates
def Option.toExcept (o : Option α) (error : ε) : Except ε α :=
  match o with
  | some a => .ok a
  | none => .error error
namespace Suimon
open Lean

structure Reject where
  code : String
  message : String
  deriving DecidableEq, BEq, Repr, ToJson, FromJson

abbrev Result := Except Reject

def require (ok : Bool) (code : String) (message : String := code) : Result Unit :=
  if ok then .ok () else .error { code, message }

def getInstance (s : State) (id : InstanceId) : Result Instance :=
  (s.instance? id).toExcept { code := "UNKNOWN_INSTANCE", message := id }

def getNode (s : State) (path : Path) (id : NodeId) : Result Node := do
  let f ← (s.frame? path).toExcept { code := "UNKNOWN_FRAME", message := identity path }
  require (!f.closed) "CLOSED_FRAME"
  (f.graph.node? id).toExcept { code := "UNKNOWN_NODE", message := id }

def setInstance (s : State) (i : Instance) : State :=
  { s with instances := s.instances.map (fun j => if j.id == i.id then i else j) }

def setAttempt (s : State) (id : AttemptId) (status : AttemptStatus) : State :=
  { s with attempts := s.attempts.map (fun a => if a.id == id then { a with status } else a) }

def freshInstance (s : State) (i : Instance) : Result State := do
  require (!s.instances.any (fun j => j.id == i.id || instanceKey j == instanceKey i)) "DUPLICATE_INSTANCE"
  return { s with instances := s.instances ++ [i] }

/-- Deduplicate against the full history, including consumed items. --/
def placeToken (c : Channel) (t : Token) : Result Channel := do
  require (!c.closed) "AFTER_EOS" c.id
  if c.placed.contains t then return c
  require (c.kind != .plain || t == .eos || c.items.isEmpty) "PLAIN_CARDINALITY"
  return { c with placed := c.placed ++ [t] }

/-- After EOS even duplicates are rejected; placement does not change consumption. --/
def place (s : State) (ids : List String) (t : Token) : Result State := do
  let cs ← s.channels.mapM fun c => if ids.contains c.id then placeToken c t else pure c
  return { s with channels := cs }

def putOutput (s : State) (path : Path) (node port : String) (t : Token) : Result State :=
  place s ((s.outgoing path node port).map (·.id)) t

def closeOutputs (s : State) (path : Path) (n : Node) : Result State :=
  n.outputs.foldlM (fun s p => putOutput s path n.id p.name .eos) s

def placeOutputs (s : State) (path : Path) (node : NodeId) (outputs : List Output) : Result State :=
  outputs.foldlM (fun state output =>
    output.items.foldlM (fun state item => putOutput state path node output.port (.item item)) state) s

def placeBodyOutputs (s : State) (path : Path) (n : Node) (items : List ItemId) : Result State :=
  (n.outputs.zip items).foldlM (fun state (p, item) => putOutput state path n.id p.name (.item item)) s

def startInputs (s : State) (inputs : List Input) : Result State :=
  inputs.foldlM (fun state input => do
    let channels := state.channels.filter (fun c => c.path.isEmpty && c.entry && c.edge.dst == input.entry)
    require (unique input.items && channels.all (fun c => c.kind != .plain || input.items.length == 1)) "INVALID_INPUT"
    let state ← input.items.foldlM (fun state item => place state (channels.map (·.id)) (.item item)) state
    place state (channels.map (·.id)) .eos) s

def consume (s : State) (channel : String) (who : InstanceId) (expected : Option ItemId := none) : Result State := do
  let c ← (s.channels.find? (·.id == channel)).toExcept { code := "UNKNOWN_CHANNEL", message := channel }
  let t ← c.pending.head?.toExcept { code := "NO_TOKEN", message := channel }
  match expected, t with
  | some x, .item y => require (x == y) "WRONG_ITEM"
  | some _, .eos => require false "EXPECTED_ITEM"
  | _, _ => pure ()
  let audit := match t with
    | .item item => [{ channel, index := c.consumed, item, byInstance := who : Consumption }]
    | .eos => []
  return { s with
    channels := s.channels.map (fun d => if d.id == c.id then { d with consumed := d.consumed + 1 } else d)
    consumed := s.consumed ++ audit }

def consumeRest (s : State) (c : Channel) (who : InstanceId) : Result State :=
  c.pending.foldlM (fun s _ => consume s c.id who) s

def consumeChannels (s : State) (channels : List Channel) (who : InstanceId) : Result State :=
  channels.foldlM (fun state c => consumeRest state c who) s

def decision (s : State) (key value : String) : Result State := do
  match s.decisions.find? (·.key == key) with
  | some d =>
    require (d.value == value) "NONDETERMINISTIC_ORACLE"
    return s
  | none => return { s with decisions := s.decisions ++ [{ key, value }] }

def leafPolicy (n : Node) : Result (RetryPolicy × Nat) :=
  match n.kind with
  | .leaf r c => .ok (r, c)
  | _ => .error { code := "NOT_LEAF", message := n.id }

def plainInputs (s : State) (path : Path) (n : Node) : Result (List (PortName × ItemId)) := do
  require (allKind n.inputs .plain) "NOT_PLAIN"
  n.inputs.mapM fun p => do
    let c ← ((s.incoming path n.id).find? (·.edge.dst.port == p.name)).toExcept
      { code := "MISSING_INPUT", message := p.name }
    require (c.closed) "UPSTREAM_NOT_FINISHED"
    require (c.entry || (s.nodeInstance? path c.edge.src.node).any (·.status == .succeeded))
      "UPSTREAM_NOT_SUCCEEDED"
    match c.pending with
    | .item id :: _ => return (p.name, id)
    | _ => throw { code := "INPUT_NOT_READY", message := c.id }

def consumeInputs (s : State) (path : Path) (node : NodeId) (who : InstanceId) : Result State :=
  consumeChannels s (s.incoming path node) who

def makeInstance (path : Path) (n : Node) (status : InstanceStatus)
    (inputs : List (PortName × ItemId) := []) (trigger : Option ItemId := none) : Instance :=
  { id := instanceId path n.id trigger, node := n.id, path, status, inputs, trigger }

def streamController (s : State) (path : Path) (n : Node) : Result State := do
  match s.nodeInstance? path n.id with
  | some i =>
    require (i.status == .waitingInputs) "CONTROL_FINISHED"
    return s
  | none => freshInstance s (makeInstance path n .waitingInputs)

def seedEntries (s : State) (path : Path) (entries : List PortRef) (items : List ItemId) : Result State :=
  (entries.zip items).foldlM (fun state (p, id) => do
    let ids := ((state.incoming path p.node).filter (fun c => c.entry && c.edge.dst == p)).map (·.id)
    let state ← place state ids (.item id)
    place state ids .eos) s

def addFrame (s : State) (owner : Instance) (body : Graph) (items : List ItemId) : Result State := do
  let path := owner.path ++ [identity [owner.id, toString owner.iteration]]
  require (!(s.frame? path).isSome) "DUPLICATE_FRAME"
  require (items.length == body.entries.length) "BODY_INPUT_ARITY"
  let definition := ((s.frame? owner.path).map (·.definition)).getD [] ++ [owner.node]
  let f : Frame := { path, graph := body, definition, owner := some owner.id }
  let s := { s with frames := s.frames ++ [f], channels := s.channels ++ f.channels }
  seedEntries s path body.entries items

def currentFrame (s : State) (i : Instance) : Result Frame :=
  (s.frame? (i.path ++ [identity [i.id, toString i.iteration]])).toExcept
    { code := "MISSING_BODY", message := i.id }

def frameDone (s : State) (f : Frame) : Bool :=
  !f.closed &&
  (s.channels.filter (fun c => c.path == f.path && c.exit)).all (·.closed) &&
  (s.channels.filter (fun c => c.path == f.path && !c.exit)).all (fun c => c.closed && c.pendingItems.isEmpty) &&
  (s.instances.filter (·.path == f.path)).all (fun i => i.status == .succeeded || i.status == .cancelled) &&
  f.graph.nodes.all (fun n => (s.nodeInstance? f.path n.id).any
    (fun i => i.status == .succeeded || i.status == .cancelled))

def frameOutputItems (s : State) (f : Frame) : Result (List ItemId) := do
  f.graph.exits.mapM fun p => do
    let c ← (s.channels.find? (fun c => c.path == f.path && c.exit && c.edge.src == p)).toExcept
      { code := "MISSING_EXIT", message := p.port }
    match c.items with
    | [item] => return item
    | _ => throw { code := "BODY_RESULT_ARITY", message := p.port }

def bodyResults (s : State) (f : Frame) : Result (List ItemId) := do
  require (frameDone s f) "BODY_NOT_FINISHED"
  frameOutputItems s f

def closeFrame (s : State) (f : Frame) (who : InstanceId) : Result State := do
  let s ← consumeChannels s (s.channels.filter (fun c => c.path == f.path && c.exit)) who
  return { s with frames := s.frames.map (fun g => if g.path == f.path then { g with closed := true } else g) }

def routeOutput (arm : Option PortName) (port : PortName) (output : Option ItemId) : Option ItemId :=
  if arm.isNone || arm == some port then output else none

/-- Readiness deliberately does not inspect EOS or the length of the remaining stream. --/
def spawnInputReady (c : Channel) (item : ItemId) : Bool :=
  c.pending.head? == some (.item item)

def routeOutputs (s : State) (path : Path) (n : Node) (output : Option ItemId) (arm : Option PortName) : Result State :=
  n.outputs.foldlM (fun s p => do
    match routeOutput arm p.name output with
    | some id => putOutput s path n.id p.name (.item id)
    | none => pure s) s

def finishControl (s : State) (path : Path) (n : Node) (inputs : List (PortName × ItemId))
    (output : Option ItemId) (arm : Option PortName := none) : Result State := do
  let i := makeInstance path n .succeeded inputs
  let s ← freshInstance s i
  let s ← consumeInputs s path n.id i.id
  let s ← routeOutputs s path n output arm
  closeOutputs s path n

def expireOrFail (s : State) (i : Instance) (n : Node) (now : Time)
    (outcome : AttemptStatus) (retryable : Bool) (code : String) : Result State := do
  let (r, _) ← leafPolicy n
  let l ← i.lease.toExcept { code := "NO_LEASE", message := i.id }
  let retry := retryable && i.attemptCount < r.maxAttempts + i.extraAttempts
  let s := setAttempt s l.attempt outcome
  let s := setInstance s { i with
    status := if retry then .retryWait else .failed
    lease := none
    retryAt := if retry then some (now + r.retrySeconds) else none }
  return { s with
    now
    status := if retry then s.status else .blocked
    reason := if retry then s.reason else some code }

/-- Plain inputs become usable only after their producer has committed success. --/
def plainChannelReady (s : State) (c : Channel) : Bool :=
  c.kind == .plain && c.closed &&
    (c.pending.head?.any (fun t => match t with | .item _ => true | _ => false)) &&
    (c.entry || (s.nodeInstance? c.path c.edge.src.node).any (·.status == .succeeded))

def plainReady (s : State) (path : Path) (node : NodeId) : Bool :=
  (s.incoming path node).all (plainChannelReady s)

def coalesceReady (s : State) (path : Path) (node edge : String) (item : ItemId) : Bool :=
  ((s.incoming path node).find? (·.id == edge)).any fun c =>
    plainChannelReady s c && c.pending.head? == some (.item item)

def preconditions (s : State) : Op → Bool
  | .activate p n | .fireWaitAll p n | .fireBranch p n _ => plainReady s p n
  | .spawn p n item => (s.incoming p n).head?.any (fun c => spawnInputReady c item)
  | .fireCoalesce p n edge item => coalesceReady s p n edge item
  | _ => true

/-- Operational rules. `step` below commits only invariant-preserving results. --/
def transition (s : State) (op : Op) : Result State := do
  match op with
  | .start inputs =>
    require (!s.started && s.instances.isEmpty) "ALREADY_STARTED"
    let f ← (s.frame? []).toExcept { code := "NO_ROOT", message := "missing root graph" }
    require (unique (inputs.map (·.entry)) && inputs.length == f.graph.entries.length &&
      inputs.all (fun i => f.graph.entries.contains i.entry)) "ENTRY_MISMATCH"
    let s ← startInputs s inputs
    return { s with started := true }
  | .activate path node =>
    require s.started "NOT_STARTED"
    let n ← getNode s path node
    let inputs ← plainInputs s path n
    match n.kind with
    | .leaf .. =>
      let i := makeInstance path n .ready inputs
      let s ← freshInstance s i
      consumeInputs s path node i.id
    | .subworkflow body | .loop body _ =>
      let iteration := match n.kind with | .loop .. => 1 | _ => 0
      let i := { makeInstance path n .waitingInputs inputs with iteration }
      let s ← freshInstance s i
      let s ← consumeInputs s path node i.id
      addFrame s i body (inputs.map (·.2))
    | _ => throw { code := "NOT_ACTIVATABLE", message := node }
  | .spawn path node item =>
    require s.started "NOT_STARTED"
    let n ← getNode s path node
    let .forEach body := n.kind | throw { code := "NOT_FOREACH", message := node }
    let c ← (s.incoming path node).head?.toExcept { code := "MISSING_INPUT", message := node }
    let i := makeInstance path n .waitingInputs [("item", item)] (some item)
    let s ← freshInstance s i
    let s ← consume s c.id i.id (some item)
    addFrame s i body [item]
  | .claim auth worker =>
    let i ← getInstance s auth.instance
    let n ← getNode s i.path i.node
    let (r, concurrency) ← leafPolicy n
    require (auth.now ≥ s.now) "CLOCK_REGRESSION"
    require (i.status == .ready && i.lease.isNone && i.retryAt.isNone) "NOT_READY"
    require (i.attemptCount < r.maxAttempts + i.extraAttempts) "ATTEMPTS_EXHAUSTED"
    require (!auth.attempt.isEmpty && !auth.token.isEmpty && !worker.isEmpty &&
      !s.attempts.any (fun a => a.id == auth.attempt || a.token == auth.token)) "DUPLICATE_ATTEMPT_OR_TOKEN"
    require (!s.instances.any (fun j =>
      (j.status == .running && j.lease.any (·.until_ ≤ auth.now)) ||
      (j.status == .retryWait && j.retryAt.any (· ≤ auth.now)))) "MAINTENANCE_REQUIRED"
    -- Node definitions in different body invocations share a concurrency budget.
    let definitionPath := (s.frame? i.path).map (·.definition)
    require ((s.instances.filter (fun j => j.node == i.node && (s.frame? j.path).map (·.definition) == definitionPath &&
      j.status == .running)).length < concurrency) "CONCURRENCY_LIMIT"
    let lease : Lease := { attempt := auth.attempt, token := auth.token, until_ := auth.now + r.leaseSeconds }
    let a : Attempt := {
      id := auth.attempt
      «instance» := i.id
      no := i.attemptCount + 1
      status := .running
      token := auth.token
      worker }
    let s := setInstance s { i with status := .running, attemptCount := i.attemptCount + 1, lease := some lease }
    return { s with attempts := s.attempts ++ [a], now := auth.now }
  | .renew auth =>
    let i ← getInstance s auth.instance
    let n ← getNode s i.path i.node
    let (r, _) ← leafPolicy n
    let s := setInstance s { i with lease := i.lease.map (fun l => { l with until_ := auth.now + r.leaseSeconds }) }
    return { s with now := auth.now }
  | .expireLease inst now =>
    let i ← getInstance s inst
    let n ← getNode s i.path i.node
    require (now ≥ s.now && i.status == .running && i.lease.any (·.until_ ≤ now)) "LEASE_NOT_EXPIRED"
    expireOrFail s i n now .abandoned true "LEASE_EXPIRED"
  | .promoteRetry inst now =>
    let i ← getInstance s inst
    require (now ≥ s.now && i.status == .retryWait && i.retryAt.any (· ≤ now)) "RETRY_NOT_DUE"
    return { setInstance s { i with status := .ready, retryAt := none } with now }
  | .emit auth port item =>
    let i ← getInstance s auth.instance
    let n ← getNode s i.path i.node
    let _ ← leafPolicy n
    require (n.outputs.any (fun p => p.name == port && p.kind == .stream)) "NOT_STREAM_OUTPUT"
    let s ← putOutput s i.path i.node port (.item item)
    return { s with now := auth.now }
  | .complete auth outputs =>
    let i ← getInstance s auth.instance
    let n ← getNode s i.path i.node
    let _ ← leafPolicy n
    let ps := n.outputs.filter (·.kind == .plain)
    require (unique (outputs.map (·.port)) && outputs.length == ps.length &&
      outputs.all (fun o => o.items.length == 1 && ps.any (·.name == o.port))) "OUTPUT_MISMATCH"
    let s ← decision s (identity ["leaf", i.id]) (toJson outputs).compress
    let s ← placeOutputs s i.path i.node outputs
    let s ← closeOutputs s i.path n
    let s := setAttempt s auth.attempt .succeeded
    let s := setInstance s { i with status := .succeeded, lease := none }
    return { s with now := auth.now, receipts := s.receipts ++ [{
      «instance» := i.id, attempt := auth.attempt, token := auth.token, outputs }] }
  | .fail auth code retryable =>
    let i ← getInstance s auth.instance
    let n ← getNode s i.path i.node
    expireOrFail s i n auth.now .failed retryable code
  | .fireWaitAll path node =>
    let n ← getNode s path node
    let .waitAll := n.kind | throw { code := "NOT_WAIT_ALL", message := node }
    let inputs ← plainInputs s path n
    let item := derivedItem "record" path node (inputs.map (fun (p, i) => identity [p, i]))
    finishControl s path n inputs (some item)
  | .fireBranch path node arm =>
    let n ← getNode s path node
    let .branch arms := n.kind | throw { code := "NOT_BRANCH", message := node }
    require (arms.contains arm) "UNKNOWN_ARM"
    let inputs ← plainInputs s path n
    let item ← (inputs.head?.map (·.2)).toExcept { code := "MISSING_INPUT", message := node }
    let s ← decision s (identity ["branch", instanceId path node, item]) arm
    finishControl s path n inputs (some item) (some arm)
  | .fireCollect path node =>
    let n ← getNode s path node
    let .collect := n.kind | throw { code := "NOT_COLLECT", message := node }
    let c ← (s.incoming path node).head?.toExcept { code := "MISSING_INPUT", message := node }
    require (c.closed && c.consumed == 0) "COLLECT_NOT_READY"
    let items := sortedItems c.items
    finishControl s path n (items.map ("item", ·)) (some (derivedItem "list" path node items))
  | .fireCoalesce path node edge item =>
    let n ← getNode s path node
    let .coalesce := n.kind | throw { code := "NOT_COALESCE", message := node }
    let c ← ((s.incoming path node).find? (·.id == edge)).toExcept
      { code := "WRONG_INPUT_EDGE", message := edge }
    let i := makeInstance path n .succeeded [(c.edge.dst.port, item)]
    let s ← freshInstance s i
    let s ← consume s c.id i.id (some item)
    let p ← n.outputs.head?.toExcept { code := "MISSING_OUTPUT", message := node }
    let s ← putOutput s path node p.name (.item item)
    closeOutputs s path n
  | .fireFilter path node item keep =>
    let n ← getNode s path node
    let .filter := n.kind | throw { code := "NOT_FILTER", message := node }
    let c ← (s.incoming path node).head?.toExcept { code := "MISSING_INPUT", message := node }
    let who := instanceId path node
    let s ← streamController s path n
    let s ← decision s (identity ["filter", who, item]) (toJson keep).compress
    let s ← consume s c.id who (some item)
    if keep then
      let p ← n.outputs.head?.toExcept { code := "MISSING_OUTPUT", message := node }
      putOutput s path node p.name (.item item)
    else pure s
  | .fireMerge path node edge item =>
    let n ← getNode s path node
    let .merge := n.kind | throw { code := "NOT_MERGE", message := node }
    require ((s.incoming path node).any (·.id == edge)) "WRONG_INPUT_EDGE"
    let s ← streamController s path n
    let s ← consume s edge (instanceId path node) (some item)
    let p ← n.outputs.head?.toExcept { code := "MISSING_OUTPUT", message := node }
    -- Preserve occurrences from distinct input edges; same id may arrive on both.
    putOutput s path node p.name (.item (derivedItem "merge" path node [edge, item]))
  | .propagateEos path node =>
    let n ← getNode s path node
    require (match n.kind with | .filter | .merge | .forEach _ => true | _ => false) "NOT_STREAM_CONTROL"
    let cs := s.incoming path node
    require (cs.all (fun c => c.closed && c.pendingItems.isEmpty)) "INPUT_NOT_DRAINED"
    require ((s.instances.filter (fun i => i.path == path && i.node == node && i.trigger.isSome)).all (·.status == .succeeded))
      "CHILDREN_NOT_FINISHED"
    let i := makeInstance path n .succeeded
    let s ← match s.nodeInstance? path node with
      | none => freshInstance s i
      | some old => do
        require (old.status == .waitingInputs) "CONTROL_FINISHED"
        pure (setInstance s { old with status := .succeeded })
    let s ← consumeChannels s cs i.id
    closeOutputs s path n
  | .finishSubworkflow inst =>
    let i ← getInstance s inst
    require (i.status == .waitingInputs) "NOT_WAITING_BODY"
    let n ← getNode s i.path i.node
    require (match n.kind with | .subworkflow _ | .forEach _ => true | _ => false) "NOT_SUBWORKFLOW"
    let f ← currentFrame s i
    let items ← bodyResults s f
    require (n.outputs.length == items.length) "BODY_OUTPUT_ARITY"
    let s ← closeFrame s f i.id
    let s ← placeBodyOutputs s i.path n items
    let s := setInstance s { i with status := .succeeded }
    match n.kind with
    | .subworkflow _ => closeOutputs s i.path n
    | _ => pure s
  | .loopIterate inst done =>
    let i ← getInstance s inst
    require (i.status == .waitingInputs) "NOT_WAITING_BODY"
    let n ← getNode s i.path i.node
    let .loop body max := n.kind | throw { code := "NOT_LOOP", message := inst }
    let f ← currentFrame s i
    let items ← bodyResults s f
    let item ← items.head?.toExcept { code := "MISSING_BODY_RESULT", message := inst }
    let s ← decision s (identity ["loop", inst, toString i.iteration, item]) (toJson done).compress
    let s ← closeFrame s f i.id
    if done then
      let p ← n.outputs.head?.toExcept { code := "MISSING_OUTPUT", message := inst }
      let s ← putOutput s i.path n.id p.name (.item item)
      let s ← closeOutputs s i.path n
      return setInstance s { i with status := .succeeded }
    else if i.iteration ≥ max + i.extraIterations then
      return { setInstance s { i with status := .failed } with status := .blocked, reason := some "LOOP_LIMIT" }
    else
      let i := { i with iteration := i.iteration + 1 }
      addFrame (setInstance s i) i body [item]
  | .skip path node =>
    let n ← getNode s path node
    let inputs := s.incoming path node
    let absent := match n.kind with
      | .coalesce => !inputs.isEmpty && inputs.all (fun c => c.closed && c.items.isEmpty)
      | _ => inputs.any (fun c => c.closed && c.items.isEmpty)
    require (allKind n.inputs .plain && absent) "NOT_SKIPPABLE"
    require ((s.incoming path node).all (·.closed)) "INPUT_NOT_FINISHED"
    require (!s.instances.any (fun j => j.path == path && j.node == node)) "NODE_ALREADY_STARTED"
    let i := makeInstance path n .cancelled
    let s ← freshInstance s i
    let s ← consumeInputs s path node i.id
    closeOutputs s path n
  | .idle => pure s -- The public prepare classifies idle after probing non-idle operations.
  | .cancel =>
    return { s with
      status := .cancelled
      instances := s.instances.map (fun i => if i.status.finished then i else { i with status := .cancelled, lease := none, retryAt := none })
      attempts := s.attempts.map (fun a => if a.status == .running then { a with status := .cancelled } else a)
      reason := some "CANCELLED" }
  | .manualRetry inst =>
    let i ← getInstance s inst
    let n ← getNode s i.path i.node
    require (i.status == .failed) "NOT_FAILED"
    match n.kind with
    | .leaf .. =>
      return { setInstance s { i with status := .retryWait, extraAttempts := i.extraAttempts + 1, retryAt := some s.now } with
        status := .running, reason := none }
    | .loop body _ =>
      let f ← currentFrame s i
      require f.closed "BODY_NOT_FINISHED"
      let items ← frameOutputItems s f
      let i := { i with status := .waitingInputs, extraIterations := i.extraIterations + 1, iteration := i.iteration + 1 }
      let s ← addFrame (setInstance s i) i body items
      return { s with status := .running, reason := none }
    | _ => throw { code := "NOT_RETRYABLE_NODE", message := i.node }

/-- Exact complete re-delivery is accepted; changing output or credentials is not. --/
def duplicateComplete (s : State) : Op → Bool
  | .complete c outputs => s.receipts.contains { «instance» := c.instance, attempt := c.attempt, token := c.token, outputs }
  | _ => false

def Op.credentials : Op → Option Credentials
  | .emit c .. | .complete c .. | .fail c .. | .renew c => some c
  | _ => none

def authorized (s : State) (op : Op) : Bool :=
  op.credentials.all (validLease s)

/-- Terminal operations preserve state; invalid worker credentials still reject (T8). --/
def absorbed (s : State) (op : Op) : Bool :=
  duplicateComplete s op || (s.status.terminal && authorized s op)

def startupAllowed (s : State) (op : Op) : Bool :=
  s.started || match op with | .start _ | .cancel => true | _ => false

/-- The commit guard is part of the specification, not an unchecked runtime assertion. --/
def commit (before after : State) : Result State :=
  if invariants after && historyOK before after then .ok after
  else .error { code := "INVARIANT", message := "invalid transaction boundary" }

/-- Shared startup / precondition checks before any operational body. --/
def prepareWith (body : State → Op → Result State) (s : State) (op : Op) : Result State := do
  require (startupAllowed s op) "NOT_STARTED"
  require (preconditions s op) "PRECONDITION"
  body s op

/-- Shared guard: absorption, lease authority, then commit of the executed body. --/
def guarded (execute : State → Op → Result State) (s : State) (op : Op) : Result State :=
  if absorbed s op then .ok s
  else if !authorized s op then .error { code := "INVALID_LEASE", message := "stale, mismatched or expired lease" }
  else match execute s op with
    | .error e => .error e
    | .ok next => commit s next

def prepareNonIdle : State → Op → Result State := prepareWith transition

/-- The same guarded execution as step, without consulting idle/hasWork. --/
def stepNonIdle : State → Op → Result State := guarded prepareNonIdle

/-- Work changes state. Accepted retries of completed operations are not work. --/
def acceptedProgress (s : State) (op : Op) : Bool :=
  op.countsAsWork && match stepNonIdle s op with
    | .ok next => next != s
    | .error _ => false

/-- D2: existence of a progressing candidate, including future maintenance. --/
def State.hasWork (s : State) : Bool :=
  (Explore.candidates {} s).any (acceptedProgress s)

def idleState (s : State) : State :=
  if s.hasWork then s else
  let success := s.started && (s.frame? []).any (frameDone s)
  { s with
    status := if success then .succeeded else .blocked
    reason := if success then none else
      if s.status == .blocked && s.reason.isSome then s.reason else some "DEPENDENCIES_UNRESOLVED" }

/-- idle is classified after the non-idle rules; every other Op runs `transition`. --/
def transitionOrIdle (s : State) : Op → Result State
  | .idle => pure (idleState s)
  | op => transition s op

def prepare : State → Op → Result State := prepareWith transitionOrIdle

def step : State → Op → Result State := guarded prepare
end Suimon
