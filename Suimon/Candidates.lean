import Suimon.Op
namespace Suimon.Explore
open Lean

structure Config where
  depth : Nat := 8
  workers : Nat := 1
  tick : Nat := 1
  maxItems : Nat := 2
  maxStates : Nat := 100000
  deriving ToJson, FromJson

/-- Finite oracle domain. Exhaustiveness is relative to this domain, not arbitrary strings. --/
def inputValues (g : Graph) : List Input := g.entries.map fun p =>
  { entry := p, items := [identity ["input", p.node, p.port]] }

def outputs (i : Instance) (n : Node) : List Output :=
  (n.outputs.filter (·.kind == .plain)).map fun p =>
    { port := p.name, items := [derivedItem "leaf" i.path i.node (p.name :: i.inputs.map (·.2))] }

/-- A longest used identifier gives a fresh witness without any assumption
    about the injectivity of a JSON printer or a hash. --/
def longestId : List String → String
  | [] => ""
  | id :: rest =>
    let tail := longestId rest
    if tail.length < id.length then id else tail

/-- External traces may have used any strings. This identifier is strictly
    longer than every used identifier, even when the tag is empty. --/
def freshId (tag : String) (used : List String) : String :=
  tag ++ ":" ++ longestId used

def pendingCandidates (s : State) (path : Path) (n : Node) (c : Channel) : List Op :=
  match c.pending.head? with
  | some (.item item) => match n.kind with
    | .coalesce => [.fireCoalesce path n.id c.id item]
    | .filter => [.fireFilter path n.id item true, .fireFilter path n.id item false]
    | .merge => [.fireMerge path n.id c.id item]
    | .forEach _ => [.spawn path n.id item]
    | _ => []
  | _ => []

def nodeCandidates (s : State) (path : Path) (n : Node) : List Op :=
  .skip path n.id :: match n.kind with
    | .leaf .. | .subworkflow .. | .loop .. => [.activate path n.id]
    | .waitAll => [.fireWaitAll path n.id]
    | .branch arms => arms.map (.fireBranch path n.id ·)
    | .collect => [.fireCollect path n.id]
    | .coalesce => (s.incoming path n.id).flatMap (pendingCandidates s path n)
    | .filter | .merge | .forEach _ =>
      .propagateEos path n.id :: (s.incoming path n.id).flatMap (pendingCandidates s path n)

def claimCredentials (s : State) (i : Instance) : Credentials := {
  «instance» := i.id
  attempt := freshId "attempt" (s.attempts.map (·.id))
  token := freshId "lease" (s.attempts.map (·.token))
  now := s.now }

def instanceCandidates (cfg : Config) (s : State) (i : Instance) : List Op :=
  match i.status with
  | .ready => (List.range cfg.workers).map (fun worker => .claim (claimCredentials s i) (toString worker))
  | .running => match i.lease with
    | none => []
    | some l =>
      let auth : Credentials := { «instance» := i.id, attempt := l.attempt, token := l.token, now := s.now }
      [.fail auth "TRANSIENT" true, .fail auth "PERMANENT" false,
        .expireLease i.id (max (s.now + cfg.tick) l.until_), .renew { auth with now := s.now + cfg.tick }] ++
        match s.node? i.path i.node with
        | none => []
        | some n => .complete auth (outputs i n) ::
          (n.outputs.filter (·.kind == .stream)).flatMap (fun p =>
            (List.range cfg.maxItems).map (fun idx => .emit auth p.name (derivedItem "emit" i.path i.node [p.name, toString idx])))
  | .retryWait => [.promoteRetry i.id (max s.now (i.retryAt.getD (s.now + cfg.tick)))]
  | .failed => [.manualRetry i.id]
  | .waitingInputs => [.finishSubworkflow i.id, .loopIterate i.id true, .loopIterate i.id false]
  | _ => []

def candidates (cfg : Config) (s : State) : List Op :=
  if s.status.terminal then []
  else if !s.started then match s.frame? [] with
    | some f => [.start (inputValues f.graph), .cancel]
    | none => []
  else [.idle, .cancel] ++
    (s.frames.filter (! ·.closed)).flatMap (fun f => f.graph.nodes.flatMap (nodeCandidates s f.path)) ++
    s.instances.flatMap (instanceCandidates cfg s)

end Suimon.Explore
