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

/-- External traces may have used our usual IDs already; always choose fresh witnesses. --/
def freshId (tag : String) (used : List String) : String :=
  let choices := (List.range (used.length + 1)).map (fun n => identity [tag, toString n])
  (choices.find? (fun id => !used.contains id)).getD (identity [tag, toString used.length])

def candidates (cfg : Config) (s : State) : List Op := Id.run do
  if s.status.terminal then return []
  if !s.started then
    return match s.frame? [] with
      | some f => [.start (inputValues f.graph), .cancel]
      | none => []
  let mut ops := [.idle, .cancel]
  for f in s.frames.filter (! ·.closed) do
    for n in f.graph.nodes do
      let p := f.path
      ops := ops ++ [.skip p n.id]
      match n.kind with
      | .leaf .. | .subworkflow .. | .loop .. => ops := ops ++ [.activate p n.id]
      | .waitAll => ops := ops ++ [.fireWaitAll p n.id]
      | .branch arms => ops := ops ++ arms.map (.fireBranch p n.id ·)
      | .collect => ops := ops ++ [.fireCollect p n.id]
      | .coalesce =>
        for c in s.incoming p n.id do
          if let some (.item item) := c.pending.head? then
            ops := ops ++ [.fireCoalesce p n.id c.id item]
      | .filter | .merge | .forEach _ =>
        ops := ops ++ [.propagateEos p n.id]
        for c in s.incoming p n.id do
          if let some (.item item) := c.pending.head? then
            match n.kind with
            | .filter => ops := ops ++ [.fireFilter p n.id item true, .fireFilter p n.id item false]
            | .merge => ops := ops ++ [.fireMerge p n.id c.id item]
            | .forEach _ => ops := ops ++ [.spawn p n.id item]
            | _ => pure ()
  for i in s.instances do
    match i.status with
    | .ready =>
      for worker in List.range cfg.workers do
        let auth : Credentials := {
          «instance» := i.id
          attempt := freshId "attempt" (s.attempts.map (·.id))
          token := freshId "lease" (s.attempts.map (·.token))
          now := s.now }
        ops := ops ++ [.claim auth (toString worker)]
    | .running =>
      if let some l := i.lease then
        let auth : Credentials := { «instance» := i.id, attempt := l.attempt, token := l.token, now := s.now }
        ops := ops ++ [.fail auth "TRANSIENT" true, .fail auth "PERMANENT" false, .expireLease i.id (max (s.now + cfg.tick) l.until_), .renew { auth with now := s.now + cfg.tick }]
        if let some n := s.node? i.path i.node then
          ops := ops ++ [.complete auth (outputs i n)]
          for p in n.outputs.filter (·.kind == .stream) do
            for idx in List.range cfg.maxItems do
              ops := ops ++ [.emit auth p.name (derivedItem "emit" i.path i.node [p.name, toString idx])]
    | .retryWait => ops := ops ++ [.promoteRetry i.id (max s.now (i.retryAt.getD (s.now + cfg.tick)))]
    | .failed => ops := ops ++ [.manualRetry i.id]
    | .waitingInputs => ops := ops ++ [.finishSubworkflow i.id, .loopIterate i.id true, .loopIterate i.id false]
    | _ => pure ()
  return ops

end Suimon.Explore
