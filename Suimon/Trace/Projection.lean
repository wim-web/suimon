import Suimon.State

namespace Suimon.Trace.Projection
open Lean

/-- The v2 wire contract is an explicit allowlist, never a derived State codec. --/
def instanceCreated (i : Instance) : Json := Json.mkObj [
  ("id", toJson i.id), ("node", toJson i.node), ("path", toJson i.path),
  ("trigger", toJson i.trigger)]

def attemptStatus : AttemptStatus → String
  | .running => "running"
  | .succeeded => "succeeded"
  | .failed => "failed"
  | .abandoned => "abandoned"
  | .cancelled => "cancelled"

def attempt (a : Attempt) : Json := Json.mkObj [
  ("id", toJson a.id), ("instance", toJson a.instance), ("no", toJson a.no),
  ("status", toJson (attemptStatus a.status)), ("token", toJson a.token),
  ("worker", toJson a.worker)]

def lease (l : Lease) : Json := Json.mkObj [
  ("attempt", toJson l.attempt), ("token", toJson l.token), ("lease_until", toJson l.until_)]

def token : Token → Json
  | .item id => Json.mkObj [("item", Json.mkObj [("id", toJson id)])]
  | .eos => toJson "eos"

def consumption (c : Consumption) : Json := Json.mkObj [
  ("channel", toJson c.channel), ("index", toJson c.index),
  ("item", toJson c.item), ("by_instance", toJson c.byInstance)]

def execStatus : ExecStatus → String
  | .running => "running"
  | .blocked => "blocked"
  | .succeeded => "succeeded"
  | .failed => "failed"
  | .cancelled => "cancelled"

end Suimon.Trace.Projection
