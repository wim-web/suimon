import Suimon.Oracle
namespace Suimon
open Lean

structure Input where
  entry : PortRef
  items : List ItemId
  deriving DecidableEq, BEq, Repr, ToJson, FromJson

inductive Op where
  | start (inputs : List Input)
  | activate (path : Path) (node : NodeId)
  | spawn (path : Path) (node : NodeId) (item : ItemId)
  | claim (auth : Credentials) (worker : String)
  | renew (auth : Credentials)
  | expireLease (inst : InstanceId) (now : Time)
  | promoteRetry (inst : InstanceId) (now : Time)
  | emit (auth : Credentials) (port : PortName) (item : ItemId)
  | complete (auth : Credentials) (outputs : List Output)
  | fail (auth : Credentials) (code : String) (retryable : Bool)
  | fireWaitAll (path : Path) (node : NodeId)
  | fireBranch (path : Path) (node : NodeId) (arm : PortName)
  | fireCoalesce (path : Path) (node : NodeId) (edge : String) (item : ItemId)
  | fireCollect (path : Path) (node : NodeId)
  | fireFilter (path : Path) (node : NodeId) (item : ItemId) (keep : Bool)
  | fireMerge (path : Path) (node : NodeId) (edge : String) (item : ItemId)
  | propagateEos (path : Path) (node : NodeId)
  | finishSubworkflow (inst : InstanceId)
  | loopIterate (inst : InstanceId) (done : Bool)
  | skip (path : Path) (node : NodeId)
  | idle
  | cancel
  | manualRetry (inst : InstanceId)
  deriving BEq, Repr, ToJson, FromJson

def Op.countsAsWork : Op → Bool
  | .idle | .cancel | .manualRetry _ => false
  | _ => true
end Suimon
