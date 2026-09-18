import Suimon
import Test.Examples

namespace Suimon.Test.OracleConformance

private def graph : Graph := {
  nodes := [emitter "emit"]
  edges := []
  entries := [ref "emit" "in"]
  exits := [ref "emit" "out"] }

private def oracle : ScopedOracle := fun _ => {
  leaf := fun _ _ => [{ port := "out", items := ["x", "y"] }]
  branch := fun _ _ => "left"
  filter := fun _ _ => true
  loop := fun _ _ _ => true }

private theorem oracle_deterministic : oracle.Deterministic := by
  intro path node a b same
  rfl

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def applyOp (s : State) (op : Op) : IO State := do
  match step s op with
  | .ok next => return next
  | .error e => throw (IO.userError s!"oracle conformance setup: {e.code}")

private def checked (s : State) (op : Op) : IO State := do
  ensure (oracleConforms oracle s op) s!"fixed oracle rejected {repr op}"
  applyOp s op

def run : IO Unit := do
  ensure (graph.validate matches .ok _) "invalid oracle conformance graph"
  let _ := oracle_deterministic
  let first : Credentials := {
    «instance» := instanceId [] "emit", attempt := "a1", token := "t1", now := 0 }
  let second : Credentials := { first with attempt := "a2", token := "t2", now := 4 }
  let s ← checked (.initial graph) (.start (Explore.inputValues graph))
  let s ← checked s (.activate [] "emit")
  let s ← checked s (.claim first "worker-1")
  let s ← checked s (.emit first "out" "x")
  ensure (!oracleConforms oracle s (.emit first "out" "unprescribed")) "extra yield conforms"
  ensure (!oracleConforms oracle s (.complete first [])) "truncated stream conforms"
  -- The executable model intentionally cannot run user code. Its successful
  -- drain alone does not establish that the prescribed stream was fully emitted.
  let truncated ← applyOp s (.complete first [])
  let truncated ← applyOp truncated .idle
  ensure (succeededDrained truncated) "truncation witness stopped being a successful raw execution"
  let normal ← checked s (.emit first "out" "y")
  let normal ← checked normal (.complete first [])
  let normal ← checked normal .idle
  let retried ← checked s (.expireLease first.instance 3)
  let retried ← checked retried (.promoteRetry first.instance 4)
  let retried ← checked retried (.claim second "worker-2")
  let channels := retried.channels
  let retried ← checked retried (.emit second "out" "x")
  ensure (retried.channels == channels) "conforming re-emission changed history"
  let retried ← checked retried (.emit second "out" "y")
  let retried ← checked retried (.complete second [])
  let retried ← checked retried .idle
  ensure (succeededDrained normal && succeededDrained retried) "conforming runs did not drain"
  ensure (channelBags normal == channelBags retried) "conforming retry changed the multiset"
  ensure (channelBags normal != channelBags truncated) "truncation witness lost its differing result"
  IO.println "ok: oracle conformance requires complete streams and accepts stable-ID retries"

end Suimon.Test.OracleConformance
