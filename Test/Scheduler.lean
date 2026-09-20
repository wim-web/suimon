import Suimon
import Test.Examples

namespace Suimon.Test.SchedulerTests

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def applyOp (s : State) (op : Op) : IO State := do
  match step s op with
  | .ok next => return next
  | .error e => throw (IO.userError s!"scheduler setup: {e.code}")

private def service (s : State) (owned : List AttemptId) (auto : Bool) (now : Nat) : IO State := do
  match Scheduler.service s owned auto now with
  | .ok (some next) => return next
  | .ok none => throw (IO.userError "scheduler skipped due maintenance")
  | .error e => throw (IO.userError s!"scheduler maintenance: {e.code}")

-- An explicit inhabitant checks that the environmental premises are consistent.
example : Scheduler.PollProgress (fun n => n) (fun _ => true) := {
  monotone := fun _ _ h => h
  unbounded := fun n => ⟨n, Nat.le_refl n⟩
  fair := fun n => ⟨n, Nat.le_refl n, rfl⟩ }

def run : IO Unit := do
  let x := {leaf "x" ["in"] ["out"] with kind := .leaf {maxAttempts := 2, leaseSeconds := 3, retrySeconds := 20} 2}
  let g : Graph := {
    nodes := [x, leaf "y" ["in"] ["out"]]
    edges := []
    entries := [ref "x" "in", ref "y" "in"]
    exits := [ref "x" "out", ref "y" "out"] }
  ensure (g.validate matches .ok _) "invalid scheduler test graph"
  let first : Credentials := {«instance» := instanceId [] "x", attempt := "x-1", token := "x-token", now := 1000}
  let external : Credentials := {«instance» := instanceId [] "y", attempt := "external", token := "external-token", now := 1023}
  let initial ← applyOp (.initial g) (.start (Explore.inputValues g))
  let initial ← applyOp initial (.activate [] "x")
  let initial ← applyOp initial (.activate [] "y")
  let running ← applyOp initial (.claim first "local")
  let waiting ← service running [] false 1003
  let timers := Scheduler.timers waiting [] false
  let deadline := Scheduler.waitDeadline timers (some 1005) true
  ensure (deadline == some 1023) "announced stall hid retry deadline"
  ensure (!Scheduler.wake deadline 1005 false) "poll woke before retry deadline"
  ensure (Scheduler.wake deadline 1023 false) "stall suppressed retry wake"
  ensure (!Scheduler.announceStall timers (some 1005) false 1023) "announced stall before overdue maintenance"
  let ready ← service waiting [] false 1023
  ensure ((ready.instance? first.instance).any (·.status == .ready)) "retry was not promoted"
  let runningExternal ← applyOp ready (.claim external "remote")
  let deadline := Scheduler.waitDeadline (Scheduler.timers runningExternal [] false) (some 1005) true
  ensure (deadline == some 1026 && Scheduler.wake deadline 1026 false) "stall hid external lease"
  let expired ← service runningExternal [] false 1026
  let readyExternal ← service expired [] false 1027
  ensure ((readyExternal.instance? external.instance).any (·.status == .ready)) "external retry did not progress"
  let simultaneous ← applyOp running (.claim {external with now := 1000} "remote")
  let simultaneous ← applyOp simultaneous (.renew {first with now := 1002})
  ensure (Scheduler.maintenance simultaneous [first.attempt] true 1004 == some (.expireLease external.instance 1004))
    "optional renewal outranked an expired lease"
  let _ ← service simultaneous [first.attempt] true 1004
  ensure (!Scheduler.waitPrefix (some 1003) (fun _ => 1000) (fun _ => true) 128)
    "a fixed clock advanced past a deadline"
  IO.println "ok: scheduler maintenance wakes through stalls, clock jumps, and external leases"

end Suimon.Test.SchedulerTests
