import Suimon
import Test.Regression
import Test.Work
import Test.Determinism
import Test.OracleConformance
import Test.Scheduler
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

def main (args : List String) : IO Unit := do
  Regression.run args
  Work.run
  Determinism.run
  OracleConformance.run
  SchedulerTests.run
