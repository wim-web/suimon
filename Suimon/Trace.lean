import Suimon.Trace.Bounded

namespace Suimon.Trace

/-- Check external records with finite resource limits and indexed payload bookkeeping. The
    unbounded reference for the recovery proofs is `checkModel`; executable behavior is compared
    against it on valid, malformed, and torn records in `Test.Trace`. --/
def check (c : Codec) (load : Header → Except String Definition) (text : String)
    (limits : Limits := {}) : Except String Checked :=
  checkWithLimits c load text limits

/-- Recover only the committed state, under the same limits as `check`. --/
def recover (c : Codec) (load : Header → Except String Definition) (text : String)
    (limits : Limits := {}) : Except String State :=
  (check c load text limits).map (·.state)

/-- Resume a matching definition from a bounded, checked record. --/
def resume (c : Codec) (load : Header → Except String Definition) (p : Definition) (text : String)
    (limits : Limits := {}) : Except String State := do
  let checked ← check c (agreeing load p) text limits
  match checked.definition with
  | some _ => return checked.state
  | none => throw "the record has no header"

end Suimon.Trace
