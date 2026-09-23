import Suimon.Theorems.Round3.Conformance
import Suimon.Theorems.Round3.LedgerSteps

namespace Suimon.Round3
open State

/-! ## [18] Round3/Ledger.lean — task E5

Failure records have no key, and equal records can be distinct failures (two elements of one Stream
that fail their transform). Each failure has exactly one source record, and the source records
determine the failure. -/

section LedgerSection
variable {p : Program} {s : State}

/-- The owner of a call failed: its invocation, or its task. -/
def ownerFailed (s : State) (c : Call) : Bool :=
  match c.task with
  | none => (s.invocation? c.owner).any (·.status == .failed)
  | some name => (s.execution? c.owner).any fun e => e.tasks.any fun t => t.name == name && t.status == .failed

/-- The cause a call recorded: an error, a lost lease, or a timeout (a cancelled call counts only when
    its owner failed, i.e. it was timed out rather than cancelled by a stop). -/
def callCause (s : State) (c : Call) : Option Cause :=
  match c.status with
  | .failed => some .error
  | .lost => some .lost
  | .cancelling | .cancelled => if ownerFailed s c then some .timeout else none
  | _ => none

def callLedger (s : State) (c : Call) : Option Failure := do
  let cause ← callCause s c
  match c.task with
  | none =>
    let i ← s.invocation? c.owner
    pure { run := i.run, placement := i.placement, cause }
  | some name =>
    let e ← s.execution? c.owner
    pure { run := e.run, placement := e.placement, task := some name, cause }

def deliveryLedger (p : Program) (s : State) (d : Delivery) : Option Failure := do
  guard (d.outcome == .failed)
  let w ← s.workflow? p d.run
  let c ← w.connections[d.connection]?
  pure { run := d.run, placement := c.target, cause := .transform }

def taskInputLedger (s : State) (e : Execution) (t : TaskState) : Option Failure :=
  if t.status == .failed && (s.call? (Key.task e.id t.name)).isNone &&
      !(s.runs.any fun r => r.owner == some e.id && r.task == some t.name) then
    some { run := e.run, placement := e.placement, task := some t.name, cause := .transform }
  else none

def taskOutputLedger (s : State) (r : TaskResult) : Option Failure := do
  guard (r.output == .failed)
  let e ← s.execution? r.execution
  pure { run := e.run, placement := e.placement, task := some r.task, cause := .transform }

/-- The failures the records of `s` account for, one per source record. -/
def ledger (p : Program) (s : State) : List Failure :=
  s.calls.filterMap (callLedger s) ++ s.deliveries.filterMap (deliveryLedger p s) ++
    s.executions.flatMap (fun e => e.tasks.filterMap (taskInputLedger s e)) ++
    s.taskResults.filterMap (taskOutputLedger s)

/-! The proof reads the ledger through the views of `LedgerCore` (`Round3/LedgerView.lean`), where
    every accepted step is shown to record exactly the failures its ledger gains
    (`Round3/LedgerSteps.lean`). -/

theorem callLedger_eq (s : State) (c : Call) : callLedger s c = LedgerCore.callL s c := by
  have hcause : ∀ b, ownerFailed s c = b → callCause s c = LedgerCore.causeOf c.status b := by
    intro b hb
    unfold callCause
    rw [hb]
    cases c.status <;> rfl
  unfold callLedger LedgerCore.callL LedgerCore.ownerView
  cases ht : c.task with
  | none =>
    cases hi : s.invocation? c.owner with
    | none => cases callCause s c <;> rfl
    | some i =>
      rw [hcause (i.status == .failed) (by unfold ownerFailed; rw [ht, hi]; rfl)]
      show (LedgerCore.causeOf c.status (i.status == .failed) >>= fun cause =>
          some ({ run := i.run, placement := i.placement, cause } : Failure)) =
        (LedgerCore.causeOf c.status (i.status == .failed)).map fun cause =>
          { run := i.run, placement := i.placement, task := none, cause }
      cases LedgerCore.causeOf c.status (i.status == .failed) <;> rfl
  | some name =>
    cases he : s.execution? c.owner with
    | none => cases callCause s c <;> rfl
    | some e =>
      rw [hcause (e.tasks.any fun t => t.name == name && t.status == .failed)
        (by unfold ownerFailed; rw [ht, he]; rfl)]
      show (LedgerCore.causeOf c.status (e.tasks.any fun t => t.name == name && t.status == .failed) >>= fun cause =>
          some ({ run := e.run, placement := e.placement, task := some name, cause } : Failure)) =
        (LedgerCore.causeOf c.status (e.tasks.any fun t => t.name == name && t.status == .failed)).map fun cause =>
          { run := e.run, placement := e.placement, task := some name, cause }
      cases LedgerCore.causeOf c.status (e.tasks.any fun t => t.name == name && t.status == .failed) <;> rfl

theorem taskInputLedger_eq (s : State) (e : Execution) (t : TaskState) :
    taskInputLedger s e t = LedgerCore.taskInputL s e t := by
  unfold taskInputLedger LedgerCore.taskInputL LedgerCore.hasBody
  cases (s.call? (Key.task e.id t.name)) <;>
    cases (s.runs.any fun r => r.owner == some e.id && r.task == some t.name) <;>
    cases (t.status == .failed) <;> rfl

theorem taskOutputLedger_eq (s : State) (r : TaskResult) : taskOutputLedger s r = LedgerCore.taskOutputL s r := by
  unfold taskOutputLedger LedgerCore.taskOutputL LedgerCore.execPos
  by_cases h : r.output = .failed
  · have hb : (r.output == .failed) = true := by simp [h]
    rw [ite_eq_left h, hb]
    cases s.execution? r.execution <;> rfl
  · have hb : (r.output == .failed) = false := by simpa using h
    rw [ite_eq_right h, hb]
    rfl

theorem ledger_eq (p : Program) (s : State) : ledger p s = LedgerCore.ledgerL p s := by
  have h1 : callLedger s = LedgerCore.callL s := funext (callLedger_eq s)
  have h2 : deliveryLedger p s = LedgerCore.deliveryL p s := rfl
  have h3 : taskInputLedger s = LedgerCore.taskInputL s := funext fun e => funext (taskInputLedger_eq s e)
  have h4 : taskOutputLedger s = LedgerCore.taskOutputL s := funext (taskOutputLedger_eq s)
  unfold ledger LedgerCore.ledgerL LedgerCore.callPart LedgerCore.deliveryPart LedgerCore.inputPart
    LedgerCore.outputPart
  rw [h1, h2, h3, h4]

/-- Every failure has exactly one source record, in every reachable state of a valid program, stopped
    or not. Validity is needed: with two tasks of one name, a failed input transform fails both tasks
    but records one failure (reviewers' counterexample `cex.lean`, CEX 5). -/
theorem Reachable.failures_ledger (valid : p.validate = .ok ()) (h : Reachable p s) :
    s.failures.Perm (ledger p s) := by
  rw [ledger_eq]
  exact LedgerCore.Reachable.failures_ledgerL valid h

end LedgerSection

end Suimon.Round3
