import Suimon.Trace.Model
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

namespace Suimon.Trace

/-- Limits for checking external records. Bytes include the header and an incomplete tail; records
    count complete op/commit lines, including an uncommitted op. Work is a deterministic allowance
    for parsing and the list-based state machine, not elapsed time. Zero is a real limit. --/
structure Limits where
  maxBytes : Nat := 16 * 1024 * 1024
  maxRecords : Nat := 100000
  maxValues : Nat := 100000
  maxWork : Nat := 1000000000
  deriving Repr

namespace Bounded

/-- Every mentioned value has a committed payload, and reachable states retain their values.
    Consequently the payload map also indexes the values already present in the state. Keep output
    order separately by consing; only the final result reverses it. --/
structure Payloads where
  known : Std.HashMap Value String := ∅
  reversed : List (Value × String) := []

/-- A successful step can introduce at most one identity. Reports supply it directly; judges and
    aggregations append it to results. The other operations only copy existing values or change
    status. Match every constructor so additions to `Op` require revisiting this boundary. --/
def candidate (op : Op) (after : State) : Option Value :=
  match op with
  | .start value | .deliver _ _ _ value | .taskInput _ _ value => value
  | .returned _ value | .yielded _ value | .taskOutput _ _ _ value => some value
  | .judged .. | .settle .. | .closeExecution .. => after.results.getLast?.map (·.value)
  | .invoke .. | .fetch .. | .ended .. | .failed .. | .timedOut .. | .lost ..
  | .terminated .. | .transformFailed .. | .taskInputFailed .. | .beginTask ..
  | .taskOutputFailed .. | .closeRun .. | .cancel | .conclude => none

/-- Check the transition's candidate once. The map replaces both a scan of `State.values` and a
    scan of all earlier payloads. Pending payloads are added only after all checks pass. --/
def Payloads.commit (p : Payloads) (value : Option Value) (values : List (Value × String))
    (maxValues : Nat) (at_ : String) : Except String Payloads := do
  let fresh := value.filter fun v => !p.known.contains v
  let mut supplied : Std.HashSet Value := ∅
  let mut extra := []
  for (v, _) in values do
    if supplied.contains v then throw s!"{at_}: duplicate payloads for [{v}]"
    supplied := supplied.insert v
    unless fresh == some v do extra := v :: extra
  unless extra.isEmpty do
    throw s!"{at_}: payloads for {extra.reverse}, which the transition does not introduce"
  if let some v := fresh then
    unless supplied.contains v do throw s!"{at_}: missing payloads for {[v]}"
    if p.known.size + 1 > maxValues then
      throw s!"{at_}: introduced-value limit exceeded (max {maxValues})"
  let mut known := p.known
  let mut reversed := p.reversed
  for (v, payload) in values do
    known := known.insert v payload
    reversed := (v, payload) :: reversed
  return { known, reversed }

/-- Count state rows, including nested tasks, without reconstructing their values. A commit is
    charged before `step` for pairwise row searches and definition lookups. This also budgets the
    underlying state machine's list scans/appends, which payload indexing alone cannot remove. --/
def stateRows (s : State) : Nat :=
  s.runs.length + s.invocations.length + s.calls.length + s.executions.length +
    (s.executions.foldl (fun n e => n + e.tasks.length) 0) + s.results.length +
    s.taskResults.length + s.deliveries.length + s.settled.length + s.failures.length

def charge (used amount limit : Nat) (at_ : String) : Except String Nat :=
  if used + amount > limit then throw s!"{at_}: replay-work limit exceeded (max {limit})"
  else pure (used + amount)

structure Replay where
  state : State := {}
  committed : Nat := 0
  payloads : Payloads := {}
  pending : Option (Op × List (Value × String)) := none
  next : Nat := 1
  rows : Nat := 0
  work : Nat := 0

def replayLine (c : Codec) (p : Definition) (limits : Limits) (definitionBytes : Nat)
    (r : Replay) (index : Nat) (line : String) : Except String Replay := do
  let at_ := s!"line {index + 1}"
  let work ← charge r.work (line.utf8ByteSize + 1) limits.maxWork at_
  let record ← (c.decode line).mapError (s!"{at_}: {·}")
  if record.seq != r.next then throw s!"{at_}: expected sequence {r.next}, got {record.seq}"
  match record, r.pending with
  | .op _ o values, none =>
    return { r with pending := some (o, values), next := r.next + 1, work }
  | .commit _, some (o, values) =>
    let work ← charge work ((r.rows + 1) * (r.rows + definitionBytes + 1)) limits.maxWork at_
    let next ← (step p r.state o).mapError fun e => s!"{at_}: rejected {(opWire o).render}: {e}"
    let payloads ← r.payloads.commit (candidate o next) values limits.maxValues at_
    return { state := next, committed := r.committed + 1, payloads, next := r.next + 1,
             rows := stateRows next, work }
  | .op .., some _ => throw s!"{at_}: an op before the previous commit"
  | .commit _, none => throw s!"{at_}: a commit without an op"

end Bounded

/-- Check external text with indexed payload bookkeeping and finite resource limits. `checkModel`
    is the unbounded specification used by the recovery proofs. Byte and record counts are checked
    before splitting/decoding, and work is charged before each transition. --/
def checkWithLimits (c : Codec) (load : Header → Except String Definition) (text : String)
    (limits : Limits := {}) : Except String Checked := do
  if text.utf8ByteSize > limits.maxBytes then
    throw s!"record-byte limit exceeded (max {limits.maxBytes})"
  let work ← Bounded.charge 0 text.utf8ByteSize limits.maxWork "record"
  let complete := text.foldl (fun n ch => if ch == '\n' then n + 1 else n) 0
  if complete - 1 > limits.maxRecords then
    throw s!"record-count limit exceeded (max {limits.maxRecords})"
  if complete == 0 then
    return { definition := none, validated := none, state := {}, committed := 0,
             uncommitted := !text.isEmpty, values := [] }
  let lines := text.splitOn "\n"
  let headerLine := lines.head!
  let work ← Bounded.charge work (headerLine.utf8ByteSize + 1) limits.maxWork "line 1"
  let header ← (c.decodeHeader headerLine).mapError (s!"line 1: {·}")
  let p ← (load header).mapError (s!"line 1: {·}")
  let mut r : Bounded.Replay := { work }
  for (line, i) in (lines.tail!.take (complete - 1)).zipIdx do
    r ← Bounded.replayLine c p limits headerLine.utf8ByteSize r (i + 1) line
  return { definition := some p, validated := some header.validated, state := r.state,
           committed := r.committed, uncommitted := r.pending.isSome || !text.endsWith "\n",
           values := r.payloads.reversed.reverse }

end Suimon.Trace
