import Suimon.Step

namespace Suimon.Scheduler
open Lean

inductive TimerKind where
  | expireLease | promoteRetry | renew
  deriving DecidableEq, BEq, Repr, ToJson, FromJson

structure Timer where
  deadline : Time
  kind : TimerKind
  target : InstanceId
  attempt : AttemptId := ""
  token : LeaseToken := ""
  deriving DecidableEq, BEq, Repr, ToJson, FromJson

def Timer.operation (t : Timer) (now : Time) : Op :=
  match t.kind with
  | .expireLease => .expireLease t.target now
  | .promoteRetry => .promoteRetry t.target now
  | .renew => .renew {«instance» := t.target, attempt := t.attempt, token := t.token, now}

def instanceTimer (i : Instance) : Option Timer :=
  match i.status with
  | .running => i.lease.map fun l => {deadline := l.until_, kind := .expireLease, target := i.id}
  | .retryWait => i.retryAt.map fun deadline => {deadline, kind := .promoteRetry, target := i.id}
  | _ => none

def mandatoryTimers (s : State) : List Timer := s.instances.filterMap instanceTimer

def renewalAt (until_ duration : Nat) : Option Time :=
  let deadline := max (until_ - max 1 (duration / 2)) (until_ - duration + 1)
  if deadline < until_ then some deadline else none

def renewalTimer (s : State) (owned : List AttemptId) (autoRenew : Bool) (i : Instance) : Option Timer := do
  if !(autoRenew && i.status == .running) then none else do
    let lease ← i.lease
    if !owned.contains lease.attempt then none else do
      let node ← s.node? i.path i.node
      match node.kind with
      | .leaf retry _ =>
        let deadline ← renewalAt lease.until_ retry.leaseSeconds
        some {deadline, kind := .renew, target := i.id, attempt := lease.attempt, token := lease.token}
      | _ => none

/-- Expiry/retry maintenance precedes optional renewals, independently of worker
    capacity, callback ownership, and whether a stall has been announced. --/
def timers (s : State) (owned : List AttemptId) (autoRenew : Bool) : List Timer :=
  mandatoryTimers s ++ s.instances.filterMap (renewalTimer s owned autoRenew)

def firstDue (now : Time) : List Timer → Option Timer
  | [] => none
  | t :: ts => if t.deadline ≤ now then some t else firstDue now ts

def earlier (a b : Option Time) : Option Time :=
  match a, b with
  | none, x | x, none => x
  | some x, some y => some (min x y)

def earliest : List Timer → Option Time
  | [] => none
  | t :: ts => earlier (some t.deadline) (earliest ts)

def due (deadline : Option Time) (now : Time) : Bool := deadline.any (· ≤ now)

def pollEnabled (deadline : Option Time) : Bool := deadline.isSome

/-- Announcing a stall removes only its own notification deadline. --/
def waitDeadline (ts : List Timer) (stale : Option Time) (announced : Bool) : Option Time :=
  earlier (earliest ts) (if announced then none else stale)

/-- A fresh clock sample is checked before publishing a stall. --/
def announceStall (ts : List Timer) (stale : Option Time) (announced : Bool) (now : Time) : Bool :=
  !due (earliest ts) now && !announced && due stale now

def maintenance (s : State) (owned : List AttemptId) (autoRenew : Bool) (now : Time) : Option Op :=
  (firstDue now (timers s owned autoRenew)).map (·.operation now)

/-- One actual model-operation attempt. Validation failures are observable;
    only the absence of due maintenance may return `ok none`. --/
def service (s : State) (owned : List AttemptId) (autoRenew : Bool) (now : Time) : Result (Option State) := do
  match maintenance s owned autoRenew now with
  | none => pure none
  | some op => return some (← step s op)

/-- A wait turn first samples the clock, then may block only while this predicate
    is false. An incoming message also wakes the turn and invalidates its cache. --/
def wake (deadline : Option Time) (now : Time) (message : Bool) : Bool :=
  message || due deadline now

def waitPrefix (deadline : Option Time) (clock : Nat → Time) (poll : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => waitPrefix deadline clock poll n || (poll n && wake deadline (clock n) false)

/-- Clock progress and scheduling fairness are environmental conditions, not
    conclusions about arbitrary Go callbacks, persistence, or the OS. --/
structure PollProgress (clock : Nat → Time) (poll : Nat → Bool) : Prop where
  monotone : ∀ a b, a ≤ b → clock a ≤ clock b
  unbounded : ∀ time, ∃ n, time ≤ clock n
  fair : ∀ n, ∃ k, n ≤ k ∧ poll k = true

end Suimon.Scheduler
