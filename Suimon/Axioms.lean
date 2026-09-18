import Suimon.Trace.Check
namespace Suimon

/-- Environmental assumptions are parameters, never kernel axioms. --/
structure Assumptions (oracle : Oracle) where
  deterministic : oracle.Deterministic
  /-- A1: observers see committed states only. --/
  observed : List State
  committed : List State
  atomicity : ∀ s ∈ observed, s ∈ committed
  /-- A2: timestamps in committed records are monotone. --/
  times : List Time
  monotoneClock : times.Pairwise (· ≤ ·)
  /-- A3: IDs are globally unique, including abandoned attempts. --/
  attemptIds : List AttemptId
  leaseTokens : List LeaseToken
  uniqueAttempts : attemptIds.Nodup
  uniqueTokens : leaseTokens.Nodup
  /-- A5: a crash may tear the uncommitted suffix but cannot change this prefix. --/
  durable : List Trace.Event
  recovered : List Trace.Event
  persistence : recovered = durable
end Suimon
