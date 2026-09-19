import Suimon.Theorems.TraceWire

namespace Suimon.Trace

/-- A commit strictly increases the committed transaction count. Equality of
    the counts therefore implies that the durable boundary did not move. --/
theorem checkEvent_commit_count (c next : Cursor) (e : Event)
    (accepted : checkEvent c e = .ok next) :
    c.completed.length ≤ next.completed.length ∧
      (next.completed.length = c.completed.length → next.boundary = c.boundary) := by
  rcases (checkEvent_effect c next e accepted).2 with same | committed
  · simp [same.1, same.2]
  · have changed := committed.2.2.2.2
    simp only [changed, List.length_append, List.length_singleton]
    exact ⟨by omega, by omega⟩

theorem checkEvents_commit_count (c next : Cursor) (events : List Event)
    (accepted : events.foldlM checkEvent c = .ok next) :
    c.completed.length ≤ next.completed.length ∧
      (next.completed.length = c.completed.length → next.boundary = c.boundary) := by
  induction events generalizing c with
  | nil => cases accepted; exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | cons e events ih =>
    cases head : checkEvent c e with
    | error d => simp [List.foldlM_cons, head, bind, Except.bind] at accepted
    | ok middle =>
      have tail : events.foldlM checkEvent middle = .ok next := by
        simpa [List.foldlM_cons, head, bind, Except.bind] using accepted
      obtain ⟨headLe, headSame⟩ := checkEvent_commit_count c middle e head
      obtain ⟨tailLe, tailSame⟩ := ih middle tail
      refine ⟨Nat.le_trans headLe tailLe, ?_⟩
      intro same
      have middleSame : middle.completed.length = c.completed.length := by omega
      exact (tailSame (by omega)).trans (headSame middleSame)

/-- Every prefix of an accepted uncommitted batch is accepted, and all such
    prefixes have exactly the same durable boundary. No prefix-acceptance or
    operation-replay equality is assumed. --/
theorem uncommitted_prefix (c last : Cursor) (events : List Event) (count : Nat)
    (accepted : events.foldlM checkEvent c = .ok last) (noCommit : last.completed = c.completed) :
    ∃ middle, (events.take count).foldlM checkEvent c = .ok middle ∧ middle.boundary = c.boundary := by
  have partition : events = events.take count ++ events.drop count := (List.take_append_drop count events).symm
  rw [partition, List.foldlM_append] at accepted
  cases pre : (events.take count).foldlM checkEvent c with
  | error d => simp [pre, bind, Except.bind] at accepted
  | ok middle =>
    have tail : (events.drop count).foldlM checkEvent middle = .ok last := by
      simpa [pre, bind, Except.bind] using accepted
    obtain ⟨preLe, preSame⟩ := checkEvents_commit_count c middle (events.take count) pre
    have tailLe := (checkEvents_commit_count middle last (events.drop count) tail).1
    have sameLength : middle.completed.length = c.completed.length := by rw [noCommit] at tailLe; omega
    exact ⟨middle, rfl, preSame sameLength⟩

/-- Arbitrary cuts through the recorder's command/fact batch, including inside
    an operation's fact list, discard all changes since the preceding commit. --/
theorem recordCommands_torn_prefix (c : Cursor) (ops : List Op) (txn : String) (time : Nat)
    (state : State) (events : List Event) (clock count : Nat)
    (empty : c.expected = []) (named : txn.isEmpty = false) (monotone : c.time ≤ time)
    (pending : (c.txn = none ∧ txn ∉ c.completed) ∨ c.txn = some txn)
    (recorded : recordCommands c.state ops c.sequence txn time = .ok (state, events, clock)) :
    ∃ middle, (events.take count).foldlM checkEvent c = .ok middle ∧ middle.boundary = c.boundary := by
  obtain ⟨last, accepted, _, _, _, _, _, completed, _, _⟩ :=
    recordCommands_checked c ops txn time state events clock empty named monotone pending recorded
  exact uncommitted_prefix c last events count accepted completed

/-- The same arbitrary-cut result through the real string encoder and decoder. --/
theorem recordCommands_torn_jsonl (g : Graph) (durable : List Event) (c : Cursor)
    (ops : List Op) (txn : String) (time : Nat) (state : State) (events : List Event) (clock count : Nat)
    (prefixAccepted : durable.foldlM checkEvent {state := .initial g, boundary := .initial g} = .ok c)
    (empty : c.expected = []) (named : txn.isEmpty = false) (monotone : c.time ≤ time)
    (pending : (c.txn = none ∧ txn ∉ c.completed) ∨ c.txn = some txn)
    (recorded : recordCommands c.state ops c.sequence txn time = .ok (state, events, clock)) :
    recoverText g ((durable ++ events.take count).map encodeEvent) = .ok c.boundary := by
  obtain ⟨middle, accepted, boundary⟩ :=
    recordCommands_torn_prefix c ops txn time state events clock count empty named monotone pending recorded
  apply recoverText_encode
  simp [recover, List.foldlM_append, prefixAccepted, accepted, boundary, bind, Except.bind, pure, Except.pure]

end Suimon.Trace
