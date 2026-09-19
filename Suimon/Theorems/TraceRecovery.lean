import Suimon.Theorems.Replay

namespace Suimon.Trace
open Lean

theorem checkMetadata_fields (c next : Cursor) (e : Event) (accepted : checkMetadata c e = .ok next) :
    next.state = c.state ∧ next.boundary = c.boundary ∧ next.completed = c.completed ∧
    next.expected = c.expected ∧ next.currentOp = c.currentOp ∧ next.commands = c.commands := by
  simp only [checkMetadata, bind, Except.bind, pure, Except.pure] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases txn : c.txn <;> simp only [txn] at accepted
  all_goals
    split at accepted <;> try contradiction
    cases accepted
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem checkPayload_effect (c next : Cursor) (e : Event) (accepted : checkPayload c e = .ok next) :
    replayOps c.state e.op.toList = .ok next.state ∧
    ((next.boundary = c.boundary ∧ next.completed = c.completed) ∨
      (e.type = "transaction.committed" ∧ e.op = none ∧ next.state = c.state ∧
        next.boundary = c.state ∧ next.completed = c.completed ++ [e.txn])) := by
  simp only [checkPayload, checkPayloadWith, bind, Except.bind, pure, Except.pure] at accepted
  cases expected : c.expected <;> simp only [expected] at accepted
  · split at accepted
    · rename_i commit
      split at accepted <;> try contradiction
      rename_i valid
      have noOp : e.op = none := by
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at valid
        exact valid.1.1
      cases accepted
      simp [noOp, replayOps, pure, Except.pure, beq_iff_eq.mp commit]
    · cases op : e.op with
      | none => simp [op, Option.toExcept, bind, Except.bind] at accepted
      | some command =>
        simp only [op, Option.toExcept, bind, Except.bind] at accepted
        split at accepted <;> try contradiction
        split at accepted <;> try contradiction
        cases transition : step c.state command with
        | error reject => simp [transition] at accepted
        | ok state =>
          simp only [transition, Except.ok.injEq] at accepted
          subst next
          simp [replayOps, op, List.foldlM_cons, transition]
  · split at accepted <;> try contradiction
    rename_i valid
    have noOp : e.op = none := by
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at valid
      exact valid.1.1
    cases accepted
    simp [replayOps, noOp, pure, Except.pure]

/-- Every accepted record either verifies a fact, executes its command, or
    advances the durable boundary at an explicit commit marker. --/
theorem checkEvent_effect (c next : Cursor) (e : Event) (accepted : checkEvent c e = .ok next) :
    replayOps c.state e.op.toList = .ok next.state ∧
    ((next.boundary = c.boundary ∧ next.completed = c.completed) ∨
      (e.type = "transaction.committed" ∧ e.op = none ∧ next.state = c.state ∧
        next.boundary = c.state ∧ next.completed = c.completed ++ [e.txn])) := by
  cases metadata : checkMetadata c e with
  | error reject => simp [checkEvent, metadata, bind, Except.bind] at accepted
  | ok ready =>
    have payload : checkPayload ready e = .ok next := by simpa [checkEvent, metadata, bind, Except.bind] using accepted
    obtain ⟨state, boundary, completed, _⟩ := checkMetadata_fields c ready e metadata
    simpa only [state, boundary, completed] using checkPayload_effect ready next e payload


def eventCommands (events : List Event) : List Op := events.flatMap (·.op.toList)

theorem checkEvents_state (c next : Cursor) (events : List Event)
    (accepted : events.foldlM checkEvent c = .ok next) :
    replayOps c.state (eventCommands events) = .ok next.state := by
  induction events generalizing c with
  | nil => cases accepted; rfl
  | cons e events ih =>
    simp only [List.foldlM_cons] at accepted
    cases checked : checkEvent c e with
    | error d => simp [checked, bind, Except.bind] at accepted
    | ok middle =>
      have tail : events.foldlM checkEvent middle = .ok next := by simpa [checked, bind, Except.bind] using accepted
      have head := (checkEvent_effect c middle e checked).1
      simp only [eventCommands, List.flatMap_cons, replay_append, head, bind, Except.bind]
      exact ih middle tail

theorem checkEvent_boundary_without_commit (c next : Cursor) (e : Event)
    (accepted : checkEvent c e = .ok next) (notCommit : e.type ≠ "transaction.committed") :
    next.boundary = c.boundary := by
  rcases (checkEvent_effect c next e accepted).2 with same | committed
  · exact same.1
  · exact False.elim (notCommit committed.1)

theorem checkEvents_boundary_without_commit (c next : Cursor) (events : List Event)
    (accepted : events.foldlM checkEvent c = .ok next)
    (noCommit : ∀ e ∈ events, e.type ≠ "transaction.committed") : next.boundary = c.boundary := by
  induction events generalizing c with
  | nil => cases accepted; rfl
  | cons e events ih =>
    simp only [List.foldlM_cons] at accepted
    cases checked : checkEvent c e with
    | error d => simp [checked, bind, Except.bind] at accepted
    | ok middle =>
      have tail : events.foldlM checkEvent middle = .ok next := by simpa [checked, bind, Except.bind] using accepted
      exact (ih middle tail (fun e h => noCommit e (by simp [h]))).trans
        (checkEvent_boundary_without_commit c middle e checked (noCommit e (by simp)))

/-- Recovery cannot expose the effects of any accepted uncommitted suffix,
    including a suffix ending between a command and its last expected fact. --/
theorem recover_torn_suffix (g : Graph) (durable torn : List Event) (boundary next : Cursor)
    (prefixAccepted : durable.foldlM checkEvent {state := .initial g, boundary := .initial g} = .ok boundary)
    (suffixAccepted : torn.foldlM checkEvent boundary = .ok next)
    (noCommit : ∀ e ∈ torn, e.type ≠ "transaction.committed") :
    recover g (durable ++ torn) = .ok boundary.boundary := by
  have same := checkEvents_boundary_without_commit boundary next torn suffixAccepted noCommit
  simp [recover, List.foldlM_append, prefixAccepted, suffixAccepted, same, bind, Except.bind, pure, Except.pure]

/-- Every boundary reached by the checker is a replay of a pre of the
    accepted command log; no partially executed operation supplies a boundary. --/
theorem checkEvents_boundary_prefix (c next : Cursor) (events : List Event)
    (accepted : events.foldlM checkEvent c = .ok next) :
    next.boundary = c.boundary ∨ ∃ pre suffix, events = pre ++ suffix ∧
      replayOps c.state (eventCommands pre) = .ok next.boundary := by
  induction events generalizing c with
  | nil => cases accepted; exact .inl rfl
  | cons e events ih =>
    simp only [List.foldlM_cons] at accepted
    cases checked : checkEvent c e with
    | error d => simp [checked, bind, Except.bind] at accepted
    | ok middle =>
      have tail : events.foldlM checkEvent middle = .ok next := by simpa [checked, bind, Except.bind] using accepted
      obtain ⟨head, effects⟩ := checkEvent_effect c middle e checked
      rcases ih middle tail with same | ⟨pre, suffix, partition, replayed⟩
      · rcases effects with unchanged | committed
        · exact .inl (same.trans unchanged.1)
        · refine .inr ⟨[e], events, rfl, ?_⟩
          have stateEq : next.boundary = middle.state := same.trans (committed.2.2.2.1.trans committed.2.2.1.symm)
          simpa only [eventCommands, List.flatMap_cons, List.flatMap_nil, List.append_nil, stateEq] using head
      · refine .inr ⟨e :: pre, suffix, by simp only [List.cons_append, partition], ?_⟩
        simpa only [eventCommands, List.flatMap_cons, replay_append, head, bind, Except.bind] using replayed

theorem recover_replays_prefix (g : Graph) (events : List Event) (s : State)
    (recovered : recover g events = .ok s) :
    ∃ pre suffix, events = pre ++ suffix ∧ replayOps (.initial g) (eventCommands pre) = .ok s := by
  cases scanned : events.foldlM checkEvent {state := .initial g, boundary := .initial g} with
  | error d => simp [recover, scanned, bind, Except.bind] at recovered
  | ok cursor =>
    have eq : cursor.boundary = s := by simpa [recover, scanned, bind, Except.bind, pure, Except.pure] using recovered
    rcases checkEvents_boundary_prefix _ cursor events scanned with unchanged | pre
    · exact ⟨[], events, rfl, by rw [← eq, unchanged]; rfl⟩
    · simpa only [eq] using pre

theorem check_is_recover (g : Graph) (events : List Event) (s : State)
    (checked : check g events = .ok s) : recover g events = .ok s := by
  cases scanned : events.foldlM checkEvent {state := .initial g, boundary := .initial g} with
  | error d => simp [check, scanned, bind, Except.bind] at checked
  | ok cursor =>
    have done : finish cursor = .ok s := by simpa [check, scanned, bind, Except.bind] using checked
    cases txn : cursor.txn with
    | none =>
      have eq : cursor.boundary = s := by simpa [finish, txn] using done
      simp [recover, scanned, eq, bind, Except.bind, pure, Except.pure]
    | some id => simp [finish, txn] at done

theorem checkMetadata_txn (c next : Cursor) (e : Event) (accepted : checkMetadata c e = .ok next) : next.txn.isSome = true := by
  simp only [checkMetadata, bind, Except.bind, pure, Except.pure] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases txn : c.txn <;> simp only [txn] at accepted
  all_goals
    split at accepted <;> try contradiction
    cases accepted
    simp [txn]

theorem checkPayload_ready (c next : Cursor) (e : Event) (pending : c.txn.isSome = true)
    (accepted : checkPayload c e = .ok next) (done : next.txn = none) : next.state = next.boundary := by
  simp only [checkPayload, checkPayloadWith, bind, Except.bind, pure, Except.pure] at accepted
  cases expected : c.expected <;> simp only [expected] at accepted
  · split at accepted
    · split at accepted <;> try contradiction
      cases accepted; rfl
    · cases op : e.op with
      | none => simp [op, Option.toExcept, bind, Except.bind] at accepted
      | some command =>
        simp only [op, Option.toExcept, bind, Except.bind] at accepted
        split at accepted <;> try contradiction
        split at accepted <;> try contradiction
        cases transition : step c.state command with
        | error d => simp [transition] at accepted
        | ok state =>
          simp only [transition, Except.ok.injEq] at accepted
          subst next
          change c.txn = none at done
          rw [done] at pending; contradiction
  · split at accepted <;> try contradiction
    cases accepted
    change c.txn = none at done
    rw [done] at pending; contradiction

theorem checkEvent_ready (c next : Cursor) (e : Event) (accepted : checkEvent c e = .ok next)
    (done : next.txn = none) : next.state = next.boundary := by
  cases metadata : checkMetadata c e with
  | error reject => simp [checkEvent, metadata, bind, Except.bind] at accepted
  | ok ready =>
    have payload : checkPayload ready e = .ok next := by simpa [checkEvent, metadata, bind, Except.bind] using accepted
    exact checkPayload_ready ready next e (checkMetadata_txn c ready e metadata) payload done

theorem checkEvents_ready (c next : Cursor) (events : List Event)
    (initial : c.txn = none → c.state = c.boundary)
    (accepted : events.foldlM checkEvent c = .ok next) (done : next.txn = none) : next.state = next.boundary := by
  induction events generalizing c with
  | nil => cases accepted; exact initial done
  | cons e events ih =>
    simp only [List.foldlM_cons] at accepted
    cases checked : checkEvent c e with
    | error d => simp [checked, bind, Except.bind] at accepted
    | ok middle =>
      have tail : events.foldlM checkEvent middle = .ok next := by simpa [checked, bind, Except.bind] using accepted
      exact ih middle (checkEvent_ready c middle e checked) tail

/-- T11 at the event protocol boundary: checking a complete log reproduces
    exactly the state obtained by replaying its commands through step. --/
theorem check_replays_commands (g : Graph) (events : List Event) (s : State)
    (checked : check g events = .ok s) : replayOps (.initial g) (eventCommands events) = .ok s := by
  cases scanned : events.foldlM checkEvent {state := .initial g, boundary := .initial g} with
  | error d => simp [check, scanned, bind, Except.bind] at checked
  | ok cursor =>
    have done : finish cursor = .ok s := by simpa [check, scanned, bind, Except.bind] using checked
    cases txn : cursor.txn with
    | none =>
      have eq : cursor.boundary = s := by simpa [finish, txn] using done
      have state := checkEvents_ready _ cursor events (fun _ => rfl) scanned txn
      simpa only [state, eq] using checkEvents_state _ cursor events scanned
    | some id => simp [finish, txn] at done

end Suimon.Trace
