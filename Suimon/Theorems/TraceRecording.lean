import Suimon.Theorems.TraceRecovery

namespace Suimon.Trace
open Lean

private theorem recording_require_ok (ok : Bool) (code message : String) (u : Unit)
    (accepted : require ok code message = .ok u) : ok = true := by
  cases ok <;> simp [require] at accepted ⊢

/-- Conditions on the metadata alone; model transitions and facts are checked separately. --/
def MetadataMatches (c : Cursor) (e : Event) : Prop :=
  e.schema_version = 2 ∧ e.sequence = c.sequence ∧ e.txn.isEmpty = false ∧ c.time ≤ e.recorded_at ∧
    ((c.txn = none ∧ e.txn ∉ c.completed) ∨ c.txn = some e.txn)

theorem checkMetadata_record (c : Cursor) (e : Event) (metadata : MetadataMatches c e) :
    checkMetadata c e = .ok {c with txn := some e.txn, sequence := c.sequence + 1, time := e.recorded_at} := by
  obtain ⟨version, sequence, named, time, started⟩ := metadata
  rcases started with ⟨fresh, unused⟩ | same
  · simp [checkMetadata, version, sequence, named, time, fresh, unused, bind, Except.bind, pure, Except.pure]
  · cases c
    simp_all [checkMetadata, bind, Except.bind, pure, Except.pure]

@[simp] theorem commandType_not_commit (op : Op) : commandType op ≠ "transaction.committed" := by
  cases op <;> simp only [commandType] <;> decide

@[simp] theorem recordFacts_length (facts : List Fact) (sequence : Nat) (txn : String) (time : Nat) :
    (recordFacts facts sequence txn time).length = facts.length := by
  induction facts generalizing sequence with
  | nil => rfl
  | cons f fs ih => simp [recordFacts, ih]

@[simp] theorem recordOp_length (s next : State) (op : Op) (sequence : Nat) (txn : String) (time : Nat) :
    (recordOp s next op sequence txn time).length = 1 + (effects s next op).length := by
  simp [recordOp, Nat.add_comm]

theorem checkFacts_record (c : Cursor) (facts : List Fact) (txn : String) (time : Nat)
    (expected : c.expected = facts) (pending : c.txn = some txn) (named : txn.isEmpty = false) (clock : c.time ≤ time) :
    (recordFacts facts c.sequence txn time).foldlM checkEvent c =
      .ok {c with expected := [], sequence := c.sequence + facts.length, time := if facts.isEmpty then c.time else time} := by
  induction facts generalizing c with
  | nil => simp [recordFacts, pure, Except.pure]; cases c; simp_all
  | cons f fs ih =>
    let e : Event := {sequence := c.sequence, txn, recorded_at := time, type := f.type, data := f.data}
    let advanced : Cursor := {c with sequence := c.sequence + 1, time, txn := some txn}
    have metadata : checkMetadata c e = .ok advanced :=
      checkMetadata_record c e ⟨rfl, rfl, named, clock, .inr pending⟩
    have payload : checkPayload advanced e = .ok {advanced with expected := fs} := by
      simp [checkPayload, checkPayloadWith, advanced, expected, e, sameJson_self, bind, Except.bind, pure, Except.pure]
    have checked : checkEvent c e = .ok {advanced with expected := fs} := by
      simp [checkEvent, metadata, payload, bind, Except.bind]
    have rest := ih {advanced with expected := fs} rfl rfl (Nat.le_refl _)
    simp only [recordFacts, List.foldlM_cons]
    change (checkEvent c e >>= fun middle => (recordFacts fs (c.sequence + 1) txn time).foldlM checkEvent middle) = _
    rw [checked]
    simp only [bind, Except.bind]
    rw [rest]
    cases c
    simp_all [advanced, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem recordTime_properties (time clock : Nat) (op : Op) (recorded : recordTime time op = .ok clock) :
    time ≤ clock ∧ (opTime op).all (· == clock) = true := by
  simp only [recordTime, require, bind, Except.bind, pure, Except.pure] at recorded
  split at recorded <;> try contradiction
  rename_i monotone
  cases recorded
  constructor
  · simpa using monotone
  · cases opTime op <;> simp


theorem checkOp_record (c : Cursor) (next : State) (op : Op) (txn : String) (time : Nat)
    (empty : c.expected = []) (named : txn.isEmpty = false) (clock : c.time ≤ time)
    (pending : (c.txn = none ∧ txn ∉ c.completed) ∨ c.txn = some txn)
    (opClock : (opTime op).all (· == time) = true) (accepted : step c.state op = .ok next) :
    (recordOp c.state next op c.sequence txn time).foldlM checkEvent c = .ok {c with
      state := next
      sequence := c.sequence + (recordOp c.state next op c.sequence txn time).length
      time := time
      txn := some txn
      expected := []
      currentOp := some op
      commands := c.commands + 1} := by
  let command : Event := {sequence := c.sequence, txn, recorded_at := time, type := commandType op, op := some op}
  let ready : Cursor := {c with sequence := c.sequence + 1, time, txn := some txn}
  let after : Cursor := {ready with state := next, expected := effects c.state next op, currentOp := some op, commands := c.commands + 1}
  have metadata : checkMetadata c command = .ok ready :=
    checkMetadata_record c command ⟨rfl, rfl, named, clock, pending⟩
  have payload : checkPayload ready command = .ok after := by
    simp [checkPayload, checkPayloadWith, ready, after, command, empty, commandType_not_commit, opClock, accepted,
      Option.toExcept, bind, Except.bind, pure, Except.pure]
  have checked : checkEvent c command = .ok after := by simp [checkEvent, metadata, payload, bind, Except.bind]
  have facts := checkFacts_record after (effects c.state next op) txn time rfl rfl named (Nat.le_refl _)
  simp only [recordOp, List.foldlM_cons]
  change (checkEvent c command >>= fun mid => (recordFacts (effects c.state next op) (c.sequence + 1) txn time).foldlM checkEvent mid) = _
  rw [checked]
  simp only [bind, Except.bind]
  rw [facts]
  simp [after, ready, Nat.add_assoc, Nat.add_comm]

/-- Checking the records emitted by an arbitrary accepted command sequence
    preserves its uncommitted boundary and reconstructs the modeled state. --/
theorem recordCommands_checked (c : Cursor) (ops : List Op) (txn : String) (time : Nat)
    (last : State) (events : List Event) (clock : Nat)
    (empty : c.expected = []) (named : txn.isEmpty = false) (monotone : c.time ≤ time)
    (pending : (c.txn = none ∧ txn ∉ c.completed) ∨ c.txn = some txn)
    (recorded : recordCommands c.state ops c.sequence txn time = .ok (last, events, clock)) :
    ∃ next, events.foldlM checkEvent c = .ok next ∧ next.state = last ∧ next.boundary = c.boundary ∧
      next.sequence = c.sequence + events.length ∧ next.time ≤ clock ∧
      next.txn = (if ops.isEmpty then c.txn else some txn) ∧ next.completed = c.completed ∧
      next.expected = [] ∧ next.commands = c.commands + ops.length := by
  induction ops generalizing c time last events clock with
  | nil =>
    simp only [recordCommands, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at recorded
    obtain ⟨rfl, rfl, rfl⟩ := recorded
    exact ⟨c, rfl, rfl, rfl, by simp, monotone, rfl, rfl, empty, by simp⟩
  | cons op ops ih =>
    simp only [recordCommands] at recorded
    cases timed : recordTime time op with
    | error reject => simp [timed, bind, Except.bind] at recorded
    | ok atTime =>
      cases executed : step c.state op with
      | error reject => simp [timed, executed, bind, Except.bind] at recorded
      | ok state =>
        let head := recordOp c.state state op c.sequence txn atTime
        let middle : Cursor := {c with
          state := state
          sequence := c.sequence + head.length
          time := atTime
          txn := some txn
          expected := []
          currentOp := some op
          commands := c.commands + 1}
        have properties := recordTime_properties time atTime op timed
        have headChecked : head.foldlM checkEvent c = .ok middle :=
          checkOp_record c state op txn atTime empty named (Nat.le_trans monotone properties.1) pending properties.2 executed
        cases tail : recordCommands state ops (c.sequence + head.length) txn atTime with
        | error reject =>
          have rejected : recordCommands state ops
              (c.sequence + (recordOp c.state state op c.sequence txn atTime).length) txn atTime = .error reject := tail
          simp only [timed, executed, bind, Except.bind, rejected] at recorded
          contradiction
        | ok result =>
          obtain ⟨last', tailEvents, lastTime⟩ := result
          have resultEq : (last', head ++ tailEvents, lastTime) = (last, events, clock) := by
            simpa only [timed, executed, head, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using recorded
          simp only [Prod.mk.injEq] at resultEq
          obtain ⟨rfl, rfl, rfl⟩ := resultEq
          obtain ⟨next, tailChecked, stateEq, boundaryEq, sequenceEq, timeLe, txnEq, completedEq, expectedEq, commandsEq⟩ :=
            ih middle atTime last' tailEvents lastTime rfl (Nat.le_refl _) (.inr rfl) tail
          refine ⟨next, ?_, stateEq, boundaryEq, ?_, timeLe, ?_, completedEq, expectedEq, ?_⟩
          · simp only [List.foldlM_append, headChecked, bind, Except.bind]
            exact tailChecked
          · simpa only [middle, List.length_append, Nat.add_assoc] using sequenceEq
          · simpa only [middle, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ite_self] using txnEq
          · simpa only [middle, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using commandsEq


theorem checkCommit_record (c : Cursor) (txn : String) (time : Nat) (empty : c.expected = [])
    (pending : c.txn = some txn) (named : txn.isEmpty = false) (clock : c.time ≤ time) (nonempty : 0 < c.commands) :
    checkEvent c (commitEvent c.sequence txn time) = .ok {c with
      boundary := c.state
      sequence := c.sequence + 1
      time := time
      txn := none
      completed := c.completed ++ [txn]
      currentOp := none
      commands := 0} := by
  have metadata := checkMetadata_record c (commitEvent c.sequence txn time) ⟨rfl, rfl, named, clock, .inr pending⟩
  simp only [checkEvent, metadata, bind, Except.bind]
  simp [checkPayload, checkPayloadWith, commitEvent, empty, nonempty, bind, Except.bind, pure, Except.pure]

/-- Transaction recording and event checking agree for arbitrary accepted
    command sequences. Metadata freshness is relative to the supplied cursor. --/
theorem recordTransaction_checked (c : Cursor) (ops : List Op) (txn : String) (time : Nat)
    (last : State) (events : List Event) (empty : c.expected = []) (idle : c.txn = none)
    (zero : c.commands = 0) (fresh : txn ∉ c.completed) (monotone : c.time ≤ time)
    (recorded : recordTransaction c.state ops c.sequence txn time = .ok (last, events)) :
    ∃ next, events.foldlM checkEvent c = .ok next ∧ finish next = .ok last ∧
      next.boundary = last ∧ next.completed = c.completed ++ [txn] := by
  simp only [recordTransaction] at recorded
  cases nonempty : require (!ops.isEmpty) "EMPTY_TRANSACTION" with
  | error reject => simp [nonempty, bind, Except.bind] at recorded
  | ok u =>
    have nonemptyOps : ops.isEmpty = false := by simpa using recording_require_ok _ _ _ u nonempty
    cases named : require (!txn.isEmpty) "EMPTY_TRANSACTION_ID" with
    | error reject => simp [nonempty, named, bind, Except.bind] at recorded
    | ok v =>
      have namedTxn : txn.isEmpty = false := by simpa using recording_require_ok _ _ _ v named
      cases body : recordCommands c.state ops c.sequence txn time with
      | error reject => simp [nonempty, named, body, bind, Except.bind] at recorded
      | ok result =>
        obtain ⟨state, records, clock⟩ := result
        have eq : (state, records ++ [commitEvent (c.sequence + records.length) txn clock]) = (last, events) := by
          simpa only [nonempty, named, body, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using recorded
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
        obtain ⟨middle, scanned, stateEq, _, sequenceEq, clockLe, txnEq, completedEq, expectedEq, commandsEq⟩ :=
          recordCommands_checked c ops txn time state records clock empty namedTxn monotone (.inl ⟨idle, fresh⟩) body
        have pending : middle.txn = some txn := by simpa only [nonemptyOps, Bool.false_eq_true, ↓reduceIte] using txnEq
        have commands : 0 < middle.commands := by
          rw [commandsEq, zero, Nat.zero_add]
          exact List.length_pos_iff.mpr (List.isEmpty_eq_false_iff.mp nonemptyOps)
        have checked := checkCommit_record middle txn clock expectedEq pending namedTxn clockLe commands
        let next : Cursor := {middle with
          boundary := middle.state
          sequence := middle.sequence + 1
          time := clock
          txn := none
          completed := middle.completed ++ [txn]
          currentOp := none
          commands := 0}
        refine ⟨next, ?_, ?_, stateEq, by simp only [next, completedEq]⟩
        · simp only [List.foldlM_append, scanned, bind, Except.bind, List.foldlM_cons, List.foldlM_nil]
          rw [← sequenceEq, checked]
          rfl
        · simp [finish, next, stateEq]

/-- A complete transaction generated from the initial graph round-trips through
    the actual event checker, with all public facts and metadata verified. --/
theorem recordTransaction_roundtrip (g : Graph) (ops : List Op) (txn : String) (time : Nat)
    (last : State) (events : List Event)
    (recorded : recordTransaction (.initial g) ops 1 txn time = .ok (last, events)) :
    check g events = .ok last := by
  obtain ⟨cursor, scanned, finished, _, _⟩ := recordTransaction_checked
    {state := .initial g, boundary := .initial g} ops txn time last events rfl rfl rfl (by simp) (Nat.zero_le _) recorded
  simp [check, scanned, finished, bind, Except.bind]

end Suimon.Trace
