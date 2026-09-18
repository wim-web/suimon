import Suimon.Theorems.CompletedRun

namespace Suimon

/-- The cursor cannot hide an unrecorded input item at a drained boundary. --/
theorem Channel.drained_item_consumed (c : Channel) (drained : c.pendingItems = [])
    (item : ItemId) (member : item ∈ c.items) : Token.item item ∈ c.placed.take c.consumed := by
  have token := (Effects.item_mem c item).mp member
  have split : c.placed = c.placed.take c.consumed ++ c.placed.drop c.consumed :=
    (List.take_append_drop c.consumed c.placed).symm
  rw [split, List.mem_append] at token
  rcases token with consumed | pending
  · exact consumed
  · have stillPending : item ∈ c.pendingItems := List.mem_filterMap.mpr ⟨.item item, pending, rfl⟩
    rw [drained] at stillPending
    contradiction

theorem Invariants.drained_item_receipt {s : State} (safe : Invariants s)
    (c : Channel) (member : c ∈ s.channels) (drained : c.pendingItems = [])
    (item : ItemId) (present : item ∈ c.items) :
    ∃ receipt ∈ s.consumed, receipt.channel = c.id ∧ receipt.item = item := by
  have token := c.drained_item_consumed drained item present
  obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp token
  have indexed : (Token.item item, index) ∈ (c.placed.take c.consumed).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr atIndex
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  have accounting := safe.1.2
  simp only [accountingOK, Bool.and_eq_true] at accounting
  have all := List.all_eq_true.mp accounting.1.2 c member
  have recorded := List.all_eq_true.mp all (.item item, index) indexed
  obtain ⟨receipt, memberReceipt, fields⟩ := List.any_eq_true.mp recorded
  simp only [Bool.and_eq_true, beq_iff_eq] at fields
  exact ⟨receipt, memberReceipt, fields.1.1, fields.2⟩

theorem succeededDrained_input_receipt (s : State) (safe : Invariants s)
    (finished : succeededDrained s = true) (c : Channel) (member : c ∈ s.channels)
    (internal : (c.path.isEmpty && c.exit) = false) (item : ItemId) (present : item ∈ c.items) :
    ∃ receipt ∈ s.consumed, receipt.channel = c.id ∧ receipt.item = item := by
  simp only [succeededDrained, Bool.and_eq_true] at finished
  have drained := List.all_eq_true.mp finished.1.2 c member
  simp only [internal, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at drained
  exact safe.drained_item_receipt c member drained.2 item present

/-- An accepted consume of an item creates exactly its audit entry. No lease
    operation or re-emission is involved in this update. --/
theorem consume_item_receipt (s next : State) (channel who : String) (item : ItemId)
    (accepted : consume s channel who (some item) = .ok next) :
    ∃ c ∈ s.channels, c.id = channel ∧ c.pending.head? = some (.item item) ∧
      next.consumed = s.consumed ++ [{ channel, index := c.consumed, item, byInstance := who }] := by
  cases found : s.channels.find? (·.id == channel) with
  | none => simp [consume, found, Option.toExcept, bind, Except.bind] at accepted
  | some c =>
    have member := List.mem_of_find?_eq_some found
    have idEq : c.id = channel := by simpa using List.find?_some found
    cases pending : c.pending.head? with
    | none => simp [consume, found, pending, Option.toExcept, bind, Except.bind] at accepted
    | some token =>
      cases token with
      | eos => simp [consume, found, pending, Option.toExcept, require, bind, Except.bind] at accepted
      | item actual =>
        by_cases same : item = actual
        · subst actual
          simp only [consume, found, pending, Option.toExcept, require, BEq.rfl, ↓reduceIte,
            bind, Except.bind, pure, Except.pure] at accepted
          cases accepted
          exact ⟨c, member, idEq, pending, rfl⟩
        · simp [consume, found, pending, Option.toExcept, require, same, bind, Except.bind] at accepted

end Suimon
