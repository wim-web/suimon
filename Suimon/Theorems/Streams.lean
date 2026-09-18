import Suimon.Theorems.Replay
namespace Suimon

/-- T4: the EOS marker occupies the final position, with no following token. --/
theorem eos_final (s : State) (c : Channel) (safe : Invariants s) (member : c ∈ s.channels) :
    (c.placed.takeWhile (· != .eos)).length + (if c.closed then 1 else 0) = c.placed.length := by
  have all : s.channels.all channelOK = true := by
    simp only [Invariants, invariants, Bool.and_eq_true] at safe
    exact safe.1.1.1.1.1.1.1
  have h := List.all_eq_true.mp all c member
  simp only [channelOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

/-- T2 safety form: every consumed item has a durable accounting record. --/
theorem consumed_items_accounted (s : State) (safe : Invariants s) :
    s.channels.all (fun c => (c.placed.take c.consumed).zipIdx.all fun (t, idx) =>
      match t with
      | .eos => true
      | .item id => s.consumed.any (fun a => a.channel == c.id && a.index == idx && a.item == id)) = true := by
  simp only [Invariants, invariants, Bool.and_eq_true] at safe
  have h := safe.1.2
  simp only [accountingOK, Bool.and_eq_true] at h
  exact h.1.2

/-- The scheduler-independent part of T9: a pure item transform preserves input permutations. --/
theorem deterministic_item_multiset (f : ItemId → ItemId) (a b : List ItemId)
    (sameInputs : a.Perm b) : (a.map f).Perm (b.map f) := sameInputs.map f

theorem deterministic_item_counts (f : ItemId → ItemId) (a b : List ItemId) (item : ItemId)
    (sameInputs : a.Perm b) : (a.map f).count item = (b.map f).count item :=
  (sameInputs.map f).count_eq item

/-- A4 explicitly removes arrival-order dependence from opaque leaf output. --/
theorem deterministic_leaf (oracle : Oracle) (h : oracle.Deterministic)
    (node : NodeId) (a b : List (PortName × ItemId)) (sameInputs : a.Perm b) :
    oracle.leaf node a = oracle.leaf node b := h node a b sameInputs
/-- T10 local rule: a head item enables spawning, with no EOS premise. --/
theorem spawn_without_eos (c : Channel) (item : ItemId) (tail : List Token)
    (h : c.pending = .item item :: tail) : spawnInputReady c item = true := by
  simp only [spawnInputReady, h, List.head?_cons]
  change (item == item) = true
  simp
end Suimon
