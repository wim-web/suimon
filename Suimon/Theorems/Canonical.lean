import Suimon.Theorems.Determinism
import Suimon.Theorems.Semantics
import Suimon.Theorems.Bindings

/-! Canonical item lists: sorting, duplicate removal, and sorted channel data. -/

namespace Suimon
open Semantics

theorem sortedItems_perm (l : List ItemId) : (sortedItems l).Perm l := List.mergeSort_perm l _

theorem sortedItems_pairwise (l : List ItemId) : (sortedItems l).Pairwise (· ≤ ·) := by
  let le := fun (a b : String) => decide (a ≤ b)
  have trans : ∀ a b c, le a b → le b c → le a c := by
    intro a b c hab hbc
    exact decide_eq_true (Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have total : ∀ a b, le a b || le b a := by
    intro a b
    simp only [le, Bool.or_eq_true, decide_eq_true_eq]
    exact Std.le_total
  simpa [sortedItems, le] using List.pairwise_mergeSort trans total l

theorem sortedItems_of_pairwise {l : List ItemId} (h : l.Pairwise (· ≤ ·)) : sortedItems l = l := by
  apply List.mergeSort_of_pairwise
  simpa using h

theorem sortedItems_nodup {l : List ItemId} (h : l.Nodup) : (sortedItems l).Nodup :=
  (sortedItems_perm l).nodup_iff.mpr h

theorem eraseDups_of_nodup {l : List ItemId} (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.eraseDups_cons]
    have parts := List.nodup_cons.mp h
    have same : as.filter (fun b => !b == a) = as := by
      apply List.filter_eq_self.mpr
      intro b hb
      have : b ≠ a := fun eq => parts.1 (eq ▸ hb)
      simpa using this
    rw [same, ih parts.2]

theorem canonical_of_nodup {l : List ItemId} (h : l.Nodup) : canonical l = sortedItems l := by
  simp only [canonical, eraseDups_of_nodup h]

theorem canonical_nodup (l : List ItemId) : (canonical l).Nodup :=
  sortedItems_nodup (eraseDups_nodup l)

theorem canonical_pairwise (l : List ItemId) : (canonical l).Pairwise (· ≤ ·) :=
  sortedItems_pairwise _

theorem canonical_of_sorted {l : List ItemId} (nd : l.Nodup) (sorted : l.Pairwise (· ≤ ·)) : canonical l = l := by
  rw [canonical_of_nodup nd, sortedItems_of_pairwise sorted]

theorem canonical_idem (l : List ItemId) : canonical (canonical l) = canonical l :=
  canonical_of_sorted (canonical_nodup l) (canonical_pairwise l)

theorem canonical_sortedItems {l : List ItemId} (nd : l.Nodup) : canonical (sortedItems l) = sortedItems l :=
  canonical_of_sorted (sortedItems_nodup nd) (sortedItems_pairwise l)

theorem canonical_eq_of_perm {a b : List ItemId} (na : a.Nodup) (h : a.Perm b) : canonical a = canonical b := by
  rw [canonical_of_nodup na, canonical_of_nodup (h.nodup_iff.mp na)]
  exact sortedItems_eq_of_perm a b h

theorem canonical_perm (l : List ItemId) : (canonical l).Perm l.eraseDups := sortedItems_perm _

theorem mem_canonical {l : List ItemId} {x : ItemId} : x ∈ canonical l ↔ x ∈ l := by
  rw [(canonical_perm l).mem_iff, List.mem_eraseDups]

/-- Sorted channel data with distinct ids is determined by its multiset. -/
theorem sorted_data_eq_of_perm {a b : ChannelData} (keys : (a.map (·.1)).Nodup) (h : a.Perm b) :
    a.mergeSort (fun x y => x.1 ≤ y.1) = b.mergeSort (fun x y => x.1 ≤ y.1) := by
  let le := fun (x y : String × List ItemId) => decide (x.1 ≤ y.1)
  have trans : ∀ x y z, le x y → le y z → le x z := by
    intro x y z hxy hyz
    exact decide_eq_true (Std.le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))
  have total : ∀ x y, le x y || le y x := by
    intro x y
    simp only [le, Bool.or_eq_true, decide_eq_true_eq]
    exact Std.le_total
  apply List.Perm.eq_of_pairwise (le := fun (x y : String × List ItemId) => x.1 ≤ y.1)
  · intro x y hx hy hxy hyx
    have sameKey : x.1 = y.1 := Std.le_antisymm hxy hyx
    have memX : x ∈ a := List.mem_mergeSort.mp hx
    have memY : y ∈ a := h.symm.subset (List.mem_mergeSort.mp hy)
    exact eq_of_mapped_nodup (·.1) a keys x y memX memY sameKey
  · simpa [le] using List.pairwise_mergeSort trans total a
  · simpa [le] using List.pairwise_mergeSort trans total b
  · exact (List.mergeSort_perm a le).trans (h.trans (List.mergeSort_perm b le).symm)

end Suimon
