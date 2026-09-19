import Suimon.Theorems.Safety

namespace Suimon.Explore

theorem longestId_bound (used : List String) (id : String) (member : id ∈ used) :
    id.length ≤ (longestId used).length := by
  induction used with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    simp only [longestId]
    split
    · rename_i bound
      rcases member with rfl | member
      · omega
      · have := ih member; omega
    · rename_i bound
      rcases member with rfl | member
      · omega
      · exact ih member

theorem freshId_not_mem (tag : String) (used : List String) : freshId tag used ∉ used := by
  intro member
  have bound := longestId_bound used (freshId tag used) member
  simp only [freshId, String.length_append] at bound
  have one : ":".length = 1 := rfl
  rw [one] at bound
  omega

theorem freshId_nonempty (tag : String) (used : List String) : (freshId tag used).isEmpty = false := by
  apply Bool.eq_false_iff.mpr
  intro isEmpty
  have empty := String.isEmpty_iff.mp isEmpty
  have sizes := congrArg String.length empty
  simp only [freshId, String.length_append] at sizes
  have one : ":".length = 1 := rfl
  have zero : "".length = 0 := rfl
  rw [one, zero] at sizes
  omega

end Suimon.Explore
