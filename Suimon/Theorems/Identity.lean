import Suimon.Identity
import Suimon.Theorems.WireText

namespace Suimon
open WireText

theorem not_isDigit_colon : ¬ isDigit ':' := by decide

theorem decodeParts_flatMap (parts : List String) :
    ∀ fuel, (parts.flatMap encodePart).length ≤ fuel → decodeParts fuel (parts.flatMap encodePart) = some parts := by
  induction parts with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons part rest ih =>
    intro fuel hlen
    obtain ⟨d, ds, hdigits, hd, hds, hval, -⟩ := natDigits_spec part.length []
    have hchars : (part :: rest).flatMap encodePart =
        (d :: ds) ++ ':' :: (part.toList ++ rest.flatMap encodePart) := by
      simp [List.flatMap_cons, encodePart, hdigits]
    rw [hchars] at hlen ⊢
    have hlen' := hlen
    simp only [List.length_append, List.length_cons] at hlen'
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hspan := spanDigits_append (d :: ds) (':' :: (part.toList ++ rest.flatMap encodePart))
      (by simpa [hd] using hds) (fun c r h => by cases h; exact not_isDigit_colon) 0
    rw [List.cons_append] at hspan ⊢
    rw [decodeParts, hspan, hval]
    have htake : (part.toList ++ rest.flatMap encodePart).take part.length = part.toList := by
      rw [← String.length_toList]; simp
    have hdrop : (part.toList ++ rest.flatMap encodePart).drop part.length = rest.flatMap encodePart := by
      rw [← String.length_toList]; simp
    have hle : part.length ≤ (part.toList ++ rest.flatMap encodePart).length := by
      rw [← String.length_toList]; simp
    simp only [hle, ite_true, htake, hdrop, String.ofList_toList]
    rw [ih fuel (by omega)]
    rfl

theorem decodeIdentity_identity (parts : List String) : decodeIdentity (identity parts) = some parts := by
  unfold decodeIdentity identity
  rw [String.toList_ofList]
  exact decodeParts_flatMap parts _ (Nat.le_refl _)

theorem identity_injective {a b : List String} (h : identity a = identity b) : a = b := by
  have ha := decodeIdentity_identity a
  rw [h, decodeIdentity_identity] at ha
  exact (Option.some.inj ha).symm

end Suimon
