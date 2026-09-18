import Suimon.Theorems.Determinism

namespace Suimon

/-- An EOS-terminated prefix cannot be extended at a valid boundary. --/
theorem closed_channel_prefix_eq (before after : Channel)
    (oldSafe : channelOK before = true) (newSafe : channelOK after = true)
    (closed : before.closed = true) (history : before.placed.isPrefixOf after.placed = true) :
    after.placed = before.placed := by
  obtain ⟨suffix, prefixEq⟩ := List.isPrefixOf_iff_prefix.mp history
  have eos : Token.eos ∈ before.placed := by simpa [Channel.closed] using closed
  have newClosed : after.closed = true := by
    simp [Channel.closed, ← prefixEq, eos]
  simp only [channelOK, Bool.and_eq_true] at oldSafe newSafe
  have endBefore := oldSafe.1.1.2
  simp only [closed, ↓reduceIte, beq_iff_eq] at endBefore
  have shorter : (before.placed.takeWhile (· != Token.eos)).length ≠ before.placed.length := by omega
  have takeEq : after.placed.takeWhile (· != Token.eos) = before.placed.takeWhile (· != Token.eos) := by
    rw [← prefixEq, List.takeWhile_append]
    simp [shorter]
  have lengths : after.placed.length = before.placed.length := by
    have a := endBefore
    have b := newSafe.1.1.2
    simp only [newClosed, ↓reduceIte, beq_iff_eq, takeEq] at a b
    omega
  have empty : suffix = [] := by
    have hlen := congrArg List.length prefixEq
    simp only [List.length_append, lengths] at hlen
    have : suffix.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  simpa [empty] using prefixEq.symm

theorem step_retains_closed_channel (s next : State) (op : Op) (c : Channel)
    (initial : Invariants s) (member : c ∈ s.channels) (closed : c.closed = true)
    (accepted : step s op = .ok next) :
    ∃ d ∈ next.channels, d.id = c.id ∧ d.placed = c.placed := by
  have oldSafe : channelOK c = true := by
    have all := initial
    simp only [Invariants, invariants, Bool.and_eq_true] at all
    exact List.all_eq_true.mp all.1.1.1.1.1.1.1 c member
  rcases step_ok_cases s op next accepted with ⟨_, same⟩ | ⟨_, _, _, safe, history⟩
  · subst next
    exact ⟨c, member, rfl, rfl⟩
  · simp only [historyOK, Bool.and_eq_true] at history
    obtain ⟨d, memberD, props⟩ := List.any_eq_true.mp (List.all_eq_true.mp history.2 c member)
    simp only [Bool.and_eq_true, beq_iff_eq] at props
    have newSafe : channelOK d = true := by
      simp only [Invariants, invariants, Bool.and_eq_true] at safe
      exact List.all_eq_true.mp safe.1.1.1.1.1.1.1 d memberD
    exact ⟨d, memberD, props.1.1.symm, closed_channel_prefix_eq c d oldSafe newSafe closed props.1.2⟩

theorem ConformingSteps.retains_closed_channel {allows : State → Op → Prop}
    {s next : State} {ops : List Op} (run : ConformingSteps allows s ops next)
    (initial : Invariants s) (c : Channel) (member : c ∈ s.channels) (closed : c.closed = true) :
    ∃ d ∈ next.channels, d.id = c.id ∧ d.placed = c.placed := by
  induction run generalizing c with
  | nil => exact ⟨c, member, rfl, rfl⟩
  | @cons s middle last op ops allowed accepted tail ih =>
    obtain ⟨d, memberD, idD, dataD⟩ := step_retains_closed_channel s middle op c initial member closed accepted
    have closedD : d.closed = true := by simpa [Channel.closed, dataD] using closed
    obtain ⟨e, memberE, idE, dataE⟩ := ih (preserves_invariants s middle op initial accepted) d memberD closedD
    exact ⟨e, memberE, idE.trans idD, dataE.trans dataD⟩

end Suimon
