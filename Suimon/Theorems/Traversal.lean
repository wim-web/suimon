import Lean

namespace Suimon

theorem eraseDups_sublist {α : Type} [BEq α] (xs : List α) : xs.eraseDups.Sublist xs := by
  match xs with
  | [] => simp
  | x :: xs =>
    rw [List.eraseDups_cons]
    exact .cons_cons x ((eraseDups_sublist _).trans (List.filter_sublist))
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | x :: xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · intro member
      have := List.mem_eraseDups.mp member
      simp at this
    · exact eraseDups_nodup _
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem mapM_ok_members {α β ε : Type} (f : α → Except ε β) (xs : List α) (ys : List β)
    (accepted : xs.mapM f = .ok ys) : ∀ x ∈ xs, ∃ y, f x = .ok y := by
  induction xs generalizing ys with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases first : f head with
    | error e => simp [first, bind, Except.bind] at accepted
    | ok value =>
      cases rest : tail.mapM f with
      | error e => simp [first, rest, bind, Except.bind] at accepted
      | ok values =>
        intro x member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨value, first⟩
        · exact ih values rest x member

theorem mapM_preserves {α β ε : Type} (observe : α → β) (f : α → Except ε α)
    (xs ys : List α)
    (effect : ∀ x ∈ xs, ∀ y, f x = .ok y → observe y = observe x)
    (accepted : xs.mapM f = .ok ys) : ys.map observe = xs.map observe := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure] at accepted
    cases accepted
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases first : f head with
    | error e => simp [first, bind, Except.bind] at accepted
    | ok value =>
      cases rest : tail.mapM f with
      | error e => simp [first, rest, bind, Except.bind] at accepted
      | ok values =>
        have tailEq := ih values (fun x member => effect x (by simp [member])) rest
        have headEq := effect head (by simp) value first
        simp only [first, rest, bind, Except.bind, pure, Except.pure] at accepted
        cases accepted
        simp [headEq, tailEq]

theorem foldlM_preserves {α β γ ε : Type} (observe : α → γ) (f : α → β → Except ε α)
    (xs : List β) (start last : α)
    (effect : ∀ s x, x ∈ xs → ∀ next, f s x = .ok next → observe next = observe s)
    (accepted : xs.foldlM f start = .ok last) : observe last = observe start := by
  induction xs generalizing start with
  | nil => cases accepted; rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons] at accepted
    cases first : f start x with
    | error e => simp [first, bind, Except.bind] at accepted
    | ok middle =>
      have tailEq := ih middle (fun s y member => effect s y (by simp [member]))
        (by simpa [first, bind, Except.bind] using accepted)
      exact tailEq.trans (effect start x (by simp) middle first)

theorem mapM_eq_map {α β ε : Type} (f : α → Except ε β) (value : α → β)
    (xs : List α) (ys : List β)
    (effect : ∀ x ∈ xs, ∀ y, f x = .ok y → y = value x)
    (accepted : xs.mapM f = .ok ys) : ys = xs.map value := by
  induction xs generalizing ys with
  | nil => simpa only [List.mapM_nil, List.map_nil, pure, Except.pure, Except.ok.injEq] using accepted.symm
  | cons x xs ih =>
    simp only [List.mapM_cons] at accepted
    cases head : f x with
    | error e => simp [head, bind, Except.bind] at accepted
    | ok y =>
      cases tail : xs.mapM f with
      | error e => simp [head, tail, bind, Except.bind] at accepted
      | ok rest =>
        have hy := effect x (by simp) y head
        have hr := ih rest (fun z hz => effect z (by simp [hz])) tail
        simpa [head, tail, bind, Except.bind, pure, Except.pure, hy, hr] using accepted.symm

theorem foldlM_eq_foldl {α β ε : Type} (f : α → β → Except ε α)
    (value : α → β → α) (xs : List β) (start last : α)
    (effect : ∀ s x, x ∈ xs → ∀ next, f s x = .ok next → next = value s x)
    (accepted : xs.foldlM f start = .ok last) : last = xs.foldl value start := by
  induction xs generalizing start with
  | nil => cases accepted; rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons] at accepted
    cases head : f start x with
    | error e => simp [head, bind, Except.bind] at accepted
    | ok middle =>
      have first := effect start x (by simp) middle head
      have rest := ih middle (fun s y member => effect s y (by simp [member]))
        (by simpa [head, bind, Except.bind] using accepted)
      simpa [List.foldl_cons, first] using rest

end Suimon
