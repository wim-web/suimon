import Suimon.State
import Suimon.Theorems.Identity

/-! Identities of records. `Key.split` inverts `Key.within`, so an identity determines its run path
    and its label; a label refers to the records of its run injectively (`Key.relative_inj`); hence
    every key is injective in its arguments. Keys of different kinds differ in the tag their labels
    start with (`Key.kind?`). Every key is an identity `within` builds (`Key.Within`), and on those
    `Key.child` is injective, so the runs that different records own have different paths. -/

namespace Suimon.Key

/-! ### Scoped identities -/

theorem within_eq (path : Path) (label : String) : within path label = identity (path ++ [label]) := by
  unfold within; rfl

theorem split_within (path : Path) (label : String) : split (within path label) = some (path, label) := by
  unfold split
  rw [within_eq, decodeIdentity_identity]
  simp

theorem eq_within_of_split {id : String} {path : Path} {label : String} (h : split id = some (path, label)) :
    id = within path label := by
  unfold split at h
  split at h
  · rename_i parts _
    split at h
    · rename_i last hlast
      split at h
      · rename_i hid
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
        rw [List.dropLast_concat, within_eq]
        exact hid.symm
      · cases h
    · cases h
  · cases h

theorem within_inj {p q : Path} {a b : String} (h : within p a = within q b) : p = q ∧ a = b := by
  rw [within_eq, within_eq] at h
  obtain ⟨h1, h2⟩ := List.append_inj' (identity_injective h) rfl
  exact ⟨h1, by simpa using h2⟩

@[simp] theorem scope_within (p : Path) (a : String) : scope (within p a) = p := by
  simp [scope, split_within]

@[simp] theorem child_within (p : Path) (a : String) : child (within p a) = p ++ [a] := by
  simp [child, split_within]

@[simp] theorem relative_within (p : Path) (a : String) : relative p (within p a) = [a] := by
  simp [relative, split_within]

theorem child_ne_nil (id : String) : child id ≠ [] := by
  unfold child
  split <;> simp

theorem relative_ne_nil (p : Path) (id : String) : relative p id ≠ [] := by
  unfold relative
  split
  · split <;> simp
  · simp

theorem relative_inj {p : Path} {a b : String} (h : relative p a = relative p b) : a = b := by
  unfold relative at h
  rcases ha : split a with _ | ⟨ra, la⟩ <;> rcases hb : split b with _ | ⟨rb, lb⟩ <;>
    simp only [ha, hb] at h
  · simpa using h
  · split at h
    · simp at h
    · simpa using h
  · split at h
    · simp at h
    · simpa using h
  · split at h <;> split at h
    · rename_i hra hrb
      simp only [List.cons.injEq, and_true] at h
      rw [eq_within_of_split ha, eq_within_of_split hb, hra, hrb, h]
    · simp at h
    · simp at h
    · simpa using h

/-- An identity that `within` builds; every key is one. -/
def Within (id : String) : Prop := ∃ path label, id = within path label

theorem child_inj {a b : String} (ha : Within a) (hb : Within b) (h : child a = child b) : a = b := by
  obtain ⟨p, x, rfl⟩ := ha
  obtain ⟨q, y, rfl⟩ := hb
  rw [child_within, child_within] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  have h3 : x = y := by simpa using h2
  rw [h1, h3]

theorem child_within_ne (p : Path) (a : String) : child (within p a) ≠ p := by
  rw [child_within]
  intro h
  have := congrArg List.length h
  simp at this

/-! ### Keys -/

theorem within_invocation (path : Path) (placement : String) (trigger : Option ResultId) :
    Within (invocation path placement trigger) := ⟨_, _, rfl⟩
theorem within_owned (kind owner : String) (parts : List String) : Within (owned kind owner parts) := ⟨_, _, rfl⟩
theorem within_task (execution name : String) : Within (task execution name) := ⟨_, _, rfl⟩
theorem within_aggregate (path : Path) (placement : String) : Within (aggregate path placement) := ⟨_, _, rfl⟩

@[simp] theorem scope_invocation (path : Path) (placement : String) (trigger : Option ResultId) :
    scope (invocation path placement trigger) = path := scope_within _ _

theorem child_invocation_ne (path : Path) (placement : String) (trigger : Option ResultId) :
    child (invocation path placement trigger) ≠ path := child_within_ne _ _

@[simp] theorem scope_task (execution name : String) : scope (task execution name) = scope execution := by
  simp [task, owned]

/-- The run of an invocation is one level below the invocation's run. -/
theorem length_child_invocation (path : Path) (placement : String) (trigger : Option ResultId) :
    (child (invocation path placement trigger)).length = path.length + 1 := by
  simp [invocation]

/-- The run of a task is one level below the run of its execution. -/
theorem length_child_task (execution name : String) :
    (child (task execution name)).length = (scope execution).length + 1 := by
  simp [task, owned]

theorem owned_inj {k k' o o' : String} {ps ps' : List String} (h : owned k o ps = owned k' o' ps')
    (hlen : ps.length = ps'.length) : k = k' ∧ o = o' ∧ ps = ps' := by
  obtain ⟨h1, h2⟩ := within_inj h
  have h3 := identity_injective h2
  simp only [List.cons_append, List.cons.injEq] at h3
  obtain ⟨hk, h4⟩ := h3
  obtain ⟨h5, h6⟩ := List.append_inj' h4 hlen
  rw [h1] at h5
  exact ⟨hk, relative_inj h5, h6⟩

theorem invocation_inj {a b : Path} {m n : String} {t t' : Option String}
    (h : invocation a m t = invocation b n t') : a = b ∧ m = n ∧ t = t' := by
  obtain ⟨rfl, h2⟩ := within_inj h
  have h3 := identity_injective h2
  simp only [List.cons_append, List.cons.injEq, true_and, List.nil_append] at h3
  refine ⟨rfl, h3.1, ?_⟩
  have h4 := h3.2
  cases t <;> cases t' <;> simp only [Option.toList_none, Option.toList_some, List.flatMap_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at h4
  · rfl
  · exact absurd h4.symm (relative_ne_nil _ _)
  · exact absurd h4 (relative_ne_nil _ _)
  · rw [relative_inj h4]

theorem task_inj {a b m n : String} (h : task a m = task b n) : a = b ∧ m = n := by
  obtain ⟨-, h1, h2⟩ := owned_inj h rfl
  exact ⟨h1, by simpa using h2⟩

theorem callResult_inj {a b : String} {m n : Nat} (h : callResult a m = callResult b n) : a = b ∧ m = n := by
  obtain ⟨-, h1, h2⟩ := owned_inj h rfl
  exact ⟨h1, Nat.repr_injective (by simpa using h2)⟩

theorem aggregate_inj {a b : Path} {m n : String} (h : aggregate a m = aggregate b n) : a = b ∧ m = n := by
  obtain ⟨h1, h2⟩ := within_inj h
  exact ⟨h1, by simpa using identity_injective h2⟩

theorem taskOutput_inj {a b m n : String} {i j : Nat} (h : taskOutput a m i = taskOutput b n j) :
    a = b ∧ m = n ∧ i = j := by
  obtain ⟨-, h1, h2⟩ := owned_inj h rfl
  simp only [List.cons.injEq, and_true] at h2
  exact ⟨h1, h2.1, Nat.repr_injective h2.2⟩

theorem list_inj {a b : String} (h : list a = list b) : a = b := (owned_inj h rfl).2.1

theorem returned_inj {a b : String} (h : returned a = returned b) : a = b := (owned_inj h rfl).2.1

/-! ### Kinds -/

/-- The tag the label of a key starts with. -/
def kind? (id : String) : Option String :=
  (split id).bind fun (_, label) => (decodeIdentity label).bind (·.head?)

theorem kind?_within (p : Path) (k : String) (rest : List String) :
    kind? (within p (identity (k :: rest))) = some k := by
  simp [kind?, split_within, decodeIdentity_identity]

@[simp] theorem kind?_invocation (path : Path) (placement : String) (trigger : Option ResultId) :
    kind? (invocation path placement trigger) = some "invocation" := kind?_within _ _ _
@[simp] theorem kind?_task (execution name : String) : kind? (task execution name) = some "task" :=
  kind?_within _ _ _
@[simp] theorem kind?_callResult (call : String) (index : Nat) : kind? (callResult call index) = some "result" :=
  kind?_within _ _ _
@[simp] theorem kind?_aggregate (path : Path) (placement : String) :
    kind? (aggregate path placement) = some "aggregate" := kind?_within _ _ _
@[simp] theorem kind?_taskOutput (execution name : String) (index : Nat) :
    kind? (taskOutput execution name index) = some "output" := kind?_within _ _ _
@[simp] theorem kind?_list (execution : String) : kind? (list execution) = some "list" := kind?_within _ _ _
@[simp] theorem kind?_returned (invocation : String) : kind? (returned invocation) = some "return" :=
  kind?_within _ _ _

/-- Keys whose labels start with different tags differ. -/
theorem ne_of_kind? {a b : String} (h : kind? a ≠ kind? b) : a ≠ b := fun e => h (congrArg _ e)

theorem invocation_ne_task {a : Path} {m b n : String} {t : Option String} : invocation a m t ≠ task b n :=
  ne_of_kind? (by simp)
theorem invocation_ne_aggregate {a b : Path} {m n : String} {t : Option String} :
    invocation a m t ≠ aggregate b n := ne_of_kind? (by simp)
theorem task_ne_aggregate {a m : String} {b : Path} {n : String} : task a m ≠ aggregate b n := ne_of_kind? (by simp)
theorem aggregate_ne_callResult {path : Path} {name x : String} {k : Nat} : aggregate path name ≠ callResult x k :=
  ne_of_kind? (by simp)
theorem taskOutput_ne_callResult {e n x : String} {i k : Nat} : taskOutput e n i ≠ callResult x k :=
  ne_of_kind? (by simp)
theorem list_ne_callResult {e x : String} {k : Nat} : list e ≠ callResult x k := ne_of_kind? (by simp)
theorem returned_ne_callResult {o x : String} {k : Nat} : returned o ≠ callResult x k := ne_of_kind? (by simp)
theorem callResult_ne_taskOutput {x e n : String} {k i : Nat} : callResult x k ≠ taskOutput e n i :=
  ne_of_kind? (by simp)
theorem aggregate_ne_taskOutput {path : Path} {x e n : String} {i : Nat} : aggregate path x ≠ taskOutput e n i :=
  ne_of_kind? (by simp)
theorem list_ne_taskOutput {x e n : String} {i : Nat} : list x ≠ taskOutput e n i := ne_of_kind? (by simp)
theorem returned_ne_taskOutput {x e n : String} {i : Nat} : returned x ≠ taskOutput e n i := ne_of_kind? (by simp)

/-! ### Runs that records own -/

/-- The run of a sub-workflow invocation is the run of no other invocation. -/
theorem child_invocation_inj {a b : Path} {m n : String} {t t' : Option String}
    (h : child (invocation a m t) = child (invocation b n t')) : a = b ∧ m = n ∧ t = t' :=
  invocation_inj (child_inj (within_invocation _ _ _) (within_invocation _ _ _) h)

/-- The run of a workflow task is the run of no other task. -/
theorem child_task_inj {a b m n : String} (h : child (task a m) = child (task b n)) : a = b ∧ m = n :=
  task_inj (child_inj (within_task _ _) (within_task _ _) h)

/-- The run of an invocation is the run of no task. -/
theorem child_invocation_ne_task {a : Path} {m b n : String} {t : Option String} :
    child (invocation a m t) ≠ child (task b n) := fun h =>
  invocation_ne_task (child_inj (within_invocation _ _ _) (within_task _ _) h)

end Suimon.Key
