import Suimon.Theorems.WorkTime

namespace Suimon

/-- Parts of the commit invariant unaffected by leaf scheduling metadata. --/
def staticOK (s : State) : Bool :=
  s.channels.all channelOK && unique (s.channels.map (·.id)) &&
  unique (s.instances.map (·.id)) && unique (s.instances.map instanceKey) && accountingOK s && loopBoundsOK s

theorem invariants_parts (s : State) : Invariants s ↔ staticOK s = true ∧ leaseOK s = true ∧ attemptOK s = true := by
  simp only [Invariants, invariants, staticOK, Bool.and_eq_true]
  constructor <;> intro h <;> grind only []

def InstanceShape (a b : Instance) : Prop :=
  a.id = b.id ∧ a.node = b.node ∧ a.path = b.path ∧ a.trigger = b.trigger ∧
  a.iteration = b.iteration ∧ a.extraIterations = b.extraIterations

theorem instance_present (s : State) (id : InstanceId) :
    (s.instance? id).isSome = (s.instances.map (·.id)).contains id := by
  rw [Bool.eq_iff_iff]
  simp [State.instance?, List.find?_isSome, List.contains_iff_mem]

theorem find_congr_on {α : Type} (xs : List α) (p q : α → Bool)
    (same : ∀ x ∈ xs, p x = q x) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?_cons, same x (by simp)]
    rw [ih (fun y hy => same y (by simp [hy]))]

theorem all_congr_on {α : Type} (xs : List α) (p q : α → Bool)
    (same : ∀ x ∈ xs, p x = q x) : xs.all p = xs.all q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor <;> intro h x hx
  · rw [← same x hx]; exact h x hx
  · rw [same x hx]; exact h x hx

theorem staticOK_map (s next : State) (update : Instance → Instance)
    (channels : next.channels = s.channels) (frames : next.frames = s.frames)
    (consumed : next.consumed = s.consumed) (instances : next.instances = s.instances.map update)
    (shape : ∀ i ∈ s.instances, InstanceShape (update i) i) : staticOK next = staticOK s := by
  have ids : next.instances.map (·.id) = s.instances.map (·.id) := by
    rw [instances, List.map_map]
    exact List.map_congr_left (fun i member => (shape i member).1)
  have keys : next.instances.map instanceKey = s.instances.map instanceKey := by
    rw [instances, List.map_map]
    apply List.map_congr_left
    intro i member
    obtain ⟨_, node, path, trigger, _⟩ := shape i member
    simp [instanceKey, node, path, trigger]
  have present : ∀ id, (next.instance? id).isSome = (s.instance? id).isSome := by
    intro id
    rw [instance_present, instance_present, ids]
  have accounts : accountingOK next = accountingOK s := by
    simp only [accountingOK, channels, consumed, present]
  have loops : loopBoundsOK next = loopBoundsOK s := by
    simp only [loopBoundsOK, instances, List.all_map]
    apply all_congr_on
    intro i member
    obtain ⟨id, node, path, _, iteration, extra⟩ := shape i member
    simp only [Function.comp_def, State.node?, State.frame?, frames, node, path, id, iteration, extra]
  simp only [staticOK, channels, ids, keys, accounts, loops]

theorem instance?_map (s : State) (update : Instance → Instance)
    (ids : ∀ i ∈ s.instances, (update i).id = i.id) (id : InstanceId) :
    ({s with instances := s.instances.map update} : State).instance? id = (s.instance? id).map update := by
  simp only [State.instance?, List.find?_map]
  congr 1
  apply find_congr_on
  intro i member
  simp [ids i member]

theorem setInstance_lookup (s : State) (old replacement : Instance) (sameId : replacement.id = old.id)
    (id : InstanceId) :
    (setInstance s replacement).instance? id = (s.instance? id).map
      (fun i => if i.id == old.id then replacement else i) := by
  have ids : ∀ i ∈ s.instances, (if i.id == old.id then replacement else i).id = i.id := by
    intro i _
    split
    · rename_i selected
      exact sameId.trans (beq_iff_eq.mp selected).symm
    · rfl
  have result := instance?_map s (fun i => if i.id == old.id then replacement else i) ids id
  simpa only [setInstance, sameId] using result

theorem staticOK_setInstance (s : State) (old replacement : Instance) (safe : Invariants s)
    (memberOld : old ∈ s.instances) (shape : InstanceShape replacement old) :
    staticOK (setInstance s replacement) = staticOK s := by
  apply staticOK_map s (setInstance s replacement) (fun i => if i.id == replacement.id then replacement else i) rfl rfl rfl rfl
  intro i memberI
  split
  · rename_i selected
    have same := unique_instance safe memberI memberOld ((beq_iff_eq.mp selected).trans shape.1)
    subst i
    exact shape
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Suimon
