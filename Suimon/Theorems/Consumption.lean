import Suimon.Theorems.ClosingStep

/-! Draining channels that hold no pending items creates no consumption record. -/

namespace Suimon

/-- Channels with the given identifiers hold no pending item. -/
def Quiet (ids : List String) (st : State) : Prop :=
  ∀ d ∈ st.channels, d.id ∈ ids → d.pendingItems = []

theorem drop_mem_of_le {α : Type} {l : List α} {m n : Nat} (le : n ≤ m) {x : α} (h : x ∈ l.drop m) :
    x ∈ l.drop n := by
  have : l.drop m = (l.drop n).drop (m - n) := by
    rw [List.drop_drop, Nat.add_sub_of_le le]
  rw [this] at h
  exact List.drop_subset _ _ h

theorem pendingItems_bump (c : Channel) (h : c.pendingItems = []) :
    ({ c with consumed := c.consumed + 1 } : Channel).pendingItems = [] := by
  simp only [Channel.pendingItems, Channel.pending, List.filterMap_eq_nil_iff] at h ⊢
  intro t member
  exact h t (drop_mem_of_le (Nat.le_succ _) member)

/-- The relation threaded through folds of consumes over quiet channels. -/
def QuietStep (ids : List String) (a b : State) : Prop :=
  Quiet ids a → b.consumed = a.consumed ∧ Quiet ids b

theorem QuietStep.refl (ids : List String) (a : State) : QuietStep ids a a := fun q => ⟨rfl, q⟩
theorem QuietStep.trans {ids : List String} {a b c : State} (ab : QuietStep ids a b) (bc : QuietStep ids b c) :
    QuietStep ids a c := by
  intro qa
  obtain ⟨eab, qb⟩ := ab qa
  obtain ⟨ebc, qc⟩ := bc qb
  exact ⟨ebc.trans eab, qc⟩

theorem consume_quiet (s next : State) (channel who : String) (ids : List String) (selected : channel ∈ ids)
    (accepted : consume s channel who none = .ok next) : QuietStep ids s next := by
  intro quiet
  cases found : s.channels.find? (·.id == channel) with
  | none => simp [consume, found, Option.toExcept, bind, Except.bind] at accepted
  | some c =>
    have memberC : c ∈ s.channels := List.mem_of_find?_eq_some found
    have idC : c.id = channel := by simpa using List.find?_some found
    have quietC : c.pendingItems = [] := quiet c memberC (idC ▸ selected)
    cases pending : c.pending.head? with
    | none => simp [consume, found, pending, Option.toExcept, bind, Except.bind] at accepted
    | some t =>
      have headMem : t ∈ c.pending := List.mem_of_mem_head? pending
      have eos : t = .eos := by
        cases t with
        | eos => rfl
        | item x =>
          exfalso
          have : x ∈ c.pendingItems := List.mem_filterMap.mpr ⟨.item x, headMem, rfl⟩
          rw [quietC] at this
          exact absurd this (List.not_mem_nil)
      subst eos
      simp only [consume, found, pending, Option.toExcept, bind, Except.bind, pure, Except.pure, List.append_nil] at accepted
      cases accepted
      refine ⟨rfl, ?_⟩
      intro d hd hid
      obtain ⟨e, memberE, eq⟩ := List.mem_map.mp hd
      subst eq
      by_cases same : (e.id == c.id) = true
      · simp only [same, ↓reduceIte] at hid ⊢
        exact pendingItems_bump e (quiet e memberE hid)
      · simp only [same, Bool.false_eq_true, ↓reduceIte] at hid ⊢
        exact quiet e memberE hid

theorem consumeRest_quiet (s next : State) (c : Channel) (who : String) (ids : List String) (selected : c.id ∈ ids)
    (accepted : consumeRest s c who = .ok next) : QuietStep ids s next :=
  foldlM_effect (QuietStep ids) (QuietStep.refl ids) (fun _ _ _ => QuietStep.trans) _ c.pending s next
    (fun a _ _ b h => consume_quiet a b c.id who ids selected h) accepted

theorem consumeChannels_quiet (s next : State) (channels : List Channel) (who : String)
    (accepted : consumeChannels s channels who = .ok next) : QuietStep (channels.map (·.id)) s next :=
  foldlM_effect (QuietStep (channels.map (·.id))) (QuietStep.refl _) (fun _ _ _ => QuietStep.trans) _ channels s next
    (fun a c member b h => consumeRest_quiet a b c who _ (List.mem_map.mpr ⟨c, member, rfl⟩) h) accepted

/-- Draining stream controls consume only EOS: the consumption log is unchanged. -/
theorem effect_propagateEos_records (s next : State) (path : Path) (node : NodeId) (safe : Invariants s)
    (h : transition s (.propagateEos path node) = .ok next) : next.consumed = s.consumed := by
  simp only [transition, Option.toExcept, bind, Except.bind, pure, Except.pure] at h
  cases hn : getNode s path node with
  | error e => simp [hn] at h
  | ok n =>
    simp only [hn] at h
    split at h
    · contradiction
    · rename_i u1 hk
      split at h
      · contradiction
      · rename_i u2 hd
        have drained := require_ok _ _ _ u2 hd
        split at h
        · contradiction
        · rename_i u3 hch
          have quiet : ∀ s1 : State, s1.channels = s.channels → Quiet ((s.incoming path node).map (·.id)) s1 := by
            intro s1 ch1 d hd hid
            rw [ch1] at hd
            obtain ⟨c, memberC, idC⟩ := List.mem_map.mp hid
            have inChannels : c ∈ s.channels := (List.mem_filter.mp memberC).1
            have same : c = d := unique_channel safe inChannels hd idC
            subst same
            have := List.all_eq_true.mp drained c memberC
            simp only [Bool.and_eq_true, List.isEmpty_iff] at this
            exact this.2
          have finish : ∀ s1 s2 : State, s1.channels = s.channels → s1.consumed = s.consumed →
              consumeChannels s1 (s.incoming path node) (makeInstance path n .succeeded).id = .ok s2 →
              closeOutputs s2 path n = .ok next → next.consumed = s.consumed := by
            intro s1 s2 ch1 co1 consumed closed
            obtain ⟨eq, _⟩ := consumeChannels_quiet s1 s2 _ _ consumed (quiet s1 ch1)
            rw [closeOutputs_writes s2 next path n closed, applyWrites_consumed, eq, co1]
          cases found : s.nodeInstance? path node with
          | none =>
            simp only [found] at h
            split at h
            · contradiction
            · rename_i s1 created
              have value := freshInstance_value s s1 _ created
              subst value
              split at h
              · contradiction
              · rename_i s2 consumed
                exact finish { s with instances := s.instances ++ [makeInstance path n .succeeded] } s2 rfl rfl consumed h
          | some old =>
            simp only [found] at h
            split at h
            · contradiction
            · split at h
              · contradiction
              · rename_i s2 consumed
                exact finish (setInstance s { old with status := .succeeded }) s2 rfl rfl consumed h

end Suimon
