import Suimon.Theorems.Streams
import Suimon.Execution
import Init.Data.List.Sort.Lemmas

namespace Suimon

/-- The exact retry rule, including items consumed by downstream nodes. --/
theorem placeToken_duplicate (c : Channel) (t : Token)
    (seen : c.placed.contains t = true) :
    placeToken c t = if c.closed then
      .error { code := "AFTER_EOS", message := c.id } else .ok c := by
  have member : t ∈ c.placed := by simpa using seen
  cases hc : c.closed <;> simp [placeToken, require, member, hc, bind, Except.bind, pure, Except.pure]

private theorem mapM_identity_of_ok {α : Type} (f : α → Result α) (xs ys : List α)
    (identity : ∀ x ∈ xs, ∀ y, f x = .ok y → y = x)
    (accepted : xs.mapM f = .ok ys) : ys = xs := by
  induction xs generalizing ys with
  | nil => simpa [List.mapM_nil, pure, Except.pure] using accepted.symm
  | cons x xs ih =>
    simp only [List.mapM_cons] at accepted
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at accepted
    | ok y =>
      have same := identity x (by simp) y hx
      subst y
      cases ht : xs.mapM f with
      | error e => simp [hx, ht, bind, Except.bind] at accepted
      | ok zs =>
        have rest := ih zs (fun z hz => identity z (by simp [hz])) ht
        simpa [hx, ht, bind, Except.bind, pure, Except.pure, rest] using accepted.symm

/-- Retrying placement is an identity for every selected channel, independently
    of how many tokens its consumer has already read. --/
theorem place_duplicate (s next : State) (ids : List String) (t : Token)
    (seen : ∀ c ∈ s.channels, ids.contains c.id = true → c.placed.contains t = true)
    (accepted : place s ids t = .ok next) : next = s := by
  change ((s.channels.mapM (fun c => if ids.contains c.id then placeToken c t else .ok c)) >>= fun cs =>
    Except.ok { s with channels := cs }) = .ok next at accepted
  cases hm : s.channels.mapM (fun c => if ids.contains c.id then placeToken c t else .ok c) with
  | error e => simp only [hm, bind, Except.bind] at accepted; contradiction
  | ok cs =>
    have same := mapM_identity_of_ok _ s.channels cs (by
      intro c hc d hd
      dsimp at hd
      split at hd
      · rename_i selected
        rw [placeToken_duplicate c t (seen c hc selected)] at hd
        split at hd
        · contradiction
        · cases hd; rfl
      · cases hd; rfl) hm
    rw [hm] at accepted
    simp only [bind, Except.bind] at accepted
    rw [same] at accepted
    cases accepted
    rfl

/-- Successful preparation executes the body after checking its premises. --/
theorem prepareWith_body (body : State → Op → Result State) (s next : State) (op : Op)
    (accepted : prepareWith body s op = .ok next) : body s op = .ok next := by
  unfold prepareWith require at accepted
  split at accepted
  · split at accepted
    · simpa [bind, Except.bind, pure, Except.pure] using accepted
    · simp [bind, Except.bind] at accepted
  · simp [bind, Except.bind] at accepted

/-- An accepted repeated emit preserves all channel fields, not just its output
    multiset; authority and the clock are still checked by the public step. --/
theorem emit_duplicate_channels (s next : State) (auth : Credentials) (port : PortName)
    (item : ItemId) (i : Instance) (found : s.instance? auth.instance = some i)
    (seen : ∀ c ∈ s.channels,
      ((s.outgoing i.path i.node port).map (·.id)).contains c.id = true →
      c.placed.contains (.item item) = true)
    (accepted : step s (.emit auth port item) = .ok next) : next.channels = s.channels := by
  rcases step_ok_cases s (.emit auth port item) next accepted with ⟨_, eq⟩ | ⟨_, _, effect, _, _⟩
  · rw [eq]
  · have h := prepareWith_body transitionOrIdle s next (.emit auth port item) effect
    simp only [transitionOrIdle, transition, getInstance, found, Option.toExcept,
      bind, Except.bind, pure, Except.pure] at h
    cases hn : getNode s i.path i.node with
    | error e => simp [hn] at h
    | ok n =>
      simp only [hn] at h
      cases hl : leafPolicy n with
      | error e => simp [hl] at h
      | ok policy =>
      simp only [hl] at h
      cases hr : require (n.outputs.any (fun p => p.name == port && p.kind == .stream)) "NOT_STREAM_OUTPUT" with
      | error e => simp only [hr] at h; contradiction
      | ok value =>
        simp only [hr] at h
        cases hp : putOutput s i.path i.node port (.item item) with
        | error e => simp only [hp] at h; contradiction
        | ok out =>
          have same := place_duplicate s out _ (.item item) seen hp
          simp only [hp] at h
          cases h
          simp [same]

/-- Lease and retry bookkeeping operations have no data-plane effects. --/
def Op.Administrative : Op → Prop
  | .claim .. | .renew .. | .expireLease .. | .promoteRetry .. | .fail .. => True
  | _ => False

theorem transition_administrative_channels (s next : State) (op : Op)
    (admin : op.Administrative) (accepted : transition s op = .ok next) :
    next.channels = s.channels := by
  cases op <;> simp only [Op.Administrative] at admin <;> try contradiction
  all_goals
    simp only [transition, expireOrFail, require, setInstance, setAttempt,
      bind, Except.bind, pure, Except.pure] at accepted
    repeat (first
      | (split at accepted)
      | (simp only [bind, Except.bind, pure, Except.pure] at accepted)
      | contradiction
      | (cases accepted; rfl))

/-- This theorem follows the operational bodies, not the invariant guard. --/
theorem administrative_step_channels (s next : State) (op : Op)
    (admin : op.Administrative) (accepted : step s op = .ok next) :
    next.channels = s.channels := by
  rcases step_ok_cases s op next accepted with ⟨_, eq⟩ | ⟨_, _, effect, _, _⟩
  · rw [eq]
  · have h := prepareWith_body transitionOrIdle s next op effect
    apply transition_administrative_channels s next op admin
    cases op <;> simp_all only [Op.Administrative, transitionOrIdle]

/-- A retry fragment may change attempt IDs, workers, lease clocks and statuses.
    Its emissions must be repetitions of an already placed occurrence. --/
def RetryOnlyOp (s : State) (op : Op) : Prop :=
  op.Administrative ∨ match op with
    | .emit auth port item => ∃ i, s.instance? auth.instance = some i ∧
      ∀ c ∈ s.channels, ((s.outgoing i.path i.node port).map (·.id)).contains c.id = true →
        c.placed.contains (.item item) = true
    | _ => False

theorem ConformingSteps.replay {allows : State → Op → Prop} {s next : State} {ops : List Op}
    (run : ConformingSteps allows s ops next) : Trace.replayOps s ops = .ok next := by
  induction run with
  | nil => rfl
  | cons allowed accepted tail ih =>
    simpa [Trace.replayOps, List.foldlM_cons, accepted, bind, Except.bind] using ih

/-- Any finite accepted lease/retry/re-emission fragment preserves the entire
    channel state. This includes retransmission after downstream consumption. --/
theorem retry_fragment_channels {s next : State} {ops : List Op}
    (run : ConformingSteps RetryOnlyOp s ops next) : next.channels = s.channels := by
  induction run with
  | nil => rfl
  | @cons s middle last op ops allowed accepted tail ih =>
    have same : middle.channels = s.channels := by
      rcases allowed with admin | emission
      · exact administrative_step_channels s middle op admin accepted
      · cases op <;> try contradiction
        rename_i auth port item
        obtain ⟨i, found, seen⟩ := emission
        exact emit_duplicate_channels s middle auth port item i found seen accepted
    exact ih.trans same

theorem retry_fragment_multisets {s next : State} {ops : List Op}
    (run : ConformingSteps RetryOnlyOp s ops next) : channelBags next = channelBags s := by
  simp only [channelBags, retry_fragment_channels run]

/-- The sort used by Collect depends on the multiset, including multiplicity. --/
theorem sortedItems_eq_of_perm (a b : List ItemId) (same : a.Perm b) :
    sortedItems a = sortedItems b := by
  let le := fun (a b : String) => decide (a ≤ b)
  have trans : ∀ a b c, le a b → le b c → le a c := by
    intro a b c hab hbc
    exact decide_eq_true (Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have total : ∀ a b, le a b || le b a := by
    intro a b
    simp only [le, Bool.or_eq_true, decide_eq_true_eq]
    exact Std.le_total
  apply List.Perm.eq_of_pairwise (le := fun (a b : String) => a ≤ b)
  · intro x y _ _ hxy hyx
    exact Std.le_antisymm hxy hyx
  · simpa [sortedItems, le] using List.pairwise_mergeSort trans total a
  · simpa [sortedItems, le] using List.pairwise_mergeSort trans total b
  · exact (List.mergeSort_perm a le).trans (same.trans (List.mergeSort_perm b le).symm)

theorem collect_value_deterministic (path : Path) (node : NodeId) (a b : List ItemId)
    (same : a.Perm b) :
    derivedItem "list" path node (sortedItems a) = derivedItem "list" path node (sortedItems b) := by
  rw [sortedItems_eq_of_perm a b same]

end Suimon
