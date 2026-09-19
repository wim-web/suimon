import Suimon.Theorems.Controls

/-! Provenance of consumption records: which operation created a record and on which channel. -/

namespace Suimon
open Effects

/-- The operation that created a record consumed an input of its target node, or an exit of a
    frame it collected. Item facts are recorded where the operation consumes a single item. -/
def RecordOrigin (s : State) (op : Op) (r : Consumption) : Prop :=
  (∃ P N, r.channel ∈ (s.incoming P N).map (·.id) ∧
      (op = .activate P N ∨ (∃ x, op = .spawn P N x ∧ r.item = x) ∨ op = .fireWaitAll P N ∨
       (∃ a, op = .fireBranch P N a) ∨ op = .fireCollect P N ∨ (∃ e x, op = .fireCoalesce P N e x ∧ r.item = x ∧ r.channel = e) ∨
       (∃ x k, op = .fireFilter P N x k ∧ r.item = x) ∨ (∃ e x, op = .fireMerge P N e x ∧ r.item = x ∧ r.channel = e) ∨
       op = .propagateEos P N ∨ op = .skip P N)) ∨
  (∃ inst i f, s.instance? inst = some i ∧ currentFrame s i = .ok f ∧
      (op = .finishSubworkflow inst ∨ ∃ d, op = .loopIterate inst d) ∧ r.channel ∈ exitIds s f)

@[simp] theorem idleState_consumed (s : State) : (idleState s).consumed = s.consumed := by
  unfold idleState
  split <;> rfl

theorem records_new {s next : State} {who : InstanceId} {chans : List String} (h : RecordsBy s next who chans)
    (r : Consumption) (new : r ∈ next.consumed) (old : r ∉ s.consumed) : r.channel ∈ chans := by
  obtain ⟨rs, log, all⟩ := h
  rw [log] at new
  rcases List.mem_append.mp new with before | fresh
  · exact absurd before old
  · exact (all r fresh).2

theorem records_mono {s next : State} {who : InstanceId} {chans : List String} (h : RecordsBy s next who chans)
    (r : Consumption) (member : r ∈ s.consumed) : r ∈ next.consumed := by
  obtain ⟨rs, log, _⟩ := h
  rw [log]; exact List.mem_append_left _ member

theorem single_record {s next : State} {rec : Consumption} (log : next.consumed = s.consumed ++ [rec])
    (r : Consumption) (new : r ∈ next.consumed) (old : r ∉ s.consumed) : r = rec := by
  rw [log] at new
  rcases List.mem_append.mp new with before | fresh
  · exact absurd before old
  · simpa using fresh

/-- Records are append-only, and each new record has a provenance. -/
theorem step_records (s next : State) (op : Op) (safe : Invariants s) (h : step s op = .ok next) :
    (∀ r ∈ s.consumed, r ∈ next.consumed) ∧
    ∀ r ∈ next.consumed, r ∉ s.consumed → RecordOrigin s op r := by
  have distinct := safe.channelIds
  rcases step_ok_cases s op next h with ⟨_, same⟩ | ⟨_, _, prepared, _, _⟩
  · subst same; exact ⟨fun r hr => hr, fun r hr hn => absurd hr hn⟩
  · have executed := prepareWith_body transitionOrIdle s next op prepared
    have ofSame : next.consumed = s.consumed → (∀ r ∈ s.consumed, r ∈ next.consumed) ∧
        ∀ r ∈ next.consumed, r ∉ s.consumed → RecordOrigin s op r := by
      intro same
      refine ⟨fun r hr => by rw [same]; exact hr, fun r hr hn => ?_⟩
      rw [same] at hr; exact absurd hr hn
    cases op with
    | idle =>
      simp only [transitionOrIdle, pure, Except.pure, Except.ok.injEq] at executed
      subst executed
      exact ofSame (idleState_consumed s)
    | start inputs =>
      simp only [transitionOrIdle] at executed
      exact ofSame (effect_start s next inputs executed).2.2.2.2.2.2.1
    | activate path node =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, inputs, _, _, ⟨_, _, _, _, _, _, records⟩ | ⟨_, _, _, _, _, _, _, _, _, _, records⟩⟩ :=
        effect_activate s next path node executed
      · exact ⟨records_mono records, fun r hr hn => .inl ⟨path, node, records_new records r hr hn, .inl rfl⟩⟩
      · exact ⟨records_mono records, fun r hr hn => .inl ⟨path, node, records_new records r hr hn, .inl rfl⟩⟩
    | spawn path node item =>
      simp only [transitionOrIdle] at executed
      obtain ⟨_, n, body, c, _, _, hc, _, _, _, _, _, _, _, _, consumed⟩ := effect_spawn s next path node item distinct executed
      refine ⟨fun r hr => by rw [consumed]; exact List.mem_append_left _ hr, fun r hr hn => ?_⟩
      have eq := single_record consumed r hr hn
      subst eq
      exact .inl ⟨path, node, List.mem_map.mpr ⟨c, List.mem_of_mem_head? hc, rfl⟩, .inr (.inl ⟨item, rfl, rfl⟩)⟩
    | claim auth worker => exact ofSame (effect_claim s next auth worker executed).2.2.1
    | renew auth => exact ofSame (effect_renew s next auth executed).2.2.1
    | expireLease inst now => exact ofSame (effect_expireLease s next inst now executed).2.2.1
    | promoteRetry inst now => exact ofSame (effect_promoteRetry s next inst now executed).2.2.1
    | fail auth code retryable => exact ofSame (effect_fail s next auth code retryable executed).2.2.1
    | emit auth port item =>
      obtain ⟨_, _, _, _, _, _, _, _, _, consumed⟩ := effect_emit s next auth port item executed
      exact ofSame consumed
    | complete auth outputs =>
      obtain ⟨_, _, _, _, _, _, _, _, _, consumed⟩ := effect_complete s next auth outputs executed
      exact ofSame consumed
    | fireWaitAll path node =>
      obtain ⟨_, _, _, _, _, _, _, _, records⟩ := effect_fireWaitAll s next path node executed
      exact ⟨records_mono records, fun r hr hn => .inl ⟨path, node, records_new records r hr hn, .inr (.inr (.inl rfl))⟩⟩
    | fireBranch path node arm =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, records⟩ := effect_fireBranch s next path node arm executed
      exact ⟨records_mono records, fun r hr hn => .inl ⟨path, node, records_new records r hr hn, .inr (.inr (.inr (.inl ⟨arm, rfl⟩)))⟩⟩
    | fireCollect path node =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, records⟩ := effect_fireCollect s next path node executed
      exact ⟨records_mono records, fun r hr hn => .inl ⟨path, node, records_new records r hr hn, .inr (.inr (.inr (.inr (.inl rfl))))⟩⟩
    | fireCoalesce path node edge item =>
      obtain ⟨_, c, _, _, _, hc, _, _, _, _, _, consumed⟩ := effect_fireCoalesce s next path node edge item distinct executed
      refine ⟨fun r hr => by rw [consumed]; exact List.mem_append_left _ hr, fun r hr hn => ?_⟩
      have eq := single_record consumed r hr hn
      subst eq
      have memberC := List.mem_of_find?_eq_some hc
      have idC : c.id = edge := by simpa using List.find?_some hc
      exact .inl ⟨path, node, List.mem_map.mpr ⟨c, memberC, rfl⟩, .inr (.inr (.inr (.inr (.inr (.inl ⟨edge, item, rfl, rfl, idC⟩)))))⟩
    | fireFilter path node item keep =>
      obtain ⟨_, c, _, _, hc, _, _, _, consumed, _⟩ := effect_fireFilter s next path node item keep distinct executed
      refine ⟨fun r hr => by rw [consumed]; exact List.mem_append_left _ hr, fun r hr hn => ?_⟩
      have eq := single_record consumed r hr hn
      subst eq
      exact .inl ⟨path, node, List.mem_map.mpr ⟨c, List.mem_of_mem_head? hc, rfl⟩,
        .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨item, keep, rfl, rfl⟩))))))⟩
    | fireMerge path node edge item =>
      obtain ⟨_, c, _, _, _, memberC, idC, _, _, _, _, consumed, _⟩ := effect_fireMerge s next path node edge item distinct executed
      refine ⟨fun r hr => by rw [consumed]; exact List.mem_append_left _ hr, fun r hr hn => ?_⟩
      have eq := single_record consumed r hr hn
      subst eq
      exact .inl ⟨path, node, List.mem_map.mpr ⟨c, memberC, idC⟩,
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨edge, item, rfl, rfl, rfl⟩)))))))⟩
    | propagateEos path node =>
      obtain ⟨_, _, _, _, _, _, _, records, _⟩ := effect_propagateEos s next path node executed
      exact ⟨records_mono records, fun r hr hn => .inl ⟨path, node, records_new records r hr hn,
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))⟩⟩
    | finishSubworkflow inst =>
      obtain ⟨i, _, f, _, found, _, _, hf, _, _, _, records, _⟩ := effect_finishSubworkflow s next inst executed
      exact ⟨records_mono records, fun r hr hn => .inr ⟨inst, i, f, found, hf, .inl rfl, records_new records r hr hn⟩⟩
    | loopIterate inst done =>
      obtain ⟨i, _, _, _, f, _, _, found, _, _, _, hf, _, _, records, _⟩ := effect_loopIterate s next inst done executed
      exact ⟨records_mono records, fun r hr hn => .inr ⟨inst, i, f, found, hf, .inr ⟨done, rfl⟩, records_new records r hr hn⟩⟩
    | skip path node =>
      obtain ⟨_, _, _, _, _, _, _, records, _⟩ := effect_skip s next path node executed
      exact ⟨records_mono records, fun r hr hn => .inl ⟨path, node, records_new records r hr hn,
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))⟩⟩
    | cancel => exact ofSame (effect_cancel s next executed).2.2.1
    | manualRetry inst =>
      obtain ⟨_, _, _, _, _, ⟨_, _, _, admin, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, consumed⟩⟩ :=
        effect_manualRetry s next inst executed
      · exact ofSame admin.2.2.1
      · exact ofSame consumed

/-- Decomposition of a run at the step that created a record. -/
theorem record_origin {allows : State → Op → Prop} {s0 last : State} {ops : List Op}
    (run : ConformingSteps allows s0 ops last) (safe0 : Invariants s0)
    (r : Consumption) (memberL : r ∈ last.consumed) (absent0 : r ∉ s0.consumed) :
    ∃ pre op post s s', ops = pre ++ op :: post ∧
      ConformingSteps allows s0 pre s ∧ allows s op ∧ step s op = .ok s' ∧
      ConformingSteps allows s' post last ∧ Invariants s ∧ r ∉ s.consumed ∧ r ∈ s'.consumed ∧
      RecordOrigin s op r := by
  induction run with
  | nil => exact absurd memberL absent0
  | @cons s middle final op ops allowed accepted tail ih =>
    have safeMid : Invariants middle := preserves_invariants s middle op safe0 accepted
    by_cases inMid : r ∈ middle.consumed
    · exact ⟨[], op, ops, s, middle, rfl, .nil s, allowed, accepted, tail, safe0, absent0, inMid,
        (step_records s middle op safe0 accepted).2 r inMid absent0⟩
    · obtain ⟨pre, op', post, t, t', split, head, allowed', accepted', rest, safeT, absentT, presentT, origin⟩ :=
        ih safeMid memberL inMid
      exact ⟨op :: pre, op', post, t, t', by simp [split], .cons allowed accepted head, allowed', accepted',
        rest, safeT, absentT, presentT, origin⟩

end Suimon
