import Suimon.Theorems.Round3.CallConformBase

/-! Helpers for [14] Round3/CallConform.lean — task E2.

The invariant `CallInv` behind `callConform`, the Round 2 facts it relies on (`Facts`), and the
call a report updates: its results, task results and owner after the report. -/

namespace Suimon.Round3
open State

namespace CallConformAux

variable {p : Program} {env : Env} {s t u : State}

/-! ### The invariant and the facts it relies on -/

/-- Every call conforms, and every result identified as a call result belongs to a stored call. -/
structure CallInv (env : Env) (s : State) : Prop where
  calls : ∀ c ∈ s.calls, CallConform env s c ∧ OwnerConform s c
  prov : ∀ r ∈ s.results, ∀ x k, r.id = Key.callResult x k → ∃ c ∈ s.calls, c.id = x

theorem CallInv.empty : CallInv env {} :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

/-- Round 2 invariants of a reachable state that the proof uses. -/
structure Facts (p : Program) (s : State) : Prop where
  wk : s.WellKeyed
  keys : Calls.Keys s
  dinv : Delivery.Inv p s
  limit : Limit.Inv s
  sprov : Settle.Prov p s

theorem facts (h : Reachable p s) : Facts p s :=
  ⟨h.wellKeyed, Calls.reachable_keys h, Delivery.Reachable.inv h, Limit.reachable_inv h, (Settle.reachable h).2.2.1⟩

/-- The call of an invocation has the invocation's identity. -/
theorem Facts.id_of_none (F : Facts p s) {c : Call} (hc : c ∈ s.calls) (hn : c.task = none) : c.id = c.owner := by
  rcases F.dinv.own.calls c hc with ⟨-, hid, -⟩ | ⟨name, hn', -⟩
  · exact hid
  · rw [hn] at hn'
    cases hn'

/-- Two calls of the same kind with the same owner are the same call. -/
theorem Facts.owner_ne (F : Facts p s) {c c₀ : Call} (hc : c ∈ s.calls) (hc₀ : c₀ ∈ s.calls) (hid : c.id ≠ c₀.id) :
    c.task = c₀.task → c.owner ≠ c₀.owner := by
  intro ht ho
  apply hid
  rcases hn : c.task with _ | name
  · rw [F.id_of_none hc hn, F.id_of_none hc₀ (ht ▸ hn), ho]
  · rw [F.limit.keys c hc name hn, F.limit.keys c₀ hc₀ name (ht ▸ hn), ho]

/-- A judge of an invocation has no Stream contract. -/
theorem Facts.stream_of_judge (F : Facts p s) {c : Call} {j : String} (hc : c ∈ s.calls) (hn : c.task = none)
    (hj : c.target = .judge j) : c.stream = false := by
  rcases F.dinv.own.calls c hc with ⟨-, -, -, -, -, -, -, -, -, ⟨f, d, -, -, hf, -⟩ | ⟨-, -, -, -, hs⟩⟩ |
      ⟨name, hn', -⟩
  · rw [hj] at hf
    cases hf
  · exact hs
  · rw [hn] at hn'
    cases hn'

/-- A task that has not begun has no call and no run, hence no task result. -/
theorem Facts.no_taskResult (F : Facts p s) {e : Execution} {ts : TaskState} (he : e ∈ s.executions)
    (hts : ts ∈ e.tasks) (hb : ¬Limit.Begun ts.status) :
    ∀ r ∈ s.taskResults, r.execution = e.id → r.task = ts.name → False := by
  intro r hr he' ht
  rcases F.sprov.taskResultSrc r hr with ⟨c, hc, hco, hct⟩ | ⟨R, hR, hRo, hRt, -⟩
  · exact F.limit.no_call he hts hb c hc (by rw [hct, ht]) (hco.trans he')
  · exact F.limit.no_run he hts hb R hR (by rw [hRt, ht]) (by rw [hRo, he'])

/-! ### Assembling the invariant after a step -/

/-- The invariant after a step: each call is untouched (kept with a frame) or shown to conform, and
    each new result is not a call result or belongs to a call of the state before. -/
theorem CallInv.step (inv : CallInv env s) (K : Delivery.Kept s t) (wk : t.WellKeyed)
    (hcalls : ∀ c ∈ t.calls, (c ∈ s.calls ∧ Frame s t c ∧ OwnerKept s t c) ∨ (CallConform env t c ∧ OwnerConform t c))
    (hres : ∀ r ∈ t.results, r ∈ s.results ∨ (∀ x k, r.id ≠ Key.callResult x k) ∨
      ∃ c ∈ s.calls, ∃ k, r.id = Key.callResult c.id k) : CallInv env t where
  calls c hc := by
    rcases hcalls c hc with ⟨hc', F, O⟩ | h
    · obtain ⟨h1, h2⟩ := inv.calls c hc'
      exact ⟨callConform_frame h1 K wk F, ownerConform_frame h2 O⟩
    · exact h
  prov r hr x k hk := by
    rcases hres r hr with hr' | hne | ⟨c, hc, k', hk'⟩
    · obtain ⟨c, hc, rfl⟩ := inv.prov r hr' x k hk
      obtain ⟨c', hc', hid, -⟩ := K.call c hc
      exact ⟨c', hc', hid⟩
    · exact absurd hk (hne x k)
    · obtain ⟨c', hc', hid, -⟩ := K.call c hc
      exact ⟨c', hc', hid.trans (callResult_inj (hk'.symm.trans hk)).1⟩

/-! ### Owners -/

/-- Settling the owner of another call keeps the owner of `c`. -/
theorem OwnerKept.settleOwner {c c₀ : Call} {inv : InvocationStatus} {task : TaskStatus}
    (hown : c.task = c₀.task → c.owner ≠ c₀.owner) (ho : u.settleOwner c₀ inv task = .ok t) : OwnerKept u t c := by
  rcases settleOwner_eq_ok.mp ho with ⟨hn₀, i, hi, rfl⟩ | ⟨name, e, ts, hn₀, he, hts, rfl⟩
  · refine OwnerKept.setInvocation fun hn h => ?_
    exact hown (hn.trans hn₀.symm) (h.symm.trans (invocation?_eq_some hi).2)
  · have heid := (execution?_eq_some he).2
    refine OwnerKept.setTask (by rw [heid]; exact he) fun name' hn' hid h => ?_
    have hname : ts.name = name := Delivery.find?_name_of_task hts
    exact hown (by rw [hn', hn₀, ← h, hname]) (hid.symm.trans heid)

/-- Cancelling the owner of another call keeps the owner of `c`. -/
theorem OwnerKept.cancelOwner {c c₀ : Call} (hown : c.task = c₀.task → c.owner ≠ c₀.owner)
    (ho : u.cancelOwner c₀ = .ok t) : OwnerKept u t c := by
  rcases cancelOwner_eq_ok.mp ho with ⟨hn₀, i, hi, rfl⟩ | ⟨name, e, ts, hn₀, he, hts, rfl⟩ <;> split
  · refine OwnerKept.setInvocation fun hn h => ?_
    exact hown (hn.trans hn₀.symm) (h.symm.trans (invocation?_eq_some hi).2)
  · exact OwnerKept.of_eq rfl rfl
  · have heid := (execution?_eq_some he).2
    refine OwnerKept.setTask (by rw [heid]; exact he) fun name' hn' hid h => ?_
    have hname : ts.name = name := Delivery.find?_name_of_task hts
    exact hown (by rw [hn', hn₀, ← h, hname]) (hid.symm.trans heid)
  · exact OwnerKept.of_eq rfl rfl

/-- The owner of the call that `settleOwner` settles, after it. -/
theorem settleOwner_owner {c₀ : Call} {inv : InvocationStatus} {task : TaskStatus}
    (ho : u.settleOwner c₀ inv task = .ok t) :
    (c₀.task = none → ∃ i, u.invocation? c₀.owner = some i ∧ t.invocation? c₀.owner = some { i with status := inv }) ∧
    (∀ name, c₀.task = some name → ∃ e ts, t.execution? c₀.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
      ts.status = task) := by
  rcases settleOwner_eq_ok.mp ho with ⟨hn₀, i, hi, rfl⟩ | ⟨name, e, ts, hn₀, he, hts, rfl⟩
  · refine ⟨fun _ => ⟨i, hi, ?_⟩, fun name hn => by rw [hn₀] at hn; cases hn⟩
    rw [invocation?_setInvocation, ite_of_pos (invocation?_eq_some hi).2, hi]
    rfl
  · refine ⟨fun hn => (by rw [hn₀] at hn; cases hn), fun name' hn' => ?_⟩
    rw [hn₀] at hn'
    cases hn'
    have hname : ts.name = name := Delivery.find?_name_of_task hts
    refine ⟨withTask e { ts with status := task }, { ts with status := task }, ?_, ?_, rfl⟩
    · rw [execution?_setTask, ite_of_pos (execution?_eq_some he).2, he]
      rfl
    · rw [Settle.withTask_find?, ite_of_pos hname, hts]
      rfl

/-- Cancelling an owner that already failed changes nothing. -/
theorem cancelOwner_failed {c₀ : Call} (ho : u.cancelOwner c₀ = .ok t)
    (hinv : c₀.task = none → ∃ i, u.invocation? c₀.owner = some i ∧ i.status = .failed)
    (htask : ∀ name, c₀.task = some name → ∃ e ts, u.execution? c₀.owner = some e ∧
      e.tasks.find? (·.name == name) = some ts ∧ ts.status = .failed) : t = u := by
  rcases cancelOwner_eq_ok.mp ho with ⟨hn₀, i, hi, rfl⟩ | ⟨name, e, ts, hn₀, he, hts, rfl⟩
  · obtain ⟨i', hi', hst⟩ := hinv hn₀
    rw [hi] at hi'
    cases hi'
    rw [hst]
    rfl
  · obtain ⟨e', ts', he', hts', hst⟩ := htask name hn₀
    rw [he] at he'
    cases he'
    rw [hts] at hts'
    cases hts'
    rw [hst]
    rfl

/-! ### The call a report updates -/

/-- A new call: it has no result and no task result yet. -/
theorem newCall_conform (inv : CallInv env s) {c : Call} (hfresh : s.call? c.id = none) (hstatus : c.status = .running)
    (hyields : c.yields = 0) (hres : t.results = s.results)
    (htr : ∀ name, c.task = some name → ∀ r ∈ t.taskResults, r.execution = c.owner → r.task = name → False) :
    CallConform env t c ∧ OwnerConform t c := by
  have noRes : ∀ r ∈ t.results, ∀ k, r.id ≠ Key.callResult c.id k := by
    intro r hr k hk
    rw [hres] at hr
    obtain ⟨c', hc', hid⟩ := inv.prov r hr c.id k hk
    rw [call?_eq_none_iff] at hfresh
    exact hfresh (List.mem_map.mpr ⟨c', hc', hid⟩)
  refine ⟨⟨by rw [hyields]; exact Nat.zero_le _, fun _ => hyields, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun k => ⟨fun ⟨r, hr, hk⟩ => absurd hk (noRes r hr k), fun h => ?_⟩,
    fun r hr k hk => absurd hk (noRes r hr k),
    fun name hn k => ⟨fun ⟨r, hr, he, ht, _⟩ => (htr name hn r hr he ht).elim, fun h => ?_⟩,
    fun name hn r hr he ht => (htr name hn r hr he ht).elim⟩, fun h => ?_, fun h => ?_⟩
  all_goals simp only [hstatus, hyields, reduceCtorEq, or_false, Nat.not_lt_zero] at h
  · split at h <;> simp at h
  · split at h <;> simp at h

/-- A report that only changes the status of a call keeps its results. -/
theorem callConform_setStatus {c₀ : Call} {st : CallStatus} (h : CallConform env s c₀)
    (K : Delivery.Kept s t) (wk : t.WellKeyed) (F : Frame s t c₀)
    (hold : c₀.status ≠ .returned) (hnew : c₀.stream = false → st ≠ .returned)
    (hreturned : st = .returned → (env.behavior.script c₀.id).Final c₀ ∧ c₀.stream = true ∧
      (env.behavior.script c₀.id).ending = .ended)
    (hfailed : st = .failed → (env.behavior.script c₀.id).Final c₀ ∧ (env.behavior.script c₀.id).ending = .failed)
    (hlost : st = .lost → (env.behavior.script c₀.id).Final c₀ ∧ (env.behavior.script c₀.id).ending = .lost)
    (hcancelled : st = .cancelling ∨ st = .cancelled →
      (env.behavior.script c₀.id).Final c₀ ∧ ∃ el, (env.behavior.script c₀.id).ending = .timedOut el) :
    CallConform env t { c₀ with status := st } := by
  have h' := callConform_frame h K wk F
  refine ⟨h.yields, h.single, fun hs => ?_, hfailed, hlost, hcancelled, fun k => ?_, h'.values,
    fun name hn k => ?_, h'.taskValues⟩
  · obtain ⟨a, b, c⟩ := hreturned hs
    exact ⟨a, Or.inr ⟨b, c⟩⟩
  · rw [h'.results k]
    cases hs : c₀.stream
    · simp [hold, hnew hs]
    · simp
  · rw [h'.taskResults name hn k]
    cases hs : c₀.stream
    · simp [hold, hnew hs]
    · simp

/-- `returned`: the call accepted its value at index 0 and its owner succeeded. -/
theorem returned_conform (inv : CallInv env s) {c₀ : Call} {value : Value} {s₁ : State}
    (hc₀ : c₀ ∈ s.calls) (hstream : c₀.stream = false) (hrun : c₀.status = .running)
    (hfinal : (env.behavior.script c₀.id).Final c₀) (hend : (env.behavior.script c₀.id).ending = .returned value)
    (hacc : s.accept c₀ 0 value = .ok s₁)
    (hso : (s₁.setCall { c₀ with status := .returned }).settleOwner c₀ .succeeded .succeeded = .ok t) :
    CallConform env t { c₀ with status := .returned } ∧ OwnerConform t { c₀ with status := .returned } := by
  have h := (inv.calls c₀ hc₀).1
  have U := settleOwner_update hso
  have hres : t.results = s₁.results := by rw [U.results, setCall_results]
  have htr : t.taskResults = s₁.taskResults := by rw [U.taskResults, setCall_taskResults]
  have noOld : ∀ r ∈ s.results, ∀ k, r.id ≠ Key.callResult c₀.id k := fun r hr k hk => by
    have := (h.results k).mp ⟨r, hr, hk⟩
    simp [hstream, hrun] at this
  have noOldT : ∀ name, c₀.task = some name → ∀ r ∈ s.taskResults, r.execution = c₀.owner → r.task = name → False :=
    fun name hn r hr he ht => by
      have := (h.taskResults name hn r.index).mp ⟨r, hr, he, ht, rfl⟩
      simp [hstream, hrun] at this
  have owner := settleOwner_owner hso
  have hinvs : ∀ x, (s₁.setCall { c₀ with status := .returned }).invocation? x = s.invocation? x := fun x => by
    simp only [State.invocation?, setCall_invocations, (accept_frame hacc).2.2.2.2.1]
  refine ⟨⟨h.yields, h.single, fun _ => ⟨hfinal, Or.inl ⟨hstream, Or.inl ⟨value, hend⟩⟩⟩, fun h => by simp at h,
    fun h => by simp at h, fun h => by simp at h, fun k => ?_, fun r hr k hk => ?_, fun name hn k => ?_,
    fun name hn r hr he ht => ?_⟩, fun _ => ?_, fun h => by simp at h⟩
  · rw [hres]
    rcases accept_eq_ok.mp hacc with ⟨hn, i, hi, -, rfl⟩ | ⟨name, hn, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨r, hr | rfl, hk⟩
        · exact absurd hk (noOld r hr k)
        · exact ⟨hn, by simp [hstream, (callResult_inj hk).2.symm]⟩
      · rintro ⟨-, hk⟩
        simp only [hstream, Bool.false_eq_true, ite_false, and_true] at hk
        exact ⟨_, Or.inr rfl, by rw [hk]⟩
    · constructor
      · rintro ⟨r, hr, hk⟩
        exact absurd hk (noOld r hr k)
      · rintro ⟨hn', -⟩
        rw [hn] at hn'
        cases hn'
  · rw [hres] at hr
    rcases accept_eq_ok.mp hacc with ⟨hn, i, hi, -, rfl⟩ | ⟨name, hn, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd hk (noOld r hr k)
      · obtain ⟨i', hi', ht'⟩ := owner.1 hn
        rw [hinvs, hi] at hi'
        cases hi'
        refine ⟨rfl, _, ht', rfl, rfl, fun hs => by simp [hstream] at hs, fun v _ hv => ?_, fun a _ ha => ?_⟩
        · rw [hend] at hv
          cases hv
          exact ⟨rfl, rfl⟩
        · rw [hend] at ha
          cases ha
    · exact absurd hk (noOld r hr k)
  · rw [htr]
    rcases accept_eq_ok.mp hacc with ⟨hn', -, -, -, rfl⟩ | ⟨name', hn', -, rfl⟩
    · rw [hn] at hn'
      cases hn'
    · rw [hn] at hn'
      cases hn'
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨r, hr | rfl, he, ht, hk⟩
        · exact (noOldT name hn r hr he ht).elim
        · simp [hstream, ← hk]
      · intro hk
        simp only [hstream, Bool.false_eq_true, ite_false, and_true] at hk
        exact ⟨_, Or.inr rfl, rfl, rfl, hk.symm⟩
  · rw [htr] at hr
    rcases accept_eq_ok.mp hacc with ⟨hn', -, -, -, rfl⟩ | ⟨name', hn', -, rfl⟩
    · rw [hn] at hn'
      cases hn'
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact (noOldT name hn r hr he ht).elim
      · refine ⟨fun hs => by simp [hstream] at hs, fun v _ hv => ?_⟩
        rw [hend] at hv
        cases hv
        rfl
  · show match c₀.task with
      | none => ∃ i, t.invocation? c₀.owner = some i ∧ i.status = .succeeded
      | some name => ∃ e ts, t.execution? c₀.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
          ts.status = .succeeded
    rcases hn : c₀.task with _ | name
    · obtain ⟨i, -, hi⟩ := owner.1 hn
      exact ⟨_, hi, rfl⟩
    · exact owner.2 name hn

/-- `judged`: the judge accepted its invocation's input at index 0 with the arm, and its invocation
    succeeded with that arm. -/
theorem judged_conform (inv : CallInv env s) {c₀ : Call} {arm : String} {i : Invocation} {s₁ : State}
    (hc₀ : c₀ ∈ s.calls) (hstream : c₀.stream = false) (hrun : c₀.status = .running) (hn : c₀.task = none)
    (hi : s.invocation? c₀.owner = some i)
    (hfinal : (env.behavior.script c₀.id).Final c₀) (hend : (env.behavior.script c₀.id).ending = .judged arm)
    (hacc : s.accept c₀ 0 (i.input.getD "") (some arm) = .ok s₁) :
    CallConform env ((s₁.setCall { c₀ with status := .returned }).setInvocation
        { i with status := .succeeded, arm := some arm }) { c₀ with status := .returned } ∧
      OwnerConform ((s₁.setCall { c₀ with status := .returned }).setInvocation
        { i with status := .succeeded, arm := some arm }) { c₀ with status := .returned } := by
  have h := (inv.calls c₀ hc₀).1
  have noOld : ∀ r ∈ s.results, ∀ k, r.id ≠ Key.callResult c₀.id k := fun r hr k hk => by
    have := (h.results k).mp ⟨r, hr, hk⟩
    simp [hstream, hrun] at this
  have hinv : ((s₁.setCall { c₀ with status := .returned }).setInvocation
      { i with status := .succeeded, arm := some arm }).invocation? c₀.owner =
      some { i with status := .succeeded, arm := some arm } := by
    rw [invocation?_setInvocation, ite_of_pos (invocation?_eq_some hi).2]
    simp only [State.invocation?, setCall_invocations, (accept_frame hacc).2.2.2.2.1]
    simp only [State.invocation?] at hi
    rw [hi]
    rfl
  obtain ⟨-, i', hi', -, rfl⟩ := (accept_eq_ok.mp hacc).resolve_right fun ⟨name, hn', _⟩ => by
    rw [hn] at hn'
    cases hn'
  rw [hi] at hi'
  cases hi'
  refine ⟨⟨h.yields, h.single, fun _ => ⟨hfinal, Or.inl ⟨hstream, Or.inr ⟨arm, hend⟩⟩⟩, fun h => by simp at h,
    fun h => by simp at h, fun h => by simp at h, fun k => ?_, fun r hr k hk => ?_,
    fun name hn' => by simp [hn] at hn', fun name hn' => by simp [hn] at hn'⟩,
    fun _ => ?_, fun h => by simp at h⟩
  · simp only [setInvocation_results, setCall_results, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨r, hr | rfl, hk⟩
      · exact absurd hk (noOld r hr k)
      · exact ⟨hn, by simp [hstream, (callResult_inj hk).2.symm]⟩
    · rintro ⟨-, hk⟩
      simp only [hstream, Bool.false_eq_true, ite_false, and_true] at hk
      exact ⟨_, Or.inr rfl, by rw [hk]⟩
  · simp only [setInvocation_results, setCall_results, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact absurd hk (noOld r hr k)
    · refine ⟨rfl, _, hinv, rfl, rfl, fun hs => by simp [hstream] at hs, fun v _ hv => ?_, fun a _ ha => ?_⟩
      · rw [hend] at hv
        cases hv
      · rw [hend] at ha
        cases ha
        exact ⟨rfl, rfl⟩
  · split
    · exact ⟨_, hinv, rfl⟩
    · rename_i name heq
      simp [hn] at heq

/-- `yielded`: the Stream call accepted its next element at index `yields`. -/
theorem yielded_conform (inv : CallInv env s) {c₀ : Call} {value : Value} {s₁ : State}
    (hc₀ : c₀ ∈ s.calls) (hstream : c₀.stream = true)
    (hy : (env.behavior.script c₀.id).yields[c₀.yields]? = some value)
    (hacc : s.accept c₀ c₀.yields value = .ok s₁) :
    CallConform env (s₁.setCall { c₀ with status := .running, yields := c₀.yields + 1 })
        { c₀ with status := .running, yields := c₀.yields + 1 } ∧
      OwnerConform (s₁.setCall { c₀ with status := .running, yields := c₀.yields + 1 })
        { c₀ with status := .running, yields := c₀.yields + 1 } := by
  have h := (inv.calls c₀ hc₀).1
  have hlt : c₀.yields < (env.behavior.script c₀.id).yields.length := (List.getElem?_eq_some_iff.mp hy).1
  have hinvs : ∀ x, (s₁.setCall { c₀ with status := .running, yields := c₀.yields + 1 }).invocation? x =
      s.invocation? x := fun x => by
    simp only [State.invocation?, setCall_invocations, (accept_frame hacc).2.2.2.2.1]
  refine ⟨⟨hlt, fun hs => by simp [hstream] at hs, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h, fun h => by simp at h, fun k => ?_, fun r hr k hk => ?_, fun name hn k => ?_,
    fun name hn r hr he ht => ?_⟩, fun h => by simp at h, fun h => by simp at h⟩
  · rw [setCall_results]
    rcases accept_eq_ok.mp hacc with ⟨hn, i, hi, -, rfl⟩ | ⟨name, hn, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton, hstream, ite_true]
      have := h.results k
      simp only [hstream, ite_true] at this
      constructor
      · rintro ⟨r, hr | rfl, hk⟩
        · exact ⟨hn, Nat.lt_succ_of_lt (this.mp ⟨r, hr, hk⟩).2⟩
        · exact ⟨hn, by rw [← (callResult_inj hk).2]; exact Nat.lt_succ_self _⟩
      · rintro ⟨-, hk⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · obtain ⟨r, hr, hk'⟩ := this.mpr ⟨hn, hk⟩
          exact ⟨r, Or.inl hr, hk'⟩
        · exact ⟨_, Or.inr rfl, rfl⟩
    · have := h.results k
      rw [this]
      simp [hn]
  · rw [setCall_results] at hr
    rcases accept_eq_ok.mp hacc with ⟨hn, i, hi, -, rfl⟩ | ⟨name, hn, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · obtain ⟨hprod, i', hi', rest⟩ := h.values r hr k hk
        exact ⟨hprod, i', by rw [hinvs]; exact hi', rest⟩
      · refine ⟨rfl, i, by rw [hinvs]; exact hi, rfl, rfl, fun _ => ⟨?_, rfl⟩, fun v hs => by simp [hstream] at hs,
          fun a hs => by simp [hstream] at hs⟩
        rw [← (callResult_inj hk).2]
        exact hy
    · obtain ⟨hprod, i', hi', rest⟩ := h.values r hr k hk
      exact ⟨hprod, i', by rw [hinvs]; exact hi', rest⟩
  · rw [setCall_taskResults]
    rcases accept_eq_ok.mp hacc with ⟨hn', -, -, -, rfl⟩ | ⟨name', hn', -, rfl⟩
    · rw [hn] at hn'
      cases hn'
    · rw [hn] at hn'
      cases hn'
      have := h.taskResults name hn k
      simp only [hstream, ite_true] at this
      simp only [List.mem_append, List.mem_singleton, hstream, ite_true]
      constructor
      · rintro ⟨r, hr | rfl, he, ht, hk⟩
        · exact Nat.lt_succ_of_lt (this.mp ⟨r, hr, he, ht, hk⟩)
        · rw [← hk]
          exact Nat.lt_succ_self _
      · intro hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · obtain ⟨r, hr, he, ht, hk'⟩ := this.mpr hk
          exact ⟨r, Or.inl hr, he, ht, hk'⟩
        · exact ⟨_, Or.inr rfl, rfl, rfl, rfl⟩
  · rw [setCall_taskResults] at hr
    rcases accept_eq_ok.mp hacc with ⟨hn', -, -, -, -⟩ | ⟨name', hn', -, rfl⟩
    · rw [hn] at hn'
      cases hn'
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h.taskValues name hn r hr he ht
      · exact ⟨fun _ => hy, fun v hs => by simp [hstream] at hs⟩

/-- The owner of a call whose owner `settleOwner` made succeed. -/
theorem ownerConform_returned {c₀ : Call} (ho : u.settleOwner c₀ .succeeded .succeeded = .ok t) :
    OwnerConform t { c₀ with status := .returned } := by
  have owner := settleOwner_owner ho
  refine ⟨fun _ => ?_, fun h => by simp at h⟩
  show match c₀.task with
    | none => ∃ i, t.invocation? c₀.owner = some i ∧ i.status = .succeeded
    | some name => ∃ e ts, t.execution? c₀.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ts.status = .succeeded
  rcases hn : c₀.task with _ | name
  · obtain ⟨i, -, hi⟩ := owner.1 hn
    exact ⟨_, hi, rfl⟩
  · exact owner.2 name hn

/-- The owner of a call whose owner `settleOwner` made fail. -/
theorem ownerConform_failed {c₀ : Call} {st : CallStatus} (hst : st ≠ .returned)
    (ho : u.settleOwner c₀ .failed .failed = .ok t) : OwnerConform t { c₀ with status := st } := by
  have owner := settleOwner_owner ho
  refine ⟨fun h => absurd h hst, fun _ => ?_⟩
  show match c₀.task with
    | none => ∃ i, t.invocation? c₀.owner = some i ∧ i.status = .failed
    | some name => ∃ e ts, t.execution? c₀.owner = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ts.status = .failed
  rcases hn : c₀.task with _ | name
  · obtain ⟨i, -, hi⟩ := owner.1 hn
    exact ⟨_, hi, rfl⟩
  · exact owner.2 name hn

/-- A cancelling call terminates: its owner failed when it timed out, and stays failed. -/
theorem ownerConform_cancelled {c₀ : Call} (h : OwnerConform s c₀) (hc : c₀.status = .cancelling)
    (ho : (s.setCall { c₀ with status := .cancelled }).cancelOwner c₀ = .ok t) :
    OwnerConform t { c₀ with status := .cancelled } := by
  have hf := h.2 (Or.inr (Or.inr (Or.inl hc)))
  have ht : t = s.setCall { c₀ with status := .cancelled } := by
    refine cancelOwner_failed ho (fun hn => ?_) (fun name hn => ?_)
    · rw [hn] at hf
      exact hf
    · rw [hn] at hf
      exact hf
  subst ht
  refine ⟨fun h => by simp at h, fun _ => ?_⟩
  show match c₀.task with
    | none => ∃ i, (s.setCall { c₀ with status := .cancelled }).invocation? c₀.owner = some i ∧ i.status = .failed
    | some name => ∃ e ts, (s.setCall { c₀ with status := .cancelled }).execution? c₀.owner = some e ∧
        e.tasks.find? (·.name == name) = some ts ∧ ts.status = .failed
  exact hf

end CallConformAux

end Suimon.Round3
