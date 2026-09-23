import Suimon.Theorems.Round3.Enabled
import Suimon.Theorems.Round3.FreshKeys

namespace Suimon.Round3
open State

/-! ## Helpers for [5] Round3/Fresh.lean — task B3: the indices a call has accepted

A running or fetching call has accepted exactly the indices below its count (`CallIndexInv`):
`returned` and `judged` accept index 0 and end the call, and `yielded` accepts index `yields` and
raises the count. A new call starts without results, since a result identity names its call
(`ResultKeys`) and a task result needs a call or a run of its task, which a task that has not begun
lacks (`Limit.Inv`). -/

namespace FreshAux

/-! ### Free indices as membership -/

theorem indexFree_iff {s : State} {c : Call} {k : Nat} : IndexFree s c k ↔
    (c.task = none → ∀ r ∈ s.results, r.id ≠ Key.callResult c.id k) ∧
    (∀ name, c.task = some name → ∀ x ∈ s.taskResults, ¬ (x.execution = c.owner ∧ x.task = name ∧ x.index = k)) := by
  unfold IndexFree
  rcases hc : c.task with _ | name
  · simp only [State.result?_eq_none_iff, List.mem_map, not_exists, not_and, forall_const, reduceCtorEq,
      false_implies, and_true]
  · simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, reduceCtorEq, false_implies, true_and,
      Option.some.injEq, forall_eq', and_assoc]

theorem indexFree_congr {s t : State} {c : Call} {k : Nat} (hres : t.results = s.results)
    (htr : t.taskResults = s.taskResults) (h : IndexFree s c k) : IndexFree t c k := by
  rw [indexFree_iff] at h ⊢
  rw [hres, htr]
  exact h

/-- A value accepted from another call leaves the indices of `c'` as they were: a call result names
    its call, and a task result names its execution and task, whose call is unique. -/
theorem indexFree_accept_other {s s' : State} {c c' : Call} {idx k : Nat} {value : Value} {arm : Option String}
    (linv : Limit.Inv s) (hc : c ∈ s.calls) (hc' : c' ∈ s.calls) (hne : c'.id ≠ c.id)
    (ha : s.accept c idx value arm = .ok s') (h : IndexFree s c' k) : IndexFree s' c' k := by
  obtain ⟨h1, h2⟩ := indexFree_iff.mp h
  refine indexFree_iff.mpr ⟨fun hnone r hr heq => ?_, fun name hname x hx hkey => ?_⟩
  · rcases State.accept_eq_ok.mp ha with ⟨-, i, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h1 hnone r hr heq
      · exact hne (callResult_inj heq).1.symm
    · exact h1 hnone r hr heq
  · rcases State.accept_eq_ok.mp ha with ⟨-, i, -, -, rfl⟩ | ⟨name', htask', -, rfl⟩
    · exact h2 name hname x hx hkey
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 name hname x hx hkey
      · obtain ⟨e1, e2, -⟩ := hkey
        exact hne (congrArg Call.id (linv.task_call_eq hc' hc hname (by rw [htask']; exact congrArg some e2)
          e1.symm))

/-- A value accepted from `c` at `idx` leaves every other index of `c` as it was. -/
theorem indexFree_accept_self {s s' : State} {c : Call} {idx k : Nat} {value : Value} {arm : Option String}
    (ha : s.accept c idx value arm = .ok s') (hk : k ≠ idx) (h : IndexFree s c k) : IndexFree s' c k := by
  obtain ⟨h1, h2⟩ := indexFree_iff.mp h
  refine indexFree_iff.mpr ⟨fun hnone r hr heq => ?_, fun name hname x hx hkey => ?_⟩
  · rcases State.accept_eq_ok.mp ha with ⟨-, i, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h1 hnone r hr heq
      · exact hk (callResult_inj heq).2.symm
    · exact h1 hnone r hr heq
  · rcases State.accept_eq_ok.mp ha with ⟨-, i, -, -, rfl⟩ | ⟨name', -, -, rfl⟩
    · exact h2 name hname x hx hkey
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 name hname x hx hkey
      · exact hk hkey.2.2.symm

/-- A call of an invocation under a fresh identity has no result yet. -/
theorem indexFree_new_call {s : State} (hk : ResultKeys s) {c : Call} (hid : s.call? c.id = none)
    (htask : c.task = none) (k : Nat) : IndexFree s c k := by
  refine indexFree_iff.mpr ⟨fun _ r hr heq => ?_, fun name h => by rw [htask] at h; cases h⟩
  obtain ⟨c', hc', -, hc'id⟩ := (hk r hr).callResult heq
  exact call?_eq_none_iff.mp hid (List.mem_map.mpr ⟨c', hc', hc'id⟩)

/-- The call of a task that is ready has no task result yet: a task result comes from a call or a
    run of its task, and a task that has not begun has neither. -/
theorem indexFree_new_taskCall {p : Program} {s : State} (linv : Limit.Inv s) (prov : Settle.Prov p s)
    {e : Execution} {ts : TaskState} (he : e ∈ s.executions) (hts : ts ∈ e.tasks) (hready : ts.status = .ready)
    {c : Call} (howner : c.owner = e.id) (htask : c.task = some ts.name) (k : Nat) : IndexFree s c k := by
  have hb : ¬ Limit.Begun ts.status := fun h => h.2 hready
  refine indexFree_iff.mpr ⟨fun h => (by rw [htask] at h; cases h), fun name hname x hx hkey => ?_⟩
  obtain ⟨e1, e2, -⟩ := hkey
  have hn : name = ts.name := Option.some.inj (hname.symm.trans htask)
  rcases prov.taskResultSrc x hx with ⟨c1, hc1, hc1o, hc1t⟩ | ⟨r1, hr1, hr1o, hr1t, -⟩
  · exact linv.no_call he hts hb c1 hc1 (by rw [hc1t, e2, hn]) (by rw [hc1o, e1, howner])
  · exact linv.no_run he hts hb r1 hr1 (by rw [hr1t, e2, hn]) (by rw [hr1o, e1, howner])

/-! ### Running calls between two states -/

/-- Every running or fetching call of `t` was already running or fetching in `s`, with the same
    identity, owner, task and count. -/
def CallsFrom (s t : State) : Prop :=
  ∀ c ∈ t.calls, (c.status = .running ∨ c.status = .fetching) →
    ∃ c0 ∈ s.calls, (c0.status = .running ∨ c0.status = .fetching) ∧ c0.id = c.id ∧ c0.owner = c.owner ∧
      c0.task = c.task ∧ c0.yields = c.yields

namespace CallsFrom
variable {s t u : State}

theorem trans (h₁ : CallsFrom s t) (h₂ : CallsFrom t u) : CallsFrom s u := by
  intro c hc hrun
  obtain ⟨c1, hc1, hrun1, a1, a2, a3, a4⟩ := h₂ c hc hrun
  obtain ⟨c0, hc0, hrun0, b1, b2, b3, b4⟩ := h₁ c1 hc1 hrun1
  exact ⟨c0, hc0, hrun0, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

theorem of_calls (h : t.calls = s.calls) : CallsFrom s t :=
  fun c hc hrun => ⟨c, h ▸ hc, hrun, rfl, rfl, rfl, rfl⟩

/-- Storing a call that neither runs nor fetches. -/
theorem setCall_ended {d : Call} (hd : d.status ≠ .running ∧ d.status ≠ .fetching) : CallsFrom s (s.setCall d) := by
  intro c hc hrun
  rcases mem_setCall_calls hc with rfl | hc
  · rcases hrun with h | h
    · exact absurd h hd.1
    · exact absurd h hd.2
  · exact ⟨c, hc, hrun, rfl, rfl, rfl, rfl⟩

theorem setCall_fetch {c : Call} (hc : c ∈ s.calls) (hrun : c.status = .running) :
    CallsFrom s (s.setCall { c with status := .fetching }) := by
  intro x hx hxrun
  rcases mem_setCall_calls hx with rfl | hx
  · exact ⟨c, hc, Or.inl hrun, rfl, rfl, rfl, rfl⟩
  · exact ⟨x, hx, hxrun, rfl, rfl, rfl, rfl⟩

/-- After a stop no call runs or fetches. -/
theorem stop : CallsFrom s s.stop := by
  intro c hc hrun
  have hq := stop_calls_quiet hc
  rcases hrun with h | h
  · exact absurd h hq.1
  · exact absurd h hq.2

theorem fail {f : Failure} {policy : Policy} : CallsFrom s (s.fail f policy) := by
  cases policy
  · rw [fail_stop]
    exact stop
  · exact of_calls rfl

theorem failCall {c : Call} {status : CallStatus} {cause : Cause} (hst : status ≠ .running ∧ status ≠ .fetching)
    (h : s.failCall c status cause = .ok t) : CallsFrom s t := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp h
  exact ((setCall_ended hst).trans (of_calls (settleOwner_update hso).calls)).trans fail

theorem cancelled {c : Call} (h : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) :
    CallsFrom s t :=
  (setCall_ended (by simp)).trans (of_calls (cancelOwner_update h).calls)

end CallsFrom

theorem failCall_results {s t : State} {c : Call} {status : CallStatus} {cause : Cause}
    (h : s.failCall c status cause = .ok t) : t.results = s.results ∧ t.taskResults = s.taskResults := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp h
  have u := settleOwner_update hso
  simp [u.results, u.taskResults]

/-! ### The invariant -/

/-- A running or fetching call has accepted no index from its count on. -/
def CallIndexInv (s : State) : Prop :=
  ∀ c ∈ s.calls, (c.status = .running ∨ c.status = .fetching) → ∀ k, c.yields ≤ k → IndexFree s c k

/-- Running calls of `t` come from `s`, and `t` adds no result that names a call and no task result
    under a key of a call of `s`. -/
theorem CallIndexInv.frame {s t : State} (h : CallIndexInv s) (hcalls : CallsFrom s t)
    (hres : ∀ r ∈ t.results, r ∈ s.results ∨ ∀ x k, r.id ≠ Key.callResult x k)
    (htr : ∀ x ∈ t.taskResults,
      (∃ y ∈ s.taskResults, y.execution = x.execution ∧ y.task = x.task ∧ y.index = x.index) ∨
      ∀ c ∈ s.calls, c.task = some x.task → c.owner ≠ x.execution) : CallIndexInv t := by
  intro c hc hrun k hk
  obtain ⟨c0, hc0, hrun0, hid, howner, htask, hyields⟩ := hcalls c hc hrun
  obtain ⟨h1, h2⟩ := indexFree_iff.mp (h c0 hc0 hrun0 k (hyields ▸ hk))
  refine indexFree_iff.mpr ⟨fun hnone r hr heq => ?_, fun name hname x hx hkey => ?_⟩
  · rcases hres r hr with hr | hr
    · exact h1 (htask.trans hnone) r hr (by rw [hid]; exact heq)
    · exact hr _ _ heq
  · obtain ⟨e1, e2, e3⟩ := hkey
    rcases htr x hx with ⟨y, hy, f1, f2, f3⟩ | hx'
    · exact h2 name (htask.trans hname) y hy ⟨f1.trans (e1.trans howner.symm), f2.trans e2, f3.trans e3⟩
    · exact hx' c0 hc0 (by rw [htask, hname, e2]) (by rw [howner, e1])

theorem CallIndexInv.of_eq {s t : State} (h : CallIndexInv s) (hcalls : CallsFrom s t)
    (hres : t.results = s.results) (htr : t.taskResults = s.taskResults) : CallIndexInv t :=
  h.frame hcalls (fun _ hr => Or.inl (hres ▸ hr)) (fun x hx => Or.inl ⟨x, htr ▸ hx, rfl, rfl, rfl⟩)

/-- Transforming a task output keeps the keys of task results. -/
theorem setTaskResult_keys {s : State} {r : TaskResult} {x : TaskResult} (hr : r ∈ s.taskResults)
    {o : TaskOutput} (hx : x ∈ (s.setTaskResult { r with output := o }).taskResults) :
    ∃ y ∈ s.taskResults, y.execution = x.execution ∧ y.task = x.task ∧ y.index = x.index := by
  rcases mem_setTaskResult_taskResults hx with rfl | hx
  · exact ⟨r, hr, rfl, rfl, rfl⟩
  · exact ⟨x, hx, rfl, rfl, rfl⟩

theorem step_callIndex {p : Program} {s t : State} {op : Op} (h : Reachable p s) (hci : CallIndexInv s)
    (hs : step p s op = .ok t) : CallIndexInv t := by
  have wk := h.wellKeyed
  have rk := reachable_resultKeys h
  have linv := Limit.reachable_inv h
  obtain ⟨own, -, prov, -⟩ := Settle.reachable h
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, pl, input, id, -, -, -, -, -, -, -, -, hcases⟩ := Step.invoke_inv hs
    rcases hcases with ⟨f, decl, -, -, hcall, rfl⟩ | ⟨judge, arms, -, hcall, rfl⟩ | ⟨wf, out, -, -, rfl⟩ |
        ⟨cc, -, -, rfl⟩
    · intro c hc hrun k hk
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact indexFree_congr (s := s) rfl rfl (hci c hc hrun k hk)
      · exact indexFree_congr (s := s) rfl rfl (indexFree_new_call rk hcall rfl k)
    · intro c hc hrun k hk
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact indexFree_congr (s := s) rfl rfl (hci c hc hrun k hk)
      · exact indexFree_congr (s := s) rfl rfl (indexFree_new_call rk hcall rfl k)
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | fetch id =>
    obtain ⟨-, -, c, hc, -, hrun, rfl⟩ := Step.fetch_inv hs
    exact hci.of_eq (CallsFrom.setCall_fetch (call?_eq_some hc).1 hrun) rfl rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have u := settleOwner_update hso
    obtain ⟨-, -, -, -, -, hcalls', -⟩ := accept_frame hacc
    intro c' hc' hrun' k hk
    rw [u.calls] at hc'
    rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc's, hne⟩
    · simp at hrun'
    · rw [hcalls'] at hc's
      exact indexFree_congr (by rw [u.results, setCall_results]) (by rw [u.taskResults, setCall_taskResults])
        (indexFree_accept_other linv (call?_eq_some hc).1 hc's hne hacc (hci c' hc's hrun' k hk))
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    obtain ⟨-, -, -, -, -, hcalls', -⟩ := accept_frame hacc
    intro c' hc' hrun' k hk
    rw [setInvocation_calls] at hc'
    rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc's, hne⟩
    · simp at hrun'
    · rw [hcalls'] at hc's
      exact indexFree_congr (s := s') rfl rfl
        (indexFree_accept_other linv (call?_eq_some hc).1 hc's hne hacc (hci c' hc's hrun' k hk))
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, hfetch, hacc, rfl⟩ := Step.yielded_inv hs
    obtain ⟨-, -, -, -, -, hcalls', -⟩ := accept_frame hacc
    have hcs := (call?_eq_some hc).1
    intro c' hc' hrun' k hk
    rcases Limit.mem_setCall_iff hc' with rfl | ⟨hc's, hne⟩
    · -- The call itself: its new count is one past the index it accepted.
      have hk' : c.yields + 1 ≤ k := hk
      have hne' : k ≠ c.yields := by omega
      have hle : c.yields ≤ k := by omega
      exact indexFree_congr (s := s') rfl rfl
        (indexFree_accept_self hacc hne' (hci c hcs (Or.inr hfetch) k hle))
    · rw [hcalls'] at hc's
      exact indexFree_congr (s := s') rfl rfl
        (indexFree_accept_other linv hcs hc's hne hacc (hci c' hc's hrun' k hk))
  | ended id =>
    obtain ⟨-, -, c, -, -, -, hso⟩ := Step.ended_inv hs
    have u := settleOwner_update hso
    exact hci.of_eq ((CallsFrom.setCall_ended (by simp)).trans (CallsFrom.of_calls u.calls))
      (by rw [u.results, setCall_results]) (by rw [u.taskResults, setCall_taskResults])
  | failed id =>
    obtain ⟨-, -, c, -, -, hf⟩ := Step.failed_inv hs
    exact hci.of_eq (CallsFrom.failCall (by simp) hf) (failCall_results hf).1 (failCall_results hf).2
  | timedOut id element =>
    obtain ⟨-, -, c, -, -, hf⟩ := Step.timedOut_inv hs
    exact hci.of_eq (CallsFrom.failCall (by simp) hf) (failCall_results hf).1 (failCall_results hf).2
  | lost id =>
    obtain ⟨-, -, c, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact hci.of_eq (CallsFrom.failCall (by simp) hf) (failCall_results hf).1 (failCall_results hf).2
    · have u := cancelOwner_update ho
      exact hci.of_eq (CallsFrom.cancelled ho) (by rw [u.results, setCall_results])
        (by rw [u.taskResults, setCall_taskResults])
  | terminated id =>
    obtain ⟨-, -, c, -, -, ho⟩ := Step.terminated_inv hs
    have u := cancelOwner_update ho
    exact hci.of_eq (CallsFrom.cancelled ho) (by rw [u.results, setCall_results])
      (by rw [u.taskResults, setCall_taskResults])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact hci.of_eq ((CallsFrom.of_calls (t := { s with deliveries := _ }) rfl).trans CallsFrom.fail)
      (by simp) (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact hci.of_eq ((CallsFrom.of_calls (s := s) (t := s.setTask e _) rfl).trans CallsFrom.fail) (by simp)
      (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, -, -, hts, hready, -, -, hcases⟩ := Step.beginTask_inv hs
    have hes := (execution?_eq_some he).1
    have htsm := List.mem_of_find?_eq_some hts
    have htsn : ts.name = name := by simpa using List.find?_some hts
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩
    · intro c hc hrun k hk
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact indexFree_congr (s := s) rfl rfl (hci c hc hrun k hk)
      · exact indexFree_congr (s := s) rfl rfl
          (indexFree_new_taskCall linv prov hes htsm hready rfl (by rw [htsn]) k)
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, r0, -, -, -, -, hr0, -, hcases⟩ := Step.taskOutput_inv hs
    have hr0s := List.mem_of_find?_eq_some hr0
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · refine hci.frame (CallsFrom.of_calls rfl) (fun r hr => ?_) (fun x hx => Or.inl (setTaskResult_keys hr0s hx))
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr fun _ _ => taskOutput_ne_callResult
    · exact hci.frame (CallsFrom.of_calls rfl) (fun r hr => Or.inl hr)
        (fun x hx => Or.inl (setTaskResult_keys hr0s hx))
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r0, -, -, -, hr0, -, rfl⟩ := Step.taskOutputFailed_inv hs
    have hr0s := List.mem_of_find?_eq_some hr0
    refine hci.frame ((CallsFrom.of_calls (s := s) (t := s.setTaskResult _) rfl).trans CallsFrom.fail)
      (fun r hr => Or.inl (by simpa using hr)) (fun x hx => ?_)
    rw [fail_taskResults] at hx
    exact Or.inl (setTaskResult_keys hr0s hx)
  | settle path name =>
    obtain ⟨-, -, _, _, pl, _, _, x, _, -, -, -, -, -, -, -, hout, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
    · refine hci.frame (CallsFrom.of_calls rfl) (fun r hr => ?_) (fun x hx => Or.inl ⟨x, hx, rfl, rfl, rfl⟩)
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · obtain ⟨-, hid, -⟩ := (settleOutcome_some hout).2.2.2 _ rfl
        exact Or.inr fun _ _ => by rw [hid]; exact aggregate_ne_callResult
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, -, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
    · refine hci.frame (CallsFrom.of_calls rfl) (fun r hr => ?_) (fun x hx => Or.inl ⟨x, hx, rfl, rfl, rfl⟩)
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr fun _ _ => list_ne_callResult
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | closeRun path =>
    obtain ⟨-, -, r0, _, _, _, owner, hr0, -, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨-, i, -, hcases⟩ | ⟨name, e, ts, htask, he, -, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine hci.frame (CallsFrom.of_calls rfl) (fun r hr => ?_) (fun x hx => Or.inl ⟨x, hx, rfl, rfl, rfl⟩)
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Or.inl hr
        · exact Or.inr fun _ _ => returned_ne_callResult
      all_goals exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · -- The task result of a workflow task: the task has a run, hence no call.
        refine hci.frame (CallsFrom.of_calls rfl) (fun r hr => Or.inl hr) (fun x hx => ?_)
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl ⟨x, hx, rfl, rfl, rfl⟩
        · refine Or.inr fun c hc hct hco => own.taskCall_not_run wk hc hct (run?_eq_some hr0).1 htask ?_
          rw [howner, hco, (execution?_eq_some he).2]
      all_goals exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact hci.of_eq ((CallsFrom.stop (s := s)).trans (CallsFrom.of_calls rfl)) rfl rfl
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl
    · exact hci.of_eq (CallsFrom.of_calls rfl) rfl rfl

theorem reachable_callIndex {p : Program} {s : State} (h : Reachable p s) : CallIndexInv s := by
  induction h with
  | empty => intro c hc; simp at hc
  | step op hr hs ih => exact step_callIndex hr ih hs

end FreshAux

end Suimon.Round3
