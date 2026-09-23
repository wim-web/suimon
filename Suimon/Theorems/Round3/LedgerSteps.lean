import Suimon.Theorems.Round3.LedgerView

/-! Helpers for `Round3/Ledger.lean` (task E5): every accepted step records exactly the failures that
    its ledger gains (`LInv.step_books`), so the failures of a reachable state are a permutation of its
    ledger (`Reachable.failures_ledgerL`). A step changes each of the four parts of the ledger
    (calls, deliveries, tasks, task results) in a way the lemmas of `Parts` describe; a failure that
    stops the workflow records nothing more, since a stopped call's owner has not failed (`StopSafe`). -/

namespace Suimon.Round3.LedgerCore
open State

/-- The ledger of `t` is the ledger of `s` plus the entries `fs`, up to order. -/
def Grew (p : Program) (s t : State) (fs : List Failure) : Prop := (ledgerL p t).Perm (ledgerL p s ++ fs)

/-- A step records the failures `fs`, and its ledger grows by exactly those. -/
def Books (p : Program) (s t : State) : Prop := ∃ fs, t.failures = s.failures ++ fs ∧ Grew p s t fs

section Parts
variable {p : Program} {s t u : State}

theorem Grew.trans {fs gs : List Failure} (h₁ : Grew p s t fs) (h₂ : Grew p t u gs) : Grew p s u (fs ++ gs) := by
  unfold Grew at *
  rw [← List.append_assoc]
  exact h₂.trans (List.Perm.append_right gs h₁)

theorem grew_of_parts {fc fd fi fo : List Failure} (hC : (callPart t).Perm (callPart s ++ fc))
    (hD : (deliveryPart p t).Perm (deliveryPart p s ++ fd)) (hI : (inputPart t).Perm (inputPart s ++ fi))
    (hO : (outputPart t).Perm (outputPart s ++ fo)) : Grew p s t (fc ++ fd ++ fi ++ fo) := by
  unfold Grew ledgerL
  refine ((hC.append hD).append hI |>.append hO).trans ?_
  exact List.perm_iff_count.mpr fun a => by simp only [List.count_append]; omega

theorem grew_of_eq (hC : callPart t = callPart s) (hD : deliveryPart p t = deliveryPart p s)
    (hI : inputPart t = inputPart s) (hO : outputPart t = outputPart s) : Grew p s t [] := by
  unfold Grew ledgerL
  rw [hC, hD, hI, hO, List.append_nil]

theorem grew_fail (h : StopSafe s) {f : Failure} {policy : Policy} : Grew p s (s.fail f policy) [] := by
  unfold Grew
  rw [ledgerL_fail h, List.append_nil]

theorem perm_of_eq_nil {α : Type} {a b : List α} (h : a = b) : a.Perm (b ++ []) := by
  rw [List.append_nil, h]

theorem books_of_grew {fs : List Failure} (hf : t.failures = s.failures ++ fs) (h : Grew p s t fs) : Books p s t :=
  ⟨fs, hf, h⟩

/-! #### Calls -/

theorem callPart_eq_of {g : Call → Call} {N : List Call} (hc : t.calls = s.calls.map g ++ N)
    (hold : ∀ x ∈ s.calls, callL t (g x) = callL s x) (hnew : ∀ y ∈ N, callL t y = none) :
    callPart t = callPart s := by
  unfold callPart
  rw [hc, List.filterMap_append, filterMap_map_eq hold, List.filterMap_eq_nil_iff.mpr hnew, List.append_nil]

theorem callPart_append_eq {N : List Call} (hc : t.calls = s.calls ++ N)
    (hold : ∀ x ∈ s.calls, callL t x = callL s x) (hnew : ∀ y ∈ N, callL t y = none) :
    callPart t = callPart s :=
  callPart_eq_of (g := id) (by rw [hc, List.map_id]) hold hnew

theorem callPart_perm_of {g : Call → Call} {c : Call} {f : Failure} (hnd : s.calls.Nodup) (hcm : c ∈ s.calls)
    (hc : t.calls = s.calls.map g) (hold : ∀ x ∈ s.calls, x ≠ c → callL t (g x) = callL s x)
    (h0 : callL s c = none) (h1 : callL t (g c) = some f) : (callPart t).Perm (callPart s ++ [f]) := by
  unfold callPart
  rw [hc]
  exact filterMap_map_perm_one hnd hcm hold h0 h1

theorem callPart_of (hc : t.calls = s.calls) (hi : t.invocations = s.invocations)
    (he : t.executions = s.executions) : callPart t = callPart s :=
  callPart_append_eq (N := []) (by rw [hc, List.append_nil])
    (fun x _ => callL_congr rfl rfl (ownerView_congr hi he x)) (fun _ h => by cases h)

/-! #### Deliveries -/

theorem deliveryPart_eq_of {N : List Delivery} (hd : t.deliveries = s.deliveries ++ N)
    (hold : ∀ d ∈ s.deliveries, deliveryL p t d = deliveryL p s d) (hnew : ∀ d ∈ N, deliveryL p t d = none) :
    deliveryPart p t = deliveryPart p s := by
  unfold deliveryPart
  rw [hd, List.filterMap_append, filterMap_congr' hold, List.filterMap_eq_nil_iff.mpr hnew, List.append_nil]

theorem deliveryPart_append_one {d : Delivery} {f : Failure} (hd : t.deliveries = s.deliveries ++ [d])
    (hold : ∀ d ∈ s.deliveries, deliveryL p t d = deliveryL p s d) (hnew : deliveryL p t d = some f) :
    deliveryPart p t = deliveryPart p s ++ [f] := by
  unfold deliveryPart
  rw [hd, List.filterMap_append, filterMap_congr' hold]
  simp [hnew]

theorem deliveryPart_of (hd : t.deliveries = s.deliveries) (hr : t.runs = s.runs) :
    deliveryPart p t = deliveryPart p s :=
  deliveryPart_eq_of (N := []) (by rw [hd, List.append_nil])
    (fun _ _ => deliveryL_congr (Settle.SameWorkflows.of_runs hr _)) (fun _ h => by cases h)

/-! #### Tasks -/

theorem inputPart_eq_of {g : Execution → Execution} {N : List Execution} (he : t.executions = s.executions.map g ++ N)
    (hold : ∀ e ∈ s.executions, (g e).tasks.filterMap (taskInputL t (g e)) = e.tasks.filterMap (taskInputL s e))
    (hnew : ∀ e ∈ N, ∀ x ∈ e.tasks, taskInputL t e x = none) : inputPart t = inputPart s := by
  unfold inputPart
  rw [he, List.flatMap_append, flatMap_map_eq hold, List.append_right_eq_self]
  exact List.flatMap_eq_nil_iff.mpr fun e he' => List.filterMap_eq_nil_iff.mpr (hnew e he')

theorem inputPart_perm_of {g : Execution → Execution} {e0 : Execution} {f : Failure} (hnd : s.executions.Nodup)
    (he0 : e0 ∈ s.executions) (he : t.executions = s.executions.map g)
    (hold : ∀ e ∈ s.executions, e ≠ e0 →
      (g e).tasks.filterMap (taskInputL t (g e)) = e.tasks.filterMap (taskInputL s e))
    (h0 : ((g e0).tasks.filterMap (taskInputL t (g e0))).Perm (e0.tasks.filterMap (taskInputL s e0) ++ [f])) :
    (inputPart t).Perm (inputPart s ++ [f]) := by
  unfold inputPart
  rw [he]
  exact flatMap_map_perm_one (G := fun e : Execution => e.tasks.filterMap (taskInputL s e))
    (G' := fun e : Execution => e.tasks.filterMap (taskInputL t e)) hnd he0 hold h0

theorem inputPart_of (he : t.executions = s.executions) (hc : t.calls.map (·.id) = s.calls.map (·.id))
    (hr : t.runs.map (fun r => (r.owner, r.task)) = s.runs.map (fun r => (r.owner, r.task))) :
    inputPart t = inputPart s :=
  inputPart_eq_of (g := id) (N := []) (by rw [he, List.map_id, List.append_nil])
    (fun e _ => filterMap_congr' fun x _ => taskInputL_congr rfl rfl rfl rfl rfl (hasBody_congr hc hr _ _))
    (fun _ h => by cases h)

/-! #### Task results -/

theorem outputPart_eq_of {g : TaskResult → TaskResult} {N : List TaskResult}
    (htr : t.taskResults = s.taskResults.map g ++ N)
    (hold : ∀ r ∈ s.taskResults, taskOutputL t (g r) = taskOutputL s r)
    (hnew : ∀ r ∈ N, taskOutputL t r = none) : outputPart t = outputPart s := by
  unfold outputPart
  rw [htr, List.filterMap_append, filterMap_map_eq hold, List.filterMap_eq_nil_iff.mpr hnew, List.append_nil]

theorem outputPart_perm_of {g : TaskResult → TaskResult} {r0 : TaskResult} {f : Failure} (hnd : s.taskResults.Nodup)
    (hr0 : r0 ∈ s.taskResults) (htr : t.taskResults = s.taskResults.map g)
    (hold : ∀ r ∈ s.taskResults, r ≠ r0 → taskOutputL t (g r) = taskOutputL s r)
    (h0 : taskOutputL s r0 = none) (h1 : taskOutputL t (g r0) = some f) : (outputPart t).Perm (outputPart s ++ [f]) := by
  unfold outputPart
  rw [htr]
  exact filterMap_map_perm_one hnd hr0 hold h0 h1

theorem outputPart_of (htr : t.taskResults = s.taskResults) (he : t.executions = s.executions) :
    outputPart t = outputPart s :=
  outputPart_eq_of (g := id) (N := []) (by rw [htr, List.map_id, List.append_nil])
    (fun _ _ => taskOutputL_congr rfl rfl (execPos_congr he _)) (fun _ h => by cases h)

end Parts

/-! ### Consequences of the invariants -/

section Facts
variable {p : Program} {s : State}

theorem LInv.ownerView_some (hL : LInv p s) {c : Call} (hc : c ∈ s.calls) : ∃ v, ownerView s c = some v := by
  cases ht : c.task with
  | none =>
    obtain ⟨-, i, hi, hio⟩ := hL.callNone hc ht
    exact ⟨_, ownerView_of_invocation ht (hio ▸ hL.wk.invocation?_of_mem hi)⟩
  | some name =>
    obtain ⟨e, he, heo, -⟩ := hL.lim.calls c hc name ht
    exact ⟨_, ownerView_of_execution ht (heo ▸ hL.wk.execution?_of_mem he)⟩

theorem LInv.execPos_some (hL : LInv p s) {r : TaskResult} (hr : r ∈ s.taskResults) :
    ∃ v, execPos s r.execution = some v := by
  obtain ⟨e, he, heo, -⟩ := hL.lim.results r hr
  refine ⟨(e.run, e.placement), ?_⟩
  unfold execPos
  rw [← heo, hL.wk.execution?_of_mem he]
  rfl

theorem LInv.deliveryL_keep (hL : LInv p s) {t : State} (hw : Settle.KeepsWorkflows p s t) {d : Delivery}
    (hd : d ∈ s.deliveries) : deliveryL p t d = deliveryL p s d := by
  obtain ⟨w, -, -, hwd, -⟩ := hL.dinv.own.deliveries d hd
  exact deliveryL_congr ((hw _ _ hwd).trans hwd.symm)

/-- Among tasks whose same-named members are equal, the named task decides whether one failed. -/
theorem any_named {l : List TaskState} {ts : TaskState} (hts : ts ∈ l)
    (hcoh : ∀ x ∈ l, x.name = ts.name → x = ts) :
    (l.any fun x => x.name == ts.name && x.status == .failed) = (ts.status == .failed) := by
  cases hst : (ts.status == TaskStatus.failed)
  · rw [List.any_eq_false]
    intro x hx
    by_cases hn : x.name = ts.name
    · rw [hcoh x hx hn]
      simp [hst]
    · simp [hn]
  · exact List.any_eq_true.mpr ⟨ts, hts, by simp [hst]⟩

theorem LInv.ownerView_task (hL : LInv p s) {c : Call} {name : String} (ht : c.task = some name) {e : Execution}
    (he : s.execution? c.owner = some e) {ts : TaskState} (hts : e.tasks.find? (·.name == name) = some ts) :
    ownerView s c = some (e.run, e.placement, ts.status == .failed) := by
  obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
  rw [ownerView_of_execution ht he, ← htsn,
    any_named htsm fun x hx hn => hL.lim.coherent e (execution?_eq_some he).1 x hx ts htsm hn]

theorem withTask_mem {e : Execution} {ts ts' : TaskState} (hts : ts ∈ e.tasks) (hname : ts'.name = ts.name) :
    ts' ∈ (withTask e ts').tasks := by
  rw [withTask_tasks, List.mem_map]
  exact ⟨ts, hts, by simp [hname]⟩

theorem withTask_named {e : Execution} {ts' x : TaskState} (hx : x ∈ (withTask e ts').tasks)
    (hn : x.name = ts'.name) : x = ts' := by
  rw [withTask_tasks, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  by_cases hy : y.name = ts'.name
  · simp [hy]
  · simp [hy] at hn

theorem withTask_any_self {e : Execution} {ts ts' : TaskState} (hts : ts ∈ e.tasks) (hname : ts'.name = ts.name) :
    ((withTask e ts').tasks.any fun x => x.name == ts.name && x.status == .failed) = (ts'.status == .failed) := by
  have := any_named (withTask_mem hts hname) fun _ hx hn => withTask_named hx hn
  rwa [hname] at this

theorem withTask_any_ne {e : Execution} {ts : TaskState} {n : String} (hn : n ≠ ts.name) :
    ((withTask e ts).tasks.any fun x => x.name == n && x.status == .failed) =
      (e.tasks.any fun x => x.name == n && x.status == .failed) := by
  rw [withTask_tasks, List.any_map]
  apply List.any_congr rfl
  intro x
  simp only [Function.comp]
  by_cases hx : x.name = ts.name
  · have h1 : (ts.name == n) = false := by simpa using fun h => hn h.symm
    simp [hx, h1]
  · simp [hx]

theorem ownerView_setTask (wk : s.WellKeyed) {e : Execution} (he : e ∈ s.executions) {ts : TaskState} {c : Call}
    (h : ∀ n, c.task = some n → c.owner = e.id → n ≠ ts.name) : ownerView (s.setTask e ts) c = ownerView s c := by
  rw [setTask_eq]
  by_cases hc : c.task ≠ none → c.owner ≠ e.id
  · exact ownerView_setExecution_of_ne hc
  · simp only [ne_eq, Classical.not_imp, Decidable.not_not] at hc
    obtain ⟨htask, ho⟩ := hc
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp htask
    rw [ownerView_setExecution_self (e' := withTask e ts) wk he rfl hn ho,
      ownerView_of_execution hn (ho ▸ wk.execution?_of_mem he), withTask_run, withTask_placement,
      withTask_any_ne (h n hn ho)]

theorem ownerView_setExecution_tasks (wk : s.WellKeyed) {e e' : Execution} (he : e ∈ s.executions)
    (hid : e'.id = e.id) (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (htasks : e'.tasks = e.tasks)
    (c : Call) : ownerView (s.setExecution e') c = ownerView s c := by
  by_cases hc : c.task ≠ none → c.owner ≠ e.id
  · exact ownerView_setExecution_of_ne (hid ▸ hc)
  · simp only [ne_eq, Classical.not_imp, Decidable.not_not] at hc
    obtain ⟨htask, ho⟩ := hc
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp htask
    rw [ownerView_setExecution_self wk he hid hn ho, ownerView_of_execution hn (ho ▸ wk.execution?_of_mem he),
      hrun, hpl, htasks]

/-- A task call makes its task have a body. -/
theorem LInv.hasBody_of_taskCall (hL : LInv p s) {c : Call} (hc : c ∈ s.calls) {name : String}
    (ht : c.task = some name) : hasBody s c.owner name = true :=
  hasBody_of_call hc (hL.lim.keys c hc name ht)

/-- A task that has not begun has no body. -/
theorem LInv.hasBody_not_begun (hL : LInv p s) {e : Execution} (he : e ∈ s.executions) {x : TaskState}
    (hx : x ∈ e.tasks) (hb : ¬Limit.Begun x.status) : hasBody s e.id x.name = false := by
  refine hasBody_eq_false (fun c hc hid => ?_) (fun r hr ho ht => hL.lim.no_run he hx hb r hr ht ho)
  cases ht : c.task with
  | none =>
    have hkey := hL.keys.invocations _ (hL.keys.calls c hc ht)
    exact Calls.not_taskKey_of_invocationKey hkey ⟨e.id, x.name, hid⟩
  | some n =>
    have h1 := (hL.lim.keys c hc n ht).symm.trans hid
    have h2 := identity_injective h1
    simp only [List.cons.injEq, true_and] at h2
    obtain ⟨ho, hn, -⟩ := h2
    exact hL.lim.no_call he hx hb c hc (by rw [ht, hn]) ho

end Facts

/-! ### Updates of one task -/

section TaskUpdates
variable {p : Program} {s t : State}

/-- Replacing the task `ts` of `e` by `ts'` keeps the task-input part when the replaced task keeps its
    entry and no other task's body changes. -/
theorem LInv.inputPart_setTask (hL : LInv p s) {e : Execution} (he : e ∈ s.executions) {ts ts' : TaskState}
    (hts : ts ∈ e.tasks) (hname : ts'.name = ts.name) (hex : t.executions = (s.setTask e ts').executions)
    (hb : ∀ eid n, (eid ≠ e.id ∨ n ≠ ts.name) → hasBody t eid n = hasBody s eid n)
    (hself : taskInputL t (withTask e ts') ts' = taskInputL s e ts) : inputPart t = inputPart s := by
  refine inputPart_eq_of (g := fun x => if x.id == (withTask e ts').id then withTask e ts' else x) (N := [])
    (by rw [hex, setTask_eq, setExecution_executions, List.append_nil]) ?_ (fun _ h => by cases h)
  intro e2 he2
  by_cases h2 : e2.id = e.id
  · have := hL.wk.execution_eq_of_id he2 he h2
    subst this
    simp only [withTask_id, beq_self_eq_true, ite_true]
    rw [withTask_tasks]
    apply filterMap_map_eq
    intro x hx
    by_cases hx' : x.name = ts'.name
    · have hxts : x = ts := hL.lim.coherent e2 he2 x hx ts hts (hx'.trans hname)
      subst hxts
      simp only [hx', beq_self_eq_true, ite_true]
      exact hself
    · have : (x.name == ts'.name) = false := by simpa using hx'
      simp only [this]
      exact taskInputL_congr rfl rfl rfl rfl rfl (hb _ _ (Or.inr (hname ▸ hx')))
  · have : (e2.id == (withTask e ts').id) = false := by simpa using h2
    simp only [this]
    exact filterMap_congr' fun x _ => taskInputL_congr rfl rfl rfl rfl rfl (hb _ _ (Or.inl h2))

/-- Replacing the task `ts` of `e` by `ts'` adds the entry of `ts'` when `ts` had none. Task names are
    distinct, so only `ts` is replaced. -/
theorem LInv.inputPart_setTask_perm (hL : LInv p s) {e : Execution} (he : e ∈ s.executions) {ts ts' : TaskState}
    (hts : ts ∈ e.tasks) (hname : ts'.name = ts.name) (hex : t.executions = (s.setTask e ts').executions)
    (hb : ∀ eid n, (eid ≠ e.id ∨ n ≠ ts.name) → hasBody t eid n = hasBody s eid n) {f : Failure}
    (h0 : taskInputL s e ts = none) (h1 : taskInputL t (withTask e ts') ts' = some f) :
    (inputPart t).Perm (inputPart s ++ [f]) := by
  refine inputPart_perm_of (g := fun x => if x.id == (withTask e ts').id then withTask e ts' else x) (e0 := e)
    hL.executions_nodup he (by rw [hex, setTask_eq, setExecution_executions]) ?_ ?_
  · intro e2 he2 hne
    have h2 : e2.id ≠ e.id := fun h => hne (hL.wk.execution_eq_of_id he2 he h)
    have : (e2.id == (withTask e ts').id) = false := by simpa using h2
    simp only [this]
    exact filterMap_congr' fun x _ => taskInputL_congr rfl rfl rfl rfl rfl (hb _ _ (Or.inl h2))
  · simp only [withTask_id, beq_self_eq_true, ite_true]
    rw [withTask_tasks]
    refine filterMap_map_perm_one (hL.tasks_nodup he) hts ?_ h0 ?_
    · intro x hx hne
      have hxn : x.name ≠ ts.name := fun h => hne (Limit.eq_of_key (hL.names e he) hx hts h)
      have : (x.name == ts'.name) = false := by simpa [hname] using hxn
      simp only [this]
      exact taskInputL_congr rfl rfl rfl rfl rfl (hb _ _ (Or.inr hxn))
    · have : (ts.name == ts'.name) = true := by simp [hname]
      simp only [this, ite_true]
      exact h1

/-- Marking an execution complete keeps the task-input part. -/
theorem LInv.inputPart_setExecution_tasks (hL : LInv p s) {e e' : Execution} (he : e ∈ s.executions)
    (hid : e'.id = e.id) (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (htasks : e'.tasks = e.tasks)
    (hex : t.executions = (s.setExecution e').executions) (hb : ∀ eid n, hasBody t eid n = hasBody s eid n) :
    inputPart t = inputPart s := by
  refine inputPart_eq_of (g := fun x => if x.id == e'.id then e' else x) (N := [])
    (by rw [hex, setExecution_executions, List.append_nil]) ?_ (fun _ h => by cases h)
  intro e2 he2
  by_cases h2 : e2.id = e.id
  · have := hL.wk.execution_eq_of_id he2 he h2
    subst this
    simp only [hid, beq_self_eq_true, ite_true]
    rw [htasks]
    exact filterMap_congr' fun x _ => taskInputL_congr hid hrun hpl rfl rfl (hb _ _)
  · have : (e2.id == e'.id) = false := by simpa [hid] using h2
    simp only [this]
    exact filterMap_congr' fun x _ => taskInputL_congr rfl rfl rfl rfl rfl (hb _ _)

end TaskUpdates

/-! ### Updates of the owner of a call -/

/-- `u` is `s0` with the status of the invocation or task owning `c` updated, or `s0` itself. -/
def OwnerStep (s0 u : State) (c : Call) : Prop :=
  u = s0 ∨
  (c.task = none ∧ ∃ i i', s0.invocation? c.owner = some i ∧ i'.id = i.id ∧ u = s0.setInvocation i') ∨
  (∃ name e ts st, c.task = some name ∧ s0.execution? c.owner = some e ∧
    e.tasks.find? (·.name == name) = some ts ∧ u = s0.setTask e { ts with status := st })

section Owners
variable {p : Program} {s : State}

theorem ownerStep_settleOwner {s0 u : State} {c : Call} {inv : InvocationStatus} {task : TaskStatus}
    (h : s0.settleOwner c inv task = .ok u) : OwnerStep s0 u c := by
  rcases settleOwner_eq_ok.mp h with ⟨ht, i, hi, rfl⟩ | ⟨name, e, ts, ht, he, hts, rfl⟩
  · exact Or.inr (Or.inl ⟨ht, i, { i with status := inv }, hi, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨name, e, ts, task, ht, he, hts, rfl⟩)

theorem ownerStep_cancelOwner {s0 u : State} {c : Call} (h : s0.cancelOwner c = .ok u) : OwnerStep s0 u c := by
  rcases cancelOwner_eq_ok.mp h with ⟨ht, i, hi, rfl⟩ | ⟨name, e, ts, ht, he, hts, rfl⟩
  · split
    · exact Or.inr (Or.inl ⟨ht, i, { i with status := .cancelled }, hi, rfl, rfl⟩)
    · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr ⟨name, e, ts, .cancelled, ht, he, hts, rfl⟩)
    · exact Or.inl rfl

theorem invocation?_congr {s t : State} (h : t.invocations = s.invocations) (id : String) :
    t.invocation? id = s.invocation? id := by
  unfold State.invocation?
  rw [h]

theorem execution?_congr {s t : State} (h : t.executions = s.executions) (id : String) :
    t.execution? id = s.execution? id := by
  unfold State.execution?
  rw [h]

/-- An owner update changes the view of no other call, and keeps the delivery, task-input and
    task-output parts: the task of a task call has a body, so its entry stays absent. -/
theorem LInv.ownerStep (hL : LInv p s) {c : Call} (hc : c ∈ s.calls) {s0 u : State} (hstep : OwnerStep s0 u c)
    (hcalls : s0.calls.map (·.id) = s.calls.map (·.id)) (hi : s0.invocations = s.invocations)
    (he : s0.executions = s.executions) (hr : s0.runs = s.runs) (hd : s0.deliveries = s.deliveries)
    {N : List TaskResult} (htr : s0.taskResults = s.taskResults ++ N) (hN : ∀ r ∈ N, r.output = .pending) :
    (∀ x ∈ s.calls, x ≠ c → ownerView u x = ownerView s x) ∧ deliveryPart p u = deliveryPart p s ∧
      inputPart u = inputPart s ∧ outputPart u = outputPart s ∧ u.calls = s0.calls ∧ u.failures = s0.failures := by
  have hrmap : s0.runs.map (fun r => (r.owner, r.task)) = s.runs.map (fun r => (r.owner, r.task)) := by rw [hr]
  have hout : ∀ {v : State}, v.taskResults = s0.taskResults → (∀ id, execPos v id = execPos s id) →
      outputPart v = outputPart s := by
    intro v hv hpos
    exact outputPart_eq_of (g := id) (N := N) (by rw [hv, htr, List.map_id])
      (fun r _ => taskOutputL_congr rfl rfl (hpos _)) (fun r hr' => taskOutputL_of_ne (by rw [hN r hr']; simp))
  rcases hstep with rfl | ⟨ht, i, i', hi', hid, rfl⟩ | ⟨name, e, ts, st, ht, he', hts, rfl⟩
  · exact ⟨fun x _ _ => ownerView_congr hi he x, deliveryPart_of hd hr, inputPart_of he hcalls hrmap,
      hout rfl (fun id => execPos_congr he id), rfl, rfl⟩
  · have hio : i.id = c.owner := (invocation?_eq_some hi').2
    refine ⟨fun x hx hne => ?_, deliveryPart_of hd hr, inputPart_of he hcalls hrmap,
      hout rfl (fun id => execPos_congr he id), rfl, rfl⟩
    rw [ownerView_congr (t := s0.setInvocation i') (s := s.setInvocation i')
      (by simp only [setInvocation_invocations, hi]) he x]
    refine ownerView_setInvocation_of_ne fun hxt hxo => hne ?_
    exact hL.call_eq_of_owner hx hc (hxo.trans (hid.trans hio)) (hxt.trans ht.symm)
  · obtain ⟨hem, heo⟩ := execution?_eq_some he'
    rw [he] at hem
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    have hex : (s0.setTask e { ts with status := st }).executions =
        (s.setTask e { ts with status := st }).executions := by
      rw [setTask_eq, setTask_eq, setExecution_executions, setExecution_executions, he]
    have hbody : ∀ eid n, hasBody (s0.setTask e { ts with status := st }) eid n = hasBody s eid n :=
      fun eid n => hasBody_congr (by simpa using hcalls) (by simpa using hrmap) eid n
    have hself : hasBody s e.id ts.name = true := by
      rw [heo, htsn]
      exact hL.hasBody_of_taskCall hc ht
    refine ⟨fun x hx hne => ?_, deliveryPart_of hd hr, ?_, hout rfl fun id => ?_, rfl, rfl⟩
    · rw [ownerView_congr (t := s0.setTask e { ts with status := st }) (s := s.setTask e { ts with status := st })
        (by simp only [setTask_invocations, hi]) hex x]
      refine ownerView_setTask hL.wk hem fun n hxt hxo hn => hne ?_
      exact hL.call_eq_of_owner hx hc (hxo.trans heo) (hxt.trans (by rw [hn, ht]; exact congrArg some htsn))
    · refine hL.inputPart_setTask (ts' := { ts with status := st }) hem htsm rfl hex (fun eid n _ => hbody eid n) ?_
      rw [taskInputL_of_hasBody (by rw [hbody]; exact hself), taskInputL_of_hasBody hself]
    · rw [execPos_congr hex, setTask_eq,
        execPos_setExecution (e' := withTask e { ts with status := st }) hL.wk hem rfl rfl rfl]

theorem LInv.stopSafe (hL : LInv p s) : StopSafe s := by
  intro c hc hrun v hv
  cases ht : c.task with
  | none =>
    obtain ⟨i, hi, hio, hact⟩ := hL.act.callActive c hc ht hrun
    rw [ownerView_of_invocation ht (by rw [← hio]; exact hL.wk.invocation?_of_mem hi)] at hv
    cases hv
    simp [hact]
  | some name =>
    obtain ⟨e, he, heo, x, hx, hxn, hxa⟩ := hL.lim.active c hc hrun name ht
    rw [ownerView_of_execution ht (by rw [← heo]; exact hL.wk.execution?_of_mem he)] at hv
    cases hv
    show (e.tasks.any fun t => t.name == name && t.status == .failed) = false
    rw [← hxn, any_named hx (fun y hy hn => hL.lim.coherent e he y hy x hx hn), hxa]
    rfl

/-- Cancelling the owner of a cancelling call keeps whether that owner failed. -/
theorem LInv.ownerView_cancelOwner_self (hL : LInv p s) {c : Call} {s0 u : State}
    (hi : s0.invocations = s.invocations) (he : s0.executions = s.executions) (h : s0.cancelOwner c = .ok u) :
    ownerView u c = ownerView s c := by
  rcases cancelOwner_eq_ok.mp h with ⟨ht, i, hi', rfl⟩ | ⟨name, e, ts, ht, he', hts, rfl⟩
  · have hi'' : s.invocation? c.owner = some i := by rw [← invocation?_congr hi]; exact hi'
    obtain ⟨him, hio⟩ := invocation?_eq_some hi''
    split
    · rename_i hact
      rw [ownerView_congr (t := s0.setInvocation { i with status := .cancelled })
          (s := s.setInvocation { i with status := .cancelled }) (by simp only [setInvocation_invocations, hi]) he c,
        ownerView_setInvocation_self (i' := { i with status := .cancelled }) hL.wk him rfl ht hio.symm,
        ownerView_of_invocation ht hi'', hact]
      rfl
    · exact ownerView_congr hi he c
  · have he'' : s.execution? c.owner = some e := by rw [← execution?_congr he]; exact he'
    obtain ⟨hem, heo⟩ := execution?_eq_some he''
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    split
    · rename_i hact
      rw [ownerView_congr (t := s0.setTask e { ts with status := .cancelled })
          (s := s.setTask e { ts with status := .cancelled }) (by simp only [setTask_invocations, hi])
          (by rw [setTask_eq, setTask_eq, setExecution_executions, setExecution_executions, he]) c,
        setTask_eq, ownerView_setExecution_self (e' := withTask e { ts with status := .cancelled }) hL.wk hem rfl ht
          heo.symm,
        hL.ownerView_task ht he'' hts, hact, withTask_run, withTask_placement, ← htsn,
        withTask_any_self (ts' := { ts with status := .cancelled }) htsm rfl]
      rfl
    · exact ownerView_congr hi he c

end Owners

/-! ### Steps -/

section Ops
variable {p : Program} {s t : State}

theorem viewEntry_cancelled (task : Option String) (v : Option (Path × String × Bool)) :
    viewEntry .cancelled task v = viewEntry .cancelling task v := by
  cases v with
  | none => rfl
  | some v =>
    obtain ⟨_, _, _⟩ := v
    rfl

theorem accept_taskResults {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State}
    (h : s.accept c index value arm = .ok s') :
    ∃ N : List TaskResult, s'.taskResults = s.taskResults ++ N ∧ ∀ r ∈ N, r.output = .pending := by
  rcases accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
  · exact ⟨[], by simp, fun _ h => by cases h⟩
  · exact ⟨[_], rfl, fun r hr => by rw [List.mem_singleton.mp hr]⟩

/-- A report that stores `c'` in place of `c` and may update `c`'s owner, where `c'` keeps `c`'s entry. -/
theorem LInv.books_report (hL : LInv p s) {c c' : Call} (hc : c ∈ s.calls) (hid : c'.id = c.id) {s0 : State}
    (hcalls : s0.calls = (s.setCall c').calls) (hi : s0.invocations = s.invocations)
    (he : s0.executions = s.executions) (hr : s0.runs = s.runs) (hd : s0.deliveries = s.deliveries)
    (hf : s0.failures = s.failures) {N : List TaskResult} (htr : s0.taskResults = s.taskResults ++ N)
    (hN : ∀ r ∈ N, r.output = .pending) (hstep : OwnerStep s0 t c) (hself : callL t c' = callL s c) :
    Books p s t := by
  obtain ⟨hothers, hD, hI, hO, htc, htf⟩ :=
    hL.ownerStep hc hstep (by rw [hcalls]; exact setCall_calls_map_id) hi he hr hd htr hN
  refine books_of_grew (fs := []) (by rw [htf, hf, List.append_nil]) (grew_of_eq ?_ hD hI hO)
  refine callPart_eq_of (g := fun x => if x.id == c'.id then c' else x) (N := [])
    (by rw [htc, hcalls, setCall_calls, List.append_nil]) ?_ (fun _ h => by cases h)
  intro x hx
  by_cases hxc : x = c
  · subst hxc
    simp only [hid, beq_self_eq_true, ite_true]
    exact hself
  · have : (x.id == c'.id) = false := by simpa [hid] using fun h => hxc (hL.wk.call_eq_of_id hx hc h)
    simp only [this]
    exact callL_congr rfl rfl (hothers x hx hxc)

/-- A failure of a running or fetching call records one entry for the call: its cause, at its owner. -/
theorem LInv.books_failCall (hL : LInv p s) {c : Call} (hc : c ∈ s.calls)
    (hrun : c.status = .running ∨ c.status = .fetching) {status : CallStatus} {cause : Cause}
    (hcause : causeOf status true = some cause) (hst : status ≠ .running ∧ status ≠ .fetching)
    (h : s.failCall c status cause = .ok t) : Books p s t := by
  obtain ⟨f, s', hf, hso, rfl⟩ := failCall_eq_ok.mp h
  have hstep := ownerStep_settleOwner hso
  obtain ⟨hothers, hD, hI, hO, hcalls', hfail'⟩ := hL.ownerStep (s0 := s.setCall { c with status }) hc hstep
    (by simp) rfl rfl rfl rfl (N := []) (by simp) (fun _ h => by cases h)
  -- The entry of the failed call.
  have hself : callL s' { c with status } = some f := by
    unfold callL
    rw [ownerView_of_owner (c := c) (c' := { c with status }) rfl rfl]
    rcases settleOwner_eq_ok.mp hso with ⟨ht, i, hi, rfl⟩ | ⟨name, e, ts, ht, he, hts, rfl⟩
    · have hi' : s.invocation? c.owner = some i := hi
      obtain ⟨him, hio⟩ := invocation?_eq_some hi'
      rw [ownerView_congr (t := (s.setCall { c with status }).setInvocation { i with status := .failed })
        (s := s.setInvocation { i with status := .failed }) rfl rfl c,
        ownerView_setInvocation_self (i' := { i with status := .failed }) hL.wk him rfl ht hio.symm]
      rcases callFailure_eq_ok.mp hf with ⟨-, i2, hi2, rfl⟩ | ⟨name, e, ht', -, -⟩
      · rw [hi'] at hi2
        cases hi2
        simp only [ht]
        simp [viewEntry, hcause]
      · rw [ht] at ht'
        cases ht'
    · have he' : s.execution? c.owner = some e := he
      obtain ⟨hem, heo⟩ := execution?_eq_some he'
      obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
      rw [ownerView_congr (t := (s.setCall { c with status }).setTask e { ts with status := .failed })
        (s := s.setTask e { ts with status := .failed }) rfl rfl c,
        setTask_eq, ownerView_setExecution_self (e' := withTask e { ts with status := .failed }) hL.wk hem rfl ht
          heo.symm, withTask_run, withTask_placement, ← htsn,
        withTask_any_self (ts' := { ts with status := .failed }) htsm rfl]
      rcases callFailure_eq_ok.mp hf with ⟨ht', -⟩ | ⟨name', e2, ht', he2, rfl⟩
      · rw [ht] at ht'
        cases ht'
      · rw [he'] at he2
        cases he2
        rw [ht] at ht'
        cases ht'
        simp only [ht]
        simp [viewEntry, hcause]
  have hC : (callPart s').Perm (callPart s ++ [f]) := by
    refine callPart_perm_of (g := fun x => if x.id == ({ c with status } : Call).id then { c with status } else x)
      (c := c) hL.calls_nodup hc (by rw [hcalls', setCall_calls]) ?_
      (callL_live (by rcases hrun with h1 | h1 <;> simp [h1]))
      (by simpa using hself)
    intro x hx hne
    have : (x.id == c.id) = false := by simpa using fun h => hne (hL.wk.call_eq_of_id hx hc h)
    simp only [this]
    exact callL_congr rfl rfl (hothers x hx hne)
  have hsafe : StopSafe s' := by
    intro x hx hxr v hv
    rw [hcalls', setCall_calls] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    by_cases hyc : y = c
    · subst hyc
      simp only [beq_self_eq_true, ite_true] at hxr
      rcases hxr with h1 | h1
      · exact absurd h1 hst.1
      · exact absurd h1 hst.2
    · have : (y.id == c.id) = false := by simpa using fun h => hyc (hL.wk.call_eq_of_id hy hc h)
      simp only [this, Bool.false_eq_true, ↓reduceIte] at hxr hv ⊢
      rw [hothers y hy hyc] at hv
      exact hL.stopSafe y hy hxr v hv
  have h1 : Grew p s s' [f] := grew_of_parts (fc := [f]) (fd := []) (fi := []) (fo := []) hC
    (perm_of_eq_nil hD) (perm_of_eq_nil hI) (perm_of_eq_nil hO)
  refine books_of_grew (fs := [f]) (by rw [fail_failures, hfail']; rfl) ?_
  simpa using h1.trans (grew_fail hsafe (f := f) (policy := c.policy))

/-- `lost` or `terminated` of a cancelling call keeps the ledger: the call's entry depends only on
    whether its owner failed, which cancelling the owner keeps. -/
theorem LInv.books_cancelled (hL : LInv p s) {c : Call} (hc : c ∈ s.calls) (hcan : c.status = .cancelling)
    (h : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) : Books p s t := by
  refine hL.books_report (c' := { c with status := .cancelled }) hc rfl
    (s0 := s.setCall { c with status := .cancelled }) rfl rfl rfl rfl rfl rfl (N := []) (by simp)
    (fun _ h => by cases h) (ownerStep_cancelOwner h) ?_
  unfold callL
  rw [ownerView_of_owner (c := c) (c' := { c with status := .cancelled }) rfl rfl,
    hL.ownerView_cancelOwner_self (s0 := s.setCall { c with status := .cancelled }) rfl rfl h, hcan]
  exact viewEntry_cancelled _ _

/-- Appending records that carry no entry and hide no lookup keeps the ledger. -/
theorem LInv.books_append (hL : LInv p s) {I : List Invocation} {C : List Call} {R : List Run}
    {E : List Execution} (hi : t.invocations = s.invocations ++ I) (hc : t.calls = s.calls ++ C)
    (hr : t.runs = s.runs ++ R) (he : t.executions = s.executions ++ E) (hd : t.deliveries = s.deliveries)
    (htr : t.taskResults = s.taskResults) (hf : t.failures = s.failures) (hCst : ∀ c ∈ C, c.status = .running)
    (hCid : ∀ c ∈ C, ∀ eid n, c.id ≠ Key.task eid n) (hR : ∀ r ∈ R, r.task = none)
    (hE : ∀ e ∈ E, ∀ x ∈ e.tasks, x.status ≠ .failed) : Books p s t := by
  refine books_of_grew (fs := []) (by rw [hf, List.append_nil]) (grew_of_eq ?_ ?_ ?_ ?_)
  · refine callPart_append_eq hc (fun x hx => ?_) (fun y hy => callL_live (Or.inl (hCst y hy)))
    obtain ⟨v, hv⟩ := hL.ownerView_some hx
    exact callL_congr rfl rfl ((ownerView_append hi he hv).trans hv.symm)
  · exact deliveryPart_eq_of (N := []) (by rw [hd, List.append_nil])
      (fun d hd' => hL.deliveryL_keep (Settle.KeepsWorkflows.of_append hr) hd') (fun _ h => by cases h)
  · refine inputPart_eq_of (g := id) (N := E) (by rw [he, List.map_id]) (fun e _ => filterMap_congr' fun x _ => ?_)
      (fun e he' x hx => taskInputL_of_ne (hE e he' x hx))
    exact taskInputL_congr rfl rfl rfl rfl rfl (hasBody_append hc hr (fun c hc' => hCid c hc' _ _)
      (fun r hr' _ => by rw [hR r hr']; simp))
  · refine outputPart_eq_of (g := id) (N := []) (by rw [htr, List.map_id, List.append_nil]) (fun r hr' => ?_)
      (fun _ h => by cases h)
    obtain ⟨v, hv⟩ := hL.execPos_some hr'
    exact taskOutputL_congr rfl rfl ((execPos_append he hv).trans hv.symm)

theorem LInv.books_invoke (hL : LInv p s) {path : Path} {name : String} {trigger : Option ResultId}
    (hs : Step.invoke p s path name trigger = .ok t) : Books p s t := by
  obtain ⟨-, -, r, w, pl, input, id, hr, -, -, -, -, hkey, -, hfresh, hcases⟩ := Step.invoke_inv hs
  have key : Calls.InvocationKey id := ⟨path, name, trigger, hkey⟩
  have hneq : ∀ eid n, id ≠ Key.task eid n := fun eid n h => Calls.not_taskKey_of_invocationKey key ⟨eid, n, h⟩
  rcases hcases with ⟨f, decl, -, -, hc, rfl⟩ | ⟨judge, arms, -, hc, rfl⟩ | ⟨wf, out, -, hrun, rfl⟩ |
    ⟨cc, -, he, rfl⟩
  · exact hL.books_append (R := []) (E := []) rfl rfl (by simp) (by simp) rfl rfl rfl
      (fun c hc' => by rw [List.mem_singleton.mp hc']) (fun c hc' => by rw [List.mem_singleton.mp hc']; exact hneq)
      (fun _ h => by cases h) (fun _ h => by cases h)
  · exact hL.books_append (R := []) (E := []) rfl rfl (by simp) (by simp) rfl rfl rfl
      (fun c hc' => by rw [List.mem_singleton.mp hc']) (fun c hc' => by rw [List.mem_singleton.mp hc']; exact hneq)
      (fun _ h => by cases h) (fun _ h => by cases h)
  · exact hL.books_append (C := []) (E := []) rfl (by simp) rfl (by simp) rfl rfl rfl
      (fun _ h => by cases h) (fun _ h => by cases h) (fun r hr' => by rw [List.mem_singleton.mp hr'])
      (fun _ h => by cases h)
  · refine hL.books_append (C := []) (R := []) rfl (by simp) (by simp) rfl rfl rfl rfl
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h) ?_
    intro e he' x hx
    rw [List.mem_singleton.mp he'] at hx
    obtain ⟨ts, -, rfl⟩ := List.mem_map.mp hx
    split <;> simp

theorem LInv.books_transformFailed (hL : LInv p s) {path : Path} {index : Nat} {source : ResultId} {w : Workflow}
    {c : Connection} {policy : Policy} (hdt : Step.deliveryTarget p s path index source = .ok (w, c)) {d : Delivery}
    (hdrun : d.run = path) (hdcon : d.connection = index) (hdout : d.outcome = .failed) {f : Failure}
    (hf : f = { run := path, placement := c.target, cause := .transform }) :
    Books p s (State.fail { s with deliveries := s.deliveries ++ [d] } f policy) := by
  obtain ⟨hw, hc, -, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
  have hnew : deliveryL p { s with deliveries := s.deliveries ++ [d] } d = some f := by
    unfold deliveryL
    rw [option_bind_eq_some]
    refine ⟨(), by rw [hdout]; rfl, ?_⟩
    rw [option_bind_eq_some]
    refine ⟨w, by rw [hdrun]; exact hw, ?_⟩
    rw [option_bind_eq_some]
    exact ⟨c, by rw [hdcon]; exact hc, by rw [hdrun, hf]; rfl⟩
  have h1 : Grew p s { s with deliveries := s.deliveries ++ [d] } [f] :=
    grew_of_parts (fc := []) (fd := [f]) (fi := []) (fo := []) (perm_of_eq_nil (callPart_of rfl rfl rfl))
      (List.Perm.of_eq (deliveryPart_append_one (s := s) (t := { s with deliveries := s.deliveries ++ [d] }) rfl
        (fun d _ => deliveryL_congr rfl) hnew))
      (perm_of_eq_nil (inputPart_of rfl rfl rfl)) (perm_of_eq_nil (outputPart_of rfl rfl))
  have hsafe : StopSafe { s with deliveries := s.deliveries ++ [d] } := fun x hx hxr v hv => hL.stopSafe x hx hxr v hv
  refine books_of_grew (fs := [f]) (by simp) ?_
  simpa using h1.trans (grew_fail hsafe)

/-- A task that has not begun has no call, so updating it changes no call's owner view. -/
theorem LInv.ownerView_setTask_notBegun (hL : LInv p s) {e : Execution} (he : e ∈ s.executions) {ts : TaskState}
    (hts : ts ∈ e.tasks) (hnb : ¬Limit.Begun ts.status) {ts' : TaskState} (hname : ts'.name = ts.name) {x : Call}
    (hx : x ∈ s.calls) : ownerView (s.setTask e ts') x = ownerView s x :=
  ownerView_setTask hL.wk he fun n hxt hxo hn => hL.lim.no_call he hts hnb x hx (by rw [hxt, hn, hname]) hxo

theorem LInv.outputPart_setTask (hL : LInv p s) {e : Execution} (he : e ∈ s.executions) {ts' : TaskState}
    {u : State} {N : List TaskResult} (htr : u.taskResults = s.taskResults ++ N) (hN : ∀ r ∈ N, r.output ≠ .failed)
    (hex : u.executions = (s.setTask e ts').executions) : outputPart u = outputPart s :=
  outputPart_eq_of (g := id) (N := N) (by rw [htr, List.map_id])
    (fun r _ => taskOutputL_congr rfl rfl (by
      rw [execPos_congr hex, setTask_eq, execPos_setExecution (e' := withTask e ts') hL.wk he rfl rfl rfl]; rfl))
    (fun r hr => taskOutputL_of_ne (hN r hr))

theorem LInv.books_taskInput (hL : LInv p s) {eid name : String} {value : Option Value}
    (hs : Step.taskInput p s eid name value = .ok t) : Books p s t := by
  obtain ⟨-, -, e, ts, spec, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
  obtain ⟨hem, -⟩ := execution?_eq_some he
  obtain ⟨htsm, -⟩ := find?_key_eq_some hts
  have hnb : ¬Limit.Begun ts.status := by simp [Limit.Begun, hpend]
  refine books_of_grew (fs := []) (by simp) (grew_of_eq ?_ (deliveryPart_of rfl rfl) ?_
    (hL.outputPart_setTask hem (N := []) (by simp) (fun _ h => by cases h) rfl))
  · exact callPart_append_eq (N := []) (by simp)
      (fun x hx => callL_congr rfl rfl
        (hL.ownerView_setTask_notBegun (ts' := { ts with status := .ready, input := value }) hem htsm hnb rfl hx))
      (fun _ h => by cases h)
  · exact hL.inputPart_setTask (ts' := { ts with status := .ready, input := value }) hem htsm rfl rfl
      (fun _ _ _ => hasBody_congr rfl rfl _ _)
      (by rw [taskInputL_of_ne (by simp), taskInputL_of_ne (by simp [hpend])])

theorem LInv.books_taskInputFailed (hL : LInv p s) {eid name : String}
    (hs : Step.taskInputFailed p s eid name = .ok t) : Books p s t := by
  obtain ⟨-, -, e, ts, spec, tid, he, hts, hpend, -, -, rfl⟩ := Step.taskInputFailed_inv hs
  obtain ⟨hem, -⟩ := execution?_eq_some he
  obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
  have hnb : ¬Limit.Begun ts.status := by simp [Limit.Begun, hpend]
  have hC : callPart (s.setTask e { ts with status := .failed }) = callPart s :=
    callPart_append_eq (N := []) (by simp)
      (fun x hx => callL_congr rfl rfl
        (hL.ownerView_setTask_notBegun (ts' := { ts with status := .failed }) hem htsm hnb rfl hx))
      (fun _ h => by cases h)
  have hbf : hasBody (s.setTask e { ts with status := .failed }) (withTask e { ts with status := .failed }).id
      ({ ts with status := .failed } : TaskState).name = false := hL.hasBody_not_begun (x := ts) hem htsm hnb
  have hI : (inputPart (s.setTask e { ts with status := .failed })).Perm
      (inputPart s ++ [{ run := e.run, placement := e.placement, task := some name, cause := .transform }]) := by
    refine hL.inputPart_setTask_perm (ts' := { ts with status := .failed }) hem htsm rfl rfl
      (fun _ _ _ => hasBody_congr rfl rfl _ _) (taskInputL_of_ne (by simp [hpend])) ?_
    unfold taskInputL
    rw [hbf]
    simp [htsn]
  have hsafe : StopSafe (s.setTask e { ts with status := .failed }) := by
    intro x hx hxr v hv
    rw [hL.ownerView_setTask_notBegun (ts' := { ts with status := .failed }) hem htsm hnb rfl hx] at hv
    exact hL.stopSafe x hx hxr v hv
  have h1 : Grew p s (s.setTask e { ts with status := .failed })
      [{ run := e.run, placement := e.placement, task := some name, cause := .transform }] :=
    grew_of_parts (fc := []) (fd := []) (fi := [_]) (fo := []) (perm_of_eq_nil hC)
      (perm_of_eq_nil (deliveryPart_of rfl rfl)) hI
      (perm_of_eq_nil (hL.outputPart_setTask hem (N := []) (by simp) (fun _ h => by cases h) rfl))
  refine books_of_grew (fs := [{ run := e.run, placement := e.placement, task := some name, cause := .transform }])
    (by simp) ?_
  simpa using h1.trans (grew_fail hsafe)

theorem LInv.books_beginTask (hL : LInv p s) {eid name : String} (hs : Step.beginTask p s eid name = .ok t) :
    Books p s t := by
  obtain ⟨-, -, e, cc, ts, spec, he, -, -, hts, hready, -, -, hcases⟩ := Step.beginTask_inv hs
  obtain ⟨hem, -⟩ := execution?_eq_some he
  obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
  have hnb : ¬Limit.Begun ts.status := by simp [Limit.Begun, hready]
  have hkey : ∀ eid' n, (eid' ≠ e.id ∨ n ≠ ts.name) → State.taskId e.id name ≠ Key.task eid' n := by
    intro eid' n hne h
    have h2 := identity_injective h
    simp only [List.cons.injEq, true_and, and_true] at h2
    rcases hne with h1 | h1
    · exact h1 h2.1.symm
    · exact h1 (h2.2.symm.trans htsn.symm)
  have hself : ∀ {u : State}, taskInputL u (withTask e { ts with status := .active }) { ts with status := .active } =
      taskInputL s e ts := by
    intro u
    rw [taskInputL_of_ne (by simp), taskInputL_of_ne (by simp [hready])]
  have hview : ∀ x ∈ s.calls, ownerView t x = ownerView s x := by
    intro x hx
    rcases hcases with ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;>
      exact (ownerView_congr (s := s.setTask e { ts with status := .active }) rfl rfl x).trans
        (hL.ownerView_setTask_notBegun (ts' := { ts with status := .active }) hem htsm hnb rfl hx)
  rcases hcases with ⟨f, decl, -, -, hcall, rfl⟩ | ⟨wf, out, -, hrun, rfl⟩
  · refine books_of_grew (fs := []) (by simp) (grew_of_eq ?_ (deliveryPart_of rfl rfl) ?_
      (hL.outputPart_setTask hem (N := []) (by simp) (fun _ h => by cases h) rfl))
    · exact callPart_append_eq (N := [_]) rfl (fun x hx => callL_congr rfl rfl (hview x hx))
        (fun y hy => by rw [List.mem_singleton.mp hy]; exact callL_live (Or.inl rfl))
    · exact hL.inputPart_setTask (ts' := { ts with status := .active }) hem htsm rfl rfl
        (fun eid' n hne => hasBody_append (C := [_]) (R := []) rfl (by simp)
          (fun c hc => by rw [List.mem_singleton.mp hc]; exact hkey eid' n hne) (fun _ h => by cases h)) hself
  · refine books_of_grew (fs := []) (by simp) (grew_of_eq ?_ ?_ ?_
      (hL.outputPart_setTask hem (N := []) (by simp) (fun _ h => by cases h) rfl))
    · exact callPart_append_eq (N := []) (by simp) (fun x hx => callL_congr rfl rfl (hview x hx))
        (fun _ h => by cases h)
    · exact deliveryPart_eq_of (N := []) (by simp)
        (fun d hd => hL.deliveryL_keep (Settle.KeepsWorkflows.of_append rfl) hd) (fun _ h => by cases h)
    · refine hL.inputPart_setTask (ts' := { ts with status := .active }) hem htsm rfl rfl
        (fun eid' n hne => hasBody_append (C := []) (R := [_]) (by simp) rfl (fun _ h => by cases h) ?_) hself
      intro r hr ho
      rw [List.mem_singleton.mp hr] at ho ⊢
      simp only [Option.some.injEq] at ho
      subst ho
      simp only [ne_eq, Option.some.injEq]
      rcases hne with h1 | h1
      · exact absurd rfl h1
      · exact fun h => h1 (h.symm.trans htsn.symm)

theorem taskOutputL_failed {r : TaskResult} (ho : r.output = .failed) {v : Path × String}
    (hpos : execPos s r.execution = some v) :
    taskOutputL s r = some { run := v.1, placement := v.2, task := some r.task, cause := .transform } := by
  unfold taskOutputL
  rw [ite_eq_left ho, hpos]
  rfl

/-- With unique keys, a task result differs from `r` exactly when its key does. -/
theorem LInv.taskResult_key_ne (hL : LInv p s) {r x : TaskResult} (hr : r ∈ s.taskResults) (hx : x ∈ s.taskResults)
    (hne : x ≠ r) : (x.execution == r.execution && x.task == r.task && x.index == r.index) = false := by
  have : ¬(x.execution = r.execution ∧ x.task = r.task ∧ x.index = r.index) := by
    rintro ⟨h1, h2, h3⟩
    exact hne (Limit.eq_of_key hL.wk.taskResults hx hr (by simp [h1, h2, h3]))
  simpa [and_assoc] using this

theorem LInv.books_taskOutput (hL : LInv p s) {eid name : String} {index : Nat} {value : Value}
    (hs : Step.taskOutput p s eid name index value = .ok t) : Books p s t := by
  obtain ⟨-, -, e, cc, spec, r, he, -, -, -, hr, hpend, hcases⟩ := Step.taskOutput_inv hs
  have hrm : r ∈ s.taskResults := List.mem_of_find?_eq_some hr
  have hO : ∀ {u : State}, u.taskResults = (s.setTaskResult { r with output := .value value }).taskResults →
      u.executions = s.executions → outputPart u = outputPart s := by
    intro u htr hex
    refine outputPart_eq_of (g := fun x => if x.execution == r.execution && x.task == r.task && x.index == r.index then
      { r with output := .value value } else x) (N := []) (by rw [htr, setTaskResult_taskResults, List.append_nil])
      (fun x hx => ?_) (fun _ h => by cases h)
    by_cases hxr : x = r
    · subst hxr
      simp only [beq_self_eq_true, Bool.and_self, ite_true]
      rw [taskOutputL_of_ne (by simp), taskOutputL_of_ne (by simp [hpend])]
    · simp only [hL.taskResult_key_ne hrm hx hxr, Bool.false_eq_true, ↓reduceIte]
      exact taskOutputL_congr rfl rfl (execPos_congr hex _)
  rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
  · exact books_of_grew (fs := []) (by simp) (grew_of_eq (callPart_of rfl rfl rfl) (deliveryPart_of rfl rfl)
      (inputPart_of rfl rfl rfl) (hO rfl rfl))
  · exact books_of_grew (fs := []) (by simp) (grew_of_eq (callPart_of rfl rfl rfl) (deliveryPart_of rfl rfl)
      (inputPart_of rfl rfl rfl) (hO rfl rfl))

theorem LInv.books_taskOutputFailed (hL : LInv p s) {eid name : String} {index : Nat}
    (hs : Step.taskOutputFailed p s eid name index = .ok t) : Books p s t := by
  obtain ⟨-, -, e, spec, r, he, -, -, hr, hpend, rfl⟩ := Step.taskOutputFailed_inv hs
  have hrm : r ∈ s.taskResults := List.mem_of_find?_eq_some hr
  have hrk := List.find?_some hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hrk
  obtain ⟨⟨hre, hrt⟩, -⟩ := hrk
  have hO : (outputPart (s.setTaskResult { r with output := .failed })).Perm
      (outputPart s ++ [{ run := e.run, placement := e.placement, task := some name, cause := .transform }]) := by
    refine outputPart_perm_of (g := fun x => if x.execution == r.execution && x.task == r.task && x.index == r.index then
      { r with output := .failed } else x) (r0 := r) hL.taskResults_nodup hrm (by rw [setTaskResult_taskResults])
      (fun x hx hne => ?_) (taskOutputL_of_ne (by simp [hpend])) ?_
    · simp only [hL.taskResult_key_ne hrm hx hne, Bool.false_eq_true, ↓reduceIte]
      exact taskOutputL_congr rfl rfl (execPos_congr rfl _)
    · simp only [beq_self_eq_true, Bool.and_self, ite_true]
      have hpos : execPos (s.setTaskResult { r with output := .failed })
          ({ r with output := .failed } : TaskResult).execution = some (e.run, e.placement) := by
        show (s.execution? r.execution).map _ = _
        rw [hre, he]
        rfl
      rw [taskOutputL_failed rfl hpos]
      simp [hrt]
  have h1 : Grew p s (s.setTaskResult { r with output := .failed })
      [{ run := e.run, placement := e.placement, task := some name, cause := .transform }] :=
    grew_of_parts (fc := []) (fd := []) (fi := []) (fo := [_]) (perm_of_eq_nil (callPart_of rfl rfl rfl))
      (perm_of_eq_nil (deliveryPart_of rfl rfl)) (perm_of_eq_nil (inputPart_of rfl rfl rfl)) hO
  have hsafe : StopSafe (s.setTaskResult { r with output := .failed }) := fun x hx hxr v hv => hL.stopSafe x hx hxr v hv
  refine books_of_grew (fs := [{ run := e.run, placement := e.placement, task := some name, cause := .transform }])
    (by simp) ?_
  simpa using h1.trans (grew_fail hsafe)

theorem map_replace_map_mem {α β : Type} {l : List α} {q : α → Bool} {y : α} {f : α → β}
    (h : ∀ x ∈ l, q x = true → f y = f x) : (l.map fun x => if q x then y else x).map f = l.map f := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  by_cases hx' : q x = true
  · simp [hx', h x hx hx']
  · simp [hx']

theorem LInv.setRun_ownerTask (hL : LInv p s) {r r' : Run} (hr : r ∈ s.runs) (hpath : r'.path = r.path)
    (ho : r'.owner = r.owner) (ht : r'.task = r.task) :
    (s.setRun r').runs.map (fun x => (x.owner, x.task)) = s.runs.map (fun x => (x.owner, x.task)) := by
  rw [setRun_runs]
  apply map_replace_map_mem
  intro x hx hq
  have : x = r := hL.wk.run_eq_of_path hx hr ((beq_iff_eq.mp hq).trans hpath)
  subst this
  simp [ho, ht]

theorem LInv.books_closeExecution (hL : LInv p s) {eid : String} (hs : Step.closeExecution p s eid = .ok t) :
    Books p s t := by
  obtain ⟨-, -, e, cc, i, he, -, -, -, -, hi, hcases⟩ := Step.closeExecution_inv hs
  obtain ⟨hem, heo⟩ := execution?_eq_some he
  obtain ⟨-, hio⟩ := invocation?_eq_some hi
  -- A call of an invocation has the invocation's identity, which is no execution's.
  have hne : ∀ x ∈ s.calls, x.task = none → x.owner ≠ i.id := by
    intro x hx ht ho
    have hxid := (hL.callNone hx ht).1
    exact hL.keys.disjoint x hx (List.mem_map.mpr ⟨e, hem, by rw [heo, hxid, ho, hio]⟩)
  have hview : ∀ {st : InvocationStatus} {u : State},
      u.invocations = ((s.setExecution { e with complete := true }).setInvocation { i with status := st }).invocations →
      u.executions = (s.setExecution { e with complete := true }).executions →
      ∀ x ∈ s.calls, ownerView u x = ownerView s x := by
    intro st u hi' he' x hx
    rw [ownerView_congr hi' he' x,
      ownerView_setInvocation_of_ne (i := { i with status := st }) (fun ht ho => hne x hx ht ho),
      ownerView_setExecution_tasks (e' := { e with complete := true }) hL.wk hem rfl rfl rfl rfl x]
  have hO : ∀ {u : State}, u.executions = (s.setExecution { e with complete := true }).executions →
      u.taskResults = s.taskResults → outputPart u = outputPart s := fun hex htr =>
    outputPart_eq_of (g := id) (N := []) (by rw [htr, List.map_id, List.append_nil])
      (fun r _ => taskOutputL_congr rfl rfl (by
        rw [execPos_congr hex, execPos_setExecution (e' := { e with complete := true }) hL.wk hem rfl rfl rfl]; rfl))
      (fun _ h => by cases h)
  have hI : ∀ {u : State}, u.executions = (s.setExecution { e with complete := true }).executions →
      u.calls = s.calls → u.runs = s.runs → inputPart u = inputPart s := fun hex hc hr =>
    hL.inputPart_setExecution_tasks (e' := { e with complete := true }) hem rfl rfl rfl rfl hex
      (fun _ _ => hasBody_congr (by rw [hc]) (by rw [hr]) _ _)
  rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
    exact books_of_grew (fs := []) (by simp) (grew_of_eq
      (callPart_append_eq (N := []) (by simp) (fun x hx => callL_congr rfl rfl (hview rfl rfl x hx))
        (fun _ h => by cases h))
      (deliveryPart_of rfl rfl) (hI rfl rfl rfl) (hO rfl rfl))

theorem LInv.books_closeRun (hL : LInv p s) {path : Path} (hs : Step.closeRun p s path = .ok t) : Books p s t := by
  obtain ⟨-, -, r, w, output, x, owner, hr, -, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
  obtain ⟨hrm, hrp⟩ := run?_eq_some hr
  have hr' : s.run? ({ r with complete := true } : Run).path = some r := by
    show s.run? r.path = some r
    rw [hrp]
    exact hr
  have hsw : Settle.SameWorkflows p s (s.setRun { r with complete := true }) := Settle.SameWorkflows.setRun hr' rfl
  have hruns := hL.setRun_ownerTask (r' := { r with complete := true }) hrm rfl rfl rfl
  have hD : ∀ {u : State}, u.deliveries = s.deliveries → u.runs = (s.setRun { r with complete := true }).runs →
      deliveryPart p u = deliveryPart p s := fun hd hru =>
    deliveryPart_eq_of (N := []) (by rw [hd, List.append_nil])
      (fun d _ => deliveryL_congr ((Settle.SameWorkflows.of_runs hru d.run).trans (hsw d.run))) (fun _ h => by cases h)
  rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
  · obtain ⟨-, hio⟩ := invocation?_eq_some hi
    -- A run's owner is no call's identity, and a call of an invocation has the invocation's identity.
    have hne : ∀ y ∈ s.calls, y.task = none → y.owner ≠ i.id := by
      intro y hy ht ho
      have hyid := (hL.callNone hy ht).1
      exact (hL.keys.owners r hrm owner howner).2 y hy (by rw [hyid, ho, hio])
    have hview : ∀ {st : InvocationStatus} {u : State},
        u.invocations = ((s.setRun { r with complete := true }).setInvocation { i with status := st }).invocations →
        u.executions = s.executions → ∀ y ∈ s.calls, ownerView u y = ownerView s y := by
      intro st u hi' he' y hy
      rw [ownerView_congr (s := s.setInvocation { i with status := st }) hi' he' y,
        ownerView_setInvocation_of_ne (i := { i with status := st }) (fun ht ho => hne y hy ht ho)]
    rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact books_of_grew (fs := []) (by simp) (grew_of_eq
        (callPart_append_eq (N := []) (by simp) (fun y hy => callL_congr rfl rfl (hview rfl rfl y hy))
          (fun _ h => by cases h))
        (hD rfl rfl) (inputPart_of rfl rfl hruns) (outputPart_of rfl rfl))
  · obtain ⟨hem, heo⟩ := execution?_eq_some he
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    -- A task never has both a call and a run.
    have hapart : ∀ (st : TaskStatus), ∀ y ∈ s.calls, ∀ n, y.task = some n → y.owner = e.id →
        n ≠ ({ ts with status := st } : TaskState).name := by
      intro st y hy n hyt hyo hn
      refine hL.lim.apart y hy r hrm n hyt (by rw [htask, hn, htsn]) ?_
      rw [howner, ← heo, ← hyo]
    have hview : ∀ {st : TaskStatus} {u : State}, u.executions = (s.setTask e { ts with status := st }).executions →
        u.invocations = s.invocations → ∀ y ∈ s.calls, ownerView u y = ownerView s y := by
      intro st u he' hi' y hy
      rw [ownerView_congr (s := s.setTask e { ts with status := st }) hi' he' y]
      exact ownerView_setTask hL.wk hem (hapart st y hy)
    have hbody : hasBody s e.id ts.name = true := hasBody_of_run hrm (by rw [howner, heo]) (by rw [htask, htsn])
    have hI : ∀ {st : TaskStatus} {u : State}, u.executions = (s.setTask e { ts with status := st }).executions →
        u.calls = s.calls → u.runs = (s.setRun { r with complete := true }).runs → inputPart u = inputPart s := by
      intro st u hex hc hru
      have hb : ∀ eid n, hasBody u eid n = hasBody s eid n :=
        fun eid n => hasBody_congr (by rw [hc]) (by rw [hru]; exact hruns) eid n
      exact hL.inputPart_setTask (ts' := { ts with status := st }) hem htsm rfl hex (fun eid n _ => hb eid n)
        (by rw [taskInputL_of_hasBody (by rw [hb]; exact hbody), taskInputL_of_hasBody hbody])
    rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact books_of_grew (fs := []) (by simp) (grew_of_eq
        (callPart_append_eq (N := []) (by simp) (fun y hy => callL_congr rfl rfl (hview rfl rfl y hy))
          (fun _ h => by cases h))
        (hD rfl rfl) (hI rfl rfl rfl)
        (hL.outputPart_setTask hem (N := [_]) rfl (fun r hr => by rw [List.mem_singleton.mp hr]; simp) rfl))
    all_goals exact books_of_grew (fs := []) (by simp) (grew_of_eq
        (callPart_append_eq (N := []) (by simp) (fun y hy => callL_congr rfl rfl (hview rfl rfl y hy))
          (fun _ h => by cases h))
        (hD rfl rfl) (hI rfl rfl rfl) (hL.outputPart_setTask hem (N := []) (by simp) (fun _ h => by cases h) rfl))

/-- Every accepted step records exactly the failures its ledger gains. -/
theorem LInv.step_books (hL : LInv p s) {op : Op} (hs : step p s op = .ok t) : Books p s t := by
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases hL.start with rfl | h
    · exact books_of_grew (fs := []) rfl (List.Perm.of_eq rfl)
    · simp [h] at hst
  | invoke path name trigger => exact hL.books_invoke hs
  | fetch id =>
    obtain ⟨-, -, c, hc, -, hrun, rfl⟩ := Step.fetch_inv hs
    exact hL.books_report (c' := { c with status := .fetching }) (call?_eq_some hc).1 rfl
      (s0 := s.setCall { c with status := .fetching }) rfl rfl rfl rfl rfl rfl (N := []) (by simp)
      (fun _ h => by cases h) (Or.inl rfl) (by rw [callL_live (Or.inr (Or.inl rfl)), callL_live (Or.inl hrun)])
  | returned id value =>
    obtain ⟨-, -, c, fn, s', hc, -, hrun, -, hacc, hso⟩ := Step.returned_inv hs
    obtain ⟨N, hN1, hN2⟩ := accept_taskResults hacc
    obtain ⟨-, -, -, hr, hi, hcl, he, hd, -, hf⟩ := accept_frame hacc
    exact hL.books_report (c' := { c with status := .returned }) (call?_eq_some hc).1 rfl
      (s0 := s'.setCall { c with status := .returned }) (by rw [setCall_calls, setCall_calls, hcl]) hi he hr hd hf
      (by rw [setCall_taskResults, hN1]) hN2 (ownerStep_settleOwner hso)
      (by rw [callL_live (Or.inr (Or.inr rfl)), callL_live (Or.inl hrun)])
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, hrun, -, hnone, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    obtain ⟨N, hN1, hN2⟩ := accept_taskResults hacc
    obtain ⟨-, -, -, hr, hinv, hcl, he, hd, -, hf⟩ := accept_frame hacc
    refine hL.books_report (c' := { c with status := .returned }) (call?_eq_some hc).1 rfl
      (s0 := s'.setCall { c with status := .returned }) (by rw [setCall_calls, setCall_calls, hcl]) hinv he hr hd hf
      (by rw [setCall_taskResults, hN1]) hN2
      (Or.inr (Or.inl ⟨hnone, i, { i with status := .succeeded, arm := some arm }, ?_, rfl, rfl⟩))
      (by rw [callL_live (Or.inr (Or.inr rfl)), callL_live (Or.inl hrun)])
    rw [invocation?_congr (s := s) (by rw [setCall_invocations, hinv])]
    exact hi
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, hfetch, hacc, rfl⟩ := Step.yielded_inv hs
    obtain ⟨N, hN1, hN2⟩ := accept_taskResults hacc
    obtain ⟨-, -, -, hr, hi, hcl, he, hd, -, hf⟩ := accept_frame hacc
    exact hL.books_report (c' := { c with status := .running, yields := c.yields + 1 }) (call?_eq_some hc).1 rfl
      (s0 := s'.setCall { c with status := .running, yields := c.yields + 1 })
      (by rw [setCall_calls, setCall_calls, hcl]) hi he hr hd hf (by rw [setCall_taskResults, hN1]) hN2 (Or.inl rfl)
      (by rw [callL_live (Or.inl rfl), callL_live (Or.inr (Or.inl hfetch))])
  | ended id =>
    obtain ⟨-, -, c, hc, -, hfetch, hso⟩ := Step.ended_inv hs
    exact hL.books_report (c' := { c with status := .returned }) (call?_eq_some hc).1 rfl
      (s0 := s.setCall { c with status := .returned }) rfl rfl rfl rfl rfl rfl (N := []) (by simp)
      (fun _ h => by cases h) (ownerStep_settleOwner hso)
      (by rw [callL_live (Or.inr (Or.inr rfl)), callL_live (Or.inr (Or.inl hfetch))])
  | failed id =>
    obtain ⟨-, -, c, hc, hrun, hf⟩ := Step.failed_inv hs
    exact hL.books_failCall (call?_eq_some hc).1 hrun rfl (by simp) hf
  | timedOut id element =>
    obtain ⟨-, -, c, hc, hcond, hf⟩ := Step.timedOut_inv hs
    have hrun : c.status = .running ∨ c.status = .fetching := by
      rcases hcond with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact Or.inr h
      · exact h
    exact hL.books_failCall (call?_eq_some hc).1 hrun rfl (by simp) hf
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨hrun, hf⟩ | ⟨hcan, ho⟩⟩ := Step.lost_inv hs
    · exact hL.books_failCall (call?_eq_some hc).1 hrun rfl (by simp) hf
    · exact hL.books_cancelled (call?_eq_some hc).1 hcan ho
  | terminated id =>
    obtain ⟨-, -, c, hc, hcan, ho⟩ := Step.terminated_inv hs
    exact hL.books_cancelled (call?_eq_some hc).1 hcan ho
  | deliver path index source value =>
    obtain ⟨-, -, w, c, outcome, hdt, hout, rfl⟩ := Step.deliver_inv hs
    refine books_of_grew (fs := []) (by simp) (grew_of_eq (callPart_of rfl rfl rfl) ?_ (inputPart_of rfl rfl rfl)
      (outputPart_of rfl rfl))
    refine deliveryPart_eq_of (N := [_]) rfl (fun d _ => deliveryL_congr rfl) ?_
    intro d hd
    rw [List.mem_singleton.mp hd]
    apply deliveryL_of_ne
    rcases hout with ⟨tid, v, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp
  | transformFailed path index source =>
    obtain ⟨-, -, w, c, tid, target, hdt, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact hL.books_transformFailed hdt rfl rfl rfl rfl
  | taskInput eid name value => exact hL.books_taskInput hs
  | taskInputFailed eid name => exact hL.books_taskInputFailed hs
  | beginTask eid name => exact hL.books_beginTask hs
  | taskOutput eid name index value => exact hL.books_taskOutput hs
  | taskOutputFailed eid name index => exact hL.books_taskOutputFailed hs
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      exact books_of_grew (fs := []) (by simp) (grew_of_eq (callPart_of rfl rfl rfl) (deliveryPart_of rfl rfl)
        (inputPart_of rfl rfl rfl) (outputPart_of rfl rfl))
  | closeExecution eid => exact hL.books_closeExecution hs
  | closeRun path => exact hL.books_closeRun hs
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · refine books_of_grew (fs := []) (by simp) ?_
      unfold Grew
      rw [List.append_nil]
      exact List.Perm.of_eq (ledgerL_stop (p := p) hL.stopSafe)
    · exact books_of_grew (fs := []) (by simp) (List.Perm.of_eq (by rw [List.append_nil]; rfl))
  | conclude =>
    obtain ⟨-, ⟨-, r, w, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · obtain ⟨hrm, hrp⟩ := run?_eq_some hr
      have hr' : s.run? ({ r with complete := true } : Run).path = some r := by
        show s.run? r.path = some r
        rw [hrp]
        exact hr
      refine books_of_grew (fs := []) (by simp) (grew_of_eq (callPart_of rfl rfl rfl) ?_
        (inputPart_of rfl rfl (hL.setRun_ownerTask (r' := { r with complete := true }) hrm rfl rfl rfl))
        (outputPart_of rfl rfl))
      exact deliveryPart_eq_of (N := []) (by simp)
        (fun d _ => deliveryL_congr (Settle.SameWorkflows.setRun hr' rfl d.run)) (fun _ h => by cases h)
    · exact books_of_grew (fs := []) (by simp) (List.Perm.of_eq (by rw [List.append_nil]; rfl))

end Ops

/-- Every failure has exactly one source record, in every reachable state of a valid program. -/
theorem Reachable.failures_ledgerL {p : Program} {s : State} (valid : p.validate = .ok ()) (h : Reachable p s) :
    s.failures.Perm (ledgerL p s) := by
  induction h with
  | empty => exact List.Perm.of_eq rfl
  | step op hr hs ih =>
    obtain ⟨fs, hf, hg⟩ := (LInv.of_reachable valid hr).step_books hs
    rw [hf]
    exact (List.Perm.append_right fs ih).trans hg.symm

end Suimon.Round3.LedgerCore
