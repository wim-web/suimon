import Suimon.Theorems.Round3.Conformance

/-! Helpers for `Round3/Ledger.lean` (task E5). The ledger of a state is read here through small
    views: what a call's entry reads about its owner (`ownerView`), whether a task has a body
    (`hasBody`), and where an execution sits (`execPos`). `ledgerL` is the ledger written with these
    views; `Ledger.lean` shows it equals `ledger`. The invariants of reachable states it needs are
    bundled in `LInv`. -/

namespace Suimon.Round3.LedgerCore
open State

section Lists
variable {α β γ : Type}

theorem filterMap_congr' {l : List α} {f g : α → Option β} (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem flatMap_congr' {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem filterMap_eq_flatMap' {l : List α} {f : α → Option β} :
    l.filterMap f = l.flatMap fun x => (f x).toList := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [h, ih]

/-- Mapping keeps the filtered image when the functions agree on every member. -/
theorem filterMap_map_eq {l : List α} {g : α → γ} {F : α → Option β} {F' : γ → Option β}
    (h : ∀ x ∈ l, F' (g x) = F x) : (l.map g).filterMap F' = l.filterMap F := by
  rw [List.filterMap_map]
  exact filterMap_congr' h

theorem flatMap_map_eq {l : List α} {g : α → γ} {G : α → List β} {G' : γ → List β}
    (h : ∀ x ∈ l, G' (g x) = G x) : (l.map g).flatMap G' = l.flatMap G := by
  rw [List.flatMap_map]
  exact flatMap_congr' h

/-- The two ends of a list can be swapped up to order. -/
theorem swap_ends (X B Y : List β) : (X ++ (B ++ Y)).Perm (Y ++ (B ++ X)) :=
  ((List.Perm.append_left X List.perm_append_comm).trans (List.perm_append_comm_assoc X Y B)).trans
    (List.Perm.append_left Y List.perm_append_comm)

/-- Mapping a duplicate-free list where the functions agree on every member but `c`. -/
theorem flatMap_map_perm {l : List α} {g : α → γ} {G : α → List β} {G' : γ → List β} {c : α}
    (hnd : l.Nodup) (hc : c ∈ l) (h : ∀ x ∈ l, x ≠ c → G' (g x) = G x) :
    ((l.map g).flatMap G' ++ G c).Perm (l.flatMap G ++ G' (g c)) := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hc
  have hnd' : (c :: (A ++ B)).Nodup := List.perm_middle.nodup_iff.mp hnd
  have hcAB : c ∉ A ++ B := (List.nodup_cons.mp hnd').1
  have hA : (A.map g).flatMap G' = A.flatMap G := flatMap_map_eq fun x hx =>
    h x (List.mem_append_left _ hx) fun he => hcAB (he ▸ List.mem_append_left _ hx)
  have hB : (B.map g).flatMap G' = B.flatMap G := flatMap_map_eq fun x hx =>
    h x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
      fun he => hcAB (he ▸ List.mem_append_right _ hx)
  simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons, hA, hB,
    List.append_assoc]
  exact List.Perm.append_left _ (swap_ends _ _ _)

theorem filterMap_map_perm {l : List α} {g : α → γ} {F : α → Option β} {F' : γ → Option β} {c : α}
    (hnd : l.Nodup) (hc : c ∈ l) (h : ∀ x ∈ l, x ≠ c → F' (g x) = F x) :
    ((l.map g).filterMap F' ++ (F c).toList).Perm (l.filterMap F ++ (F' (g c)).toList) := by
  simp only [filterMap_eq_flatMap']
  exact flatMap_map_perm (G := fun x => (F x).toList) (G' := fun x => (F' x).toList) hnd hc
    fun x hx hne => by rw [h x hx hne]

/-- One member changes from no entry to the entry `f`. -/
theorem filterMap_map_perm_one {l : List α} {g : α → γ} {F : α → Option β} {F' : γ → Option β} {c : α}
    {f : β} (hnd : l.Nodup) (hc : c ∈ l) (h : ∀ x ∈ l, x ≠ c → F' (g x) = F x) (hold : F c = none)
    (hnew : F' (g c) = some f) : ((l.map g).filterMap F').Perm (l.filterMap F ++ [f]) := by
  have := filterMap_map_perm hnd hc h
  rw [hold, hnew] at this
  simpa using this

/-- One member's image grows by the entry `f`. -/
theorem flatMap_map_perm_one {l : List α} {g : α → γ} {G : α → List β} {G' : γ → List β} {c : α}
    {f : β} (hnd : l.Nodup) (hc : c ∈ l) (h : ∀ x ∈ l, x ≠ c → G' (g x) = G x)
    (hc' : (G' (g c)).Perm (G c ++ [f])) : ((l.map g).flatMap G').Perm (l.flatMap G ++ [f]) := by
  have h1 := flatMap_map_perm hnd hc h
  have h2 : (l.flatMap G ++ G' (g c)).Perm ((l.flatMap G ++ [f]) ++ G c) := by
    refine (List.Perm.append_left _ hc').trans ?_
    simp only [List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  exact (List.perm_append_right_iff (G c)).mp (h1.trans h2)

end Lists

/-! ### Invariants of reachable states that the ledger needs -/

/-- The Round 2 invariants the ledger proof reads, bundled for one reachable state. -/
structure LInv (p : Definition) (s : State) : Prop where
  wk : s.WellKeyed
  lim : Limit.Inv s
  names : ∀ e ∈ s.executions, (e.tasks.map (·.name)).Nodup
  own : Settle.Own p s
  act : Settle.Active p s
  keys : Calls.Keys s
  dinv : Delivery.Inv p s
  start : s = {} ∨ s.started = true

theorem LInv.of_reachable {p : Definition} {s : State} (valid : p.validate = .ok ()) (h : Reachable p s) :
    LInv p s := by
  obtain ⟨own, act, -, -⟩ := Settle.reachable h
  exact ⟨h.wellKeyed, Limit.reachable_inv h, Reachable.taskNames valid h, own, act, Calls.reachable_keys h,
    Delivery.Reachable.inv h, h.eq_empty_or_started⟩

/-- A list whose keys are distinct has no duplicates. -/
theorem nodup_of_map {α κ : Type} {f : α → κ} {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 a ha rfl, ih h.2⟩

section Inv
variable {p : Definition} {s : State}

theorem LInv.calls_nodup (h : LInv p s) : s.calls.Nodup := nodup_of_map h.wk.calls
theorem LInv.executions_nodup (h : LInv p s) : s.executions.Nodup := nodup_of_map h.wk.executions
theorem LInv.taskResults_nodup (h : LInv p s) : s.taskResults.Nodup := nodup_of_map h.wk.taskResults
theorem LInv.tasks_nodup (h : LInv p s) {e : Execution} (he : e ∈ s.executions) : e.tasks.Nodup :=
  nodup_of_map (h.names e he)

/-- A call of an invocation has the invocation's identity. -/
theorem LInv.callNone (h : LInv p s) {c : Call} (hc : c ∈ s.calls) (ht : c.task = none) :
    c.id = c.owner ∧ ∃ i ∈ s.invocations, i.id = c.owner := by
  obtain ⟨hid, i, hi, hio, -⟩ := h.own.callNone c hc ht
  exact ⟨hid, i, hi, hio⟩

/-- Two calls with the same owner and task are the same call. -/
theorem LInv.call_eq_of_owner (h : LInv p s) {c c' : Call} (hc : c ∈ s.calls) (hc' : c' ∈ s.calls)
    (howner : c.owner = c'.owner) (htask : c.task = c'.task) : c = c' := by
  apply h.wk.call_eq_of_id hc hc'
  cases ht : c.task with
  | none =>
    rw [(h.callNone hc ht).1, (h.callNone hc' (htask ▸ ht)).1, howner]
  | some name =>
    rw [h.lim.keys c hc name ht, h.lim.keys c' hc' name (htask ▸ ht), howner]

end Inv

/-! ### What the ledger reads -/

/-- What a call's ledger entry reads about its owner: its run, placement, and whether it failed. -/
def ownerView (s : State) (c : Call) : Option (Path × String × Bool) :=
  match c.task with
  | none => (s.invocation? c.owner).map fun i => (i.run, i.placement, i.status == .failed)
  | some name => (s.execution? c.owner).map fun e =>
      (e.run, e.placement, e.tasks.any fun t => t.name == name && t.status == .failed)

/-- The cause a call with status `st` records, given whether its owner failed. -/
def causeOf : CallStatus → Bool → Option Cause
  | .failed, _ => some .error
  | .lost, _ => some .lost
  | .cancelling, b | .cancelled, b => if b then some .timeout else none
  | _, _ => none

/-- The ledger entry of a call, from its status, its task and the view of its owner. -/
def viewEntry (st : CallStatus) (task : Option String) : Option (Path × String × Bool) → Option Failure
  | none => none
  | some (run, pl, b) => (causeOf st b).map fun cause => { run, placement := pl, task, cause }

/-- The ledger entry of a call. -/
def callL (s : State) (c : Call) : Option Failure := viewEntry c.status c.task (ownerView s c)

/-- The task `name` of execution `eid` has a call or a run. -/
def hasBody (s : State) (eid name : String) : Bool :=
  (s.call? (Key.task eid name)).isSome || s.runs.any fun r => r.owner == some eid && r.task == some name

/-- The ledger entry of a task whose input transform failed. -/
def taskInputL (s : State) (e : Execution) (t : TaskState) : Option Failure :=
  if t.status == .failed && !hasBody s e.id t.name then
    some { run := e.run, placement := e.placement, task := some t.name, cause := .transform }
  else none

/-- The ledger entry of a delivery. -/
def deliveryL (p : Definition) (s : State) (d : Delivery) : Option Failure := do
  guard (d.outcome == .failed)
  let w ← s.workflow? p d.run
  let c ← w.connections[d.connection]?
  pure { run := d.run, placement := c.target, cause := .transform }

/-- Where the execution `id` sits. -/
def execPos (s : State) (id : String) : Option (Path × String) :=
  (s.execution? id).map fun e => (e.run, e.placement)

/-- The ledger entry of a task result whose output transform failed. -/
def taskOutputL (s : State) (r : TaskResult) : Option Failure :=
  if r.output = .failed then
    (execPos s r.execution).map fun x => { run := x.1, placement := x.2, task := some r.task, cause := .transform }
  else none

/-- The entries of the calls. -/
def callPart (s : State) : List Failure := s.calls.filterMap (callL s)
/-- The entries of the deliveries. -/
def deliveryPart (p : Definition) (s : State) : List Failure := s.deliveries.filterMap (deliveryL p s)
/-- The entries of the tasks. -/
def inputPart (s : State) : List Failure := s.executions.flatMap fun e => e.tasks.filterMap (taskInputL s e)
/-- The entries of the task results. -/
def outputPart (s : State) : List Failure := s.taskResults.filterMap (taskOutputL s)

/-- The ledger, read through the views above. -/
def ledgerL (p : Definition) (s : State) : List Failure :=
  callPart s ++ deliveryPart p s ++ inputPart s ++ outputPart s

/-! ### Calls -/

section Calls
variable {s t : State}

theorem causeOf_live {st : CallStatus} (h : st = .running ∨ st = .fetching ∨ st = .returned) (b : Bool) :
    causeOf st b = none := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem callL_live {c : Call} (h : c.status = .running ∨ c.status = .fetching ∨ c.status = .returned) :
    callL s c = none := by
  unfold callL
  cases ownerView s c with
  | none => rfl
  | some v => simp [viewEntry, causeOf_live h]

theorem callL_congr {c c' : Call} (hst : c'.status = c.status) (htask : c'.task = c.task)
    (hv : ownerView t c' = ownerView s c) : callL t c' = callL s c := by
  unfold callL
  rw [hst, htask, hv]

theorem ownerView_congr (hi : t.invocations = s.invocations) (he : t.executions = s.executions) (c : Call) :
    ownerView t c = ownerView s c := by
  unfold ownerView State.invocation? State.execution?
  rw [hi, he]

theorem ownerView_of_owner {c c' : Call} (ho : c'.owner = c.owner) (ht : c'.task = c.task) :
    ownerView s c' = ownerView s c := by
  unfold ownerView
  rw [ho, ht]

theorem ownerView_of_invocation {c : Call} {i : Invocation} (ht : c.task = none)
    (hi : s.invocation? c.owner = some i) : ownerView s c = some (i.run, i.placement, i.status == .failed) := by
  unfold ownerView
  rw [ht]
  simp [hi]

theorem ownerView_of_execution {c : Call} {e : Execution} {name : String} (ht : c.task = some name)
    (he : s.execution? c.owner = some e) :
    ownerView s c = some (e.run, e.placement, e.tasks.any fun t => t.name == name && t.status == .failed) := by
  unfold ownerView
  rw [ht]
  simp [he]

theorem ownerView_setInvocation_of_ne {i : Invocation} {c : Call} (h : c.task = none → c.owner ≠ i.id) :
    ownerView (s.setInvocation i) c = ownerView s c := by
  unfold ownerView
  cases ht : c.task with
  | none =>
    simp only
    rw [invocation?_setInvocation, ite_eq_right fun he => h ht he.symm]
  | some name => rfl

theorem ownerView_setInvocation_self (wk : s.WellKeyed) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hid : i'.id = i.id) {c : Call} (ht : c.task = none) (ho : c.owner = i.id) :
    ownerView (s.setInvocation i') c = some (i'.run, i'.placement, i'.status == .failed) := by
  unfold ownerView
  rw [ht]
  simp only
  rw [invocation?_setInvocation, ite_eq_left (hid.trans ho.symm), ho, wk.invocation?_of_mem hi]
  rfl

theorem ownerView_setExecution_of_ne {e : Execution} {c : Call} (h : c.task ≠ none → c.owner ≠ e.id) :
    ownerView (s.setExecution e) c = ownerView s c := by
  unfold ownerView
  cases ht : c.task with
  | none => rfl
  | some name =>
    simp only
    rw [execution?_setExecution, ite_eq_right fun he => h (by simp [ht]) he.symm]

theorem ownerView_setExecution_self (wk : s.WellKeyed) {e e' : Execution} (he : e ∈ s.executions)
    (hid : e'.id = e.id) {c : Call} {name : String} (ht : c.task = some name) (ho : c.owner = e.id) :
    ownerView (s.setExecution e') c =
      some (e'.run, e'.placement, e'.tasks.any fun t => t.name == name && t.status == .failed) := by
  unfold ownerView
  rw [ht]
  simp only
  rw [execution?_setExecution, ite_eq_left (hid.trans ho.symm), ho, wk.execution?_of_mem he]
  rfl

/-- A stop leaves no task failed that was not, and fails none. -/
theorem stopTask_failed (name : String) (x : TaskState) :
    ((Limit.stopTask x).name == name && (Limit.stopTask x).status == .failed) =
      (x.name == name && x.status == .failed) := by
  unfold Limit.stopTask
  split
  · rename_i h
    rcases x with ⟨n, i, st⟩
    cases st <;> first | rfl | simp_all
  · rfl

theorem ownerView_stop (c : Call) : ownerView s.stop c = ownerView s c := by
  unfold ownerView
  cases ht : c.task with
  | none => rfl
  | some name =>
    simp only
    rw [execution?_stop]
    cases s.execution? c.owner with
    | none => rfl
    | some e =>
      simp only [Option.map_some, stopExecution_run, stopExecution_placement, Option.some.injEq,
        Prod.mk.injEq, true_and]
      rw [Limit.stopExecution_tasks, List.any_map]
      exact List.any_congr rfl fun x => stopTask_failed name x

theorem ownerView_append {I : List Invocation} {E : List Execution} (hi : t.invocations = s.invocations ++ I)
    (he : t.executions = s.executions ++ E) {c : Call} {v : Path × String × Bool}
    (h : ownerView s c = some v) : ownerView t c = some v := by
  unfold ownerView at h ⊢
  cases ht : c.task with
  | none =>
    rw [ht] at h
    simp only at h ⊢
    obtain ⟨i, hi', rfl⟩ := Option.map_eq_some_iff.mp h
    unfold State.invocation? at hi' ⊢
    rw [hi, List.find?_append, hi']
    rfl
  | some name =>
    rw [ht] at h
    simp only at h ⊢
    obtain ⟨e, he', rfl⟩ := Option.map_eq_some_iff.mp h
    unfold State.execution? at he' ⊢
    rw [he, List.find?_append, he']
    rfl

end Calls

/-! ### Task bodies, deliveries and task results -/

section Others
variable {p : Definition} {s t : State}

theorem find?_key_isSome {α κ : Type} [BEq κ] [LawfulBEq κ] (l : List α) (f : α → κ) (k : κ) :
    (l.find? fun x => f x == k).isSome = (l.map f).contains k := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.find?_cons, List.map_cons, List.contains_cons]
    by_cases h : f a = k
    · have h1 : (f a == k) = true := by simpa using h
      have h2 : (k == f a) = true := by simpa using h.symm
      simp only [h1, h2]
      rfl
    · have h1 : (f a == k) = false := by simpa using h
      have h2 : (k == f a) = false := by simpa using fun e => h e.symm
      simp only [h1, h2, Bool.false_or]
      exact ih

theorem call?_isSome_eq (h : t.calls.map (·.id) = s.calls.map (·.id)) (id : String) :
    (t.call? id).isSome = (s.call? id).isSome := by
  unfold State.call?
  rw [find?_key_isSome, find?_key_isSome, h]

theorem hasBody_congr (hc : t.calls.map (·.id) = s.calls.map (·.id))
    (hr : t.runs.map (fun r => (r.owner, r.task)) = s.runs.map (fun r => (r.owner, r.task))) (eid name : String) :
    hasBody t eid name = hasBody s eid name := by
  unfold hasBody
  rw [call?_isSome_eq hc]
  have e : ∀ u : State, (u.runs.any fun r => r.owner == some eid && r.task == some name) =
      (u.runs.map (fun r => (r.owner, r.task))).any (fun x => x.1 == some eid && x.2 == some name) := by
    intro u
    rw [List.any_map]
    rfl
  rw [e t, e s, hr]

theorem hasBody_append {C : List Call} {R : List Run} (hc : t.calls = s.calls ++ C) (hr : t.runs = s.runs ++ R)
    {eid name : String} (hC : ∀ c ∈ C, c.id ≠ Key.task eid name)
    (hR : ∀ r ∈ R, r.owner = some eid → r.task ≠ some name) : hasBody t eid name = hasBody s eid name := by
  unfold hasBody State.call?
  rw [hc, hr, List.find?_append, List.any_append]
  have h1 : (C.find? fun x => x.id == Key.task eid name) = none :=
    List.find?_eq_none.mpr fun c hc' => by simpa using hC c hc'
  have h2 : (R.any fun r => r.owner == some eid && r.task == some name) = false := by
    rw [List.any_eq_false]
    intro r hr'
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    exact hR r hr'
  rw [h1, h2]
  cases (s.calls.find? fun x => x.id == Key.task eid name) <;> simp

theorem hasBody_of_call {c : Call} (hc : c ∈ s.calls) {eid name : String} (hid : c.id = Key.task eid name) :
    hasBody s eid name = true := by
  unfold hasBody
  have : (s.call? (Key.task eid name)).isSome = true := by
    unfold State.call?
    rw [find?_key_isSome]
    simp only [List.contains_iff_mem, List.mem_map]
    exact ⟨c, hc, hid⟩
  rw [this]
  rfl

theorem hasBody_of_run {r : Run} (hr : r ∈ s.runs) {eid name : String} (ho : r.owner = some eid)
    (ht : r.task = some name) : hasBody s eid name = true := by
  unfold hasBody
  have : (s.runs.any fun r => r.owner == some eid && r.task == some name) = true :=
    List.any_eq_true.mpr ⟨r, hr, by simp [ho, ht]⟩
  rw [this]
  simp

theorem hasBody_eq_false {eid name : String} (hc : ∀ c ∈ s.calls, c.id ≠ Key.task eid name)
    (hr : ∀ r ∈ s.runs, r.owner = some eid → r.task ≠ some name) : hasBody s eid name = false := by
  have := hasBody_append (s := { s with calls := [], runs := [] }) (t := s) (C := s.calls) (R := s.runs)
    rfl rfl hc hr
  rw [this]
  rfl

theorem taskInputL_congr {e e' : Execution} {x x' : TaskState} (hid : e'.id = e.id) (hrun : e'.run = e.run)
    (hpl : e'.placement = e.placement) (hname : x'.name = x.name)
    (hst : (x'.status == .failed) = (x.status == .failed)) (hb : hasBody t e.id x.name = hasBody s e.id x.name) :
    taskInputL t e' x' = taskInputL s e x := by
  unfold taskInputL
  rw [hid, hrun, hpl, hname, hst, hb]

theorem taskInputL_of_ne {e : Execution} {x : TaskState} (h : x.status ≠ .failed) : taskInputL s e x = none := by
  unfold taskInputL
  simp [h]

theorem taskInputL_of_hasBody {e : Execution} {x : TaskState} (h : hasBody s e.id x.name = true) :
    taskInputL s e x = none := by
  unfold taskInputL
  simp [h]

theorem stopTask_status_failed (x : TaskState) :
    ((Limit.stopTask x).status == .failed) = (x.status == .failed) := by
  unfold Limit.stopTask
  split
  · rename_i h
    rcases x with ⟨n, i, st⟩
    cases st <;> first | rfl | simp_all
  · rfl

theorem deliveryL_congr {d : Delivery} (h : t.workflow? p d.run = s.workflow? p d.run) :
    deliveryL p t d = deliveryL p s d := by
  unfold deliveryL
  rw [h]

theorem deliveryL_of_ne {d : Delivery} (h : d.outcome ≠ .failed) : deliveryL p s d = none := by
  unfold deliveryL
  have : (d.outcome == .failed) = false := by simpa using h
  rw [this]
  rfl

theorem execPos_congr (he : t.executions = s.executions) (id : String) : execPos t id = execPos s id := by
  unfold execPos State.execution?
  rw [he]

theorem execPos_setExecution (wk : s.WellKeyed) {e e' : Execution} (he : e ∈ s.executions) (hid : e'.id = e.id)
    (hrun : e'.run = e.run) (hpl : e'.placement = e.placement) (id : String) :
    execPos (s.setExecution e') id = execPos s id := by
  unfold execPos
  rw [execution?_setExecution]
  split
  · rename_i h
    rw [← h, hid, wk.execution?_of_mem he]
    simp [hrun, hpl]
  · rfl

theorem execPos_stop (id : String) : execPos s.stop id = execPos s id := by
  unfold execPos
  rw [execution?_stop]
  cases s.execution? id <;> rfl

theorem execPos_append {E : List Execution} (he : t.executions = s.executions ++ E) {id : String}
    {v : Path × String} (h : execPos s id = some v) : execPos t id = some v := by
  unfold execPos at h ⊢
  obtain ⟨e, he', rfl⟩ := Option.map_eq_some_iff.mp h
  unfold State.execution? at he' ⊢
  rw [he, List.find?_append, he']
  rfl

theorem taskOutputL_congr {r r' : TaskResult} (ho : r'.output = r.output) (ht : r'.task = r.task)
    (he : execPos t r'.execution = execPos s r.execution) : taskOutputL t r' = taskOutputL s r := by
  unfold taskOutputL
  rw [ho, ht, he]

theorem taskOutputL_of_ne {r : TaskResult} (h : r.output ≠ .failed) : taskOutputL s r = none := by
  unfold taskOutputL
  simp [h]

end Others

/-! ### A stop records nothing -/

/-- No running or fetching call has a failed owner, so a stop records no timeout. -/
def StopSafe (s : State) : Prop :=
  ∀ c ∈ s.calls, (c.status = .running ∨ c.status = .fetching) → ∀ v, ownerView s c = some v → v.2.2 = false

section Stop
variable {p : Definition} {s : State}

theorem callPart_stop (h : StopSafe s) : callPart s.stop = callPart s := by
  unfold callPart
  rw [stop_calls]
  apply filterMap_map_eq
  intro x hx
  have hv : ownerView s.stop (stopCall x) = ownerView s x := by
    rw [ownerView_stop]
    exact ownerView_of_owner stopCall_owner stopCall_task
  unfold callL
  rw [hv, stopCall_task, stopCall_status]
  split
  · rename_i hrun
    have hl : causeOf x.status false = none := causeOf_live (by rcases hrun with h1 | h1 <;> simp [h1]) false
    cases hov : ownerView s x with
    | none => rfl
    | some v =>
      have hb := h x hx hrun v hov
      obtain ⟨run, pl, b⟩ := v
      simp only at hb
      subst hb
      simp only [viewEntry]
      rw [hl]
      rfl
  · rfl

theorem deliveryPart_stop : deliveryPart p s.stop = deliveryPart p s := rfl

theorem inputPart_stop : inputPart s.stop = inputPart s := by
  unfold inputPart
  rw [stop_executions]
  apply flatMap_map_eq
  intro e _
  rw [Limit.stopExecution_tasks]
  apply filterMap_map_eq
  intro x _
  exact taskInputL_congr rfl rfl rfl Limit.stopTask_name (stopTask_status_failed x)
    (hasBody_congr (t := s.stop) (s := s) (by simp) rfl _ _)

theorem outputPart_stop : outputPart s.stop = outputPart s := by
  unfold outputPart
  apply filterMap_congr'
  intro r _
  exact taskOutputL_congr rfl rfl (execPos_stop _)

theorem ledgerL_stop (h : StopSafe s) : ledgerL p s.stop = ledgerL p s := by
  unfold ledgerL
  rw [callPart_stop h, deliveryPart_stop, inputPart_stop, outputPart_stop]

theorem ledgerL_failures {fs : List Failure} : ledgerL p { s with failures := fs } = ledgerL p s := rfl

theorem StopSafe.failures (h : StopSafe s) {fs : List Failure} : StopSafe { s with failures := fs } :=
  fun c hc hrun v hv => h c hc hrun v hv

theorem ledgerL_fail (h : StopSafe s) {f : Failure} {policy : Policy} :
    ledgerL p (s.fail f policy) = ledgerL p s := by
  cases policy
  · rw [fail_stop, ledgerL_stop h.failures, ledgerL_failures]
  · rw [fail_continue]
    rfl

end Stop

end Suimon.Round3.LedgerCore
