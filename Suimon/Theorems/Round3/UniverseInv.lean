import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## Invariants behind `universe_covers` (task D2)

Facts about conforming executions that do not mention the universe: every task result has an index
below the length of its task call's script, or 0 (`conforming_taskIndex`); every result identity has
the shape the universe predicts, built from a trigger available to its placement (`conforming_resultShape`);
and every workflow a call or a task names exists in a valid program. -/

namespace UniverseProof

section UniverseInv
variable {p : Program} {env : Env} {s t : State} {op : Op}

/-! ### Lists -/

/-- A weighted sum over a list without duplicates is at most the sum over any list containing it. -/
theorem sum_map_le_of_nodup {α : Type} [BEq α] [LawfulBEq α] (f : α → Nat) :
    ∀ {l l' : List α}, l.Nodup → (∀ x ∈ l, x ∈ l') → (l.map f).sum ≤ (l'.map f).sum
  | [], _, _, _ => by simp
  | a :: l, l', hn, hsub => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ l' := hsub a List.mem_cons_self
    rw [List.Perm.sum_nat ((List.perm_cons_erase ha).map f)]
    simp only [List.map_cons, List.sum_cons]
    have hsub' : ∀ x ∈ l, x ∈ l'.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hn.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem a hx))
    have := sum_map_le_of_nodup f hn.2 hsub'
    omega

/-! ### Task result indices -/

/-- A task result's index is below the number of elements its task call's script yields, or is 0. -/
def TaskIndexOk (B : Behavior) (r : TaskResult) : Prop :=
  r.index < max 1 (B.script (Key.task r.execution r.task)).yields.length

theorem zero_lt_max_one (n : Nat) : 0 < max 1 n := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem failCall_taskResults {c : Call} {status : CallStatus} {cause : Cause}
    (h : s.failCall c status cause = .ok t) : t.taskResults = s.taskResults := by
  obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
  simp [(settleOwner_update hso).taskResults]

/-- Every step keeps the task result indices below the scripts: a task call accepts index 0 when it
    returns and its element count when it yields, which conforms only below the script's length, and a
    task run returns index 0. -/
theorem step_taskIndex (reach : Reachable p s) (hconf : Conforms env s op) (hs : step p s op = .ok t)
    (ih : ∀ r ∈ s.taskResults, TaskIndexOk env.behavior r) : ∀ r ∈ t.taskResults, TaskIndexOk env.behavior r := by
  intro x hx
  have same : t.taskResults = s.taskResults → TaskIndexOk env.behavior x := fun h => ih x (h ▸ hx)
  have zero : x.index = 0 → TaskIndexOk env.behavior x := fun h => by
    unfold TaskIndexOk; rw [h]; exact zero_lt_max_one _
  -- A value accepted from a call at `index`.
  have accepted : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
      s.accept c index value arm = .ok s' → t.taskResults = s'.taskResults →
      (∀ name, c.task = some name → index < max 1 (env.behavior.script (Key.task c.owner name)).yields.length) →
      TaskIndexOk env.behavior x := by
    intro c index value arm s' hacc ht hidx
    rw [ht] at hx
    rcases State.accept_eq_ok.mp hacc with ⟨-, _, -, -, rfl⟩ | ⟨name, hn, -, rfl⟩
    · exact ih x hx
    · rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih x hx
      · exact hidx name hn
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact accepted hacc (by rw [(settleOwner_update hso).taskResults, setCall_taskResults])
      fun _ _ => zero_lt_max_one _
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact accepted hacc (by rw [setInvocation_taskResults, setCall_taskResults]) fun _ _ => zero_lt_max_one _
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    refine accepted hacc (by rw [setCall_taskResults]) fun name hn => ?_
    obtain ⟨c', hc', hv⟩ := hconf
    rw [hc] at hc'
    cases hc'
    obtain ⟨hmem, hid⟩ := call?_eq_some hc
    obtain ⟨hkey, -⟩ := (Settle.reachable reach).1.callTask c hmem name hn
    rw [← hkey, hid]
    have := (List.getElem?_eq_some_iff.mp hv).1
    exact Nat.lt_of_lt_of_le this (Nat.le_max_right _ _)
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(settleOwner_update hso).taskResults, setCall_taskResults])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact same (failCall_taskResults h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact same (failCall_taskResults h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact same (failCall_taskResults h)
    · exact same (by rw [(cancelOwner_update h).taskResults, setCall_taskResults])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact same (by rw [(cancelOwner_update h).taskResults, setCall_taskResults])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same rfl
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, r, -, -, -, -, hr, -, h⟩ := Step.taskOutput_inv hs
    have hr' := List.mem_of_find?_eq_some hr
    have hkey := List.find?_some hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hkey
    have hx' : x ∈ (s.setTaskResult { r with output := .value value }).taskResults := by
      rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact hx
    rcases mem_setTaskResult_taskResults hx' with rfl | hx'
    · exact ih r hr'
    · exact ih x hx'
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, hr, -, rfl⟩ := Step.taskOutputFailed_inv hs
    have hr' := List.mem_of_find?_eq_some hr
    rw [fail_taskResults] at hx
    rcases mem_setTaskResult_taskResults hx with rfl | hx
    · exact ih r hr'
    · exact ih x hx
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same (by simp)
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, h3, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨name, e, _, htask, he, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same (by simp)
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ih x (by simpa using hx)
        · exact zero rfl
      all_goals exact same (by simp)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

theorem conforming_taskIndex {tr : List Op} (h : Conforming p env tr s) :
    ∀ r ∈ s.taskResults, TaskIndexOk env.behavior r := by
  induction h with
  | nil => intro r hr; cases hr
  | snoc hex hconf hs _ ih => exact step_taskIndex hex.reachable hconf hs ih

/-! ### Result identities -/

/-- The trigger `trig` is available to the placement `name` of the run at `path`, whose workflow is
    `w`: no trigger for an entry or a placement without input connections, or a result delivered on one
    of its input connections. Deliveries are never withdrawn, so availability is kept. -/
def TrigAvail (s : State) (path : Path) (w : Workflow) (name : String) (trig : Option ResultId) : Prop :=
  (trig = none ∧ (w.isEntry name = true ∨ w.incoming name = [])) ∨
  (∃ src, trig = some src ∧ w.isEntry name = false ∧ ∃ d ∈ s.deliveries, d.run = path ∧ d.source = src ∧
    ∃ c, w.connections[d.connection]? = some c ∧ c.target = name)

theorem TrigAvail.mono {s' : State} {path : Path} {w : Workflow} {name : String} {trig : Option ResultId}
    (h : TrigAvail s path w name trig) (hd : ∀ d ∈ s.deliveries, d ∈ s'.deliveries) :
    TrigAvail s' path w name trig := by
  rcases h with h | ⟨src, h1, h2, d, hd', h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨src, h1, h2, d, hd d hd', h3⟩

/-- The identity of a result that the invocation `id` of a placement with control `ctrl` produces:
    an element of a function call, the result of a judge, of a sub-workflow call, the list of an
    execution, or a transformed element of a task in the output. -/
def IdShape (B : Behavior) (ctrl : Control) (id : String) (rid : ResultId) : Prop :=
  match ctrl with
  | .call (.function _) => ∃ idx, idx < max 1 (B.script id).yields.length ∧ rid = Key.callResult id idx
  | .branch .. => rid = Key.callResult id 0
  | .call (.workflow ..) => rid = Key.returned id
  | .concurrency cc => rid = Key.list id ∨ ∃ spec ∈ cc.tasks, ∃ idx,
      idx < max 1 (B.script (Key.task id spec.name)).yields.length ∧ rid = Key.taskOutput id spec.name idx
  | .waitStream _ | .merge _ => False

/-- A result's identity comes from an invocation of its placement with an available trigger, or is the
    aggregate of a waitStream or Merge. -/
def ResultShape (p : Program) (B : Behavior) (s : State) (r : Result) : Prop :=
  ∃ w pl, s.workflow? p r.run = some w ∧ w.placement? r.placement = some pl ∧
    ((∃ trig, TrigAvail s r.run w r.placement trig ∧
        IdShape B pl.control (Key.invocation r.run r.placement trig) r.id) ∨
     ((∃ e, pl.control = .waitStream e ∨ pl.control = .merge e) ∧ r.id = Key.aggregate r.run r.placement))

theorem ResultShape.mono {B : Behavior} {r : Result} (h : ResultShape p B s r) (kept : Routing.RunsKept s t)
    (hd : ∀ d ∈ s.deliveries, d ∈ t.deliveries) : ResultShape p B t r := by
  obtain ⟨w, pl, hw, hpl, h⟩ := h
  refine ⟨w, pl, kept.workflow? hw, hpl, ?_⟩
  rcases h with ⟨trig, ht, hid⟩ | h
  · exact Or.inl ⟨trig, ht.mono hd, hid⟩
  · exact Or.inr h

/-- What each input shape asks of a trigger gives an available trigger. -/
theorem trigAvail_of_shape {path : Path} {w : Workflow} {name : String} {trig : Option ResultId}
    {sh : Workflow.Shape} (hsh : w.shape? p name = some sh)
    (h : match sh with
      | .none | .entry => trig = none
      | .single j _ | .stream j _ =>
        ∃ src, trig = some src ∧ ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = j ∧ d.source = src
      | .merge _ => False) :
    TrigAvail s path w name trig := by
  obtain ⟨_, -, hcase⟩ := Delivery.shape?_eq hsh
  -- Past a Merge, the shape decides whether the placement is the entry.
  have hentry : ∀ j c, (sh = .single j c ∨ sh = .stream j c) →
      w.isEntry name = false ∧ w.connections[j]? = some c ∧ c.target = name := by
    rintro j c (rfl | rfl)
    · obtain ⟨-, hcj, htgt, -⟩ := Delivery.shape?_single hsh
      rcases hcase with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨he, -⟩⟩
      · cases h
      · cases h
      · cases h
      · exact ⟨he, hcj, htgt⟩
    · obtain ⟨-, hcj, htgt, -⟩ := Delivery.shape?_stream hsh
      rcases hcase with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨he, -⟩⟩
      · cases h
      · cases h
      · cases h
      · exact ⟨he, hcj, htgt⟩
  have delivered : ∀ j c, (sh = .single j c ∨ sh = .stream j c) →
      (∃ src, trig = some src ∧ ∃ d ∈ s.deliveries, d.run = path ∧ d.connection = j ∧ d.source = src) →
      TrigAvail s path w name trig := by
    rintro j c hsh' ⟨src, htr, d, hd, hdrun, hdconn, hdsrc⟩
    obtain ⟨he, hcj, htgt⟩ := hentry j c hsh'
    exact Or.inr ⟨src, htr, he, d, hd, hdrun, hdsrc, c, by rw [hdconn]; exact hcj, htgt⟩
  cases sh with
  | none =>
    refine Or.inl ⟨h, Or.inr ?_⟩
    rcases hcase with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, hin, -⟩ | ⟨-, j, c, -, ⟨-, h⟩ | ⟨-, h⟩⟩⟩
    · cases h
    · cases h
    · rw [← Delivery.inputs_map_snd, hin]; rfl
    · cases h
    · cases h
  | entry =>
    refine Or.inl ⟨h, Or.inl ?_⟩
    rcases hcase with ⟨-, h⟩ | ⟨-, ⟨he, -⟩ | ⟨-, -, h⟩ | ⟨-, j, c, -, ⟨-, h⟩ | ⟨-, h⟩⟩⟩
    · cases h
    · exact he
    · cases h
    · cases h
    · cases h
  | single j c => exact delivered j c (Or.inl rfl) h
  | stream j c => exact delivered j c (Or.inr rfl) h
  | merge cs => exact h.elim

/-- A placed invocation took an available trigger. -/
theorem trigAvail_of_placed {i : Invocation} (h : Delivery.InvocationPlaced p s i) :
    i.id = Key.invocation i.run i.placement i.trigger ∧ ∃ w pl, s.workflow? p i.run = some w ∧
      w.placement? i.placement = some pl ∧ Delivery.Invocable pl.control ∧
      TrigAvail s i.run w i.placement i.trigger := by
  obtain ⟨hid, w, pl, sh, hw, hpl, hinv, hsh, htrig, -⟩ := h
  refine ⟨hid, w, pl, hw, hpl, hinv, trigAvail_of_shape hsh ?_⟩
  cases sh with
  | none => exact htrig
  | entry => exact htrig
  | single j c =>
    obtain ⟨src, inp, hres, htr⟩ := htrig
    obtain ⟨d, hd, hdrun, hdconn, hdsrc, -⟩ := Routing.resolveSingle_value hres
    exact ⟨src, htr, d, hd, hdrun, hdconn, hdsrc⟩
  | stream j c =>
    obtain ⟨src, d, htr, hd, -⟩ := htrig
    obtain ⟨hdm, hdrun, hdconn, hdsrc⟩ := delivery?_eq_some hd
    exact ⟨src, htr, d, hdm, hdrun, hdconn, hdsrc⟩
  | merge cs => exact htrig

/-- The trigger `invoke` checks is available. -/
theorem trigAvail_of_input {r : Run} {w : Workflow} {name : String} {trig : Option ResultId} {input : Option Value}
    (h : Step.invocationInput p s r w name trig = .ok input) : TrigAvail s r.path w name trig := by
  rcases Step.invocationInput_inv h with ⟨hsh, htr, -⟩ | ⟨hsh, htr, -⟩ |
      ⟨j, c, src, hsh, htr, hres⟩ | ⟨j, c, src, d, hsh, htr, hd, -⟩
  · exact trigAvail_of_shape hsh htr
  · exact trigAvail_of_shape hsh htr
  · obtain ⟨d, hd, hdrun, hdconn, hdsrc, -⟩ := Routing.resolveSingle_value hres
    exact trigAvail_of_shape hsh ⟨src, htr, d, hd, hdrun, hdconn, hdsrc⟩
  · obtain ⟨hdm, hdrun, hdconn, hdsrc⟩ := delivery?_eq_some hd
    exact trigAvail_of_shape hsh ⟨src, htr, d, hdm, hdrun, hdconn, hdsrc⟩

/-- A result accepted from the call of an invocation: at index 0, or, for a Stream function, at an
    index below the script's length. -/
theorem resultShape_call (reach : Reachable p s) {B : Behavior} {c : Call} {i : Invocation} {idx : Nat}
    (hc : c ∈ s.calls) (htask : c.task = none) (hi : s.invocation? c.owner = some i)
    (hidx : ∀ f, c.target = .function f → c.stream = true → idx < (B.script c.id).yields.length)
    (hidx0 : c.stream = false → idx = 0)
    (kept : Routing.RunsKept s t) (hd : ∀ d ∈ s.deliveries, d ∈ t.deliveries) (arm : Option String) (value : Value) :
    ResultShape p B t
      { id := Key.callResult c.id idx, run := i.run, placement := i.placement, producer := c.id, arm, value } := by
  have inv := Delivery.Reachable.inv reach
  obtain ⟨hmem, hio⟩ := invocation?_eq_some hi
  rcases inv.own.calls c hc with ⟨-, hco, i', hi', hi'o, w, pl, hw, hpl, hctrl⟩ | ⟨name, hname, -⟩
  · obtain rfl : i = i' := inv.wk.invocation_eq_of_id hmem hi' (hio.trans hi'o.symm)
    obtain ⟨hid, w', pl', hw', hpl', -, htrig⟩ := trigAvail_of_placed (inv.own.invocations i hmem)
    rw [hw] at hw'
    cases hw'
    rw [hpl] at hpl'
    cases hpl'
    refine ⟨w, pl, kept.workflow? hw, hpl, Or.inl ⟨i.trigger, htrig.mono hd, ?_⟩⟩
    have hcid : c.id = Key.invocation i.run i.placement i.trigger := by rw [hco, ← hio, hid]
    rcases hctrl with ⟨f, decl, hf, -, htarget, -⟩ | ⟨j, arms, hb, -, hstream⟩
    · rw [hf]
      refine ⟨idx, ?_, by simp only [hcid]⟩
      cases hs : c.stream
      · rw [hidx0 hs]; exact zero_lt_max_one _
      · rw [← hcid]; exact Nat.lt_of_lt_of_le (hidx f htarget hs) (Nat.le_max_right _ _)
    · rw [hb]
      show Key.callResult c.id idx = Key.callResult (Key.invocation i.run i.placement i.trigger) 0
      rw [hcid, hidx0 hstream]
  · rw [htask] at hname; cases hname

theorem new_of_append {x r : Result} (hr : r ∈ t.results) (hnew : r ∉ s.results)
    (ht : t.results = s.results ++ [x]) : r = x := by
  rw [ht, List.mem_append, List.mem_singleton] at hr
  exact hr.resolve_left hnew

/-- An execution's results: its list and the transformed elements of its tasks in the output. -/
theorem resultShape_execution (reach : Reachable p s) {B : Behavior} {e : Execution} {cc : Concurrency}
    (he : e ∈ s.executions) (hcc : s.concurrencyOf p e = .ok cc) {rid : ResultId}
    (hrid : ∀ id, id = e.id → IdShape B (.concurrency cc) id rid)
    (kept : Routing.RunsKept s t) (hd : ∀ d ∈ s.deliveries, d ∈ t.deliveries) (producer : String) (value : Value) :
    ResultShape p B t { id := rid, run := e.run, placement := e.placement, producer, value } := by
  have inv := Delivery.Reachable.inv reach
  obtain ⟨i, hi, hie, hir, hip, -⟩ := inv.own.executions e he
  obtain ⟨hid, w, pl, hw, hpl, -, htrig⟩ := trigAvail_of_placed (inv.own.invocations i hi)
  obtain ⟨pl', hpl', hctrl⟩ := State.concurrencyOf_eq_ok.mp hcc
  obtain ⟨w', hw', hpl''⟩ := State.placementOf_eq_ok.mp hpl'
  rw [hir] at hw htrig hid
  rw [hip] at hpl htrig hid
  rw [hw] at hw'
  cases hw'
  rw [hpl] at hpl''
  cases hpl''
  refine ⟨w, pl, kept.workflow? hw, hpl, Or.inl ⟨i.trigger, htrig.mono hd, ?_⟩⟩
  rw [hctrl]
  exact hrid _ (hid.symm.trans hie)


/-- Every step keeps the shapes of result identities. A new result comes from a call of an invocation,
    an execution, a closing sub-workflow run or a settling waitStream or Merge; an invocation's
    identity names its run, placement and trigger, and it took an available trigger. -/
theorem step_resultShape (reach : Reachable p s) (tidx : ∀ r ∈ s.taskResults, TaskIndexOk env.behavior r)
    (hconf : Conforms env s op) (hs : step p s op = .ok t)
    (ih : ∀ r ∈ s.results, ResultShape p env.behavior s r) : ∀ r ∈ t.results, ResultShape p env.behavior t r := by
  have kept := Routing.step_runsKept hs (Routing.runs_nil_or_started reach)
  have g := step_grows hs
  have hd : ∀ d ∈ s.deliveries, d ∈ t.deliveries := fun d hd => g.mem_deliveries hd
  intro r hr
  by_cases hold : r ∈ s.results
  · exact (ih r hold).mono kept hd
  have hp := step_producer hs hr hold
  cases op
  case returned id value =>
    obtain ⟨-, -, c, f, s', hc, hstream, -, -, hacc, hso⟩ := Step.returned_inv hs
    have ht : t.results = s'.results := by rw [(settleOwner_update hso).results, setCall_results]
    rcases State.accept_eq_ok.mp hacc with ⟨htask, i, hi, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · rw [new_of_append hr hold ht]
      exact resultShape_call reach (call?_eq_some hc).1 htask hi (fun _ _ h => by rw [hstream] at h; cases h)
        (fun _ => rfl) kept hd _ _
    · exact (hold (by rw [ht] at hr; exact hr)).elim
  case judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, -, htarget, htask, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    rcases State.accept_eq_ok.mp hacc with ⟨-, i', hi', -, rfl⟩ | ⟨_, h, -, -⟩
    · rw [new_of_append hr hold (by rw [setInvocation_results, setCall_results])]
      exact resultShape_call reach (call?_eq_some hc).1 htask hi' (fun f h => by rw [htarget] at h; cases h)
        (fun _ => rfl) kept hd _ _
    · rw [htask] at h; cases h
  case yielded id value =>
    obtain ⟨-, -, c, s', hc, hstream, -, hacc, rfl⟩ := Step.yielded_inv hs
    rcases State.accept_eq_ok.mp hacc with ⟨htask, i, hi, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · rw [new_of_append hr hold (by rw [setCall_results])]
      refine resultShape_call reach (call?_eq_some hc).1 htask hi (fun _ _ _ => ?_)
        (fun h => by rw [hstream] at h; cases h) kept hd _ _
      obtain ⟨c', hc', hv⟩ := hconf
      rw [hc] at hc'
      cases hc'
      rw [(call?_eq_some hc).2]
      exact (List.getElem?_eq_some_iff.mp hv).1
    · exact (hold (by simpa using hr)).elim
  case taskOutput eid name index value =>
    obtain ⟨-, -, e, cc, spec, r₀, he, hcc, hspec, -, hr₀, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · rw [new_of_append hr hold rfl]
      obtain ⟨hem, heid⟩ := execution?_eq_some he
      obtain ⟨cc', hcc', hfind⟩ := State.taskSpec_eq_ok.mp hspec
      obtain rfl : cc = cc' := Settle.concurrencyOf_det hcc hcc'
      have hname : spec.name = name := by simpa using List.find?_some hfind
      have hkey := List.find?_some hr₀
      simp only [Bool.and_eq_true, beq_iff_eq] at hkey
      obtain ⟨⟨hkx, hkt⟩, hki⟩ := hkey
      have hidx := tidx r₀ (List.mem_of_find?_eq_some hr₀)
      unfold TaskIndexOk at hidx
      rw [hkx, hkt, hki] at hidx
      refine resultShape_execution reach hem hcc
        (fun id hid => Or.inr ⟨spec, List.mem_of_find?_eq_some hfind, index, ?_, ?_⟩) kept hd _ _
      · rw [hid, heid, hname]; exact hidx
      · rw [hid, heid, hname]
    · exact (hold (by simpa using hr)).elim
  case closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, -, hcc, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact (hold (by simpa using hr)).elim
    · rw [new_of_append hr hold rfl]
      obtain ⟨hem, heid⟩ := execution?_eq_some he
      exact resultShape_execution reach hem hcc (fun id hid => Or.inl (by rw [hid, heid])) kept hd _ _
    · exact (hold (by simpa using hr)).elim
  case closeRun path =>
    obtain ⟨-, -, run, w, output, x, owner, hrun, -, -, hw, -, hout, -, howner, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨htask, i, hi, h⟩ | ⟨name, e, ts, htask, he, -, h⟩
    · rcases h with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [new_of_append hr hold rfl]
        obtain ⟨owner', howner', hcases⟩ := State.designatedOutput_eq_ok.mp hout
        rw [howner, Option.some.injEq] at howner'
        subst howner'
        rcases hcases with ⟨-, i', pl, wf, hi', hpl, hctrl⟩ | ⟨name, -, -, -, htask', -⟩
        · rw [hi, Option.some.injEq] at hi'
          subst hi'
          have inv := Delivery.Reachable.inv reach
          obtain ⟨hid, w', pl', hw', hpl', -, htrig⟩ :=
            trigAvail_of_placed (inv.own.invocations i (invocation?_eq_some hi).1)
          obtain ⟨w'', hw'', hpl''⟩ := State.placementOf_eq_ok.mp hpl
          have hww : w' = w'' := Option.some.inj (hw'.symm.trans hw'')
          rw [← hww, hpl'] at hpl''
          have hpp : pl' = pl := Option.some.inj hpl''
          refine ⟨w', pl', kept.workflow? hw', hpl', Or.inl ⟨i.trigger, htrig.mono hd, ?_⟩⟩
          rw [hpp, hctrl]
          show Key.returned i.id = Key.returned (Key.invocation i.run i.placement i.trigger)
          rw [← hid]
        · rw [htask] at htask'; cases htask'
      all_goals exact (hold (by simpa using hr)).elim
    · rcases h with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact (hold (by simpa using hr)).elim
  case settle path name =>
    obtain ⟨-, -, run, w, pl, shape, kind, x, result, hrun, -, hw, hpl, -, -, -, hout, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact (hold (by simpa using hr)).elim
    · rw [new_of_append hr hold rfl]
      obtain ⟨-, hres_run, hres_pl, hctrl⟩ := Settle.settleOutcome_aggregate hout
      obtain ⟨-, -, -, hres⟩ := State.settleOutcome_some hout
      obtain ⟨-, hid, -⟩ := hres res rfl
      have hname := (Workflow.placement?_eq_some hpl).2
      have hwf : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨run, hrun, hw⟩
      refine ⟨w, pl, kept.workflow? (hres_run ▸ hwf), by rw [hres_pl, hname]; exact hpl, Or.inr ⟨hctrl, ?_⟩⟩
      rw [hid, hres_run, hres_pl]
  all_goals exact False.elim hp

theorem conforming_resultShape {tr : List Op} (h : Conforming p env tr s) :
    ∀ r ∈ s.results, ResultShape p env.behavior s r := by
  induction h with
  | nil => intro r hr; cases hr
  | snoc hex hconf hs _ ih => exact step_resultShape hex.reachable (conforming_taskIndex hex) hconf hs ih

/-! ### Workflows named by calls exist -/

local macro "validate_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, exists_const, and_true, true_and, Bool.false_eq_true,
    ↓reduceIte, false_and, and_false, exists_false] at $h:ident)

theorem validateWorkflow_of_valid {p : Program} (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows) :
    p.validateWorkflow w = .ok () := by
  unfold Program.validate at valid
  validate_simp at valid
  obtain ⟨-, -, -, -, -, -, -, u, hloop⟩ := valid
  exact Static.forIn_yield_ok hloop w hw

theorem validatePlacement_of_valid {p : Program} (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) : p.validatePlacement w pl = .ok () := by
  have h := validateWorkflow_of_valid valid hw
  unfold Program.validateWorkflow at h
  validate_simp at h
  obtain ⟨-, -, -, -, u, -, -, h⟩ := h
  split at h <;> validate_simp at h
  case' h_1 => obtain ⟨_, -, h⟩ := h
  all_goals
    obtain ⟨u₁, h1, -⟩ := h
    exact Static.forIn_yield_ok h1 pl hpl

theorem validateBody_workflow {p : Program} {at_ : String} {wf out : String}
    (h : p.validateBody at_ (.workflow wf out) = .ok ()) : ∃ cw, p.workflow? wf = some cw := by
  unfold Program.validateBody at h
  validate_simp at h
  obtain ⟨cw, hcw, -⟩ := h
  exact ⟨cw, hcw⟩

/-- The workflow a sub-workflow call names exists in a valid program. -/
theorem call_workflow_exists {p : Program} (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) {wf out : String} (hctrl : pl.control = .call (.workflow wf out)) :
    ∃ cw, p.workflow? wf = some cw := by
  have h := validatePlacement_of_valid valid hw hpl
  rcases pl with ⟨name, control, policy, timeout⟩
  dsimp only at hctrl
  subst hctrl
  unfold Program.validatePlacement at h
  validate_simp at h
  obtain ⟨u, hbody, -⟩ := h
  exact validateBody_workflow hbody

theorem validateTask_body {p : Program} {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) : ∃ at', p.validateBody at' task.body = .ok () := by
  unfold Program.validateTask at h
  validate_simp at h
  obtain ⟨-, u, hbody, -⟩ := h
  exact ⟨_, hbody⟩

/-- The workflow a workflow task names exists in a valid program. -/
theorem task_workflow_exists {p : Program} (valid : p.validate = .ok ()) {w : Workflow} (hw : w ∈ p.workflows)
    {pl : Placement} (hpl : pl ∈ w.placements) {cc : Concurrency} (hctrl : pl.control = .concurrency cc)
    {task : TaskSpec} (htask : task ∈ cc.tasks) {wf out : String} (hbody : task.body = .workflow wf out) :
    ∃ cw, p.workflow? wf = some cw := by
  obtain ⟨-, -, -, hall⟩ := ((Program.validate_ok valid).workflows w hw).placements pl hpl |>.concurrency cc hctrl
  obtain ⟨at_, h⟩ := hall task htask
  obtain ⟨at', hb⟩ := validateTask_body h
  rw [hbody] at hb
  exact validateBody_workflow hb


end UniverseInv

end UniverseProof

end Suimon.Round3
