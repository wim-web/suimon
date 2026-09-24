import Suimon.Theorems.SettleActive

/-! Layer 3 of the settlement invariant: where triggers, results, task results and deliveries come
    from, which sub-workflow calls returned, and which runs completed, are kept by every step. -/

namespace Suimon.Settle

open State

variable {p : Definition} {s t : State}

theorem delivery?_of_prefix (h : s.deliveries <+: t.deliveries) {path : Path} {index : Nat} {source : ResultId}
    {d : Delivery} (hd : s.delivery? path index source = some d) : t.delivery? path index source = some d := by
  obtain ⟨rest, hrest⟩ := h
  simp only [State.delivery?, ← hrest, List.find?_append]
  simp only [State.delivery?] at hd
  simp [hd]

theorem settled?_of_prefix (h : s.settled <+: t.settled) {path : Path} {name : String} {x : Settled}
    (hx : s.settled? path name = some x) : t.settled? path name = some x := by
  obtain ⟨rest, hrest⟩ := h
  simp only [State.settled?, ← hrest, List.find?_append]
  simp only [State.settled?] at hx
  simp [hx]

theorem settled?_isSome_of_prefix (h : s.settled <+: t.settled) {path : Path} {name : String}
    (hx : (s.settled? path name).isSome) : (t.settled? path name).isSome := by
  cases hs : s.settled? path name with
  | none => rw [hs] at hx; cases hx
  | some x => rw [settled?_of_prefix h hs]; rfl

/-- A trigger stays available once taken. --/
theorem TriggerOk.mono {w : Workflow} {i i' : Invocation} (h : TriggerOk p s w i) (hk : invKey i' = invKey i)
    (hd : s.deliveries <+: t.deliveries) : TriggerOk p t w i' := by
  simp only [invKey_eq] at hk
  obtain ⟨-, hrun, hpl, htrig⟩ := hk
  unfold TriggerOk at h ⊢
  rw [hpl]
  cases hsh : w.shape? p i.placement with
  | none => rw [hsh] at h; exact h
  | some sh =>
    rw [hsh] at h
    cases sh with
    | none => rw [htrig]; exact h
    | entry => rw [htrig]; exact h
    | single idx c =>
      obtain ⟨src, v, ht, hv⟩ := h
      refine ⟨src, v, htrig.trans ht, ?_⟩
      rw [hrun, resolveSingle_of_prefix hd (deliveriesOn_ne_nil_of_value hv)]
      exact hv
    | stream idx c =>
      obtain ⟨src, d, ht, hd', hf⟩ := h
      exact ⟨src, d, htrig.trans ht, by rw [hrun]; exact delivery?_of_prefix hd hd', hf⟩
    | merge cs => exact h

/-- Every execution names a concurrency of its run's workflow. --/
def ExecsResolved (p : Definition) (s : State) : Prop := ∀ e ∈ s.executions, ∃ cc, s.concurrencyOf p e = .ok cc

theorem Own.execsResolved (own : Own p s) : ExecsResolved p s :=
  fun _ he => (own.exec_concurrency he).imp fun _ h => h.1

theorem ExecsResolved.of_sameKeys (h : ExecsResolved p s) (hk : SameKeys p s t) : ExecsResolved p t := by
  intro e' he'
  obtain ⟨e, he, hkey⟩ := exists_of_map_eq hk.executions.symm he'
  simp only [execKey_eq] at hkey
  obtain ⟨cc, hcc⟩ := h e he
  exact ⟨cc, hk.workflows.concurrencyOf hkey.2.1.symm hkey.2.2.1.symm hcc⟩

theorem SameWorkflows.placementAt (h : SameWorkflows p s t) {path : Path} {name : String} :
    Settle.placementAt p t path name = Settle.placementAt p s path name := by
  simp only [Settle.placementAt, h path]

/-- The concurrency of an existing execution is read back from a state that keeps workflows. --/
theorem concurrencyOf_back (hcc : ExecsResolved p s) (hw : KeepsWorkflows p s t) {e e' : Execution}
    (he : e ∈ s.executions) (hrun : e'.run = e.run) (hplace : e'.placement = e.placement) {cc : Concurrency}
    (h : t.concurrencyOf p e' = .ok cc) : s.concurrencyOf p e = .ok cc := by
  obtain ⟨cc0, hcc0⟩ := hcc e he
  rw [concurrencyOf_det h (hw.concurrencyOf hrun hplace hcc0)]
  exact hcc0

/-- Everything a result's origin refers to persists. --/
structure Persists (p : Definition) (s t : State) : Prop where
  settled : ∀ x ∈ s.settled, x ∈ t.settled
  calls : ∀ c ∈ s.calls, ∃ c' ∈ t.calls, callKey c' = callKey c
  executions : ∀ e ∈ s.executions, ∃ e' ∈ t.executions, execKey e' = execKey e
  taskResults : ∀ tr ∈ s.taskResults, ∃ tr' ∈ t.taskResults, trKey tr' = trKey tr
  workflows : KeepsWorkflows p s t

/-- How an invocation may change without breaking the origin of its results: it keeps its status
    and arm, or it was active and changes so that a Stream call's invocation is not skipped and an
    execution's invocation with an output succeeds. --/
def Compat (p : Definition) (s : State) (i i' : Invocation) : Prop :=
  (i'.status = i.status ∧ i'.arm = i.arm) ∨
  (i.status = .active ∧ (∀ c ∈ s.calls, c.task = none → c.owner = i.id → c.stream = true → i'.status ≠ .skipped) ∧
    (∀ e ∈ s.executions, e.id = i.id → (∃ tr ∈ s.taskResults, tr.execution = e.id ∧
      ∀ cc, s.concurrencyOf p e = .ok cc → tr.task ∈ included cc) → i'.status = .succeeded))

theorem Compat.refl {i : Invocation} : Compat p s i i := Or.inl ⟨rfl, rfl⟩

/-- A result's origin persists when its invocations change compatibly. --/
theorem ResultOk.transfer (hcc : ExecsResolved p s) {r : Result} (h : ResultOk p s r) (hp : Persists p s t)
    (hinv : ∀ i ∈ s.invocations, i.run = r.run → i.placement = r.placement →
      ∃ i' ∈ t.invocations, invKey i' = invKey i ∧ Compat p s i i') :
    ResultOk p t r := by
  rcases h with ⟨x, hx, h1, h2, h3, h4⟩ | ⟨c, hc, htc, j, hj, hjo, hjr, hjp, hst⟩ |
    ⟨e, he, j, hj, hje, hjr, hjp, hst⟩ | ⟨j, hj, hjr, hjp, hst, pl, wf, out, hpl, hctrl⟩
  · exact Or.inl ⟨x, hp.settled x hx, h1, h2, h3, h4⟩
  · obtain ⟨c', hc', hk⟩ := hp.calls c hc
    obtain ⟨j', hj', hk', hcomp⟩ := hinv j hj hjr hjp
    simp only [callKey_eq] at hk
    simp only [invKey_eq] at hk'
    refine Or.inr (Or.inl ⟨c', hc', hk.2.2.1.trans htc, j', hj', by rw [hk'.1, hjo, hk.2.1], by rw [hk'.2.1, hjr],
      by rw [hk'.2.2.1, hjp], ?_⟩)
    rw [hk.2.2.2]
    rcases hcomp with ⟨hs', ha'⟩ | ⟨hact, hcall, -⟩
    · rw [hs', ha']; exact hst
    · rcases hst with ⟨-, hs, -⟩ | ⟨hstream, -⟩
      · rw [hact] at hs; cases hs
      · exact Or.inr ⟨hstream, hcall c hc htc hjo.symm hstream⟩
  · obtain ⟨e', he', hk⟩ := hp.executions e he
    obtain ⟨j', hj', hk', hcomp⟩ := hinv j hj hjr hjp
    simp only [execKey_eq] at hk
    simp only [invKey_eq] at hk'
    refine Or.inr (Or.inr (Or.inl ⟨e', he', j', hj', by rw [hk'.1, hje, hk.1], by rw [hk'.2.1, hjr],
      by rw [hk'.2.2.1, hjp], ?_⟩))
    rcases hcomp with ⟨hs', -⟩ | ⟨hact, -, hexec⟩
    · rw [hs']
      rcases hst with hst | ⟨hst, tr, htr, htre, hin⟩
      · exact Or.inl hst
      · obtain ⟨tr', htr', htk⟩ := hp.taskResults tr htr
        simp only [trKey_eq] at htk
        refine Or.inr ⟨hst, tr', htr', by rw [htk.1, htre, hk.1], fun cc hcc' => ?_⟩
        rw [htk.2.1]
        exact hin cc (concurrencyOf_back hcc hp.workflows he hk.2.1 hk.2.2.1 hcc')
    · rcases hst with hs | ⟨-, htrs⟩
      · rw [hact] at hs; cases hs
      · exact Or.inl (hexec e he hje.symm htrs)
  · obtain ⟨j', hj', hk', hcomp⟩ := hinv j hj hjr hjp
    simp only [invKey_eq] at hk'
    have hs' : j'.status = .succeeded := by
      rcases hcomp with ⟨hs', -⟩ | ⟨hact, -, -⟩
      · rw [hs', hst]
      · rw [hact] at hst; cases hst
    refine Or.inr (Or.inr (Or.inr ⟨j', hj', by rw [hk'.2.1, hjr], by rw [hk'.2.2.1, hjp], hs', pl, wf, out, ?_,
      hctrl⟩))
    rw [hk'.2.1, hk'.2.2.1]
    exact hp.workflows.placementAt hpl

namespace Persists

theorem refl : Persists p s s :=
  ⟨fun _ h => h, fun c hc => ⟨c, hc, rfl⟩, fun e he => ⟨e, he, rfl⟩, fun tr htr => ⟨tr, htr, rfl⟩, KeepsWorkflows.refl⟩

theorem of_sameKeys (hk : SameKeys p s t) (hs : ∀ x ∈ s.settled, x ∈ t.settled)
    (htr : ∀ tr ∈ s.taskResults, ∃ tr' ∈ t.taskResults, trKey tr' = trKey tr) : Persists p s t :=
  ⟨hs, fun _ hc => exists_of_map_eq hk.calls hc, fun _ he => exists_of_map_eq hk.executions he, htr, hk.workflows⟩

end Persists

theorem stopExecution_find? {e : Execution} {name : String} :
    (stopExecution e).tasks.find? (·.name == name) =
      (e.tasks.find? (·.name == name)).map fun t =>
        if t.status == .pending || t.status == .ready then { t with status := .notStarted } else t := by
  simp only [stopExecution, List.find?_map]
  congr 1
  congr 1
  funext t
  simp only [Function.comp]
  split <;> rfl

namespace Prov

theorem empty : Prov p {} where
  invTrigger := by simp
  results := by simp
  skipped := by simp
  taskResultSrc := by simp
  deliveries := by simp
  callRun := by simp
  completeSettled := by simp

/-- Only the records matter. --/
theorem of_records (h : Prov p s) (hr : t.runs = s.runs) (hi : t.invocations = s.invocations)
    (hc : t.calls = s.calls) (he : t.executions = s.executions) (hres : t.results = s.results)
    (htr : t.taskResults = s.taskResults) (hd : t.deliveries = s.deliveries) (hs : t.settled = s.settled) :
    Prov p t := by
  have hw : SameWorkflows p s t := SameWorkflows.of_runs hr
  have hpa : ∀ path name, placementAt p t path name = placementAt p s path name := fun path name => by
    simp only [placementAt, hw path]
  have htrig : ∀ w i, TriggerOk p t w i ↔ TriggerOk p s w i := fun w i => by
    simp only [TriggerOk, State.resolveSingle, State.deliveriesOn, State.delivery?, State.settled?, hd, hs]
  have hres' : ∀ r, ResultOk p t r ↔ ResultOk p s r := fun r => by
    simp only [ResultOk, hs, hc, hi, he, htr, hpa, hw.concurrencyOf]
  exact {
    invTrigger := fun i hi' => by
      rw [hi] at hi'
      obtain ⟨w, hw', ht⟩ := h.invTrigger i hi'
      exact ⟨w, by rw [hw]; exact hw', (htrig w i).mpr ht⟩
    results := fun r hr' => by rw [hres] at hr'; exact (hres' r).mpr (h.results r hr')
    skipped := by rw [he, htr]; exact h.skipped
    taskResultSrc := by rw [htr, hc, hr]; exact h.taskResultSrc
    deliveries := fun d hd' => by
      rw [hd] at hd'
      obtain ⟨w, hw', rest⟩ := h.deliveries d hd'
      exact ⟨w, by rw [hw]; exact hw', by rw [hres]; exact rest⟩
    callRun := fun i hi' hst pl hpl hctrl => by
      rw [hi] at hi'
      rw [hpa] at hpl
      obtain ⟨r, hr', rest⟩ := h.callRun i hi' hst pl hpl hctrl
      exact ⟨r, by rw [hr]; exact hr', rest⟩
    completeSettled := fun r hr' hc' w hw' pl hpl => by
      rw [hr] at hr'
      have := h.completeSettled r hr' hc' w hw' pl hpl
      simp only [State.settled?, hs] at this ⊢
      exact this }

theorem stop (h : Prov p s) (hcc : ExecsResolved p s) : Prov p s.stop := by
  have hk : SameKeys p s s.stop := SameKeys.stop
  have hp : Persists p s s.stop := Persists.of_sameKeys hk (fun _ h => h) (fun tr htr => ⟨tr, htr, rfl⟩)
  exact {
    invTrigger := h.invTrigger
    results := fun r hr => (h.results r hr).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := by
      intro e he name ts hts hsk tr htr hid
      obtain ⟨e0, he0, rfl⟩ := mem_stop_executions.mp he
      rw [stopExecution_find?] at hts
      obtain ⟨ts0, hts0, rfl⟩ := Option.map_eq_some_iff.mp hts
      refine h.skipped e0 he0 name ts0 hts0 ?_ tr htr hid
      revert hsk
      split <;> simp_all
    taskResultSrc := by
      intro tr htr
      rcases h.taskResultSrc tr htr with ⟨c, hc, hco, hct⟩ | hrun
      · exact Or.inl ⟨stopCall c, mem_stop_calls.mpr ⟨c, hc, rfl⟩, by simpa using hco, by simpa using hct⟩
      · exact Or.inr hrun
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

theorem fail (h : Prov p s) (hcc : ExecsResolved p s) {f : Failure} {policy : Policy} :
    Prov p (s.fail f policy) := by
  have h' : Prov p { s with failures := s.failures ++ [f] } := h.of_records rfl rfl rfl rfl rfl rfl rfl rfl
  cases policy
  · exact h'.stop hcc
  · exact h'

/-- A call changes status. --/
theorem setCall (h : Prov p s) (hcc : ExecsResolved p s) {c' : Call} (hk : SameKeys p s (s.setCall c')) :
    Prov p (s.setCall c') := by
  have hp : Persists p s (s.setCall c') := Persists.of_sameKeys hk (fun _ h => h) (fun tr htr => ⟨tr, htr, rfl⟩)
  exact {
    invTrigger := h.invTrigger
    results := fun r hr => (h.results r hr).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := h.skipped
    taskResultSrc := by
      intro tr htr
      rcases h.taskResultSrc tr htr with ⟨x, hx, hxo, hxt⟩ | hrun
      · obtain ⟨x', hx', hk'⟩ := hp.calls x hx
        simp only [callKey_eq] at hk'
        exact Or.inl ⟨x', hx', hk'.2.1.trans hxo, hk'.2.2.1.trans hxt⟩
      · exact Or.inr hrun
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

/-- A new result with an origin. --/
theorem appendResult (h : Prov p s) {r : Result} (hr : ResultOk p s r) :
    Prov p { s with results := s.results ++ [r] } where
  invTrigger := h.invTrigger
  results := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.results x hx
    · rw [List.mem_singleton.mp hx]; exact hr
  skipped := h.skipped
  taskResultSrc := h.taskResultSrc
  deliveries := fun d hd => by
    obtain ⟨w, hw, c, hc, x, hx, rest⟩ := h.deliveries d hd
    exact ⟨w, hw, c, hc, x, List.mem_append_left _ hx, rest⟩
  callRun := h.callRun
  completeSettled := h.completeSettled

/-- A new task result from a call or a completed run of a task that is not skipped. --/
theorem appendTaskResult (h : Prov p s) (hcc : ExecsResolved p s) {tr : TaskResult}
    (hsrc : (∃ c ∈ s.calls, c.owner = tr.execution ∧ c.task = some tr.task) ∨
      (∃ r ∈ s.runs, r.owner = some tr.execution ∧ r.task = some tr.task ∧ r.complete = true))
    (hsk : ∀ e ∈ s.executions, e.id = tr.execution → ∀ ts, e.tasks.find? (·.name == tr.task) = some ts →
      ts.status ≠ .skipped) :
    Prov p { s with taskResults := s.taskResults ++ [tr] } := by
  have hp : Persists p s { s with taskResults := s.taskResults ++ [tr] } :=
    ⟨fun _ h => h, fun c hc => ⟨c, hc, rfl⟩, fun e he => ⟨e, he, rfl⟩,
      fun x hx => ⟨x, List.mem_append_left _ hx, rfl⟩, KeepsWorkflows.refl⟩
  exact {
    invTrigger := h.invTrigger
    results := fun r hr => (h.results r hr).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := by
      intro e he name ts hts hskd x hx hid
      rcases List.mem_append.mp hx with hx | hx
      · exact h.skipped e he name ts hts hskd x hx hid
      · rw [List.mem_singleton.mp hx] at hid ⊢
        intro hname
        subst hname
        exact hsk e he hid.symm ts hts hskd
    taskResultSrc := fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h.taskResultSrc x hx
      · rw [List.mem_singleton.mp hx]; exact hsrc
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

/-- A task result is transformed. --/
theorem setTaskResult (h : Prov p s) (hcc : ExecsResolved p s) {r : TaskResult} : Prov p (s.setTaskResult r) := by
  have hkeys : (s.setTaskResult r).taskResults.map trKey = s.taskResults.map trKey := setTaskResult_keys
  have hp : Persists p s (s.setTaskResult r) :=
    ⟨fun _ h => h, fun c hc => ⟨c, hc, rfl⟩, fun e he => ⟨e, he, rfl⟩,
      fun x hx => exists_of_map_eq hkeys hx, KeepsWorkflows.refl⟩
  exact {
    invTrigger := h.invTrigger
    results := fun x hx => (h.results x hx).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := by
      intro e he name ts hts hsk x hx hid
      obtain ⟨x0, hx0, hk⟩ := exists_of_map_eq hkeys.symm hx
      simp only [trKey_eq] at hk
      rw [← hk.2.1]
      exact h.skipped e he name ts hts hsk x0 hx0 (hk.1.trans hid)
    taskResultSrc := by
      intro x hx
      obtain ⟨x0, hx0, hk⟩ := exists_of_map_eq hkeys.symm hx
      simp only [trKey_eq] at hk
      rw [← hk.1, ← hk.2.1]
      exact h.taskResultSrc x0 hx0
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

/-- A new delivery of an eligible result. --/
theorem appendDelivery (h : Prov p s) {d : Delivery}
    (hd : ∃ w, s.workflow? p d.run = some w ∧ ∃ c, w.connections[d.connection]? = some c ∧
      ∃ r ∈ s.results, r.id = d.source ∧ r.run = d.run ∧ r.placement = c.source ∧
        (c.arm.isNone || r.arm == c.arm) = true) :
    Prov p { s with deliveries := s.deliveries ++ [d] } where
  invTrigger := fun i hi => by
    obtain ⟨w, hw, ht⟩ := h.invTrigger i hi
    exact ⟨w, hw, ht.mono rfl ⟨[d], rfl⟩⟩
  results := h.results
  skipped := h.skipped
  taskResultSrc := h.taskResultSrc
  deliveries := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact h.deliveries x hx
    · rw [List.mem_singleton.mp hx]; exact hd
  callRun := h.callRun
  completeSettled := h.completeSettled

/-- A new settlement. --/
theorem appendSettled (h : Prov p s) (hcc : ExecsResolved p s) {x : Settled} :
    Prov p { s with settled := s.settled ++ [x] } := by
  have hp : Persists p s { s with settled := s.settled ++ [x] } :=
    ⟨fun _ h => List.mem_append_left _ h, fun c hc => ⟨c, hc, rfl⟩, fun e he => ⟨e, he, rfl⟩,
      fun tr htr => ⟨tr, htr, rfl⟩, KeepsWorkflows.refl⟩
  exact {
    invTrigger := fun i hi => by
      obtain ⟨w, hw, ht⟩ := h.invTrigger i hi
      exact ⟨w, hw, ht.mono rfl (List.prefix_refl _)⟩
    results := fun r hr => (h.results r hr).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := h.skipped
    taskResultSrc := h.taskResultSrc
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := fun r hr hc w hw pl hpl =>
      settled?_isSome_of_prefix ⟨[x], rfl⟩ (h.completeSettled r hr hc w hw pl hpl) }

/-- A task changes status; it becomes skipped only without results. --/
theorem setTask (h : Prov p s) (hcc : ExecsResolved p s) (wk : s.WellKeyed) {e : Execution} {ts : TaskState}
    (he : e ∈ s.executions)
    (hsk : ts.status = .skipped → ∀ tr ∈ s.taskResults, tr.execution = e.id → tr.task ≠ ts.name) :
    Prov p (s.setTask e ts) := by
  have hk : SameKeys p s (s.setTask e ts) := SameKeys.setTask wk.executions he
  have hp : Persists p s (s.setTask e ts) := Persists.of_sameKeys hk (fun _ h => h) (fun tr htr => ⟨tr, htr, rfl⟩)
  exact {
    invTrigger := h.invTrigger
    results := fun r hr => (h.results r hr).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := by
      intro x hx name ts' hts' hsk' tr htr hid
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · have hts'' : (withTask e ts).tasks.find? (·.name == name) = some ts' := hts'
        rw [withTask_find?] at hts''
        replace hts' := hts''
        by_cases hn : ts.name = name
        · subst hn
          simp only [↓reduceIte, Option.map_eq_some_iff] at hts'
          obtain ⟨_, -, rfl⟩ := hts'
          exact hsk hsk' tr htr hid
        · simp only [hn, ↓reduceIte] at hts'
          exact h.skipped e he name ts' hts' hsk' tr htr hid
      · exact h.skipped x hx name ts' hts' hsk' tr htr hid
    taskResultSrc := h.taskResultSrc
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

/-- An execution changes without changing its tasks. --/
theorem setExecution (h : Prov p s) (hcc : ExecsResolved p s) (wk : s.WellKeyed) {e e' : Execution} (he : e ∈ s.executions)
    (hk : execKey e' = execKey e) (htasks : e'.tasks = e.tasks) : Prov p (s.setExecution e') := by
  have hk' : SameKeys p s (s.setExecution e') := SameKeys.setExecution wk.executions he hk
  have hp : Persists p s (s.setExecution e') := Persists.of_sameKeys hk' (fun _ h => h) (fun tr htr => ⟨tr, htr, rfl⟩)
  exact {
    invTrigger := h.invTrigger
    results := fun r hr => (h.results r hr).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := by
      intro x hx name ts hts hsk tr htr hid
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · rw [htasks] at hts
        exact h.skipped e he name ts hts hsk tr htr (hid.trans (execKey_eq.mp hk).1)
      · exact h.skipped x hx name ts hts hsk tr htr hid
    taskResultSrc := h.taskResultSrc
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

/-- A run changes; it completes only with all placements settled. --/
theorem setRun (h : Prov p s) (hcc : ExecsResolved p s) (wk : s.WellKeyed) {r r' : Run} (hr : s.run? r'.path = some r)
    (hk : runKey r' = runKey r) (hc : r.complete = true → r'.complete = true)
    (hsettled : r'.complete = true → ∀ w, p.workflow? r'.workflow = some w → ∀ pl ∈ w.placements,
      (s.settled? r'.path pl.name).isSome) :
    Prov p (s.setRun r') := by
  have hk' : SameKeys p s (s.setRun r') := SameKeys.setRun wk.runs hr hk
  have hw : SameWorkflows p s (s.setRun r') := SameWorkflows.setRun hr (runKey_eq.mp hk).2.1
  have hp : Persists p s (s.setRun r') := Persists.of_sameKeys hk' (fun _ h => h) (fun tr htr => ⟨tr, htr, rfl⟩)
  have hr0 := (run?_eq_some hr).1
  simp only [runKey_eq] at hk
  -- A run of the old state is kept, possibly completed.
  have keep : ∀ x ∈ s.runs, ∃ x' ∈ (s.setRun r').runs, x'.owner = x.owner ∧ x'.task = x.task ∧
      (x.complete = true → x'.complete = true) := by
    intro x hx
    by_cases hxp : x.path = r'.path
    · have := wk.run_eq_of_path hx hr0 (hxp.trans (run?_eq_some hr).2.symm)
      subst this
      exact ⟨r', mem_replace_self hx hxp, hk.2.2.1, hk.2.2.2, hc⟩
    · exact ⟨x, mem_replace_of_mem hx hxp, rfl, rfl, id⟩
  have hpa : ∀ path name, placementAt p (s.setRun r') path name = placementAt p s path name := fun path name => by
    simp only [placementAt, hw path]
  exact {
    invTrigger := fun i hi => by
      obtain ⟨w, hw', ht⟩ := h.invTrigger i hi
      exact ⟨w, by rw [hw]; exact hw', ht⟩
    results := fun r hr => (h.results r hr).transfer hcc hp fun i hi _ _ => ⟨i, hi, rfl, Compat.refl⟩
    skipped := h.skipped
    taskResultSrc := by
      intro tr htr
      rcases h.taskResultSrc tr htr with hcall | ⟨x, hx, hxo, hxt, hxc⟩
      · exact Or.inl hcall
      · obtain ⟨x', hx', ho, ht, hcomp⟩ := keep x hx
        exact Or.inr ⟨x', hx', ho.trans hxo, ht.trans hxt, hcomp hxc⟩
    deliveries := fun d hd => by
      obtain ⟨w, hw', rest⟩ := h.deliveries d hd
      exact ⟨w, by rw [hw]; exact hw', rest⟩
    callRun := fun i hi hst pl hpl hctrl => by
      rw [hpa] at hpl
      obtain ⟨x, hx, hxo, hxt, hxc⟩ := h.callRun i hi hst pl hpl hctrl
      obtain ⟨x', hx', ho, ht, hcomp⟩ := keep x hx
      exact ⟨x', hx', ho.trans hxo, ht.trans hxt, hcomp hxc⟩
    completeSettled := by
      intro x hx hxc w hw' pl hpl
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · exact hsettled hxc w hw' pl hpl
      · exact h.completeSettled x hx hxc w hw' pl hpl }

/-- A new active invocation with an available trigger. --/
theorem appendInvocation (h : Prov p s) (hcc : ExecsResolved p s) {i : Invocation} (hact : i.status = .active)
    (htrig : ∃ w, s.workflow? p i.run = some w ∧ TriggerOk p s w i) :
    Prov p { s with invocations := s.invocations ++ [i] } := by
  have hp : Persists p s { s with invocations := s.invocations ++ [i] } :=
    ⟨fun _ h => h, fun c hc => ⟨c, hc, rfl⟩, fun e he => ⟨e, he, rfl⟩, fun tr htr => ⟨tr, htr, rfl⟩,
      KeepsWorkflows.refl⟩
  exact {
    invTrigger := fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h.invTrigger x hx
      · rw [List.mem_singleton.mp hx]; exact htrig
    results := fun r hr => (h.results r hr).transfer hcc hp fun j hj _ _ =>
      ⟨j, List.mem_append_left _ hj, rfl, Compat.refl⟩
    skipped := h.skipped
    taskResultSrc := h.taskResultSrc
    deliveries := h.deliveries
    callRun := fun x hx hst pl hpl hctrl => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h.callRun x hx hst pl hpl hctrl
      · rw [List.mem_singleton.mp hx, hact] at hst; cases hst
    completeSettled := h.completeSettled }

theorem appendCall (h : Prov p s) (hcc : ExecsResolved p s) {c : Call} : Prov p { s with calls := s.calls ++ [c] } := by
  have hp : Persists p s { s with calls := s.calls ++ [c] } :=
    ⟨fun _ h => h, fun x hx => ⟨x, List.mem_append_left _ hx, rfl⟩, fun e he => ⟨e, he, rfl⟩,
      fun tr htr => ⟨tr, htr, rfl⟩, KeepsWorkflows.refl⟩
  exact {
    invTrigger := h.invTrigger
    results := fun r hr => (h.results r hr).transfer hcc hp fun j hj _ _ => ⟨j, hj, rfl, Compat.refl⟩
    skipped := h.skipped
    taskResultSrc := fun tr htr => by
      rcases h.taskResultSrc tr htr with ⟨x, hx, rest⟩ | hrun
      · exact Or.inl ⟨x, List.mem_append_left _ hx, rest⟩
      · exact Or.inr hrun
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

theorem appendExecution (h : Prov p s) (hcc : ExecsResolved p s) {e : Execution} (hsk : ∀ ts ∈ e.tasks, ts.status ≠ .skipped) :
    Prov p { s with executions := s.executions ++ [e] } := by
  have hp : Persists p s { s with executions := s.executions ++ [e] } :=
    ⟨fun _ h => h, fun c hc => ⟨c, hc, rfl⟩, fun x hx => ⟨x, List.mem_append_left _ hx, rfl⟩,
      fun tr htr => ⟨tr, htr, rfl⟩, KeepsWorkflows.refl⟩
  exact {
    invTrigger := h.invTrigger
    results := fun r hr => (h.results r hr).transfer hcc hp fun j hj _ _ => ⟨j, hj, rfl, Compat.refl⟩
    skipped := fun x hx name ts hts hskd tr htr hid => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h.skipped x hx name ts hts hskd tr htr hid
      · rw [List.mem_singleton.mp hx] at hts
        exact absurd hskd (hsk ts (List.mem_of_find?_eq_some hts))
    taskResultSrc := h.taskResultSrc
    deliveries := h.deliveries
    callRun := h.callRun
    completeSettled := h.completeSettled }

theorem appendRun (h : Prov p s) (hcc : ExecsResolved p s)
    (hplaced : ∀ i ∈ s.invocations, ∃ w pl, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl)
    {r : Run} (hc : r.complete = false) :
    Prov p { s with runs := s.runs ++ [r] } := by
  have hw : KeepsWorkflows p s { s with runs := s.runs ++ [r] } := KeepsWorkflows.of_append rfl
  have hp : Persists p s { s with runs := s.runs ++ [r] } :=
    ⟨fun _ h => h, fun c hc => ⟨c, hc, rfl⟩, fun e he => ⟨e, he, rfl⟩, fun tr htr => ⟨tr, htr, rfl⟩, hw⟩
  exact {
    invTrigger := fun i hi => by
      obtain ⟨w, hw', ht⟩ := h.invTrigger i hi
      exact ⟨w, hw _ _ hw', ht⟩
    results := fun r hr => (h.results r hr).transfer hcc hp fun j hj _ _ => ⟨j, hj, rfl, Compat.refl⟩
    skipped := h.skipped
    taskResultSrc := fun tr htr => by
      rcases h.taskResultSrc tr htr with hcall | ⟨x, hx, rest⟩
      · exact Or.inl hcall
      · exact Or.inr ⟨x, List.mem_append_left _ hx, rest⟩
    deliveries := fun d hd => by
      obtain ⟨w, hw', rest⟩ := h.deliveries d hd
      exact ⟨w, hw _ _ hw', rest⟩
    callRun := fun i hi hst pl hpl hctrl => by
      obtain ⟨w, pl', hw', hpl'⟩ := hplaced i hi
      have hpa : placementAt p s i.run i.placement = some pl' := by rw [placementAt_eq hw', hpl']
      have : placementAt p { s with runs := s.runs ++ [r] } i.run i.placement = some pl' := hw.placementAt hpa
      rw [hpl] at this
      cases this
      obtain ⟨x, hx, rest⟩ := h.callRun i hi hst pl hpa hctrl
      exact ⟨x, List.mem_append_left _ hx, rest⟩
    completeSettled := fun x hx hxc w hw' pl hpl => by
      rcases List.mem_append.mp hx with hx | hx
      · exact h.completeSettled x hx hxc w hw' pl hpl
      · rw [List.mem_singleton.mp hx, hc] at hxc; cases hxc }

/-- An invocation changes compatibly with its results, and succeeds as a sub-workflow call only after
    its run completed. --/
theorem setInvocation (h : Prov p s) (hcc : ExecsResolved p s) (wk : s.WellKeyed) {i i' : Invocation} (hi : i ∈ s.invocations)
    (hk : invKey i' = invKey i) (hcomp : Compat p s i i')
    (hrun : i'.status = .succeeded → ∀ pl, placementAt p s i.run i.placement = some pl →
      (∃ wf out, pl.control = .call (.workflow wf out)) →
        ∃ r ∈ s.runs, r.owner = some i.id ∧ r.task = none ∧ r.complete = true) :
    Prov p (s.setInvocation i') := by
  have hk' : SameKeys p s (s.setInvocation i') := SameKeys.setInvocation wk.invocations hi hk
  have hp : Persists p s (s.setInvocation i') := Persists.of_sameKeys hk' (fun _ h => h) (fun tr htr => ⟨tr, htr, rfl⟩)
  simp only [invKey_eq] at hk
  exact {
    invTrigger := fun x hx => by
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · obtain ⟨w, hw, ht⟩ := h.invTrigger i hi
        exact ⟨w, by rw [hk.2.1]; exact hw, ht.mono (invKey_eq.mpr hk) (List.prefix_refl _)⟩
      · exact h.invTrigger x hx
    results := fun r hr => (h.results r hr).transfer hcc hp fun j hj _ _ => by
      by_cases hji : j.id = i.id
      · have := wk.invocation_eq_of_id hj hi hji
        subst this
        exact ⟨i', mem_replace_self hj hk.1.symm, invKey_eq.mpr hk, hcomp⟩
      · exact ⟨j, mem_replace_of_mem hj (by rw [hk.1]; exact hji), rfl, Compat.refl⟩
    skipped := h.skipped
    taskResultSrc := h.taskResultSrc
    deliveries := h.deliveries
    callRun := fun x hx hst pl hpl hctrl => by
      rcases mem_replace hx with rfl | ⟨hx, -⟩
      · rw [hk.2.1, hk.2.2.1] at hpl
        rw [hk.1]
        exact hrun hst pl hpl hctrl
      · exact h.callRun x hx hst pl hpl hctrl
    completeSettled := h.completeSettled }

/-- The invocation of a call leaves the active status without being skipped. --/
theorem settleCallOwner (h : Prov p s) (hcc : ExecsResolved p s) (own : Own p s) (wk : s.WellKeyed) {c : Call}
    (hc : c ∈ s.calls) (htc : c.task = none) {i i' : Invocation} (hi : i ∈ s.invocations) (hio : i.id = c.owner)
    (hact : i.status = .active) (hk : invKey i' = invKey i) (hns : i'.status ≠ .skipped) :
    Prov p (s.setInvocation i') := by
  refine h.setInvocation hcc wk hi hk (Or.inr ⟨hact, fun _ _ _ _ _ => hns, fun e he heq _ => ?_⟩) ?_
  · exact absurd (heq.trans hio) (own.call_not_exec wk hc htc he)
  · intro _ pl hpl ⟨wf, out, hctrl⟩
    obtain ⟨-, j, hj, hjo, pl', hpl', hctrl'⟩ := own.callNone c hc htc
    rw [← Own.placementAt_of_id wk hj hi (hjo.trans hio.symm), hpl'] at hpl
    cases hpl
    rcases hctrl' with ⟨_, _, h', -⟩ | ⟨_, _, h', -⟩ <;> rw [hctrl] at h' <;> cases h'

theorem root {m : String} {input : Option Value} :
    Prov p { started := true, runs := [{ path := [], workflow := m, input }] } where
  invTrigger := by simp
  results := by simp
  skipped := by simp
  taskResultSrc := by simp
  deliveries := by simp
  callRun := by simp
  completeSettled := by simp

theorem mem_setTaskResult_self {r r' : TaskResult} (hr : r ∈ s.taskResults) (hk : trKey r' = trKey r) :
    r' ∈ (s.setTaskResult r').taskResults := by
  simp only [trKey_eq] at hk
  rw [setTaskResult_taskResults]
  exact List.mem_map.mpr ⟨r, hr, by simp [hk.1, hk.2.1, hk.2.2]⟩

theorem settleOwner_resolved (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls) {status : CallStatus}
    {inv : InvocationStatus} {task : TaskStatus} {u : State}
    (hso : (s.setCall { c with status }).settleOwner c inv task = .ok u) : ExecsResolved p u := by
  have k1 := SameKeys.setCall (p := p) (c' := { c with status }) wk.calls hc rfl
  exact (own.of_sameKeys (k1.trans (SameKeys.settleOwner (k1.invocations_nodup wk.invocations)
    (k1.executions_nodup wk.executions) hso))).execsResolved

/-- A call ends and its owner, which was active, gets a final status other than skipped. --/
theorem afterCall (h : Prov p s) (act : Active p s) (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls)
    (hrun : c.status = .running ∨ c.status = .fetching) {status : CallStatus} {inv : InvocationStatus}
    {task : TaskStatus} (hinv : inv ≠ .skipped) (htask : task ≠ .skipped)
    (ho : (s.setCall { c with status }).settleOwner c inv task = .ok t) : Prov p t := by
  have k1 := SameKeys.setCall (p := p) (c' := { c with status }) wk.calls hc rfl
  have h1 := h.setCall own.execsResolved k1
  have hc1 : { c with status } ∈ (s.setCall { c with status }).calls := mem_replace_self hc rfl
  rcases settleOwner_eq_ok.mp ho with ⟨htc, i, hi, rfl⟩ | ⟨name, e, ts, htc, he, hts, rfl⟩
  · have hi' := invocation?_eq_some hi
    obtain ⟨j, hj, hjo, hja⟩ := act.callActive c hc htc hrun
    have : j = i := wk.invocation_eq_of_id hj hi'.1 (hjo.trans hi'.2.symm)
    subst this
    exact h1.settleCallOwner own.execsResolved (own.of_sameKeys k1) (wk.setCall _) hc1 htc hj hjo hja rfl hinv
  · exact h1.setTask own.execsResolved (wk.setCall _) (execution?_eq_some he).1 (fun hsk => absurd hsk htask)

/-- A cancelled call terminates and its owner, if still active, ends as cancelled. --/
theorem afterCancel (h : Prov p s) (own : Own p s) (wk : s.WellKeyed) {c : Call} (hc : c ∈ s.calls)
    (ho : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t) : Prov p t := by
  have k1 := SameKeys.setCall (p := p) (c' := { c with status := .cancelled }) wk.calls hc rfl
  have h1 := h.setCall own.execsResolved k1
  have hc1 : { c with status := .cancelled } ∈ (s.setCall { c with status := .cancelled }).calls :=
    mem_replace_self hc rfl
  rcases cancelOwner_eq_ok.mp ho with ⟨htc, i, hi, rfl⟩ | ⟨name, e, ts, htc, he, hts, rfl⟩
  · have hi' := invocation?_eq_some hi
    split
    · rename_i hact
      exact h1.settleCallOwner own.execsResolved (own.of_sameKeys k1) (wk.setCall _) hc1 htc hi'.1 hi'.2 hact rfl
        (by simp)
    · exact h1
  · split
    · exact h1.setTask own.execsResolved (wk.setCall _) (execution?_eq_some he).1 (fun hsk => by simp at hsk)
    · exact h1

/-- Every step keeps where triggers, results, task results and deliveries come from. --/
theorem step (h : Prov p s) (act : Active p s) (own : Own p s) (wk : s.WellKeyed) (h0 : s = {} ∨ s.started = true)
    {op : Op} (hs : step p s op = .ok t) : Prov p t := by
  have hcc : ExecsResolved p s := own.execsResolved
  cases op with
  | start input =>
    obtain ⟨hns, -, _, -, -, rfl⟩ := Step.start_inv hs
    rcases h0 with rfl | h0
    · exact root
    · simp [h0] at hns
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, hinput, rfl, -, -, hcases⟩ := Step.invoke_inv hs
    have hwf := workflow?_of_run hr hw
    have hrp := (run?_eq_some hr).2
    let inv : Invocation := { id := Key.invocation path name trigger, run := path, placement := name, trigger, input }
    have htrig : TriggerOk p s w inv := by
      unfold TriggerOk
      rcases Step.invocationInput_inv hinput with ⟨hsh, htr, -⟩ | ⟨hsh, htr, -⟩ | ⟨i, c, src, hsh, htr, hres⟩ |
        ⟨i, c, src, d, hsh, htr, hd, hout⟩
      · simp only [inv, hsh]; exact htr
      · simp only [inv, hsh]; exact htr
      · simp only [inv, hsh]; exact ⟨src, input, htr, by rw [← hrp]; exact hres⟩
      · simp only [inv, hsh]
        refine ⟨src, d, htr, by rw [← hrp]; exact hd, ?_⟩
        rcases hout with ⟨v, hv, -⟩ | ⟨hv, -⟩ <;> rw [hv] <;> simp
    have h1 := h.appendInvocation hcc (i := inv) rfl ⟨w, hwf, htrig⟩
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨judge, arms, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩ | ⟨cc, -, -, rfl⟩
    · exact h1.appendCall hcc
    · exact h1.appendCall hcc
    · refine h1.appendRun hcc (fun x hx => ?_) rfl
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨w', pl', hw', hpl', -⟩ := own.invPlaced x hx
        exact ⟨w', pl', hw', hpl'⟩
      · rw [List.mem_singleton.mp hx]; exact ⟨w, pl, hwf, hpl⟩
    · refine h1.appendExecution hcc fun ts hts => ?_
      simp only [List.mem_map] at hts
      obtain ⟨_, -, rfl⟩ := hts
      split <;> simp
  | fetch id =>
    obtain ⟨-, -, c, hc, -, -, rfl⟩ := Step.fetch_inv hs
    exact h.setCall hcc (SameKeys.setCall wk.calls (call?_eq_some hc).1 rfl)
  | returned id value =>
    obtain ⟨-, -, c, f, s', hc, hstr, hst, -, hacc, hso⟩ := Step.returned_inv hs
    have hc0 := (call?_eq_some hc).1
    rcases accept_eq_ok.mp hacc with ⟨htc, i, hi, -, rfl⟩ | ⟨name, htc, hfresh, rfl⟩
    · rcases settleOwner_eq_ok.mp hso with ⟨-, i2, hi2, rfl⟩ | ⟨_, _, _, htc', -, -, -⟩
      · have hi' := invocation?_eq_some hi
        have : i2 = i := by
          have : s.invocation? c.owner = some i2 := hi2
          rw [hi] at this; exact (Option.some.inj this).symm
        subst this
        obtain ⟨j, hj, hjo, hja⟩ := act.callActive c hc0 htc (Or.inl hst)
        have : j = i2 := wk.invocation_eq_of_id hj hi'.1 (hjo.trans hi'.2.symm)
        subst this
        have k1 := SameKeys.setCall (p := p) (c' := { c with status := .returned }) wk.calls hc0 rfl
        have hc1 : { c with status := .returned } ∈ (s.setCall { c with status := .returned }).calls :=
          mem_replace_self hc0 rfl
        have h2 := (h.setCall hcc k1).settleCallOwner hcc (own.of_sameKeys k1) (wk.setCall _) hc1 htc
          (i' := { j with status := .succeeded }) hj hjo hja rfl (by simp)
        have hres : ResultOk p ((s.setCall { c with status := .returned }).setInvocation { j with status := .succeeded })
            { id := Key.callResult c.id 0, run := j.run, placement := j.placement, producer := c.id, value } :=
          Or.inr (Or.inl ⟨_, hc1, htc, _, mem_replace_self hj rfl, hjo, rfl, rfl,
            Or.inl ⟨hstr, rfl, (act.activeArm j hj hja).symm⟩⟩)
        exact h2.appendResult hres
      · rw [htc] at htc'; cases htc'
    · obtain ⟨e, he, heo, -, ts, hts, hta⟩ := act.taskCallActive c hc0 name htc (Or.inl hst)
      have h1 := h.appendTaskResult hcc (tr := { execution := c.owner, task := name, index := 0, value })
        (Or.inl ⟨c, hc0, rfl, htc⟩) (fun e2 he2 hid ts2 hts2 => by
          have : e2 = e := wk.execution_eq_of_id he2 he (hid.trans heo.symm)
          subst this
          rw [hts] at hts2; cases hts2; rw [hta]; simp)
      have wku := wk.accept hacc
      have k1 := SameKeys.setCall (p := p) (c' := { c with status := .returned }) wku.calls hc0 rfl
      rcases settleOwner_eq_ok.mp hso with ⟨htc', -⟩ | ⟨name', e2, ts2, -, he2, -, rfl⟩
      · rw [htc] at htc'; cases htc'
      · exact (h1.setCall hcc k1).setTask hcc (wku.setCall _) (execution?_eq_some he2).1 (fun hsk => by simp at hsk)
  | judged id arm =>
    obtain ⟨-, -, c, j, i, pl, judge, arms, s', hc, hst, -, htc, hi, hpl, hctrl, -, hacc, rfl⟩ := Step.judged_inv hs
    have hc0 := (call?_eq_some hc).1
    have hi' := invocation?_eq_some hi
    rcases accept_eq_ok.mp hacc with ⟨-, i0, hi0, -, rfl⟩ | ⟨_, htc', -, -⟩
    · have : i0 = i := by rw [hi] at hi0; exact (Option.some.inj hi0).symm
      subst this
      obtain ⟨j', hj', hjo, hja⟩ := act.callActive c hc0 htc (Or.inl hst)
      have : j' = i0 := wk.invocation_eq_of_id hj' hi'.1 (hjo.trans hi'.2.symm)
      subst this
      have k1 := SameKeys.setCall (p := p) (c' := { c with status := .returned }) wk.calls hc0 rfl
      have hc1 : { c with status := .returned } ∈ (s.setCall { c with status := .returned }).calls :=
        mem_replace_self hc0 rfl
      have h2 := (h.setCall hcc k1).settleCallOwner hcc (own.of_sameKeys k1) (wk.setCall _) hc1 htc
        (i' := { j' with status := .succeeded, arm := some arm }) hj' hjo hja rfl (by simp)
      -- A branch call has no Stream contract.
      have hstr : c.stream = false := by
        obtain ⟨-, i3, hi3, hi3o, pl3, hpl3, hctrl3⟩ := own.callNone c hc0 htc
        have hpa : placementAt p s j'.run j'.placement = some pl := by
          rw [placementOf_eq_ok] at hpl
          obtain ⟨w, hw, hpl⟩ := hpl
          rw [placementAt_eq hw, hpl]
        rw [Own.placementAt_of_id wk hi3 hj' (hi3o.trans hjo.symm), hpa] at hpl3
        cases hpl3
        rcases hctrl3 with ⟨_, _, h3, -⟩ | ⟨_, _, -, hs3⟩
        · rw [hctrl] at h3; cases h3
        · exact hs3
      have hres : ResultOk p ((s.setCall { c with status := .returned }).setInvocation
          { j' with status := .succeeded, arm := some arm })
          { id := Key.callResult c.id 0, run := j'.run, placement := j'.placement, producer := c.id, arm := some arm,
            value := j'.input.getD "" } :=
        Or.inr (Or.inl ⟨_, hc1, htc, _, mem_replace_self hj' rfl, hjo, rfl, rfl, Or.inl ⟨hstr, rfl, rfl⟩⟩)
      exact h2.appendResult hres
    · rw [htc] at htc'; cases htc'
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, hstr, hst, hacc, rfl⟩ := Step.yielded_inv hs
    have hc0 := (call?_eq_some hc).1
    have wku := wk.accept hacc
    rcases accept_eq_ok.mp hacc with ⟨htc, i, hi, -, rfl⟩ | ⟨name, htc, -, rfl⟩
    · have hi' := invocation?_eq_some hi
      obtain ⟨j, hj, hjo, hja⟩ := act.callActive c hc0 htc (Or.inr hst)
      have : j = i := wk.invocation_eq_of_id hj hi'.1 (hjo.trans hi'.2.symm)
      subst this
      have h1 := h.appendResult (r := ⟨Key.callResult c.id c.yields, j.run, j.placement, c.id, none, value⟩)
        (Or.inr (Or.inl ⟨c, hc0, htc, j, hj, hjo, rfl, rfl, Or.inr ⟨hstr, by rw [hja]; simp⟩⟩))
      exact h1.setCall hcc (SameKeys.setCall wku.calls hc0 rfl)
    · obtain ⟨e, he, heo, -, ts, hts, hta⟩ := act.taskCallActive c hc0 name htc (Or.inr hst)
      have h1 := h.appendTaskResult hcc (tr := { execution := c.owner, task := name, index := c.yields, value })
        (Or.inl ⟨c, hc0, rfl, htc⟩) (fun e2 he2 hid ts2 hts2 => by
          have : e2 = e := wk.execution_eq_of_id he2 he (hid.trans heo.symm)
          subst this
          rw [hts] at hts2; cases hts2; rw [hta]; simp)
      exact h1.setCall hcc (SameKeys.setCall wku.calls hc0 rfl)
  | ended id =>
    obtain ⟨-, -, c, hc, -, hst, hso⟩ := Step.ended_inv hs
    exact h.afterCall act own wk (call?_eq_some hc).1 (Or.inr hst) (by simp) (by simp) hso
  | failed id =>
    obtain ⟨-, -, c, hc, hrun, hf⟩ := Step.failed_inv hs
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact (h.afterCall act own wk (call?_eq_some hc).1 hrun (by simp) (by simp) hso).fail
      (settleOwner_resolved own wk (call?_eq_some hc).1 hso)
  | timedOut id element =>
    obtain ⟨-, -, c, hc, hcond, hf⟩ := Step.timedOut_inv hs
    have hrun : c.status = .running ∨ c.status = .fetching := by
      rcases hcond with ⟨-, h1, -⟩ | ⟨-, h1, -⟩
      · exact Or.inr h1
      · exact h1
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact (h.afterCall act own wk (call?_eq_some hc).1 hrun (by simp) (by simp) hso).fail
      (settleOwner_resolved own wk (call?_eq_some hc).1 hso)
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨hrun, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp hf
      exact (h.afterCall act own wk (call?_eq_some hc).1 hrun (by simp) (by simp) hso).fail
        (settleOwner_resolved own wk (call?_eq_some hc).1 hso)
    · exact h.afterCancel own wk (call?_eq_some hc).1 ho
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact h.afterCancel own wk (call?_eq_some hc).1 ho
  | deliver path index source value =>
    obtain ⟨-, -, w, c, outcome, hdt, -, rfl⟩ := Step.deliver_inv hs
    obtain ⟨hw, hc, ⟨r, hr, h1, h2, h3⟩, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
    have hr' := result?_eq_some hr
    refine h.appendDelivery ⟨w, hw, c, hc, r, hr'.1, hr'.2, h1, h2, ?_⟩
    rcases h3 with h3 | h3 <;> simp [h3]
  | transformFailed path index source =>
    obtain ⟨-, -, w, c, tid, target, hdt, -, -, rfl⟩ := Step.transformFailed_inv hs
    obtain ⟨hw, hc, ⟨r, hr, h1, h2, h3⟩, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
    have hr' := result?_eq_some hr
    refine (h.appendDelivery ⟨w, hw, c, hc, r, hr'.1, hr'.2, h1, h2, ?_⟩).fail hcc
    rcases h3 with h3 | h3 <;> simp [h3]
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact h.setTask hcc wk (execution?_eq_some he).1 (fun hsk => by simp at hsk)
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (h.setTask hcc wk (execution?_eq_some he).1 (ts := { ts with status := .failed })
      (fun hsk => by simp at hsk)).fail (hcc.of_sameKeys (SameKeys.setTask wk.executions (execution?_eq_some he).1))
  | beginTask eid name =>
    obtain ⟨-, -, e, cc, ts, spec, he, -, -, -, -, -, -, hcases⟩ := Step.beginTask_inv hs
    have h1 := h.setTask hcc wk (execution?_eq_some he).1 (ts := { ts with status := .active })
      (fun hsk => by simp at hsk)
    have hcc1 := hcc.of_sameKeys (SameKeys.setTask (ts := { ts with status := .active }) wk.executions
      (execution?_eq_some he).1)
    rcases hcases with ⟨f, decl, -, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩
    · exact h1.appendCall hcc1
    · refine h1.appendRun hcc1 (fun x hx => ?_) rfl
      obtain ⟨w', pl', hw', hpl', -⟩ := own.invPlaced x hx
      exact ⟨w', pl', hw', hpl'⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, e, cc, spec, r, he, hcc0, hspec, hout, hr, hpend, hcases⟩ := Step.taskOutput_inv hs
    have he' := execution?_eq_some he
    have hr' := List.mem_of_find?_eq_some hr
    have hrk : r.execution = eid ∧ r.task = name ∧ r.index = index := by
      simpa [and_assoc] using List.find?_some hr
    have h1 := h.setTaskResult hcc (r := { r with output := .value value })
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · -- The result of an open execution whose invocation is active.
      have hin : name ∈ included cc := by
        rw [taskSpec_eq_ok] at hspec
        obtain ⟨cc', hcc', hfind⟩ := hspec
        rw [concurrencyOf_det hcc' hcc0] at hfind
        obtain ⟨hmem, hn⟩ := find?_key_eq_some hfind
        exact List.mem_map.mpr ⟨spec, List.mem_filter.mpr ⟨hmem, hout⟩, hn⟩
      have hopen : e.complete = false := by
        cases hc : e.complete
        · rfl
        · exact absurd hpend (act.completeOutputs e he'.1 hc r hr' (hrk.1.trans he'.2.symm) cc hcc0
            (by rw [hrk.2.1]; exact hin))
      obtain ⟨i, hi, hie, hia⟩ := act.execActive e he'.1 hopen
      obtain ⟨i2, hi2, hi2e, hi2r, hi2p, -⟩ := own.execOwner e he'.1
      have : i2 = i := wk.invocation_eq_of_id hi2 hi (hi2e.trans hie.symm)
      subst this
      refine h1.appendResult (Or.inr (Or.inr (Or.inl ⟨e, he'.1, i2, hi2, hi2e, hi2r, hi2p, Or.inr ⟨hia,
        { r with output := .value value }, mem_setTaskResult_self hr' rfl, hrk.1.trans he'.2.symm,
        fun cc' hcc' => ?_⟩⟩)))
      have : s.concurrencyOf p e = .ok cc' := hcc'
      rw [concurrencyOf_det this hcc0]
      rw [hrk.2.1]
      exact hin
    · exact h1
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (h.setTaskResult hcc (r := { r with output := .failed })).fail hcc
  | settle path name =>
    obtain ⟨-, -, r, w, pl, shape, kind, x, result, -, -, -, -, -, -, -, hout, hcases⟩ := Step.settle_inv hs
    have h1 := h.appendSettled hcc (x := x)
    rcases hcases with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact h1
    · obtain ⟨hx, hrun, hplace, -⟩ := settleOutcome_aggregate hout
      subst hx
      exact h1.appendResult (Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hrun.symm, hplace.symm,
        rfl, rfl⟩)
  | closeExecution eid =>
    obtain ⟨-, -, e, cc, i, he, hec, hcc0, hended, -, hi, hcases⟩ := Step.closeExecution_inv hs
    have he' := execution?_eq_some he
    have hi' := invocation?_eq_some hi
    obtain ⟨j, hj, hje, hja⟩ := act.execActive e he'.1 hec
    have : j = i := wk.invocation_eq_of_id hj hi'.1 (hje.trans (he'.2.trans hi'.2.symm))
    subst this
    have h1 := h.setExecution hcc wk he'.1 (e' := { e with complete := true }) rfl rfl
    have wk1 : (s.setExecution { e with complete := true }).WellKeyed := wk.setExecution _
    have hcc1 := hcc.of_sameKeys (SameKeys.setExecution (e' := { e with complete := true }) wk.executions he'.1 rfl)
    have hcalls : ∀ c ∈ (s.setExecution { e with complete := true }).calls, c.task = none → c.owner = j.id →
        c.stream = true → False :=
      fun c hc htc hco _ => own.call_not_exec wk hc htc he'.1 (hje.symm.trans hco.symm)
    have hrun : ∀ pl, placementAt p (s.setExecution { e with complete := true }) j.run j.placement = some pl →
        (∃ wf out, pl.control = .call (.workflow wf out)) → False := by
      intro pl hpl ⟨wf, out, hctrl⟩
      obtain ⟨i3, hi3, hi3e, hi3r, hi3p, pl3, cc3, hpl3, hcc3, -⟩ := own.execOwner e he'.1
      have : i3 = j := wk.invocation_eq_of_id hi3 hj (hi3e.trans hje.symm)
      subst this
      have : placementAt p s i3.run i3.placement = some pl := hpl
      rw [hi3r, hi3p, hpl3] at this
      cases this
      rw [hcc3] at hctrl
      cases hctrl
    rcases hcases with ⟨hsk, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · refine h1.setInvocation hcc1 wk1 hj (i' := { j with status := .skipped }) rfl
        (Or.inr ⟨hja, fun c hc htc hco hst => (hcalls c hc htc hco hst).elim,
          fun e2 he2 hid ⟨tr, htr, htre, hin⟩ => ?_⟩) (fun hst => by simp at hst)
      -- An output of a task contradicts every output task being skipped.
      exfalso
      have he2e : e2 = { e with complete := true } := by
        rcases mem_replace he2 with h' | ⟨-, hne⟩
        · exact h'
        · exact absurd (hid.trans hje) hne
      subst he2e
      have hin' : tr.task ∈ included cc := hin cc hcc0
      obtain ⟨cc', hcc', hnames⟩ := own.exec_concurrency he'.1
      rw [concurrencyOf_det hcc' hcc0] at hnames
      have hname : tr.task ∈ e.tasks.map (·.name) := by
        rw [hnames]
        obtain ⟨ts, hts, hn⟩ := List.mem_map.mp hin'
        exact List.mem_map.mpr ⟨ts, (List.mem_filter.mp hts).1, hn⟩
      have hfind : (e.tasks.find? (·.name == tr.task)).isSome := by
        rw [List.find?_isSome]
        obtain ⟨ts, hts, hn⟩ := List.mem_map.mp hname
        exact ⟨ts, hts, by simp [hn]⟩
      obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp hfind
      obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
      have hskd : ts.status = .skipped := by
        have := List.all_eq_true.mp hsk ts (List.mem_filter.mpr ⟨htsm, by
          simp only [List.contains_iff_mem, htsn]; exact hin'⟩)
        simpa using this
      exact h.skipped e he'.1 tr.task ts hts hskd tr htr htre rfl
    · refine (h1.setInvocation hcc1 wk1 hj (i' := { j with status := .succeeded }) rfl
        (Or.inr ⟨hja, fun c hc htc hco hst => (hcalls c hc htc hco hst).elim, fun _ _ _ _ => rfl⟩)
        (fun _ pl hpl hctrl => (hrun pl hpl hctrl).elim)).appendResult ?_
      obtain ⟨i3, hi3, hi3e, hi3r, hi3p, -⟩ := own.execOwner e he'.1
      have : i3 = j := wk.invocation_eq_of_id hi3 hj (hi3e.trans hje.symm)
      subst this
      exact Or.inr (Or.inr (Or.inl ⟨{ e with complete := true }, mem_replace_self he'.1 rfl,
        { i3 with status := .succeeded }, mem_replace_self hj rfl, hje, hi3r, hi3p, Or.inl rfl⟩))
    · exact h1.setInvocation hcc1 wk1 hj (i' := { j with status := .succeeded }) rfl
        (Or.inr ⟨hja, fun c hc htc hco hst => (hcalls c hc htc hco hst).elim, fun _ _ _ _ => rfl⟩)
        (fun _ pl hpl hctrl => (hrun pl hpl hctrl).elim)
  | closeRun path =>
    obtain ⟨-, -, r, w, output, x, owner, hr, hrc, -, hw, hall, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
    have hr0 := (run?_eq_some hr).1
    have hsettled : ∀ w', p.workflow? r.workflow = some w' → ∀ pl ∈ w'.placements,
        (s.settled? r.path pl.name).isSome := by
      intro w' hw' pl hpl
      rw [hw] at hw'
      cases hw'
      rw [(run?_eq_some hr).2]
      exact List.all_eq_true.mp hall pl hpl
    have h1 := h.setRun hcc wk hr' (r' := { r with complete := true }) rfl (fun _ => rfl) (fun _ => hsettled)
    have wk1 : (s.setRun { r with complete := true }).WellKeyed := wk.setRun _
    have hcc1 := hcc.of_sameKeys (SameKeys.setRun (r' := { r with complete := true }) wk.runs hr' rfl)
    have hw1 : SameWorkflows p s (s.setRun { r with complete := true }) := SameWorkflows.setRun hr' rfl
    have hr1 : { r with complete := true } ∈ (s.setRun { r with complete := true }).runs := mem_replace_self hr0 rfl
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨name, e, ts, htask, he, hts, hcases⟩
    · have hi' := invocation?_eq_some hi
      obtain ⟨j, hj, hjo, hja⟩ := act.runActive r hr0 owner howner htask hrc
      have : j = i := wk.invocation_eq_of_id hj hi'.1 (hjo.trans hi'.2.symm)
      subst this
      have hset : ∀ st : InvocationStatus,
          Prov p ((s.setRun { r with complete := true }).setInvocation { j with status := st }) := by
        intro st
        refine h1.setInvocation hcc1 wk1 hj rfl (Or.inr ⟨hja, fun c hc htc hco _ => ?_, fun e he hid _ => ?_⟩)
          (fun _ _ _ _ => ⟨_, hr1, by rw [howner, ← hjo], htask, rfl⟩)
        · exact absurd (by rw [howner, ← hjo, hco]) (own.call_not_run wk hc htc hr0 htask)
        · exact absurd (by rw [howner, ← hjo, hid]) (own.exec_not_run wk he hr0 htask)
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · obtain ⟨i3, hi3, hi3o, -, pl, wf, out, hpl, hctrl⟩ := own.runNone r hr0 owner howner htask
        have : i3 = j := wk.invocation_eq_of_id hi3 hj (hi3o.trans hjo.symm)
        subst this
        refine (hset .succeeded).appendResult (Or.inr (Or.inr (Or.inr ⟨{ i3 with status := .succeeded },
          mem_replace_self hj rfl, rfl, rfl, rfl, pl, wf, out, ?_, hctrl⟩)))
        show placementAt p (s.setRun { r with complete := true }) i3.run i3.placement = some pl
        rw [hw1.placementAt]
        exact hpl
      · exact hset _
      · exact hset _
      · exact hset _
    · have he' := execution?_eq_some he
      have hname : ts.name = name := (find?_key_eq_some hts).2
      have hmem : withTask e { ts with status := .succeeded } ∈
          ((s.setRun { r with complete := true }).setTask e { ts with status := .succeeded }).executions :=
        mem_replace_self he'.1 rfl
      rcases hcases with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine (h1.setTask hcc1 wk1 he'.1 (ts := { ts with status := .succeeded })
          (fun hsk => by simp at hsk)).appendTaskResult
          (hcc1.of_sameKeys (SameKeys.setTask wk1.executions he'.1))
          (Or.inr ⟨_, hr1, by rw [howner, he'.2], htask, rfl⟩) (fun e2 he2 hid ts2 hts2 => ?_)
        rcases mem_replace he2 with rfl | ⟨-, hne⟩
        · have hts2' : (withTask e { ts with status := .succeeded }).tasks.find? (·.name == name) = some ts2 := hts2
          rw [withTask_find?] at hts2'
          simp only [hname, ↓reduceIte, Option.map_eq_some_iff] at hts2'
          obtain ⟨_, -, rfl⟩ := hts2'
          simp
        · exact absurd hid hne
      · refine h1.setTask hcc1 wk1 he'.1 (fun _ tr htr hid hn => ?_)
        rw [hname] at hn
        rcases h.taskResultSrc tr htr with ⟨c, hc, hco, hct⟩ | ⟨r2, hr2, hr2o, hr2t, hr2c⟩
        · exact own.taskCall_not_run wk hc (hct.trans (by rw [hn])) hr0 htask (by rw [howner, ← he'.2, ← hid, hco])
        · have : r2 = r := own.taskRun_unique wk hr2 hr0 (hr2t.trans (by rw [hn])) htask
            (by rw [hr2o, howner, hid, he'.2])
          subst this
          rw [hrc] at hr2c
          cases hr2c
      · exact h1.setTask hcc1 wk1 he'.1 (fun hsk => by simp at hsk)
      · exact h1.setTask hcc1 wk1 he'.1 (fun hsk => by simp at hsk)
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact (h.stop hcc).of_records rfl rfl rfl rfl rfl rfl rfl rfl
    · exact h.of_records rfl rfl rfl rfl rfl rfl rfl rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, w, hr, hw, hall, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
      have hsettled : ∀ w', p.workflow? r.workflow = some w' → ∀ pl ∈ w'.placements,
          (s.settled? r.path pl.name).isSome := by
        intro w' hw' pl hpl
        rw [hw] at hw'
        cases hw'
        rw [(run?_eq_some hr).2]
        exact List.all_eq_true.mp hall pl hpl
      exact (h.setRun hcc wk hr' (r' := { r with complete := true }) rfl (fun _ => rfl) (fun _ => hsettled)).of_records
        rfl rfl rfl rfl rfl rfl rfl rfl
    · exact h.of_records rfl rfl rfl rfl rfl rfl rfl rfl

end Prov

end Suimon.Settle
