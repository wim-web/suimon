import Suimon.Theorems.Round3.Frozen
import Suimon.Theorems.Round3.SettleView
import Suimon.Theorems.Round3.StableFrame
import Suimon.Theorems.Round3.StableView

namespace Suimon.Round3
open State

/-! ## [17] Round3/Stable.lean — task E4 -/

section StableSection
variable {p : Definition} {s : State}

/-- The tasks whose results a concurrency outputs, their results in a state, and whether they all
    skipped: what `closeExecution` reads. -/
def includedTasks (c : Concurrency) : List String := (c.tasks.filter (·.output.isSome)).map (·.name)

def includedOutputs (s : State) (eid : String) (c : Concurrency) : List TaskResult :=
  s.taskResults.filter fun x => x.execution == eid && (includedTasks c).contains x.task

def allIncludedSkipped (e : Execution) (c : Concurrency) : Bool :=
  (e.tasks.filter fun t => (includedTasks c).contains t.name).all (·.status == .skipped)

/-- The results `closeExecution` and `closeRun` build. -/
def listResult (e : Execution) (value : Value) : Result :=
  { id := Key.list e.id, run := e.run, placement := e.placement, producer := e.id, value }

def returnedResult (i : Invocation) (value : Value) : Result :=
  { id := Key.returned i.id, run := i.run, placement := i.placement, producer := i.id, value }

/-- The owner status a closed run hands back (§4.5). -/
def closedStatus : Outcome → InvocationStatus
  | .normal => .succeeded
  | .skipped => .skipped
  | .failed => .failed
  | .upstreamFailed => .upstreamFailed

def closedTaskStatus : Outcome → TaskStatus
  | .normal => .succeeded
  | .skipped => .skipped
  | .failed => .failed
  | .upstreamFailed => .upstreamFailed

/-- What a settlement, a closed execution and a closed run recorded is what their rule computes on the
    current state, because everything the rule reads is frozen once it applied (§10.3). -/
structure Stable (p : Definition) (s : State) : Prop where
  settled : ∀ x ∈ s.settled, ∃ w pl shape kind agg, s.workflow? p x.run = some w ∧
    w.placement? x.placement = some pl ∧ w.shape? p x.placement = some shape ∧
    w.outputKind? p x.placement = some kind ∧ s.settleOutcome x.run pl shape kind = some (x, agg) ∧
    ∀ r, agg = some r → r ∈ s.results
  execution : ∀ e ∈ s.executions, e.complete = true → ∀ cc i, s.concurrencyOf p e = .ok cc →
    s.invocation? e.id = some i →
    (allIncludedSkipped e cc = true ∧ i.status = .skipped) ∨
    (allIncludedSkipped e cc = false ∧ i.status = .succeeded ∧
      (cc.output = .list →
        listResult e (listValue ((includedOutputs s e.id cc).filterMap (·.output.value?))) ∈ s.results))
  run : ∀ r ∈ s.runs, r.complete = true → ∀ o output x, r.owner = some o → s.designatedOutput p r = .ok output →
    s.settled? r.path output = some x →
    match r.task with
    | none => ∃ i, s.invocation? o = some i ∧ i.status = closedStatus x.outcome ∧
        (x.outcome = .normal → ∃ res ∈ s.resultsOf r.path output, returnedResult i res.value ∈ s.results)
    | some name => ∃ e ts, s.execution? o = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ts.status = closedTaskStatus x.outcome ∧
        (x.outcome = .normal → ∃ res ∈ s.resultsOf r.path output,
          ∃ tr ∈ s.taskResults, tr.execution = o ∧ tr.task = name ∧ tr.index = 0 ∧ tr.value = res.value)

/-! ### One step keeps `Stable` -/

namespace StableAux

/-- Settlements: an old one reads the same view after the step (`view_kept`), and a new one read it in
    the step that recorded it (`view_settle`). -/
theorem stable_settled_step (h : Reachable p s) {t : State} {op : Op} (hs : step p s op = .ok t)
    (ih : Stable p s) :
    ∀ x ∈ t.settled, ∃ w pl shape kind agg, t.workflow? p x.run = some w ∧
      w.placement? x.placement = some pl ∧ w.shape? p x.placement = some shape ∧
      w.outputKind? p x.placement = some kind ∧ t.settleOutcome x.run pl shape kind = some (x, agg) ∧
      ∀ r, agg = some r → r ∈ t.results := by
  have inv := Delivery.Reachable.inv h
  have wk' := step_wellKeyed inv.wk hs
  have K := inv.kept hs
  intro x hx
  rcases Delivery.step_settled_back hs x hx with hx₀ | ⟨-, -, run, w, pl, shape, kind, res, hrun, -, hw, hpl,
      hfresh, hsh, hkind, hout, -, hres, hruns, hinv, hcalls, hexec, hdel, -, -⟩
  · obtain ⟨w, pl, shape, kind, agg, hw, hpl, hsh, hkind, hout, hagg⟩ := ih.settled x hx₀
    refine ⟨w, pl, shape, kind, agg, K.workflow? wk' hw, hpl, hsh, hkind, ?_, fun r hr => K.mem_results (hagg r hr)⟩
    rw [← settleOutcome_congr (view_kept h hs hx₀ hw hpl hsh hout)]
    exact hout
  · have hws : s.workflow? p x.run = some w := Delivery.workflow?_iff.mpr ⟨run, hrun, hw⟩
    refine ⟨w, pl, shape, kind, res, K.workflow? wk' hws, hpl, hsh, hkind, ?_, fun r hr => ?_⟩
    · rw [← settleOutcome_congr (view_settle h (step_grows hs) (Workflow.placement?_eq_some hpl).2 hfresh hout hres
        hruns hinv hcalls hexec hdel)]
      exact hout
    · rw [hres, hr]
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The execution `closeExecution` completes records what its rule computes. -/
theorem stable_execution_close {t : State} {eid : String} (K : Delivery.Kept s t) (wk' : t.WellKeyed)
    (hs : step p s (.closeExecution eid) = .ok t) {e : Execution} (he : e ∈ t.executions) (hid : e.id = eid)
    {cc : Concurrency} {i : Invocation} (hcc : t.concurrencyOf p e = .ok cc) (hi : t.invocation? e.id = some i) :
    (allIncludedSkipped e cc = true ∧ i.status = .skipped) ∨
    (allIncludedSkipped e cc = false ∧ i.status = .succeeded ∧
      (cc.output = .list →
        listResult e (listValue ((includedOutputs t e.id cc).filterMap (·.output.value?))) ∈ t.results)) := by
  obtain ⟨-, -, e₁, c, i₁, he₁, -, hc₁, -, -, hi₁, hcases⟩ := Step.closeExecution_inv hs
  obtain ⟨-, he₁id⟩ := execution?_eq_some he₁
  subst he₁id
  have hte : t.executions = (s.setExecution { e₁ with complete := true }).executions := by
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  rw [hte, setExecution_executions] at he
  obtain rfl : e = { e₁ with complete := true } := by
    rcases Delivery.mem_map_replace' he with h' | ⟨-, hne⟩
    · exact h'
    · simp [hid] at hne
  obtain rfl : cc = c := by
    have ht := K.concurrencyOf wk' (e := e₁) (e' := { e₁ with complete := true }) rfl rfl hc₁
    rw [hcc] at ht
    exact Except.ok.inj ht
  -- The invocation of the execution has the status `closeExecution` gave it.
  have hlook : ∀ st, t.invocations = (s.setInvocation { i₁ with status := st }).invocations →
      i = { i₁ with status := st } := fun st ht => by
    rw [invocation?_congr ht] at hi
    rw [invocation?_setInvocation_of hi₁ st] at hi
    exact (Option.some.inj hi).symm
  rcases hcases with ⟨hsk, ht⟩ | ⟨hsk, hout, -, ht⟩ | ⟨hsk, hout, ht⟩
  · obtain rfl := hlook .skipped (by subst ht; rfl)
    exact Or.inl ⟨hsk, rfl⟩
  · obtain rfl := hlook .succeeded (by subst ht; rfl)
    refine Or.inr ⟨hsk, rfl, fun _ => ?_⟩
    subst ht
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · obtain rfl := hlook .succeeded (by subst ht; rfl)
    exact Or.inr ⟨hsk, rfl, fun hl => by rw [hout] at hl; cases hl⟩

/-- Closed executions: an old one keeps its record, its invocation and its task results
    (`step_frozen`), and a new one was just closed. -/
theorem stable_execution_step (valid : p.validate = .ok ()) (h : Reachable p s) {t : State} {op : Op}
    (hs : step p s op = .ok t) (ih : Stable p s) :
    ∀ e ∈ t.executions, e.complete = true → ∀ cc i, t.concurrencyOf p e = .ok cc → t.invocation? e.id = some i →
      (allIncludedSkipped e cc = true ∧ i.status = .skipped) ∨
      (allIncludedSkipped e cc = false ∧ i.status = .succeeded ∧
        (cc.output = .list →
          listResult e (listValue ((includedOutputs t e.id cc).filterMap (·.output.value?))) ∈ t.results)) := by
  have inv := Delivery.Reachable.inv h
  have wk' := step_wellKeyed inv.wk hs
  have K := inv.kept hs
  intro e he hc cc i hcc hi
  rcases exec_complete_cases hs he hc with ⟨e₀, he₀, hid, hc₀⟩ | hop
  · obtain ⟨-, -, hf3, -, -, hf6, hf7, -⟩ := step_frozen valid h hs
    have he₀t := hf3 e₀ he₀ hc₀
    have hee : e = e₀ := wk'.execution_eq_of_id he he₀t hid.symm
    rw [hee] at hcc hi ⊢
    clear hee he hc
    obtain ⟨i₀, hi₀, hi₀id, -, -, c₀, hcc₀⟩ := inv.own.executions e₀ he₀
    have hcc' : s.concurrencyOf p e₀ = .ok cc := by
      have ht := K.concurrencyOf wk' rfl rfl hcc₀
      rw [hcc] at ht
      rw [Except.ok.inj ht]
      exact hcc₀
    have hcase := ih.execution e₀ he₀ hc₀ cc i₀ hcc' (by rw [← hi₀id]; exact inv.wk.invocation?_of_mem hi₀)
    have hna : i₀.status ≠ .active := by
      rcases hcase with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> rw [h'] <;> simp
    obtain ⟨him, hiid⟩ := invocation?_eq_some hi
    have hii : i = i₀ := Delivery.frozen inv hs hi₀ hna him (hiid.trans hi₀id.symm)
    rw [hii]
    -- The task results of a complete execution are frozen.
    have hperm : (includedOutputs s e₀.id cc).Perm (includedOutputs t e₀.id cc) := by
      unfold includedOutputs
      refine (List.perm_ext_iff_of_nodup (nodup_filter' _ (nodup_of_map' inv.wk.taskResults))
        (nodup_filter' _ (nodup_of_map' wk'.taskResults))).mpr fun r => ?_
      simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq]
      exact ⟨fun ⟨hr, hre, hin⟩ => ⟨hf7 e₀ he₀ hc₀ r hr hre, hre, hin⟩,
        fun ⟨hr, hre, hin⟩ => ⟨hf6 e₀ he₀ hc₀ r hr hre, hre, hin⟩⟩
    rcases hcase with hcase | ⟨h1, h2, h3⟩
    · exact Or.inl hcase
    · refine Or.inr ⟨h1, h2, fun hl => ?_⟩
      rw [← listValue_perm (hperm.filterMap _)]
      exact K.mem_results (h3 hl)
  · rw [hop] at hs
    exact stable_execution_close K wk' hs he rfl hcc hi

/-- The run `closeRun` completes hands its settlement back to its owner. -/
theorem stable_run_close {t : State} {path : Path} (K : Delivery.Kept s t) (wk' : t.WellKeyed)
    (hs : step p s (.closeRun path) = .ok t) {r : Run} (hr : r ∈ t.runs) (hpath : r.path = path)
    {o output : String} {x : Settled} (ho : r.owner = some o) (hout : t.designatedOutput p r = .ok output)
    (hx : t.settled? r.path output = some x) :
    match r.task with
    | none => ∃ i, t.invocation? o = some i ∧ i.status = closedStatus x.outcome ∧
        (x.outcome = .normal → ∃ res ∈ t.resultsOf r.path output, returnedResult i res.value ∈ t.results)
    | some name => ∃ e ts, t.execution? o = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ts.status = closedTaskStatus x.outcome ∧
        (x.outcome = .normal → ∃ res ∈ t.resultsOf r.path output,
          ∃ tr ∈ t.taskResults, tr.execution = o ∧ tr.task = name ∧ tr.index = 0 ∧ tr.value = res.value) := by
  obtain ⟨-, -, r₁, w, output₁, x₁, owner₁, hr₁, -, -, -, -, hout₁, hx₁, howner₁, hcases⟩ := Step.closeRun_inv hs
  obtain ⟨-, hr₁p⟩ := run?_eq_some hr₁
  subst hr₁p
  have htr : t.runs = (s.setRun { r₁ with complete := true }).runs := by
    rcases hcases with ⟨-, _, -, h'⟩ | ⟨_, _, _, -, -, -, h'⟩ <;>
      rcases h' with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  rw [htr, setRun_runs] at hr
  obtain rfl : r = { r₁ with complete := true } := by
    rcases Delivery.mem_map_replace' hr with h' | ⟨-, hne⟩
    · exact h'
    · simp [hpath] at hne
  -- The owner, the endpoint and its settlement are those `closeRun` read.
  obtain rfl : owner₁ = o := Option.some.inj (howner₁.symm.trans ho)
  obtain rfl : output = output₁ := by
    rw [designatedOutput_congr (r := r₁) (r' := { r₁ with complete := true }) rfl rfl,
      designatedOutput_kept K wk' hout₁] at hout
    exact (Except.ok.inj hout).symm
  obtain rfl : x = x₁ := by
    have hx' : t.settled? r₁.path output = some x := hx
    rw [K.settled? hx₁] at hx'
    exact (Option.some.inj hx').symm
  show match r₁.task with
    | none => ∃ i, t.invocation? owner₁ = some i ∧ i.status = closedStatus x.outcome ∧
        (x.outcome = .normal → ∃ res ∈ t.resultsOf r₁.path output, returnedResult i res.value ∈ t.results)
    | some name => ∃ e ts, t.execution? owner₁ = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
        ts.status = closedTaskStatus x.outcome ∧
        (x.outcome = .normal → ∃ res ∈ t.resultsOf r₁.path output,
          ∃ tr ∈ t.taskResults, tr.execution = owner₁ ∧ tr.task = name ∧ tr.index = 0 ∧ tr.value = res.value)
  -- The value handed back is the one result of the endpoint.
  have head : ∀ v, ((s.resultsOf r₁.path output).head?).map (·.value) = some v →
      ∃ res ∈ t.resultsOf r₁.path output, res.value = v := by
    intro v hv
    obtain ⟨res, hres, hresv⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hres
    have hmem : res ∈ s.resultsOf r₁.path output := by rw [hrest]; exact List.mem_cons_self
    obtain ⟨hm, hrr, hrp⟩ := Delivery.mem_resultsOf.mp hmem
    exact ⟨res, Delivery.mem_resultsOf.mpr ⟨K.mem_results hm, hrr, hrp⟩, hresv⟩
  rcases hcases with ⟨htask, i₁, hi₁, hcase⟩ | ⟨name, e₁, ts₁, htask, he₁, hts₁, hcase⟩
  · rw [htask]
    have hlook : ∀ st, t.invocations = (s.setInvocation { i₁ with status := st }).invocations →
        t.invocation? owner₁ = some { i₁ with status := st } := fun st ht => by
      rw [invocation?_congr ht]
      exact invocation?_setInvocation_of hi₁ st
    rcases hcase with ⟨hxo, v, hv, -, ht⟩ | ⟨hxo, ht⟩ | ⟨hxo, ht⟩ | ⟨hxo, ht⟩
    · refine ⟨_, hlook .succeeded (by subst ht; rfl), by rw [hxo]; rfl, fun _ => ?_⟩
      obtain ⟨res, hres, rfl⟩ := head v hv
      refine ⟨res, hres, ?_⟩
      subst ht
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ⟨_, hlook .skipped (by subst ht; rfl), by rw [hxo]; rfl, fun h' => by rw [hxo] at h'; cases h'⟩
    · exact ⟨_, hlook .failed (by subst ht; rfl), by rw [hxo]; rfl, fun h' => by rw [hxo] at h'; cases h'⟩
    · exact ⟨_, hlook .upstreamFailed (by subst ht; rfl), by rw [hxo]; rfl, fun h' => by rw [hxo] at h'; cases h'⟩
  · rw [htask]
    obtain ⟨-, he₁id⟩ := execution?_eq_some he₁
    have hlook : ∀ st, t.executions = (s.setTask e₁ { ts₁ with status := st }).executions →
        t.execution? owner₁ = some (withTask e₁ { ts₁ with status := st }) := fun st ht => by
      rw [execution?_congr ht]
      exact execution?_setTask_of he₁ _
    have hfind : ∀ st, (withTask e₁ { ts₁ with status := st }).tasks.find? (·.name == name) =
        some { ts₁ with status := st } := fun st => find?_withTask hts₁ rfl
    rcases hcase with ⟨hxo, v, hv, -, ht⟩ | ⟨hxo, ht⟩ | ⟨hxo, ht⟩ | ⟨hxo, ht⟩
    · refine ⟨_, _, hlook .succeeded (by subst ht; rfl), hfind .succeeded, by rw [hxo]; rfl, fun _ => ?_⟩
      obtain ⟨res, hres, rfl⟩ := head v hv
      refine ⟨res, hres, { execution := e₁.id, task := name, index := 0, value := res.value }, ?_, he₁id, rfl, rfl,
        rfl⟩
      subst ht
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ⟨_, _, hlook .skipped (by subst ht; rfl), hfind .skipped, by rw [hxo]; rfl,
        fun h' => by rw [hxo] at h'; cases h'⟩
    · exact ⟨_, _, hlook .failed (by subst ht; rfl), hfind .failed, by rw [hxo]; rfl,
        fun h' => by rw [hxo] at h'; cases h'⟩
    · exact ⟨_, _, hlook .upstreamFailed (by subst ht; rfl), hfind .upstreamFailed, by rw [hxo]; rfl,
        fun h' => by rw [hxo] at h'; cases h'⟩

/-- Closed runs: an old one keeps its owner's record (`Delivery.frozen`, `step_frozen`) and its
    results, and a new one was just closed; the root run has no owner. -/
theorem stable_run_step (valid : p.validate = .ok ()) (h : Reachable p s) {t : State} {op : Op}
    (hs : step p s op = .ok t) (ih : Stable p s) :
    ∀ r ∈ t.runs, r.complete = true → ∀ o output x, r.owner = some o → t.designatedOutput p r = .ok output →
      t.settled? r.path output = some x →
      match r.task with
      | none => ∃ i, t.invocation? o = some i ∧ i.status = closedStatus x.outcome ∧
          (x.outcome = .normal → ∃ res ∈ t.resultsOf r.path output, returnedResult i res.value ∈ t.results)
      | some name => ∃ e ts, t.execution? o = some e ∧ e.tasks.find? (·.name == name) = some ts ∧
          ts.status = closedTaskStatus x.outcome ∧
          (x.outcome = .normal → ∃ res ∈ t.resultsOf r.path output,
            ∃ tr ∈ t.taskResults, tr.execution = o ∧ tr.task = name ∧ tr.index = 0 ∧ tr.value = res.value) := by
  have inv := Delivery.Reachable.inv h
  have wk' := step_wellKeyed inv.wk hs
  have K := inv.kept hs
  have ht : Reachable p t := .step op h hs
  intro r hr hc o output x ho hout hx
  rcases run_complete_cases (Delivery.runs_nil_or_started inv) hs hr hc with ⟨r₀, hr₀, hpath, hc₀⟩ | hop |
      ⟨-, hroot⟩
  · -- The run was complete before, and a complete run is unchanged.
    obtain ⟨r', hr', a1, a2, a3, a4, a5, a6⟩ := K.run r₀ hr₀
    have hr₀t : r₀ ∈ t.runs := by
      rw [← run_ext a1 a2 a3 a4 a5 ((a6 hc₀).trans hc₀.symm)]
      exact hr'
    have hrr : r = r₀ := wk'.run_eq_of_path hr hr₀t hpath.symm
    rw [hrr] at ho hout hx ⊢
    clear hrr hr hc
    obtain ⟨out₀, hout₀⟩ := designatedOutput_exists inv hr₀ ho
    obtain rfl : output = out₀ := by
      rw [designatedOutput_kept K wk' hout₀] at hout
      exact (Except.ok.inj hout).symm
    -- A complete run settles nothing more.
    have hx₀ : s.settled? r₀.path output = some x := by
      obtain ⟨hxm, hxr, hxp⟩ := settled?_eq_some hx
      rcases Delivery.step_settled_back hs x hxm with hx' | ⟨-, -, run, -, -, -, -, -, hrun, hrc, -⟩
      · have := inv.wk.settled?_of_mem hx'
        rwa [hxr, hxp] at this
      · have hrun' : s.run? r₀.path = some run := hxr ▸ hrun
        rw [inv.wk.run?_of_mem hr₀] at hrun'
        obtain rfl := Option.some.inj hrun'
        rw [hc₀] at hrc
        cases hrc
    have hih := ih.run r₀ hr₀ hc₀ o output x ho hout₀ hx₀
    revert hih
    cases r₀.task with
    | none =>
      intro hih
      obtain ⟨i, hi, hst, hnorm⟩ := hih
      have hna : i.status ≠ .active := by rw [hst]; cases x.outcome <;> simp [closedStatus]
      obtain ⟨him, hiid⟩ := invocation?_eq_some hi
      obtain ⟨i', hi', hid', -⟩ := K.invocation i him
      rw [Delivery.frozen inv hs him hna hi' hid'] at hi'
      refine ⟨i, by rw [← hiid]; exact wk'.invocation?_of_mem hi', hst, fun hn => ?_⟩
      obtain ⟨res, hres, hret⟩ := hnorm hn
      obtain ⟨hres, hrr, hrp⟩ := Delivery.mem_resultsOf.mp hres
      exact ⟨res, Delivery.mem_resultsOf.mpr ⟨K.mem_results hres, hrr, hrp⟩, K.mem_results hret⟩
    | some name =>
      intro hih
      obtain ⟨e, ts, he, hts, hst, hnorm⟩ := hih
      have hend : ts.status.ended = true := by rw [hst]; cases x.outcome <;> rfl
      obtain ⟨hem, heid⟩ := execution?_eq_some he
      obtain ⟨-, -, -, hf4, -, -, -, -⟩ := step_frozen valid h hs
      obtain ⟨e', he', he'id, hts'⟩ := hf4 e hem ts (List.mem_of_find?_eq_some hts) hend
      have hname := Delivery.find?_name_of_task hts
      refine ⟨e', ts, by rw [← heid, ← he'id]; exact wk'.execution?_of_mem he',
        find?_eq_some_of_nodup (Reachable.taskNames valid ht e' he') hts' (fun y => by simp [hname]), hst,
        fun hn => ?_⟩
      obtain ⟨res, hres, tr, htr, h1, h2, h3, h4⟩ := hnorm hn
      obtain ⟨hres, hrr, hrp⟩ := Delivery.mem_resultsOf.mp hres
      obtain ⟨tr', htr', b1, b2, b3, b4⟩ := step_valuesKept inv.wk hs tr htr
      exact ⟨res, Delivery.mem_resultsOf.mpr ⟨K.mem_results hres, hrr, hrp⟩, tr', htr', b1.trans h1, b2.trans h2,
        b3.trans h3, b4.trans h4⟩
  · rw [hop] at hs
    exact stable_run_close K wk' hs hr rfl ho hout hx
  · -- `conclude` completes the root run, which has no owner.
    exfalso
    rcases (Delivery.Reachable.inv ht).own.runs r hr with ⟨ho', -, -⟩ | ⟨-, i, -, -, hp, -⟩ |
        ⟨name, -, e, -, -, hp, -⟩
    · rw [ho] at ho'
      cases ho'
    · rw [hroot] at hp
      exact Key.child_ne_nil _ hp.symm
    · rw [hroot] at hp
      exact Key.child_ne_nil _ hp.symm

end StableAux

/-- Any reachable state of a valid definition. Suggested proof: induction; at the recording step
    `Stable` holds by construction, and every later step keeps the view of the rule (`step_frozen`,
    then `settleOutcome_congr` for settlements). -/
theorem Reachable.stable (valid : p.validate = .ok ()) (h : Reachable p s) : Stable p s := by
  induction h with
  | empty => exact ⟨fun _ hx => (nomatch hx), fun _ he => (nomatch he), fun _ hr => (nomatch hr)⟩
  | step op hr hs ih =>
    exact ⟨StableAux.stable_settled_step hr hs ih, StableAux.stable_execution_step valid hr hs ih,
      StableAux.stable_run_step valid hr hs ih⟩

end StableSection

end Suimon.Round3
