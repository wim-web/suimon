import Suimon.Theorems.Round3.Covers

namespace Suimon.Round3
open State

/-! ## Helpers for [21] Round3/CoversView.lean — task F3: invariants of reachable states

Three invariants that the view agreement needs and the earlier layers do not state:

* `ArmedKeys`: a result with an arm is the result a judge call accepted at index 0 (§7.1).
* `TaskResultShape`: a task result belongs to a task of an existing execution; a transformed output
  belongs to a task in the concurrency output; a result of a task without a function body is the
  index-0 result of its run, whose task succeeded (§8.1, §8.3, §4.5).
* `TaskStatusInv`: a succeeded task without a function body has its index-0 result, and a task that
  failed without ever starting its body failed its declared input transform (§8.1). -/

namespace CoversViewAux

variable {p : Definition}

/-! ### Identities -/

/-- Task identities name their execution and task. -/
theorem task_inj {a b m n : String} (h : Key.task a m = Key.task b n) : a = b ∧ m = n := Key.task_inj h

/-- An invocation identity is never a task identity (distinct tags). -/
theorem invocation_ne_task {a : Path} {m b n : String} {tr : Option String} :
    Key.invocation a m tr ≠ Key.task b n :=
  Key.ne_of_kind? (by simp)

/-! ### Results with an arm -/

/-- Only a judge gives a result an arm, at index 0 of its call: a result with an arm is identified by
    its producing call, which belongs to an invocation (§7.1). -/
def ArmedKeys (s : State) : Prop :=
  ∀ r ∈ s.results, r.arm ≠ none →
    r.id = Key.callResult r.producer 0 ∧ ∃ c ∈ s.calls, c.id = r.producer ∧ c.task = none

/-- A result a step adds with an arm is the result `judged` accepts. -/
theorem step_armed {s t : State} {op : Op} (hs : step p s op = .ok t) {r : Result}
    (hr : r ∈ t.results) (hnew : r ∉ s.results) (harm : r.arm ≠ none) :
    r.id = Key.callResult r.producer 0 ∧ ∃ c ∈ s.calls, c.id = r.producer ∧ c.task = none := by
  have keep : t.results = s.results → False := fun h => hnew (h ▸ hr)
  have added : ∀ {x : Result}, t.results = s.results ++ [x] → r = x := fun h => by
    rw [h, List.mem_append, List.mem_singleton] at hr
    exact hr.resolve_left hnew
  -- `accept` without an arm adds a result without one.
  have plain : ∀ {c : Call} {index : Nat} {value : Value} {s' : State},
      s.accept c index value = .ok s' → t.results = s'.results → False := by
    intro c index value s' ha ht
    rcases accept_eq_ok.mp ha with ⟨-, i, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact harm (by rw [added ht])
    · exact keep ht
  have failed : ∀ {c : Call} {status : CallStatus} {cause : Cause}, s.failCall c status cause = .ok t → False := by
    intro c status cause h
    obtain ⟨_, _, -, hso, rfl⟩ := failCall_eq_ok.mp h
    exact keep (by simp [(settleOwner_update hso).results])
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact (keep rfl).elim
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;>
      exact (keep rfl).elim
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact (keep rfl).elim
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact (plain hacc (by rw [(settleOwner_update hso).results, setCall_results])).elim
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, htask, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    rcases accept_eq_ok.mp hacc with ⟨-, i, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · obtain rfl := added (by rw [setInvocation_results, setCall_results])
      exact ⟨rfl, c, (call?_eq_some hc).1, rfl, htask⟩
    · exact (keep (by rw [setInvocation_results, setCall_results])).elim
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact (plain hacc (by rw [setCall_results])).elim
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact (keep (by rw [(settleOwner_update hso).results, setCall_results])).elim
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact (failed h).elim
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact (failed h).elim
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact (failed h).elim
    · exact (keep (by rw [(cancelOwner_update h).results, setCall_results])).elim
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact (keep (by rw [(cancelOwner_update h).results, setCall_results])).elim
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact (keep rfl).elim
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact (keep (by simp)).elim
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact (keep (by simp)).elim
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact (keep (by simp)).elim
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact (keep (by simp)).elim
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact (harm (by rw [added rfl])).elim
    · exact (keep (by simp)).elim
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact (keep (by simp)).elim
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, hout, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact (keep rfl).elim
    · obtain rfl := added rfl
      exact (harm ((settleOutcome_some hout).2.2.2 r rfl).2.2.2.2.2.1).elim
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact (keep (by simp)).elim
    · exact (harm (by rw [added rfl])).elim
    · exact (keep (by simp)).elim
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (harm (by rw [added rfl])).elim
      all_goals exact (keep (by simp)).elim
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact (keep (by simp)).elim
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact (keep (by simp)).elim
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact (keep (by simp)).elim

/-- `ArmedKeys` holds in every reachable state: calls are never removed and keep their identity and
    task. -/
theorem reachable_armedKeys {s : State} (h : Reachable p s) : ArmedKeys s := by
  induction h with
  | empty => intro r hr; cases hr
  | @step s t op hr hs ih =>
    have K := (Delivery.Reachable.inv hr).kept hs
    intro x hx harm
    by_cases hold : x ∈ s.results
    · obtain ⟨hid, c, hc, hcid, htask⟩ := ih x hold harm
      obtain ⟨c', hc', a1, -, a3, -⟩ := K.call c hc
      exact ⟨hid, c', hc', a1.trans hcid, a3.trans htask⟩
    · obtain ⟨hid, c, hc, hcid, htask⟩ := step_armed hs hx hold harm
      obtain ⟨c', hc', a1, -, a3, -⟩ := K.call c hc
      exact ⟨hid, c', hc', a1.trans hcid, a3.trans htask⟩

/-! ### Task results -/

/-- A task stored by `setTask` is a task of the updated execution. -/
theorem mem_withTask_self {e : Execution} {ts ts' : TaskState} (hts : ts ∈ e.tasks) (hname : ts'.name = ts.name) :
    ts' ∈ (withTask e ts').tasks := by
  rw [withTask_tasks]
  exact List.mem_map.mpr ⟨ts, hts, by simp [hname]⟩

/-- What a task result says about its task (§8.1, §8.3, §4.5): its execution exists and declares the
    task; a transformed output belongs to a task in the output; a result of a task without a function
    body is the index-0 result of its run, recorded when the task succeeded. -/
def TaskResultShape (p : Definition) (s : State) (tr : TaskResult) : Prop :=
  ∃ e ∈ s.executions, e.id = tr.execution ∧ ∃ spec, s.taskSpec p e tr.task = .ok spec ∧
    (tr.output ≠ .pending → spec.output.isSome = true) ∧
    ((∃ f, spec.body = .function f) ∨ (tr.index = 0 ∧ ∃ ts ∈ e.tasks, ts.name = tr.task ∧ ts.status = .succeeded))

/-- The shape carries over a step to a task result under the same key that is transformed only if the
    old one was: executions and their specs stay, and so do ended tasks (`step_frozen`). -/
theorem TaskResultShape.step (valid : p.validate = .ok ()) {s t : State} {op : Op} (hreach : Reachable p s)
    (hs : step p s op = .ok t) {tr tr' : TaskResult} (h : TaskResultShape p s tr)
    (h1 : tr'.execution = tr.execution) (h2 : tr'.task = tr.task) (h3 : tr'.index = tr.index)
    (hout : tr'.output ≠ .pending → tr.output ≠ .pending) : TaskResultShape p t tr' := by
  obtain ⟨e, he, heid, spec, hspec, hso, hbody⟩ := h
  have K := (Delivery.Reachable.inv hreach).kept hs
  have wk' := step_wellKeyed hreach.wellKeyed hs
  obtain ⟨e', he', a1, a2, a3, -, -⟩ := K.execution e he
  refine ⟨e', he', a1.trans (heid.trans h1.symm), spec, ?_, fun ho => hso (hout ho), ?_⟩
  · rw [h2]; exact K.taskSpec wk' a2 a3 hspec
  · rcases hbody with hf | ⟨hidx, ts, hts, hn, hst⟩
    · exact Or.inl hf
    · refine Or.inr ⟨h3.trans hidx, ts, ?_, hn.trans h2.symm, hst⟩
      obtain ⟨e'', he'', hid'', hts''⟩ := (step_frozen valid hreach hs).2.2.2.1 e he ts hts (by rw [hst]; rfl)
      obtain rfl := wk'.execution_eq_of_id he'' he' (hid''.trans a1.symm)
      exact hts''

/-- `TaskResultShape` holds for every task result of a reachable state. -/
theorem reachable_taskResultShape (valid : p.validate = .ok ()) {s : State} (h : Reachable p s) :
    ∀ tr ∈ s.taskResults, TaskResultShape p s tr := by
  induction h with
  | empty => intro tr htr; cases htr
  | @step s t op hr hs ih =>
    have own := (Settle.reachable hr).1
    have wk := hr.wellKeyed
    have K := (Delivery.Reachable.inv hr).kept hs
    have wk' := step_wellKeyed wk hs
    have old : ∀ {x : TaskResult}, x ∈ s.taskResults → TaskResultShape p t x :=
      fun hx => (ih _ hx).step valid hr hs rfl rfl rfl id
    have same : t.taskResults = s.taskResults → ∀ x ∈ t.taskResults, TaskResultShape p t x :=
      fun ht x hx => old (ht ▸ hx)
    -- A value accepted from a task call: the call's task has a function body.
    have accepted : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
        c ∈ s.calls → s.accept c index value arm = .ok s' → t.taskResults = s'.taskResults →
        ∀ x ∈ t.taskResults, TaskResultShape p t x := by
      intro c index value arm s' hc hacc ht x hx
      rw [ht] at hx
      rcases Delivery.accept_taskResults hacc with h' | ⟨name, hn, h'⟩
      · exact old (h' ▸ hx)
      · rw [h', List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact old hx
        · obtain ⟨-, e, he, heid, spec, f, hspec, hf⟩ := own.callTask c hc name hn
          exact TaskResultShape.step valid hr hs ⟨e, he, heid, spec, hspec, fun h => absurd rfl h, Or.inl ⟨f, hf⟩⟩
            rfl rfl rfl id
    -- The output transform of a pending result of a task in the output.
    have transformed : ∀ {r₀ : TaskResult} {o : TaskOutput} {e₀ : Execution} {spec₀ : TaskSpec},
        r₀ ∈ s.taskResults → s.execution? r₀.execution = some e₀ → s.taskSpec p e₀ r₀.task = .ok spec₀ →
        spec₀.output.isSome = true → t.taskResults = (s.setTaskResult { r₀ with output := o }).taskResults →
        ∀ x ∈ t.taskResults, TaskResultShape p t x := by
      intro r₀ o e₀ spec₀ hr₀ he₀ hspec₀ hout₀ ht x hx
      rw [ht] at hx
      rcases mem_setTaskResult_taskResults hx with rfl | hx
      · obtain ⟨e, he, heid, spec, hspec, -, hbody⟩ := ih r₀ hr₀
        obtain ⟨he₀m, he₀id⟩ := execution?_eq_some he₀
        obtain rfl := wk.execution_eq_of_id he₀m he (he₀id.trans heid.symm)
        rw [hspec₀] at hspec
        cases hspec
        have hshape : TaskResultShape p s { r₀ with output := o } :=
          ⟨e₀, he, heid, spec₀, hspec₀, fun _ => hout₀, hbody⟩
        exact hshape.step valid hr hs rfl rfl rfl id
      · exact old hx
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
      obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
      exact accepted (call?_eq_some hc).1 hacc (by rw [(settleOwner_update hso).taskResults, setCall_taskResults])
    | judged id arm =>
      obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
      exact accepted (call?_eq_some hc).1 hacc (by rw [setInvocation_taskResults, setCall_taskResults])
    | yielded id value =>
      obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
      exact accepted (call?_eq_some hc).1 hacc (by rw [setCall_taskResults])
    | ended id =>
      obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
      exact same (by rw [(settleOwner_update hso).taskResults, setCall_taskResults])
    | failed id =>
      obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
      exact same (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
    | timedOut id element =>
      obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
      exact same (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
    | lost id =>
      obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
      · exact same (Delivery.failCall_old (call?_eq_some hc).1 (by simp) h).2.2.2.2.1
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
      obtain ⟨-, -, e₀, _, spec₀, r₀, he₀, -, hspec₀, hout₀, hr₀, -, h⟩ := Step.taskOutput_inv hs
      have hk : (r₀.execution = eid ∧ r₀.task = name) ∧ r₀.index = index := by simpa using List.find?_some hr₀
      refine transformed (o := .value value) (List.mem_of_find?_eq_some hr₀) (by rw [hk.1.1]; exact he₀)
        (by rw [hk.1.2]; exact hspec₀) hout₀ ?_
      rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    | taskOutputFailed eid name index =>
      obtain ⟨-, -, e₀, spec₀, r₀, he₀, hspec₀, hout₀, hr₀, -, rfl⟩ := Step.taskOutputFailed_inv hs
      have hk : (r₀.execution = eid ∧ r₀.task = name) ∧ r₀.index = index := by simpa using List.find?_some hr₀
      exact transformed (o := .failed) (List.mem_of_find?_eq_some hr₀) (by rw [hk.1.1]; exact he₀)
        (by rw [hk.1.2]; exact hspec₀) hout₀ (by simp)
    | settle path name =>
      obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
      rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
    | closeExecution eid =>
      obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
      rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same rfl
    | closeRun path =>
      obtain ⟨-, -, r, _, output, _, owner, hr', -, -, -, -, hout, -, howner, h⟩ := Step.closeRun_inv hs
      rcases h with ⟨-, _, -, h⟩ | ⟨name, e, ts, htask, he, hts, h⟩
      · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
      · rcases h with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact old hx
          · -- The index-0 result of the closed task run: the task succeeds in the same step.
            obtain ⟨hem, heid⟩ := execution?_eq_some he
            obtain ⟨owner', howner', hcase⟩ := designatedOutput_eq_ok.mp hout
            rw [howner] at howner'
            cases howner'
            rcases hcase with ⟨htask', -⟩ | ⟨name', e', spec, wf, htask', he', hspec, -⟩
            · rw [htask] at htask'; cases htask'
            rw [htask] at htask'
            cases htask'
            rw [he] at he'
            cases he'
            have hname := Delivery.find?_name_of_task hts
            refine ⟨withTask e { ts with status := .succeeded }, ?_, rfl, spec, ?_, fun h => absurd rfl h,
              Or.inr ⟨rfl, { ts with status := .succeeded },
                mem_withTask_self (List.mem_of_find?_eq_some hts) rfl, hname, rfl⟩⟩
            · exact Delivery.mem_setTask_self (s := s.setRun { r with complete := true }) hem
            · exact K.taskSpec wk' rfl rfl hspec
        all_goals exact same rfl
    | cancel =>
      obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
    | conclude =>
      obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-! ### Task statuses -/

/-- How a changed task may move: it keeps its status, waits, takes its input, begins, fails its declared
    input transform, or is moved by its call or its run; a run that closes normally records the index-0
    result in `results`. -/
def TaskMove (p : Definition) (s : State) (results : List TaskResult) (e₀ : Execution) (tk₀ tk : TaskState) : Prop :=
  tk.status = tk₀.status ∨ tk.status = .notStarted ∨ tk.status = .ready ∨ tk.status = .active ∨
  (tk.status = .failed ∧ ∃ spec tid, s.taskSpec p e₀ tk.name = .ok spec ∧ spec.input = some (.declared tid)) ∨
  (∃ c ∈ s.calls, c.owner = e₀.id ∧ c.task = some tk.name) ∨
  (∃ R ∈ s.runs, R.owner = some e₀.id ∧ R.task = some tk.name ∧
    (tk.status = .succeeded → ∃ tr ∈ results, tr.execution = e₀.id ∧ tr.task = tk.name ∧ tr.index = 0))

/-- Where a task after a step comes from: a task of a new execution, which waits, or a task of a stored
    execution under the same name that moved as `TaskMove` allows. -/
def TaskOrigin (p : Definition) (s : State) (results : List TaskResult) (e : Execution) (tk : TaskState) : Prop :=
  (s.execution? e.id = none ∧ (tk.status = .pending ∨ tk.status = .ready ∨ tk.status = .notStarted)) ∨
  ∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.run = e.run ∧ e₀.placement = e.placement ∧
    ∃ tk₀ ∈ e₀.tasks, tk₀.name = tk.name ∧ TaskMove p s results e₀ tk₀ tk

section Origin
variable {s u : State} {results : List TaskResult}

/-- A task of a stored execution is its own origin. -/
theorem origin_self {e : Execution} (he : e ∈ s.executions) {tk : TaskState} (htk : tk ∈ e.tasks) :
    TaskOrigin p s results e tk :=
  Or.inr ⟨e, he, rfl, rfl, rfl, tk, htk, rfl, Or.inl rfl⟩

/-- A step that keeps the executions keeps every task. -/
theorem origin_of_executions (hu : u.executions = s.executions) :
    ∀ e ∈ u.executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk :=
  fun _ he _ htk => origin_self (hu ▸ he) htk

/-- The stop moves waiting tasks to `notStarted` and keeps the others. -/
theorem origin_stop (h : ∀ e ∈ u.executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk) :
    ∀ e ∈ u.stop.executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk := by
  intro e he tk htk
  obtain ⟨e', he', rfl⟩ := mem_stop_executions.mp he
  simp only [stopExecution, List.mem_map] at htk
  obtain ⟨tk', htk', rfl⟩ := htk
  have ho := h e' he' tk' htk'
  split
  · rcases ho with ⟨hnew, -⟩ | ⟨e₀, he₀, h1, h2, h3, tk₀, htk₀, hn, -⟩
    · exact Or.inl ⟨hnew, Or.inr (Or.inr rfl)⟩
    · exact Or.inr ⟨e₀, he₀, h1, h2, h3, tk₀, htk₀, hn, Or.inr (Or.inl rfl)⟩
  · rcases ho with ⟨hnew, hst⟩ | ⟨e₀, he₀, h1, h2, h3, tk₀, htk₀, hn, hmove⟩
    · exact Or.inl ⟨hnew, hst⟩
    · exact Or.inr ⟨e₀, he₀, h1, h2, h3, tk₀, htk₀, hn, hmove⟩

/-- Recording a failure stops or keeps the tasks. -/
theorem origin_fail {f : Failure} {policy : Policy}
    (h : ∀ e ∈ u.executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk) :
    ∀ e ∈ (u.fail f policy).executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk := by
  cases policy
  · rw [fail_stop]
    exact origin_stop (u := { u with failures := u.failures ++ [f] }) h
  · rw [fail_continue]
    exact h

/-- One task of a stored execution is replaced; the other tasks keep their status. -/
theorem origin_setTask {e₁ : Execution} {ts ts' : TaskState} (hu : u.executions = s.executions)
    (he₁ : e₁ ∈ s.executions) (hts : ts ∈ e₁.tasks) (hname : ts'.name = ts.name)
    (hmove : TaskMove p s results e₁ ts ts') :
    ∀ e ∈ (u.setTask e₁ ts').executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk := by
  intro e he tk htk
  rcases mem_setTask_executions he with rfl | he
  · rcases Delivery.mem_withTask htk with rfl | ⟨htk, -⟩
    · exact Or.inr ⟨e₁, he₁, rfl, rfl, rfl, ts, hts, hname.symm, hmove⟩
    · exact Or.inr ⟨e₁, he₁, rfl, rfl, rfl, tk, htk, rfl, Or.inl rfl⟩
  · exact origin_self (hu ▸ he) htk

/-- A stored execution is replaced by one with the same tasks. -/
theorem origin_setExecution {e₁ e₁' : Execution} (he₁ : e₁ ∈ s.executions) (h1 : e₁'.id = e₁.id)
    (h2 : e₁'.run = e₁.run) (h3 : e₁'.placement = e₁.placement) (htasks : e₁'.tasks = e₁.tasks) :
    ∀ e ∈ (s.setExecution e₁').executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk := by
  intro e he tk htk
  rcases mem_setExecution_executions he with rfl | he
  · exact Or.inr ⟨e₁, he₁, h1.symm, h2.symm, h3.symm, tk, htasks ▸ htk, rfl, Or.inl rfl⟩
  · exact origin_self he htk

/-- The owner of a call settles: an invocation, or the call's task. -/
theorem origin_settleOwner {c : Call} {inv : InvocationStatus} {task : TaskStatus} {u' : State}
    (hu : u.executions = s.executions) (hc : c ∈ s.calls) (ho : u.settleOwner c inv task = .ok u') :
    ∀ e ∈ u'.executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk := by
  rcases settleOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
  · exact origin_of_executions hu
  · obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
    have hname := Delivery.find?_name_of_task hts
    exact origin_setTask hu (hu ▸ he₁m) (List.mem_of_find?_eq_some hts) rfl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, he₁id.symm, by rw [htask, hname]⟩))))))

/-- A terminated call cancels its active owner. -/
theorem origin_cancelOwner {c : Call} {u' : State} (hu : u.executions = s.executions) (hc : c ∈ s.calls)
    (ho : u.cancelOwner c = .ok u') : ∀ e ∈ u'.executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk := by
  rcases cancelOwner_eq_ok.mp ho with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
  · split <;> exact origin_of_executions hu
  · split
    · obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
      have hname := Delivery.find?_name_of_task hts
      exact origin_setTask hu (hu ▸ he₁m) (List.mem_of_find?_eq_some hts) rfl
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, he₁id.symm, by rw [htask, hname]⟩))))))
    · exact origin_of_executions hu

/-- A failed call fails its owner and may stop the workflow. -/
theorem origin_failCall {c : Call} {status : CallStatus} {cause : Cause} {u' : State} (hc : c ∈ s.calls)
    (hf : s.failCall c status cause = .ok u') : ∀ e ∈ u'.executions, ∀ tk ∈ e.tasks, TaskOrigin p s results e tk := by
  obtain ⟨_, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  exact origin_fail (origin_settleOwner (u := s.setCall { c with status }) rfl hc hso)

end Origin

/-- Every task after a step has an origin before it (`TaskOrigin`). -/
theorem step_taskOrigin {s t : State} {op : Op} (hs : step p s op = .ok t) :
    ∀ e ∈ t.executions, ∀ tk ∈ e.tasks, TaskOrigin p s t.taskResults e tk := by
  have same : t.executions = s.executions → ∀ e ∈ t.executions, ∀ tk ∈ e.tasks, TaskOrigin p s t.taskResults e tk :=
    origin_of_executions
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, input, id, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨c, -, hexec, rfl⟩
    · exact same rfl
    · exact same rfl
    · exact same rfl
    · -- A new execution: its tasks wait for their input or are ready.
      intro e he tk htk
      rcases List.mem_append.mp he with he | he
      · exact origin_self he htk
      · rw [List.mem_singleton] at he
        subst he
        simp only [List.mem_map] at htk
        obtain ⟨ts, -, rfl⟩ := htk
        refine Or.inl ⟨hexec, ?_⟩
        split
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact origin_settleOwner (by rw [setCall_executions]; exact (accept_frame hacc).2.2.2.2.2.2.1)
      (call?_eq_some hc).1 hso
  | judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact same (by rw [setInvocation_executions, setCall_executions]; exact (accept_frame hacc).2.2.2.2.2.2.1)
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by rw [setCall_executions]; exact (accept_frame hacc).2.2.2.2.2.2.1)
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    exact origin_settleOwner (by rw [setCall_executions]) (call?_eq_some hc).1 hso
  | failed id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.failed_inv hs
    exact origin_failCall (call?_eq_some hc).1 h
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.timedOut_inv hs
    exact origin_failCall (call?_eq_some hc).1 h
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact origin_failCall (call?_eq_some hc).1 h
    · exact origin_cancelOwner (by rw [setCall_executions]) (call?_eq_some hc).1 h
  | terminated id =>
    obtain ⟨-, -, c, hc, -, h⟩ := Step.terminated_inv hs
    exact origin_cancelOwner (by rw [setCall_executions]) (call?_eq_some hc).1 h
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact origin_fail (origin_of_executions rfl)
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, hts, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact origin_setTask rfl (execution?_eq_some he).1 (List.mem_of_find?_eq_some hts) rfl
      (Or.inr (Or.inr (Or.inl rfl)))
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, hts, -, hspec, hin, rfl⟩ := Step.taskInputFailed_inv hs
    have hname := Delivery.find?_name_of_task hts
    exact origin_fail (origin_setTask rfl (execution?_eq_some he).1 (List.mem_of_find?_eq_some hts) rfl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, spec, tid, by rw [show ({ ts with status := .failed } : TaskState).name = name from hname]; exact hspec, hin⟩))))))
  | beginTask eid name =>
    obtain ⟨-, -, e, _, ts, _, he, -, -, hts, -, -, -, h⟩ := Step.beginTask_inv hs
    have hmove := origin_setTask (p := p) (u := s) (results := t.taskResults) rfl (execution?_eq_some he).1
      (List.mem_of_find?_eq_some hts) (ts' := { ts with status := .active }) rfl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact hmove
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact origin_fail (origin_of_executions rfl)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    have hmove := origin_setExecution (p := p) (results := t.taskResults) (execution?_eq_some he).1
      (e₁' := { e with complete := true }) rfl rfl rfl rfl
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact hmove
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, -, -, -, -, -, -, howner, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨name, e, ts, htask, he, hts, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
    · obtain ⟨hem, heid⟩ := execution?_eq_some he
      have hname := Delivery.find?_name_of_task hts
      have hR : r ∈ s.runs := (run?_eq_some hr).1
      have hRo : r.owner = some e.id := by rw [howner, heid]
      -- The task of the closed run moves; after a normal end its index-0 result is recorded.
      have key : ∀ {st : TaskStatus} {u : State}, u.executions = ((s.setRun { r with complete := true }).setTask e
          { ts with status := st }).executions →
          (st = .succeeded → ∃ tr ∈ u.taskResults, tr.execution = e.id ∧ tr.task = name ∧ tr.index = 0) →
          ∀ e' ∈ u.executions, ∀ tk ∈ e'.tasks, TaskOrigin p s u.taskResults e' tk := by
        intro st u hu hres e' he' tk htk
        rw [hu] at he'
        exact origin_setTask (s := s) (u := s.setRun { r with complete := true }) (results := u.taskResults)
          (ts' := { ts with status := st }) rfl hem
          (List.mem_of_find?_eq_some hts) rfl
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, hR, hRo, by simp [htask, hname], fun hst => by
            obtain ⟨tr, htr, h1, h2, h3⟩ := hres hst
            exact ⟨tr, htr, h1, h2.trans hname.symm, h3⟩⟩))))))
          e' he' tk htk
      rcases h with ⟨-, v, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact key rfl fun _ => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
      · exact key rfl fun h => by cases h
      · exact key rfl fun h => by cases h
      · exact key rfl fun h => by cases h
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact origin_stop (fun e he tk htk => origin_self he htk)
    · exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-! ### What a step keeps about tasks -/

/-- The workflow of an existing run does not change. -/
theorem workflow?_step {s t : State} {op : Op} (h : Reachable p s) (hs : step p s op = .ok t) {path : Path}
    (hr : (s.run? path).isSome) : t.workflow? p path = s.workflow? p path := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨r', hr', hwf, -⟩ := ((Delivery.Reachable.inv h).kept hs).run? (step_wellKeyed h.wellKeyed hs) hr
  unfold State.workflow?
  rw [hr, hr']
  simp [hwf]

/-- The spec of a task depends only on the workflow of the execution's run and its placement. -/
theorem taskSpec_eq_of_workflow? {s t : State} {e e' : Execution} {name : String}
    (hw : t.workflow? p e'.run = s.workflow? p e.run) (hpl : e'.placement = e.placement) :
    t.taskSpec p e' name = s.taskSpec p e name := by
  unfold State.taskSpec State.concurrencyOf State.placementOf
  rw [hw, hpl]

/-- A task spec after a step is the one before it, for an execution in the same place. -/
theorem taskSpec_back {s t : State} {op : Op} (h : Reachable p s) (hs : step p s op = .ok t) {e₀ e : Execution}
    (he₀ : e₀ ∈ s.executions) (hrun : e₀.run = e.run) (hpl : e₀.placement = e.placement) (name : String) :
    t.taskSpec p e name = s.taskSpec p e₀ name := by
  refine taskSpec_eq_of_workflow? ?_ hpl.symm
  rw [← hrun]
  exact workflow?_step h hs ((Limit.reachable_inv h).execRuns e₀ he₀)

/-- A task that has not begun after a step had not begun before it: calls and runs stay. -/
theorem notBegun_back {s t : State} {op : Op} (h : Reachable p s) (hs : step p s op = .ok t) {e₀ e : Execution}
    (hid : e₀.id = e.id) {name : String} (hnb : NotBegun t e name) : NotBegun s e₀ name := by
  have K := (Delivery.Reachable.inv h).kept hs
  have wk' := step_wellKeyed h.wellKeyed hs
  refine ⟨?_, fun r hr ⟨ho, htask⟩ => ?_⟩
  · cases hc : s.call? (Key.task e₀.id name) with
    | none => rfl
    | some c =>
      obtain ⟨hcm, hcid⟩ := call?_eq_some hc
      obtain ⟨c', hc', a1, -⟩ := K.call c hcm
      have := wk'.call?_of_mem hc'
      rw [a1, hcid, hid, hnb.1] at this
      cases this
  · obtain ⟨r', hr', -, -, -, a4, a5, -⟩ := K.run r hr
    exact hnb.2 r' hr' ⟨by rw [a4, ho, hid], by rw [a5, htask]⟩

/-! ### The task invariant -/

/-- Two facts about tasks (§8.1, §4.5): a succeeded task without a function body has the index-0 result
    of its run, and a task that failed without ever starting its body failed its declared input
    transform. -/
structure TaskStatusInv (p : Definition) (s : State) : Prop where
  succeeded : ∀ e ∈ s.executions, ∀ ts ∈ e.tasks, ts.status = .succeeded → ∀ spec,
    s.taskSpec p e ts.name = .ok spec → (∀ f, spec.body ≠ .function f) →
    ∃ tr ∈ s.taskResults, tr.execution = e.id ∧ tr.task = ts.name ∧ tr.index = 0
  failed : ∀ e ∈ s.executions, ∀ ts ∈ e.tasks, ts.status = .failed → NotBegun s e ts.name → ∀ spec,
    s.taskSpec p e ts.name = .ok spec → ∃ tid, spec.input = some (.declared tid)

/-- One step keeps `TaskStatusInv`: a task that moved took its status from its call, its run, or its
    failed input transform (`step_taskOrigin`). -/
theorem TaskStatusInv.step {s t : State} {op : Op} (hreach : Reachable p s) (hs : step p s op = .ok t)
    (h : TaskStatusInv p s) : TaskStatusInv p t := by
  have K := (Delivery.Reachable.inv hreach).kept hs
  have wk := hreach.wellKeyed
  have wk' := step_wellKeyed wk hs
  have own := (Settle.reachable hreach).1
  refine ⟨fun e he ts hts hst spec hspec hbody => ?_, fun e he ts hts hst hnb spec hspec => ?_⟩
  · rcases step_taskOrigin hs e he ts hts with ⟨-, hw⟩ | ⟨e₀, he₀, h1, h2, h3, tk₀, htk₀, hn, hmove⟩
    · rw [hst] at hw
      rcases hw with hw | hw | hw <;> cases hw
    have hspec₀ : s.taskSpec p e₀ tk₀.name = .ok spec := by
      rw [hn, ← taskSpec_back hreach hs he₀ h2 h3]; exact hspec
    rcases hmove with heq | hw | hw | hw | ⟨hw, -⟩ | ⟨c, hc, hco, hct⟩ | ⟨R, -, -, -, hres⟩
    · obtain ⟨tr, htr, a1, a2, a3⟩ := h.succeeded e₀ he₀ tk₀ htk₀ (heq.symm.trans hst) spec hspec₀ hbody
      obtain ⟨tr', htr', b1, b2, b3, -⟩ := K.taskResult tr htr
      exact ⟨tr', htr', b1.trans (a1.trans h1), b2.trans (a2.trans hn), b3.trans a3⟩
    · rw [hst] at hw; cases hw
    · rw [hst] at hw; cases hw
    · rw [hst] at hw; cases hw
    · rw [hst] at hw; cases hw
    · -- A task moved by its call has a function body.
      obtain ⟨-, e₂, he₂, he₂id, spec₂, f, hspec₂, hf⟩ := own.callTask c hc ts.name hct
      obtain rfl := wk.execution_eq_of_id he₂ he₀ (he₂id.trans hco)
      rw [← hn, hspec₀] at hspec₂
      cases hspec₂
      exact absurd hf (hbody f)
    · obtain ⟨tr, htr, a1, a2, a3⟩ := hres hst
      exact ⟨tr, htr, a1.trans h1, a2, a3⟩
  · rcases step_taskOrigin hs e he ts hts with ⟨-, hw⟩ | ⟨e₀, he₀, h1, h2, h3, tk₀, htk₀, hn, hmove⟩
    · rw [hst] at hw
      rcases hw with hw | hw | hw <;> cases hw
    have hspec₀ : s.taskSpec p e₀ tk₀.name = .ok spec := by
      rw [hn, ← taskSpec_back hreach hs he₀ h2 h3]; exact hspec
    rcases hmove with heq | hw | hw | hw | ⟨-, spec', tid, hspec', hin⟩ | ⟨c, hc, hco, hct⟩ | ⟨R, hR, hRo, hRt, -⟩
    · refine h.failed e₀ he₀ tk₀ htk₀ (heq.symm.trans hst) ?_ spec hspec₀
      rw [hn]
      exact notBegun_back hreach hs h1 hnb
    · rw [hst] at hw; cases hw
    · rw [hst] at hw; cases hw
    · rw [hst] at hw; cases hw
    · rw [← hn, hspec₀] at hspec'
      cases hspec'
      exact ⟨tid, hin⟩
    · -- The task's call exists after the step, so the task has begun.
      obtain ⟨hkey, -⟩ := own.callTask c hc ts.name hct
      obtain ⟨c', hc', a1, -⟩ := K.call c hc
      have := wk'.call?_of_mem hc'
      rw [a1, hkey, hco, h1, hnb.1] at this
      cases this
    · obtain ⟨R', hR', -, -, -, a4, a5, -⟩ := K.run R hR
      exact absurd ⟨by rw [a4, hRo, h1], by rw [a5, hRt]⟩ (hnb.2 R' hR')

/-- `TaskStatusInv` holds in every reachable state. -/
theorem reachable_taskStatusInv {s : State} (h : Reachable p s) : TaskStatusInv p s := by
  induction h with
  | empty => exact ⟨(fun _ he => nomatch he), (fun _ he => nomatch he)⟩
  | step op hr hs ih => exact ih.step hr hs

end CoversViewAux

end Suimon.Round3
