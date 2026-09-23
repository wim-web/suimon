import Suimon.Theorems.Round3.RunConformBase

/-! Helpers for [13] Round3/RunConform.lean — task E1: where a task comes from after a step that does
    not stop (`step_taskFrom`). -/

namespace Suimon.Round3
namespace RunConformAux
open State

variable {p : Program} {s t : State} {op : Op}

/-- How a task of an execution after a step that does not stop came to be: a task of a new execution;
    the same task as before, still not begun if it had not; a pending task whose input was transformed
    or failed to transform (without a stop); or a task that began, or whose call or run moved it on. -/
def TaskFrom (p : Program) (s t : State) (op : Op) (e : Execution) (tk : TaskState) : Prop :=
  (e.id ∉ s.executions.map (·.id) ∧ tk.input = none ∧
    ∃ c, t.concurrencyOf p e = .ok c ∧ tk.status = (if c.input.isSome then .pending else .ready)) ∨
  ∃ e₀ ∈ s.executions, e₀.id = e.id ∧ e₀.run = e.run ∧ e₀.placement = e.placement ∧
    ∃ tk₀ ∈ e₀.tasks, tk₀.name = tk.name ∧
      ((tk = tk₀ ∧ (notBegun s e.id tk.name → notBegun t e.id tk.name)) ∨
       (tk₀.status = .pending ∧ tk.status = .ready ∧ op = .taskInput e.id tk.name tk.input ∧
          ∃ spec, s.taskSpec p e₀ tk.name = .ok spec ∧
            ((∃ tid v, spec.input = some (.declared tid) ∧ tk.input = some v) ∨
             (spec.input = some .discard ∧ tk.input = none))) ∨
       (tk₀.status = .pending ∧ tk.status = .failed ∧ tk.input = tk₀.input ∧ op = .taskInputFailed e.id tk.name ∧
          (notBegun s e.id tk.name → notBegun t e.id tk.name) ∧
          ∃ spec tid, s.taskSpec p e₀ tk.name = .ok spec ∧ spec.input = some (.declared tid) ∧
            spec.policy = .continue) ∨
       (tk₀.status ≠ .pending ∧ (tk₀.status = .ready ∨ ¬ notBegun s e.id tk.name) ∧ tk.input = tk₀.input ∧
          tk.status ≠ .pending ∧ tk.status ≠ .ready ∧ ¬ notBegun t e.id tk.name))

/-- A step that does not stop keeps the policy of a failure: a stop policy would have stopped. -/
theorem continue_of_fail {u : State} {f : Failure} {policy : Policy} (ht : t = u.fail f policy)
    (hstop : t.status ≠ .stopping) : policy = .continue := by
  cases policy
  · subst ht; simp at hstop
  · rfl

theorem taskFrom_same (h : Reachable p s) (hs : step p s op = .ok t) {e₀ e : Execution}
    (he₀ : e₀ ∈ s.executions) (he : e ∈ t.executions) (hid : e₀.id = e.id) (hrun : e₀.run = e.run)
    (hpl : e₀.placement = e.placement) {tk : TaskState} (htk₀ : tk ∈ e₀.tasks) (htk : tk ∈ e.tasks) :
    TaskFrom p s t op e tk :=
  Or.inr ⟨e₀, he₀, hid, hrun, hpl, tk, htk₀, rfl,
    Or.inl ⟨rfl, fun hnb => notBegun_keep h hs he₀ he hid.symm htk₀ htk rfl rfl (hid ▸ hnb)⟩⟩

/-- The tasks after a step that stores one changed task `ts'` in the execution `e₁`. -/
theorem taskFrom_setTask (h : Reachable p s) (hs : step p s op = .ok t) {u : State} {e₁ : Execution}
    {ts' : TaskState} (hu : t.executions = (u.setTask e₁ ts').executions) (hue : u.executions = s.executions)
    (he₁ : e₁ ∈ s.executions) (hchanged : TaskFrom p s t op (withTask e₁ ts') ts')
    {e : Execution} (he : e ∈ t.executions) {tk : TaskState} (htk : tk ∈ e.tasks) : TaskFrom p s t op e tk := by
  have he' := he
  rw [hu] at he'
  rcases mem_setTask_executions he' with rfl | he'
  · rcases Delivery.mem_withTask htk with rfl | ⟨htk₁, -⟩
    · exact hchanged
    · exact taskFrom_same h hs he₁ he rfl rfl rfl htk₁ htk
  · rw [hue] at he'
    exact taskFrom_same h hs he' he rfl rfl rfl htk htk

/-- A task whose call or run moved it on from a status after beginning. -/
theorem taskFrom_moved (h : Reachable p s) (hs : step p s op = .ok t) {e₁ : Execution}
    (he₁ : e₁ ∈ s.executions) {ts : TaskState} (hts : ts ∈ e₁.tasks) {st : TaskStatus}
    (hst : st ≠ .pending ∧ st ≠ .ready) (hb : ¬ notBegun s e₁.id ts.name) :
    TaskFrom p s t op (withTask e₁ { ts with status := st }) { ts with status := st } :=
  Or.inr ⟨e₁, he₁, rfl, rfl, rfl, ts, hts, rfl, Or.inr (Or.inr (Or.inr
    ⟨(begun_of_not_notBegun h he₁ hts hb).1, Or.inr hb, rfl, hst.1, hst.2, not_notBegun_step h hs hb⟩))⟩

/-- The tasks after a step whose call `c` of a task moved that task to `st`. -/
theorem taskFrom_byCall (h : Reachable p s) (hs : step p s op = .ok t) {u : State} {c : Call}
    (hc : c ∈ s.calls) {name : String} (htask : c.task = some name) {e₁ : Execution} {ts : TaskState}
    (he₁ : s.execution? c.owner = some e₁) (hts : e₁.tasks.find? (·.name == name) = some ts) {st : TaskStatus}
    (hst : st ≠ .pending ∧ st ≠ .ready) (hu : t.executions = (u.setTask e₁ { ts with status := st }).executions)
    (hue : u.executions = s.executions) {e : Execution} (he : e ∈ t.executions) {tk : TaskState}
    (htk : tk ∈ e.tasks) : TaskFrom p s t op e tk := by
  obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
  obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
  refine taskFrom_setTask h hs hu hue he₁m (taskFrom_moved h hs he₁m htsm hst ?_) he htk
  rw [he₁id, htsn]
  exact not_notBegun_of_call h hc htask

/-- The tasks after a failure of a call that does not stop. -/
theorem taskFrom_failCall (h : Reachable p s) (hs : step p s op = .ok t) (hstop : t.status ≠ .stopping)
    {c : Call} (hc : c ∈ s.calls) {st : CallStatus} {cause : Cause} (hf : s.failCall c st cause = .ok t)
    {e : Execution} (he : e ∈ t.executions) {tk : TaskState} (htk : tk ∈ e.tasks) : TaskFrom p s t op e tk := by
  obtain ⟨f, s'', -, hso, ht⟩ := State.failCall_eq_ok.mp hf
  have hpol := continue_of_fail ht hstop
  have hex : t.executions = s''.executions := by rw [ht, hpol]; rfl
  rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
  · have he₀ : e ∈ s.executions := by have := he; rw [hex] at this; exact this
    exact taskFrom_same h hs he₀ he rfl rfl rfl htk htk
  · exact taskFrom_byCall h hs hc htask he₁ hts (by simp) hex rfl he htk

/-- The tasks after a cancelled call terminated. -/
theorem taskFrom_cancelled (h : Reachable p s) (hs : step p s op = .ok t) {c : Call} (hc : c ∈ s.calls)
    (ho : (s.setCall { c with status := .cancelled }).cancelOwner c = .ok t)
    {e : Execution} (he : e ∈ t.executions) {tk : TaskState} (htk : tk ∈ e.tasks) : TaskFrom p s t op e tk := by
  rcases State.cancelOwner_eq_ok.mp ho with ⟨-, _, -, ht⟩ | ⟨name, e₁, ts, htask, he₁, hts, ht⟩
  · have hex : t.executions = s.executions := by rw [ht]; split <;> rfl
    exact taskFrom_same h hs (hex ▸ he) he rfl rfl rfl htk htk
  · by_cases hact : ts.status = .active
    · simp only [hact, ↓reduceIte] at ht
      exact taskFrom_byCall (st := .cancelled) h hs hc htask he₁ hts (by simp) (by rw [ht]; rfl) rfl he htk
    · simp only [hact, ↓reduceIte] at ht
      have hex : t.executions = s.executions := by rw [ht]; rfl
      exact taskFrom_same h hs (hex ▸ he) he rfl rfl rfl htk htk

/-- Every task after a step that does not stop comes from a new execution, or from a task before the
    step as `TaskFrom` describes. -/
theorem step_taskFrom (h : Reachable p s) (hs : step p s op = .ok t) (hstop : t.status ≠ .stopping)
    {e : Execution} (he : e ∈ t.executions) {tk : TaskState} (htk : tk ∈ e.tasks) : TaskFrom p s t op e tk := by
  have same : t.executions = s.executions → TaskFrom p s t op e tk := fun hex =>
    taskFrom_same h hs (hex ▸ he) he rfl rfl rfl htk htk
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same rfl
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, -, -, -, h'⟩ := Step.invoke_inv hs
    rcases h' with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨c, hc, hexec, rfl⟩
    · exact same rfl
    · exact same rfl
    · exact same rfl
    · have he' := he
      simp only [List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact taskFrom_same h hs he' he rfl rfl rfl htk htk
      · left
        simp only [List.mem_map] at htk
        obtain ⟨ts, -, rfl⟩ := htk
        refine ⟨execution?_eq_none_iff.mp hexec, rfl, c, ?_, rfl⟩
        exact Delivery.concurrencyOf_iff.mpr ⟨w, pl, Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩, hpl, hc⟩
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact same rfl
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    have hexe : s'.executions = s.executions := (accept_frame hacc).2.2.2.2.2.2.1
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
    · exact same (by simp [hexe])
    · have he₁' : s.execution? c.owner = some e₁ := by
        rw [← execution?_of_executions (t := s'.setCall { c with status := .returned }) (by simp [hexe])]
        exact he₁
      exact taskFrom_byCall h hs (call?_eq_some hc).1 htask he₁' hts (by simp) rfl (by simp [hexe]) he htk
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, s', -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact same (by simp [(accept_frame hacc).2.2.2.2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, s', _, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact same (by simp [(accept_frame hacc).2.2.2.2.2.2.1])
  | ended id =>
    obtain ⟨-, -, c, hc, -, -, hso⟩ := Step.ended_inv hs
    rcases State.settleOwner_eq_ok.mp hso with ⟨-, _, -, rfl⟩ | ⟨name, e₁, ts, htask, he₁, hts, rfl⟩
    · exact same (by simp)
    · exact taskFrom_byCall h hs (call?_eq_some hc).1 htask he₁ hts (by simp) rfl rfl he htk
  | failed id =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.failed_inv hs
    exact taskFrom_failCall h hs hstop (call?_eq_some hc).1 hf he htk
  | timedOut id element =>
    obtain ⟨-, -, c, hc, -, hf⟩ := Step.timedOut_inv hs
    exact taskFrom_failCall h hs hstop (call?_eq_some hc).1 hf he htk
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact taskFrom_failCall h hs hstop (call?_eq_some hc).1 hf he htk
    · exact taskFrom_cancelled h hs (call?_eq_some hc).1 ho he htk
  | terminated id =>
    obtain ⟨-, -, c, hc, -, ho⟩ := Step.terminated_inv hs
    exact taskFrom_cancelled h hs (call?_eq_some hc).1 ho he htk
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, ht⟩ := Step.transformFailed_inv hs
    have hpol := continue_of_fail ht hstop
    exact same (by rw [ht, hpol]; rfl)
  | taskInput eid name value =>
    obtain ⟨-, -, e₁, ts, spec, he₁, hts, hpend, hspec, hin, ht⟩ := Step.taskInput_inv hs
    obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    refine taskFrom_setTask h hs (u := s) (by rw [ht]) rfl he₁m ?_ he htk
    refine Or.inr ⟨e₁, he₁m, rfl, rfl, rfl, ts, htsm, rfl, Or.inr (Or.inl ⟨hpend, rfl, ?_, spec, ?_, ?_⟩)⟩
    · show Op.taskInput eid name value = Op.taskInput e₁.id ts.name value
      rw [he₁id, htsn]
    · show s.taskSpec p e₁ ts.name = .ok spec
      rw [htsn]
      exact hspec
    · rcases hin with ⟨tid, v, h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨tid, v, h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
  | taskInputFailed eid name =>
    obtain ⟨-, -, e₁, ts, spec, tid, he₁, hts, hpend, hspec, hin, ht⟩ := Step.taskInputFailed_inv hs
    have hpol := continue_of_fail ht hstop
    obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    have hex : t.executions = (s.setTask e₁ { ts with status := .failed }).executions := by rw [ht, hpol]; rfl
    refine taskFrom_setTask h hs hex rfl he₁m ?_ he htk
    refine Or.inr ⟨e₁, he₁m, rfl, rfl, rfl, ts, htsm, rfl,
      Or.inr (Or.inr (Or.inl ⟨hpend, rfl, rfl, ?_, ?_, spec, tid, ?_, hin, hpol⟩))⟩
    · show Op.taskInputFailed eid name = Op.taskInputFailed e₁.id ts.name
      rw [he₁id, htsn]
    · exact notBegun_of_eq (by rw [ht, hpol]; rfl) (by rw [ht, hpol]; rfl)
    · show s.taskSpec p e₁ ts.name = .ok spec
      rw [htsn]
      exact hspec
  | beginTask eid name =>
    obtain ⟨-, -, e₁, c, ts, spec, he₁, -, -, hts, hready, -, -, h'⟩ := Step.beginTask_inv hs
    obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
    obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
    have hb : ¬ notBegun t e₁.id ts.name := by
      rcases h' with ⟨f, decl, -, -, -, rfl⟩ | ⟨wf, out, -, -, rfl⟩
      · intro hnb
        have := call?_eq_none_iff.mp hnb.1
        simp [State.taskId, htsn] at this
      · intro hnb
        exact hnb.2 _ (List.mem_append_right _ (List.mem_singleton_self _)) ⟨rfl, by rw [htsn]⟩
    have hex : t.executions = (s.setTask e₁ { ts with status := .active }).executions := by
      rcases h' with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> rfl
    refine taskFrom_setTask h hs hex rfl he₁m ?_ he htk
    exact Or.inr ⟨e₁, he₁m, rfl, rfl, rfl, ts, htsm, rfl,
      Or.inr (Or.inr (Or.inr ⟨by rw [hready]; simp, Or.inl hready, rfl, by simp, by simp, hb⟩))⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h'⟩ := Step.taskOutput_inv hs
    rcases h' with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, ht⟩ := Step.taskOutputFailed_inv hs
    have hpol := continue_of_fail ht hstop
    exact same (by rw [ht, hpol]; rfl)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h'⟩ := Step.settle_inv hs
    rcases h' with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, e₁, _, _, he₁, -, -, -, -, -, h'⟩ := Step.closeExecution_inv hs
    have hex : t.executions = (s.setExecution { e₁ with complete := true }).executions := by
      rcases h' with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
    have he' := he
    rw [hex] at he'
    rcases mem_setExecution_executions he' with rfl | he'
    · exact taskFrom_same h hs (execution?_eq_some he₁).1 he rfl rfl rfl htk htk
    · exact taskFrom_same h hs he' he rfl rfl rfl htk htk
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, -, -, -, -, -, -, howner, h'⟩ := Step.closeRun_inv hs
    rcases h' with ⟨-, i, -, h'⟩ | ⟨name, e₁, ts, htask, he₁, hts, h'⟩
    · have hex : t.executions = s.executions := by
        rcases h' with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
      exact same hex
    · obtain ⟨he₁m, he₁id⟩ := execution?_eq_some he₁
      obtain ⟨htsm, htsn⟩ := find?_key_eq_some hts
      have hb : ¬ notBegun s e₁.id ts.name := by
        rw [he₁id, htsn]
        exact not_notBegun_of_run (run?_eq_some hr).1 howner htask
      have key : ∀ st : TaskStatus, st ≠ .pending ∧ st ≠ .ready →
          t.executions = ((s.setRun { r with complete := true }).setTask e₁ { ts with status := st }).executions →
          TaskFrom p s t (.closeRun path) e tk := fun st hst hex =>
        taskFrom_setTask h hs hex rfl he₁m (taskFrom_moved h hs he₁m htsm hst hb) he htk
      rcases h' with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact key .succeeded (by simp) rfl
      · exact key .skipped (by simp) rfl
      · exact key .failed (by simp) rfl
      · exact key .upstreamFailed (by simp) rfl
  | cancel =>
    obtain ⟨-, ⟨-, ht⟩ | ⟨hst, ht⟩⟩ := Step.cancel_inv hs
    · exact absurd (show t.status = .stopping by rw [ht]; rfl) hstop
    · exact absurd (show t.status = .stopping by rw [ht]; exact hst) hstop
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

end RunConformAux
end Suimon.Round3
