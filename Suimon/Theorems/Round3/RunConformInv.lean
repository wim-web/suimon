import Suimon.Theorems.Round3.RunConformTask

/-! Helpers for [13] Round3/RunConform.lean — task E1: the invariants behind `taskConform` and
    `policyConform`, stated by identities and without matches (`TaskInv`, `PolicyInv`). -/

namespace Suimon.Round3
namespace RunConformAux
open State

variable {p : Definition} {env : Env} {s t : State} {op : Op}

/-! ### Validity -/

/-- Reduces a successful validator computation to its conditions. -/
local macro "rc_validate_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Static.except_bind_eq_ok, Static.except_pure_eq_ok, Static.except_throw_eq_ok,
    Validate.check_eq_ok, Validate.need_eq_ok, exists_const, and_true, true_and, Bool.false_eq_true,
    ↓reduceIte, false_and, and_false, exists_false] at $h:ident)

/-- A declared input transform reads the input of its concurrency. -/
theorem validateTask_declared {at_ : String} {c : Concurrency} {task : TaskSpec}
    (h : p.validateTask at_ c task = .ok ()) {tid : String} (hin : task.input = some (.declared tid)) :
    c.input.isSome = true := by
  unfold Definition.validateTask at h
  rc_validate_simp at h
  obtain ⟨-, input, -, h⟩ := h
  rw [hin] at h
  cases input with
  | none => simp at h
  | some expected =>
    rc_validate_simp at h
    obtain ⟨tr, -, source, hsource, -⟩ := h
    rw [hsource]
    rfl

/-- In a valid definition, a task with a declared input transform belongs to a concurrency that takes
    an input, so its tasks start pending. -/
theorem declared_input (valid : p.validate = .ok ()) {e : Execution} {c : Concurrency}
    (hc : t.concurrencyOf p e = .ok c) {spec : TaskSpec} (hspec : spec ∈ c.tasks) {tid : String}
    (hin : spec.input = some (.declared tid)) : c.input.isSome = true := by
  obtain ⟨w, pl, hw, hpl, hctrl⟩ := Delivery.concurrencyOf_iff.mp hc
  obtain ⟨r, -, hwr⟩ := Delivery.workflow?_iff.mp hw
  have hwm := (Definition.workflow?_eq_some hwr).1
  have hplm := (Workflow.placement?_eq_some hpl).1
  obtain ⟨-, -, -, htasks⟩ := (((Definition.validate_ok valid).workflows w hwm).placements pl hplm).concurrency c hctrl
  obtain ⟨at_, hv⟩ := htasks spec hspec
  exact validateTask_declared hv hin

/-! ### Small frames -/

theorem failCall_frame {c : Call} {st : CallStatus} {cause : Cause} (hf : s.failCall c st cause = .ok t) :
    t.taskResults = s.taskResults ∧ t.results = s.results ∧ t.deliveries = s.deliveries := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  have u := settleOwner_update hso
  simp [u.taskResults, u.results, u.deliveries]

/-- An execution found before and after a step has the same run and placement. -/
theorem execution?_step (h : Reachable p s) (hs : step p s op = .ok t) {id : String} {e₀ e : Execution}
    (he₀ : s.execution? id = some e₀) (he : t.execution? id = some e) : e.run = e₀.run ∧ e.placement = e₀.placement := by
  obtain ⟨he₀m, rfl⟩ := execution?_eq_some he₀
  obtain ⟨e', he', a1, a2, a3, -, -⟩ := ((Delivery.Reachable.inv h).kept hs).execution e₀ he₀m
  have := (step_wellKeyed h.wellKeyed hs).execution?_of_mem he'
  rw [a1, he] at this
  cases this
  exact ⟨a2, a3⟩

/-! ### Task results -/

/-- How a task result after a step came to be: it was there, or it is new and not yet transformed, or
    `taskOutput` or `taskOutputFailed` just transformed it. -/
def TaskResultFrom (s : State) (op : Op) (r : TaskResult) : Prop :=
  r ∈ s.taskResults ∨ r.output = .pending ∨
  ∃ r₀ ∈ s.taskResults, r₀.execution = r.execution ∧ r₀.task = r.task ∧ r₀.index = r.index ∧ r₀.value = r.value ∧
    r₀.output = .pending ∧
    ((∃ v, op = .taskOutput r.execution r.task r.index v ∧ r.output = .value v) ∨
     (op = .taskOutputFailed r.execution r.task r.index ∧ r.output = .failed))

theorem step_taskResultFrom (hs : step p s op = .ok t) {r : TaskResult} (hr : r ∈ t.taskResults) :
    TaskResultFrom s op r := by
  have same : t.taskResults = s.taskResults → TaskResultFrom s op r := fun h => Or.inl (h ▸ hr)
  have acc : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
      s.accept c index value arm = .ok s' → t.taskResults = s'.taskResults → TaskResultFrom s op r := by
    intro c index value arm s' hacc ht
    rcases Delivery.accept_taskResults hacc with h' | ⟨name, -, h'⟩
    · exact same (ht.trans h')
    · rw [ht, h', List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact Or.inr (Or.inl rfl)
  have setr : ∀ {r₀ : TaskResult} {o : TaskOutput}, r₀ ∈ s.taskResults →
      t.taskResults = (s.setTaskResult { r₀ with output := o }).taskResults →
      (r = { r₀ with output := o } → TaskResultFrom s op r) → TaskResultFrom s op r := by
    intro r₀ o hr₀ ht hnew
    rw [ht] at hr
    rcases mem_setTaskResult_taskResults hr with rfl | hr
    · exact hnew rfl
    · exact Or.inl hr
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
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact acc hacc (by rw [(settleOwner_update hso).taskResults, setCall_taskResults])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact acc hacc (by rw [setInvocation_taskResults, setCall_taskResults])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact acc hacc (by rw [setCall_taskResults])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(settleOwner_update hso).taskResults, setCall_taskResults])
  | failed id =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.failed_inv hs
    exact same (failCall_frame hf).1
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.timedOut_inv hs
    exact same (failCall_frame hf).1
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · exact same (failCall_frame hf).1
    · exact same (by rw [(cancelOwner_update ho).taskResults, setCall_taskResults])
  | terminated id =>
    obtain ⟨-, -, _, -, -, ho⟩ := Step.terminated_inv hs
    exact same (by rw [(cancelOwner_update ho).taskResults, setCall_taskResults])
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
    obtain ⟨-, -, _, _, _, r₀, -, -, -, -, hr₀, hp, h⟩ := Step.taskOutput_inv hs
    have hr₀m := List.mem_of_find?_eq_some hr₀
    have hk : r₀.execution = eid ∧ r₀.task = name ∧ r₀.index = index := by
      simpa [and_assoc] using List.find?_some hr₀
    have ht : t.taskResults = (s.setTaskResult { r₀ with output := .value value }).taskResults := by
      rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    refine setr hr₀m ht fun hreq => ?_
    subst hreq
    refine Or.inr (Or.inr ⟨r₀, hr₀m, rfl, rfl, rfl, rfl, hp, Or.inl ⟨value, ?_, rfl⟩⟩)
    show Op.taskOutput eid name index value = Op.taskOutput r₀.execution r₀.task r₀.index value
    rw [hk.1, hk.2.1, hk.2.2]
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, r₀, -, -, -, hr₀, hp, ht⟩ := Step.taskOutputFailed_inv hs
    have hr₀m := List.mem_of_find?_eq_some hr₀
    have hk : r₀.execution = eid ∧ r₀.task = name ∧ r₀.index = index := by
      simpa [and_assoc] using List.find?_some hr₀
    refine setr (o := .failed) hr₀m (by rw [ht]; simp) fun hreq => ?_
    subst hreq
    refine Or.inr (Or.inr ⟨r₀, hr₀m, rfl, rfl, rfl, rfl, hp, Or.inr ⟨?_, rfl⟩⟩)
    show Op.taskOutputFailed eid name index = Op.taskOutputFailed r₀.execution r₀.task r₀.index
    rw [hk.1, hk.2.1, hk.2.2]
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Or.inl hr
        · exact Or.inr (Or.inl rfl)
      all_goals exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

/-! ### Tasks follow the behavior -/

/-- `TaskConform` by identities and without matches, with the empty input of pending tasks. -/
structure TaskInv (p : Definition) (env : Env) (s : State) : Prop where
  pending : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status = .pending → tk.input = none
  declared : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, ∀ spec, s.taskSpec p e tk.name = .ok spec → tk.status ≠ .pending →
    ∀ tid, spec.input = some (.declared tid) →
      (env.behavior.taskInput e.id tk.name = none ∧ tk.status = .failed ∧ tk.input = none ∧ notBegun s e.id tk.name) ∨
      (∃ v, env.behavior.taskInput e.id tk.name = some v ∧ tk.input = some v)
  other : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, ∀ spec, s.taskSpec p e tk.name = .ok spec → tk.status ≠ .pending →
    (∀ tid, spec.input ≠ some (.declared tid)) → tk.input = none
  begun : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status ≠ .pending → tk.status ≠ .ready → notBegun s e.id tk.name →
    tk.status = .failed ∧ env.behavior.taskInput e.id tk.name = none
  output : ∀ r ∈ s.taskResults,
    (∀ v, r.output = .value v → env.behavior.taskOutput r.execution r.task r.index = some v) ∧
    (r.output = .failed → env.behavior.taskOutput r.execution r.task r.index = none)

theorem TaskInv.empty : TaskInv p env {} :=
  ⟨by simp, by simp, by simp, by simp, by simp⟩

/-- A conforming step that does not stop keeps `TaskInv`. -/
theorem step_taskInv (valid : p.validate = .ok ()) (h : Reachable p s) (hconf : Conforms env s op)
    (hs : step p s op = .ok t) (hrun : s.status = .running) (hstop : t.status ≠ .stopping) (inv : TaskInv p env s) :
    TaskInv p env t := by
  have K := (Delivery.Reachable.inv h).kept hs
  -- The spec of a task before and after the step.
  have spec₀ : ∀ {e₀ e : Execution} {tk₀ tk : TaskState} {spec : TaskSpec}, e₀ ∈ s.executions →
      e₀.run = e.run → e₀.placement = e.placement → tk₀.name = tk.name →
      t.taskSpec p e tk.name = .ok spec → s.taskSpec p e₀ tk₀.name = .ok spec := by
    intro e₀ e tk₀ tk spec he₀ hrun hpl hname hspec
    rw [← taskSpec_step h hs he₀ hrun.symm hpl.symm, hname]
    exact hspec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he tk htk hpend
    rcases step_taskFrom h hs hrun hstop he htk with ⟨-, hin, -⟩ | ⟨e₀, he₀, -, -, -, tk₀, htk₀, -, hcase⟩
    · exact hin
    · rcases hcase with ⟨rfl, -⟩ | ⟨-, hst, -⟩ | ⟨-, hst, -⟩ | ⟨-, -, -, hst, -⟩
      · exact inv.pending e₀ he₀ tk htk₀ hpend
      · rw [hst] at hpend; cases hpend
      · rw [hst] at hpend; cases hpend
      · exact absurd hpend hst
  · intro e he tk htk spec hspec hpend tid hin
    rcases step_taskFrom h hs hrun hstop he htk with ⟨-, -, c, hc, hst⟩ | ⟨e₀, he₀, hid, hrun, hpl, tk₀, htk₀, hname, hcase⟩
    · -- A new execution waits for the input of its tasks exactly when the concurrency takes one.
      exfalso
      obtain ⟨c', hc', hfind⟩ := taskSpec_eq_ok.mp hspec
      rw [hc] at hc'
      cases hc'
      rw [declared_input valid hc (List.mem_of_find?_eq_some hfind) hin] at hst
      exact hpend hst
    · have hs₀ := spec₀ he₀ hrun hpl hname hspec
      rcases hcase with ⟨rfl, hkeep⟩ | ⟨-, -, hop, spec', hspec', hin'⟩ |
          ⟨hp₀, hst, hinp, hop, hkeep, -⟩ | ⟨hp₀, hb, hinp, -, -, -⟩
      · rcases inv.declared e₀ he₀ tk htk₀ spec hs₀ hpend tid hin with ⟨h1, h2, h3, h4⟩ | ⟨v, h1, h2⟩
        · exact Or.inl ⟨hid ▸ h1, h2, h3, hkeep (hid ▸ h4)⟩
        · exact Or.inr ⟨v, hid ▸ h1, h2⟩
      · rw [← hname, hs₀] at hspec'
        cases hspec'
        rcases hin' with ⟨-, v, -, hv⟩ | ⟨hd, -⟩
        · rw [hop] at hconf
          exact Or.inr ⟨v, hconf v hv, hv⟩
        · rw [hin] at hd; cases hd
      · rw [hop] at hconf
        have hnb₀ : notBegun s e₀.id tk₀.name := notBegun_of_waiting h he₀ htk₀ fun hb => hb.1 hp₀
        rw [hid, hname] at hnb₀
        exact Or.inl ⟨hconf, hst, hinp.trans (inv.pending e₀ he₀ tk₀ htk₀ hp₀), hkeep hnb₀⟩
      · rcases inv.declared e₀ he₀ tk₀ htk₀ spec hs₀ hp₀ tid hin with ⟨-, h2, -, h4⟩ | ⟨v, h1, h2⟩
        · rcases hb with hb | hb
          · rw [h2] at hb; cases hb
          · rw [← hid, ← hname] at hb
            exact absurd h4 hb
        · refine Or.inr ⟨v, ?_, hinp.trans h2⟩
          rw [← hid, ← hname]
          exact h1
  · intro e he tk htk spec hspec hpend hnd
    rcases step_taskFrom h hs hrun hstop he htk with ⟨-, hin, -⟩ | ⟨e₀, he₀, hid, hrun, hpl, tk₀, htk₀, hname, hcase⟩
    · exact hin
    · have hs₀ := spec₀ he₀ hrun hpl hname hspec
      rcases hcase with ⟨rfl, -⟩ | ⟨-, -, -, spec', hspec', hin'⟩ | ⟨-, -, -, -, -, spec', tid', hspec', hin', -⟩ |
          ⟨hp₀, -, hinp, -, -, -⟩
      · exact inv.other e₀ he₀ tk htk₀ spec hs₀ hpend hnd
      · rw [← hname, hs₀] at hspec'
        cases hspec'
        rcases hin' with ⟨tid, -, hd, -⟩ | ⟨-, hv⟩
        · exact absurd hd (hnd tid)
        · exact hv
      · rw [← hname, hs₀] at hspec'
        cases hspec'
        exact absurd hin' (hnd tid')
      · exact hinp.trans (inv.other e₀ he₀ tk₀ htk₀ spec hs₀ hp₀ hnd)
  · intro e he tk htk hp hr hnb
    rcases step_taskFrom h hs hrun hstop he htk with ⟨-, -, c, -, hst⟩ | ⟨e₀, he₀, hid, -, -, tk₀, htk₀, -, hcase⟩
    · rw [hst] at hp hr
      by_cases hci : c.input.isSome = true
      · simp [hci] at hp
      · simp [hci] at hr
    · rcases hcase with ⟨rfl, -⟩ | ⟨-, hst, -⟩ | ⟨-, hst, -, hop, -⟩ | ⟨-, -, -, -, -, hbt⟩
      · rw [← hid] at hnb ⊢
        exact inv.begun e₀ he₀ tk htk₀ hp hr (notBegun_back K hnb)
      · exact absurd hst hr
      · rw [hop] at hconf
        exact ⟨hst, hconf⟩
      · exact absurd hnb hbt
  · intro r hr
    rcases step_taskResultFrom hs hr with hr₀ | hpend | ⟨-, -, -, -, -, -, -, ⟨v, hop, hout⟩ | ⟨hop, hout⟩⟩
    · exact inv.output r hr₀
    · rw [hpend]
      exact ⟨fun v hv => (by cases hv), fun hv => (by cases hv)⟩
    · rw [hop] at hconf
      rw [hout]
      refine ⟨fun v' hv' => ?_, fun hv' => (by cases hv')⟩
      cases hv'
      exact hconf
    · rw [hop] at hconf
      rw [hout]
      exact ⟨fun v' hv' => (by cases hv'), fun _ => hconf⟩

/-- `TaskInv` along a conforming execution that has not stopped. -/
theorem conforming_taskInv (valid : p.validate = .ok ()) {tr : List Op} (h : Conforming p env tr s) :
    Unstopped s → TaskInv p env s := by
  induction h with
  | nil => intro _; exact TaskInv.empty
  | @snoc tr s₀ t₀ op hprev hc hs _ ih =>
    intro us
    have hr := hprev.reachable
    exact step_taskInv valid hr hc hs (running_of_unstopped hr (unstopped_back hs us) hs)
      (not_stopping_of_unstopped (Reachable.step _ hr hs) us) (ih (unstopped_back hs us))

/-! ### Failures under the continue policy -/

/-- A call that failed, was lost, or was cancelled. -/
def CallFailed (c : Call) : Prop :=
  c.status = .failed ∨ c.status = .lost ∨ c.status = .cancelling ∨ c.status = .cancelled

/-- `PolicyConform` by identities. -/
structure PolicyInv (p : Definition) (s : State) : Prop where
  calls : ∀ c ∈ s.calls, (c.status = .failed ∨ c.status = .lost ∨ c.status = .cancelling ∨ c.status = .cancelled) →
    c.policy = .continue
  deliveries : ∀ d ∈ s.deliveries, d.outcome = .failed → ∀ w c pl, s.workflow? p d.run = some w →
    w.connections[d.connection]? = some c → w.placement? c.target = some pl → pl.policy = .continue
  tasks : ∀ e ∈ s.executions, ∀ tk ∈ e.tasks, tk.status = .failed → notBegun s e.id tk.name → ∀ spec,
    s.taskSpec p e tk.name = .ok spec → spec.policy = .continue
  outputs : ∀ r ∈ s.taskResults, r.output = .failed → ∀ e spec, s.execution? r.execution = some e →
    s.taskSpec p e r.task = .ok spec → spec.policy = .continue

theorem PolicyInv.empty : PolicyInv p {} :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- A failure of a call that does not stop is under the continue policy and only sets the call's
    status among the calls. -/
theorem failCall_calls {c : Call} {st : CallStatus} {cause : Cause} (hf : s.failCall c st cause = .ok t)
    (hstop : t.status ≠ .stopping) : c.policy = .continue ∧ t.calls = (s.setCall { c with status := st }).calls := by
  obtain ⟨f, s', -, hso, ht⟩ := failCall_eq_ok.mp hf
  have hpol := continue_of_fail ht hstop
  refine ⟨hpol, ?_⟩
  have hc : (s'.fail f c.policy).calls = s'.calls := by rw [hpol]; rfl
  rw [ht, hc]
  exact (settleOwner_update hso).calls

/-- A failed, lost or cancelled call after a step that does not stop was so before, or failed in this
    step under the continue policy. -/
theorem step_call_failed (hs : step p s op = .ok t) (hstop : t.status ≠ .stopping) {c : Call} (hc : c ∈ t.calls)
    (hf : CallFailed c) : c.policy = .continue ∨ ∃ c₀ ∈ s.calls, c₀.policy = c.policy ∧ CallFailed c₀ := by
  have same : c ∈ s.calls → c.policy = .continue ∨ ∃ c₀ ∈ s.calls, c₀.policy = c.policy ∧ CallFailed c₀ :=
    fun h => Or.inr ⟨c, h, rfl, hf⟩
  -- A call stored with a running, fetching or returned status is not failed.
  have alive : ∀ {c₁ : Call} {st : CallStatus} {u : State}, u.calls = s.calls →
      (st = .running ∨ st = .fetching ∨ st = .returned) → t.calls = (u.setCall { c₁ with status := st }).calls →
      c.policy = .continue ∨ ∃ c₀ ∈ s.calls, c₀.policy = c.policy ∧ CallFailed c₀ := by
    intro c₁ st u hu hst ht
    rw [ht] at hc
    rcases mem_setCall_calls hc with rfl | hc
    · exfalso
      unfold CallFailed at hf
      rcases hst with rfl | rfl | rfl <;> simp at hf
    · exact same (hu ▸ hc)
  -- A new call runs.
  have fresh : ∀ {x : Call}, x.status = .running → t.calls = s.calls ++ [x] →
      c.policy = .continue ∨ ∃ c₀ ∈ s.calls, c₀.policy = c.policy ∧ CallFailed c₀ := by
    intro x hx ht
    rw [ht, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact same hc
    · exfalso
      unfold CallFailed at hf
      rw [hx] at hf
      simp at hf
  have failed : ∀ {c₁ : Call} {st : CallStatus} {cause : Cause}, s.failCall c₁ st cause = .ok t →
      c.policy = .continue ∨ ∃ c₀ ∈ s.calls, c₀.policy = c.policy ∧ CallFailed c₀ := by
    intro c₁ st cause hf'
    obtain ⟨hpol, ht⟩ := failCall_calls hf' hstop
    rw [ht] at hc
    rcases mem_setCall_calls hc with rfl | hc
    · exact Or.inl hpol
    · exact same hc
  have cancelled : ∀ {c₁ : Call}, c₁ ∈ s.calls → c₁.status = .cancelling →
      t.calls = (s.setCall { c₁ with status := .cancelled }).calls →
      c.policy = .continue ∨ ∃ c₀ ∈ s.calls, c₀.policy = c.policy ∧ CallFailed c₀ := by
    intro c₁ hc₁ hst ht
    rw [ht] at hc
    rcases mem_setCall_calls hc with rfl | hc
    · exact Or.inr ⟨c₁, hc₁, rfl, Or.inr (Or.inr (Or.inl hst))⟩
    · exact same hc
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact same hc
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact fresh rfl rfl
    · exact fresh rfl rfl
    · exact same hc
    · exact same hc
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact alive rfl (Or.inr (Or.inl rfl)) rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact alive (accept_frame hacc).2.2.2.2.2.1 (Or.inr (Or.inr rfl)) (settleOwner_update hso).calls
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact alive (accept_frame hacc).2.2.2.2.2.1 (Or.inr (Or.inr rfl)) rfl
  | yielded id value =>
    obtain ⟨-, -, c₁, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    rcases mem_setCall_calls hc with rfl | hc
    · exfalso
      unfold CallFailed at hf
      simp at hf
    · exact same (by rwa [(accept_frame hacc).2.2.2.2.2.1] at hc)
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact alive rfl (Or.inr (Or.inr rfl)) (settleOwner_update hso).calls
  | failed id =>
    obtain ⟨-, -, _, -, -, hf'⟩ := Step.failed_inv hs
    exact failed hf'
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, hf'⟩ := Step.timedOut_inv hs
    exact failed hf'
  | lost id =>
    obtain ⟨-, -, c₁, hc₁, ⟨-, hf'⟩ | ⟨hst, ho⟩⟩ := Step.lost_inv hs
    · exact failed hf'
    · exact cancelled (call?_eq_some hc₁).1 hst (cancelOwner_update ho).calls
  | terminated id =>
    obtain ⟨-, -, c₁, hc₁, hst, ho⟩ := Step.terminated_inv hs
    exact cancelled (call?_eq_some hc₁).1 hst (cancelOwner_update ho).calls
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same hc
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, ht⟩ := Step.transformFailed_inv hs
    have hpol := continue_of_fail ht hstop
    rw [ht, hpol, fail_continue] at hc
    exact same hc
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same hc
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, ht⟩ := Step.taskInputFailed_inv hs
    have hpol := continue_of_fail ht hstop
    rw [ht, hpol, fail_continue] at hc
    exact same hc
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact fresh rfl rfl
    · exact same hc
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact same hc
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, ht⟩ := Step.taskOutputFailed_inv hs
    have hpol := continue_of_fail ht hstop
    rw [ht, hpol, fail_continue] at hc
    exact same hc
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact same hc
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact same hc
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same hc
  | cancel =>
    obtain ⟨-, ⟨-, ht⟩ | ⟨hst, ht⟩⟩ := Step.cancel_inv hs
    · exact absurd (show t.status = .stopping by rw [ht]; rfl) hstop
    · exact absurd (show t.status = .stopping by rw [ht]; exact hst) hstop
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same hc

/-- A step that does not stop keeps `PolicyInv`. -/
theorem step_policyInv (h : Reachable p s) (hs : step p s op = .ok t) (hrun : s.status = .running)
    (hstop : t.status ≠ .stopping) (inv : PolicyInv p s) : PolicyInv p t := by
  have wk := h.wellKeyed
  have wk' := step_wellKeyed wk hs
  have K := (Delivery.Reachable.inv h).kept hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc hf
    rcases step_call_failed hs hstop hc hf with hpol | ⟨c₀, hc₀, hpol, hf₀⟩
    · exact hpol
    · rw [← hpol]
      exact inv.calls c₀ hc₀ hf₀
  · intro d hd hfail w c pl hw hc hpl
    have old : d ∈ s.deliveries → pl.policy = .continue := fun hd₀ => by
      obtain ⟨w₀, -, -, hw₀, -⟩ := (Delivery.Reachable.inv h).own.deliveries d hd₀
      have hw₀' := K.workflow? wk' hw₀
      rw [hw] at hw₀'
      cases hw₀'
      exact inv.deliveries d hd₀ hfail w c pl hw₀ hc hpl
    rcases (Delivery.step_deliveries_settled_eq hs).1 with hdel | ⟨path, j, src, ⟨v, rfl⟩ | rfl⟩
    · exact old (hdel ▸ hd)
    · obtain ⟨-, -, w₁, c₁, outcome, -, hcase, rfl⟩ := Step.deliver_inv hs
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact old hd
      · rcases hcase with ⟨_, _, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> cases hfail
    · obtain ⟨-, -, w₁, c₁, tid, target, hdt, -, htarget, ht⟩ := Step.transformFailed_inv hs
      have hpol := continue_of_fail ht hstop
      obtain ⟨hw₁, hc₁, -, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
      have hdt' : d ∈ s.deliveries ++ [{ run := path, connection := j, source := src, outcome := .failed }] := by
        rw [ht] at hd; simpa using hd
      simp only [List.mem_append, List.mem_singleton] at hdt'
      rcases hdt' with hd | rfl
      · exact old hd
      · have hw₁' := K.workflow? wk' hw₁
        rw [hw] at hw₁'
        cases hw₁'
        rw [hc₁] at hc
        cases hc
        rw [htarget] at hpl
        cases hpl
        exact hpol
  · intro e he tk htk hfail hnb spec hspec
    rcases step_taskFrom h hs hrun hstop he htk with ⟨-, -, c, -, hst⟩ | ⟨e₀, he₀, hid, hrun, hpl, tk₀, htk₀, hname, hcase⟩
    · rw [hfail] at hst
      by_cases hci : c.input.isSome = true <;> simp [hci] at hst
    · have hs₀ : s.taskSpec p e₀ tk₀.name = .ok spec := by
        rw [← taskSpec_step h hs he₀ hrun.symm hpl.symm, hname]
        exact hspec
      rcases hcase with ⟨rfl, -⟩ | ⟨-, hst, -⟩ | ⟨-, -, -, -, -, spec', tid', hspec', -, hpol⟩ | ⟨-, -, -, -, -, hbt⟩
      · rw [← hid] at hnb
        exact inv.tasks e₀ he₀ tk htk₀ hfail (notBegun_back K hnb) spec hs₀
      · rw [hfail] at hst; cases hst
      · rw [← hname, hs₀] at hspec'
        cases hspec'
        exact hpol
      · exact absurd hnb hbt
  · intro r hr hfail e spec he hspec
    rcases step_taskResultFrom hs hr with hr₀ | hpend | ⟨-, -, -, -, -, -, -, ⟨v, -, hout⟩ | ⟨hop, -⟩⟩
    · obtain ⟨e₀, he₀, heid, -⟩ := (Limit.reachable_inv h).results r hr₀
      have he₀' : s.execution? r.execution = some e₀ := by rw [← heid]; exact wk.execution?_of_mem he₀
      obtain ⟨hrun, hpl⟩ := execution?_step h hs he₀' he
      refine inv.outputs r hr₀ hfail e₀ spec he₀' ?_
      rw [← taskSpec_step h hs (execution?_eq_some he₀').1 hrun hpl]
      exact hspec
    · rw [hpend] at hfail; cases hfail
    · rw [hout] at hfail; cases hfail
    · subst hop
      obtain ⟨-, -, e₁, spec₁, r₁, he₁, hspec₁, -, -, -, ht⟩ := Step.taskOutputFailed_inv hs
      have hpol := continue_of_fail ht hstop
      obtain ⟨hrun, hpl⟩ := execution?_step h hs he₁ he
      rw [taskSpec_step h hs (execution?_eq_some he₁).1 hrun hpl, hspec₁] at hspec
      cases hspec
      exact hpol

/-- `PolicyInv` in every reachable state that has not stopped. -/
theorem reachable_policyInv (h : Reachable p s) : Unstopped s → PolicyInv p s := by
  induction h with
  | empty => intro _; exact PolicyInv.empty
  | step op hr hs ih =>
    intro us
    exact step_policyInv hr hs (running_of_unstopped hr (unstopped_back hs us) hs) (not_stopping_of_unstopped (Reachable.step _ hr hs) us)
      (ih (unstopped_back hs us))

end RunConformAux
end Suimon.Round3
