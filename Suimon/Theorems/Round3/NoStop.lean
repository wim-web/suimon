import Suimon.Theorems.Round3.CoversStep

namespace Suimon.Round3
open State

/-! ## [27] Round3/NoStop.lean — task G2

A stopping step of an unstopped execution is a stop-policy failure: of a call (`failed`, `timedOut`,
`lost`), of a connection transform, or of a task input or output transform (a `cancel` does not conform
without the caller's cancel). The state before it is contained in the final state `T` of the complete
run (`covers_of_execution`), and there the same failure happened with the same answer: `T` ended every
call as its script says (`CallConform`), delivered every eligible result with the behavior's answer
(`Saturated`, `DeliveryConform`), and ended every task and transformed every output (`Saturated`,
`TaskConform`). Since `T` never stopped, `PolicyConform` of `T` gives that failure the continue policy,
so the step did not stop either. -/

namespace NoStopAux

variable {p : Definition} {env : Env} {s t T : State}

/-- A run of a state contained in `T` has the same workflow in `T`. -/
theorem workflow?_eq (cov : Covers p T s) (hT : T.WellKeyed) {path : Path} (hr : (s.run? path).isSome) :
    T.workflow? p path = s.workflow? p path := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨hrm, hrp⟩ := run?_eq_some hr
  obtain ⟨r', hr', hp, hwf, -⟩ := cov.runs r hrm
  have hT' : T.run? path = some r' := by
    rw [← hrp, ← hp]
    exact hT.run?_of_mem hr'
  unfold State.workflow?
  rw [hT', hr]
  simp [hwf]

/-- A step from a state that is not running keeps the runs (a stopping state only ends calls, takes the
    caller's cancel or concludes), so it keeps a completed root run. -/
theorem done_of_step {op : Op} (hs : step p s op = .ok t) (hrun : s.status ≠ .running) (hd : Done s) :
    Done t := by
  obtain ⟨-, -, hcases⟩ := step_of_status_ne_running hs hrun
  have hruns : t.runs = s.runs := by
    rcases hcases with ⟨c, -, -, hf⟩ | ⟨c, -, -, ho⟩ | rfl | ⟨-, rfl⟩
    · exact failCall_runs hf
    · rw [(cancelOwner_update ho).runs, setCall_runs]
    · rfl
    · rfl
  have hroot : t.run? [] = s.run? [] := by
    unfold State.run?
    rw [hruns]
  unfold Done at hd ⊢
  rw [hroot]
  exact hd

/-- Task specs read only the workflow of the run and the placement. -/
theorem taskSpec_of_workflow? {a b : State} {e e' : Execution} {name : String}
    (hw : a.workflow? p e'.run = b.workflow? p e.run) (hpl : e'.placement = e.placement) :
    a.taskSpec p e' name = b.taskSpec p e name := by
  unfold State.taskSpec State.concurrencyOf State.placementOf
  rw [hw, hpl]

/-- A call failure under the continue policy keeps the status. -/
theorem failCall_status_continue {c : Call} {st : CallStatus} {cause : Cause} (hf : s.failCall c st cause = .ok t)
    (hpol : c.policy = .continue) : t.status = s.status := by
  obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
  rw [hpol, fail_continue]
  exact (settleOwner_update hso).status

/-- A call of `s` whose script ends in a failure, a timeout or a loss has the continue policy: in `T`
    the same call ended, not by returning (its script does not return), so it failed, was lost or was
    cancelled, which `PolicyConform` of `T` allows only under `continue`. -/
theorem call_continue (RT : RunConform p env T) (sat : Saturated p T) (cov : Covers p T s) {c : Call}
    (hc : c ∈ s.calls)
    (hend : (env.behavior.script c.id).ending = .failed ∨ (∃ el, (env.behavior.script c.id).ending = .timedOut el) ∨
      (env.behavior.script c.id).ending = .lost) :
    c.policy = .continue := by
  obtain ⟨c', hc', hid, -, -, -, -, -, -, hpol, -⟩ := cov.calls c hc
  rw [← hpol]
  rw [← hid] at hend
  have hended := sat.calls c' hc'
  obtain ⟨cc, -⟩ := RT.calls c' hc'
  cases hst : c'.status with
  | running => rw [hst] at hended; cases hended
  | fetching => rw [hst] at hended; cases hended
  | cancelling => rw [hst] at hended; cases hended
  | returned =>
    exfalso
    obtain ⟨-, h⟩ := cc.returned hst
    rcases h with ⟨-, ⟨v, hv⟩ | ⟨a, ha⟩⟩ | ⟨-, he⟩ <;>
      rcases hend with h | ⟨el, h⟩ | h <;> simp_all
  | failed => exact RT.policies.calls c' hc' (Or.inl hst)
  | lost => exact RT.policies.calls c' hc' (Or.inr (Or.inl hst))
  | cancelled => exact RT.policies.calls c' hc' (Or.inr (Or.inr (Or.inr hst)))

/-- A failed connection transform of `s` falls under the continue policy of the connection's target: `T`
    contains the source result, delivered it on the same connection (`Saturated`) with the behavior's
    answer, a failure (`DeliveryConform`), which `PolicyConform` of `T` allows only under `continue`. -/
theorem transform_continue (hT : T.WellKeyed) (RT : RunConform p env T) (sat : Saturated p T)
    (cov : Covers p T s) {path : Path} {j : Nat} {src : ResultId} {w : Workflow} {c : Connection}
    {tid : String} {target : Placement} (hdt : Step.deliveryTarget p s path j src = .ok (w, c))
    (htid : c.transform = .declared tid) (htarget : w.placement? c.target = some target)
    (hnone : env.behavior.transform path j src = none) : target.policy = .continue := by
  obtain ⟨hw, hc, ⟨r, hr, hrun, hpl, harm⟩, -⟩ := Step.deliveryTarget_eq_ok.mp hdt
  have hrs : (s.run? path).isSome := by
    obtain ⟨rr, hrr, -⟩ := Delivery.workflow?_iff.mp hw
    rw [hrr]
    rfl
  have hwT : T.workflow? p path = some w := by rw [workflow?_eq cov hT hrs]; exact hw
  obtain ⟨hrm, hrid⟩ := result?_eq_some hr
  have hrT : r ∈ T.results := cov.results r hrm
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
    (sat.delivered r hrT w (by rw [hrun]; exact hwT) j c hc hpl.symm (harm.imp id Eq.symm))
  rw [hrun, hrid] at hd
  obtain ⟨hdm, hdrun, hdconn, hdsrc⟩ := delivery?_eq_some hd
  obtain ⟨w', c', hw', hc', hm⟩ := RT.deliveries d hdm
  rw [hdrun, hwT] at hw'
  cases hw'
  rw [hdconn, hc] at hc'
  cases hc'
  rw [htid, hdrun, hdconn, hdsrc, hnone] at hm
  exact RT.policies.deliveries d hdm hm w c target (by rw [hdrun]; exact hwT) (by rw [hdconn]; exact hc) htarget

/-- The execution of `s` with identity `eid` has, in `T`, an execution with the same identity, run and
    placement, and the task specs of both agree. -/
theorem execution_covered (hs : Reachable p s) (hT : T.WellKeyed) (cov : Covers p T s) {eid : String}
    {e : Execution} (he : s.execution? eid = some e) :
    ∃ e' ∈ T.executions, e'.id = eid ∧ e'.tasks.map (·.name) = e.tasks.map (·.name) ∧
      T.execution? eid = some e' ∧ ∀ name, T.taskSpec p e' name = s.taskSpec p e name := by
  obtain ⟨hem, heid⟩ := execution?_eq_some he
  obtain ⟨e', he', hid, hrun, hpl, -, hnames, -, -⟩ := cov.executions e hem
  have hwT : T.workflow? p e'.run = s.workflow? p e.run := by
    rw [hrun]
    exact workflow?_eq cov hT ((Limit.reachable_inv hs).execRuns e hem)
  refine ⟨e', he', hid.trans heid, hnames, ?_, fun name => taskSpec_of_workflow? hwT hpl⟩
  rw [← heid, ← hid]
  exact hT.execution?_of_mem he'

/-- A failed task input transform of `s` falls under the continue policy of the task: in `T` the same
    task ended, with the behavior's answer on its input, a failure (`TaskConform`), and without a body,
    which `PolicyConform` of `T` allows only under `continue`. -/
theorem taskInput_continue (hs : Reachable p s) (hT : T.WellKeyed) (RT : RunConform p env T)
    (sat : Saturated p T) (cov : Covers p T s) {eid name : String} {e : Execution} {ts : TaskState}
    {spec : TaskSpec} {tid : String} (he : s.execution? eid = some e) (hts : e.tasks.find? (·.name == name) = some ts)
    (hspec : s.taskSpec p e name = .ok spec) (hin : spec.input = some (.declared tid))
    (hnone : env.behavior.taskInput eid name = none) : spec.policy = .continue := by
  obtain ⟨e', he', hid, hnames, -, hspecs⟩ := execution_covered hs hT cov he
  have htsn : ts.name = name := by simpa using List.find?_some hts
  obtain ⟨t', ht', ht'n⟩ : ∃ t' ∈ e'.tasks, t'.name = name := by
    have hmem : name ∈ e'.tasks.map (·.name) := by
      rw [hnames]
      exact List.mem_map.mpr ⟨ts, List.mem_of_find?_eq_some hts, htsn⟩
    obtain ⟨t', ht', h⟩ := List.mem_map.mp hmem
    exact ⟨t', ht', h⟩
  have hended := (sat.executions e' he').2 t' ht'
  have hpend : t'.status ≠ .pending := by
    intro h
    rw [h] at hended
    cases hended
  have hspec' : T.taskSpec p e' t'.name = .ok spec := by rw [ht'n, hspecs]; exact hspec
  have hinp := RT.tasks.input e' he' t' ht' spec hspec' hpend
  simp only [hin] at hinp
  rw [hid, ht'n, hnone] at hinp
  rcases hinp with ⟨-, hfail, -, hnb⟩ | ⟨v, hv, -⟩
  · exact RT.policies.tasks e' he' t' ht' hfail (by rw [ht'n]; exact hnb) spec hspec'
  · cases hv

/-- A failed task output transform of `s` falls under the continue policy of the task: in `T` the same
    task result was transformed (`Saturated`), with the behavior's answer, a failure (`TaskConform`),
    which `PolicyConform` of `T` allows only under `continue`. -/
theorem taskOutput_continue (hs : Reachable p s) (hT : T.WellKeyed) (RT : RunConform p env T)
    (sat : Saturated p T) (cov : Covers p T s) {eid name : String} {index : Nat} {e : Execution}
    {spec : TaskSpec} {r : TaskResult} (he : s.execution? eid = some e) (hspec : s.taskSpec p e name = .ok spec)
    (hout : spec.output.isSome = true)
    (hr : s.taskResults.find? (fun x => x.execution == eid && x.task == name && x.index == index) = some r)
    (hnone : env.behavior.taskOutput eid name index = none) : spec.policy = .continue := by
  obtain ⟨e', he', hid, -, heT, hspecs⟩ := execution_covered hs hT cov he
  have hk : r.execution = eid ∧ r.task = name ∧ r.index = index := by
    simpa [and_assoc] using List.find?_some hr
  obtain ⟨r', hr', hx, htk, hix, -, -⟩ := cov.taskResults r (List.mem_of_find?_eq_some hr)
  rw [hk.1] at hx
  rw [hk.2.1] at htk
  rw [hk.2.2] at hix
  have hspec' : T.taskSpec p e' name = .ok spec := by rw [hspecs]; exact hspec
  obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec'
  have hne : r'.output ≠ .pending := by
    refine sat.outputs e' he' cc hcc r' hr' (by rw [hx, hid]) ⟨spec, List.mem_of_find?_eq_some hfind, ?_, hout⟩
    rw [htk]
    simpa using List.find?_some hfind
  obtain ⟨hval, -⟩ := RT.tasks.output r' hr'
  have hfailed : r'.output = .failed := by
    cases ho : r'.output with
    | pending => exact absurd ho hne
    | value v =>
      have h := hval v ho
      rw [hx, htk, hix, hnone] at h
      cases h
    | failed => rfl
  exact RT.policies.outputs r' hr' hfailed e' spec (by rw [hx]; exact heT) (by rw [htk]; exact hspec')

end NoStopAux

section NoStop
variable {p : Definition} {env : Env}

/-- If one conforming execution completes, no conforming execution of the same environment without the
    caller's cancel ever stops: every stopping step is a stop-policy failure, and the complete run met the
    same failure (same behavior, `Saturated`, `RunConform`) under the same policy, which by
    `PolicyConform` it could not have. -/
theorem no_stop (valid : p.validate = .ok ()) (nocancel : env.cancels = false) {tr₁ tr₂ : List Op} {T s : State}
    (h₁ : Conforming p env tr₁ T) (done : Done T) (h₂ : Conforming p env tr₂ s) : Unstopped s := by
  have hT := h₁.reachable.wellKeyed
  have RT := runConform valid h₁ (Or.inr done)
  have sat := saturated valid h₁.reachable done
  induction h₂ with
  | nil => exact Or.inl rfl
  | @snoc tr s₀ s₁ op h₀ hc hs _ ih =>
    -- An unstopped state that is not running is done, and its step keeps the root run.
    by_cases hrun : s₀.status = .running
    case neg => exact Or.inr (NoStopAux.done_of_step hs hrun (ih.resolve_left hrun))
    have hr₀ := h₀.reachable
    have cov := covers_of_execution valid h₁ done h₀ ih
    -- A step that keeps the status keeps running.
    have keep : s₁.status = s₀.status → Unstopped s₁ := fun h => Or.inl (h.trans hrun)
    cases op with
    | start input =>
      obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
      exact keep rfl
    | invoke path name trigger =>
      obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
      rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
    | fetch id =>
      obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
      exact keep rfl
    | returned id value =>
      obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
      exact keep (by rw [(settleOwner_update hso).status, setCall_status, (accept_frame hacc).1])
    | judged id arm =>
      obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
      exact keep (by rw [setInvocation_status, setCall_status, (accept_frame hacc).1])
    | yielded id value =>
      obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
      exact keep (by rw [setCall_status, (accept_frame hacc).1])
    | ended id =>
      obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
      exact keep (by rw [(settleOwner_update hso).status, setCall_status])
    | failed id =>
      obtain ⟨-, -, c, hcl, -, hf⟩ := Step.failed_inv hs
      obtain ⟨c', hc', -, hend⟩ := hc
      rw [hcl] at hc'
      cases hc'
      obtain ⟨hcm, hcid⟩ := call?_eq_some hcl
      have hpol := NoStopAux.call_continue RT sat cov hcm (Or.inl (by rw [hcid]; exact hend))
      exact keep (NoStopAux.failCall_status_continue hf hpol)
    | timedOut id element =>
      obtain ⟨-, -, c, hcl, -, hf⟩ := Step.timedOut_inv hs
      obtain ⟨c', hc', -, hend⟩ := hc
      rw [hcl] at hc'
      cases hc'
      obtain ⟨hcm, hcid⟩ := call?_eq_some hcl
      have hpol := NoStopAux.call_continue RT sat cov hcm (Or.inr (Or.inl ⟨element, by rw [hcid]; exact hend⟩))
      exact keep (NoStopAux.failCall_status_continue hf hpol)
    | lost id =>
      obtain ⟨-, -, c, hcl, ⟨hst, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
      · obtain ⟨c', hc', hcase⟩ := hc
        rw [hcl] at hc'
        cases hc'
        -- A running or fetching call is not cancelling, so its script ends in a loss.
        have hend : (env.behavior.script id).ending = .lost := by
          rcases hcase with h | ⟨-, h⟩
          · rcases hst with h' | h' <;> rw [h'] at h <;> cases h
          · exact h
        obtain ⟨hcm, hcid⟩ := call?_eq_some hcl
        have hpol := NoStopAux.call_continue RT sat cov hcm (Or.inr (Or.inr (by rw [hcid]; exact hend)))
        exact keep (NoStopAux.failCall_status_continue hf hpol)
      · exact keep (by rw [(cancelOwner_update ho).status, setCall_status])
    | terminated id =>
      obtain ⟨-, -, _, -, -, ho⟩ := Step.terminated_inv hs
      exact keep (by rw [(cancelOwner_update ho).status, setCall_status])
    | deliver path index source value =>
      obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
      exact keep rfl
    | transformFailed path index source =>
      obtain ⟨-, -, w, c, tid, target, hdt, htid, htarget, ht⟩ := Step.transformFailed_inv hs
      have hpol := NoStopAux.transform_continue hT RT sat cov hdt htid htarget hc
      exact keep (by rw [ht, hpol]; rfl)
    | taskInput eid name value =>
      obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
      exact keep rfl
    | taskInputFailed eid name =>
      obtain ⟨-, -, e, ts, spec, tid, he, hts, -, hspec, hin, ht⟩ := Step.taskInputFailed_inv hs
      have hpol := NoStopAux.taskInput_continue hr₀ hT RT sat cov he hts hspec hin hc
      exact keep (by rw [ht, hpol]; rfl)
    | beginTask eid name =>
      obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
      rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact keep rfl
    | taskOutput eid name index value =>
      obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
      rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
    | taskOutputFailed eid name index =>
      obtain ⟨-, -, e, spec, r, he, hspec, hout, hr, -, ht⟩ := Step.taskOutputFailed_inv hs
      have hpol := NoStopAux.taskOutput_continue hr₀ hT RT sat cov he hspec hout hr hc
      exact keep (by rw [ht, hpol]; rfl)
    | settle path name =>
      obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
      rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
    | closeExecution eid =>
      obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
      rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact keep rfl
    | closeRun path =>
      obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
      rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
        rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
    | cancel =>
      -- Without the caller's cancel, `cancel` does not conform.
      have hcan : env.cancels = true := hc
      rw [nocancel] at hcan
      cases hcan
    | conclude =>
      obtain ⟨-, ⟨-, r, w, hr, -, -, rfl⟩ | ⟨hst, -, -⟩⟩ := Step.conclude_inv hs
      · -- The conclusion from a running state completes the root run.
        refine Or.inr ?_
        have hroot : (s₀.setRun { r with complete := true }).run? [] = some { r with complete := true } := by
          rw [run?_setRun]
          simp [(run?_eq_some hr).2, hr]
        show ((s₀.setRun { r with complete := true }).run? []).any (·.complete) = true
        rw [hroot]
        rfl
      · rw [hrun] at hst
        cases hst

end NoStop

end Suimon.Round3
