import Suimon.Theorems.Round3.RunConform

/-! Helpers for [14] Round3/CallConform.lean — task E2.

Identities of call results, the root run before the conclusion (a reachable running state is never
`Done`), and what a step keeps of a call it does not touch (`Frame`, `OwnerKept`). -/

namespace Suimon.Round3
open State

namespace CallConformAux

variable {p : Definition} {env : Env} {s t u : State}

theorem ite_of_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_of_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-! ### Identities -/

theorem callResult_inj {a b : String} {m n : Nat} (h : Key.callResult a m = Key.callResult b n) :
    a = b ∧ m = n := Key.callResult_inj h

theorem aggregate_ne_callResult {path : Path} {name x : String} {k : Nat} :
    Key.aggregate path name ≠ Key.callResult x k :=
  Key.ne_of_kind? (by simp)

theorem taskOutput_ne_callResult {e n x : String} {i k : Nat} : Key.taskOutput e n i ≠ Key.callResult x k :=
  Key.ne_of_kind? (by simp)

theorem list_ne_callResult {e x : String} {k : Nat} : Key.list e ≠ Key.callResult x k :=
  Key.ne_of_kind? (by simp)

theorem returned_ne_callResult {o x : String} {k : Nat} : Key.returned o ≠ Key.callResult x k :=
  Key.ne_of_kind? (by simp)

/-! ### The root run

Only `conclude` completes the root run, and it leaves a final status, so a reachable state that is
still running or stopping is not `Done`. -/

theorem run?_eq_of_runs {path : Path} (h : t.runs = s.runs) : t.run? path = s.run? path := by
  simp only [State.run?, h]

theorem run?_append_ne {x : Run} {path : Path} (hr : t.runs = s.runs ++ [x]) (hx : x.path ≠ path) :
    t.run? path = s.run? path := by
  simp [State.run?, hr, List.find?_append, hx]

/-- A step other than `conclude` does not complete the root run. -/
theorem step_root {op : Op} (hs : step p s op = .ok t) (hop : op ≠ .conclude) :
    (t.run? []).any (·.complete) = true → (s.run? []).any (·.complete) = true := by
  have keep : t.runs = s.runs → (t.run? []).any (·.complete) = true → (s.run? []).any (·.complete) = true :=
    fun h => by rw [run?_eq_of_runs h]; exact id
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    intro h
    simp [State.run?] at h
  | invoke path name trigger =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact keep rfl
    · exact keep rfl
    · rw [run?_append_ne rfl (Key.child_ne_nil _)]
      exact id
    · exact keep rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact keep rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact keep (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact keep (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact keep (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact keep (by rw [(settleOwner_update hso).runs, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact keep (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact keep (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact keep (failCall_runs h)
    · exact keep (by rw [(cancelOwner_update h).runs, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact keep (by rw [(cancelOwner_update h).runs, setCall_runs])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact keep rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact keep (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact keep rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact keep (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
    · exact keep rfl
    · rw [run?_append_ne (s := s) rfl (Key.child_ne_nil _)]
      exact id
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact keep rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact keep (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact keep rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact keep rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, -, hne, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    have hroot : (s.setRun { r with complete := true }).run? [] = s.run? [] := by
      rw [run?_setRun]
      have : r.path ≠ [] := by rw [(run?_eq_some hr).2]; exact hne
      simp [this]
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      · intro h'
        rw [← hroot]
        exact h'
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact keep rfl
  | conclude => exact absurd rfl hop

/-- A reachable `Done` state has a final status. -/
theorem done_terminal (h : Reachable p s) (done : Done s) : s.status.terminal = true := by
  revert done
  induction h with
  | empty => intro done; simp [Done, State.run?] at done
  | @step s t op hr hs ih =>
    intro done
    by_cases hop : op = .conclude
    · subst hop
      obtain ⟨-, ⟨-, r, w, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
      · simp only
        split
        · rfl
        · split <;> rfl
      · simp only
        split <;> rfl
    · have := ih (step_root hs hop done)
      rcases step_source_status hs with h' | h' <;> simp [h', Status.terminal] at this

/-- A reachable running state is not `Done`. -/
theorem not_done_of_running (h : Reachable p s) (running : s.status = .running) : ¬ Done s := fun done => by
  have := done_terminal h done
  simp [running, Status.terminal] at this

/-- A reachable unstopped state that takes a step is running. -/
theorem running_of_unstopped {op : Op} (h : Reachable p s) (us : Unstopped s) (hs : step p s op = .ok t) :
    s.status = .running := by
  rcases us with h' | done
  · exact h'
  · have := done_terminal h done
    rcases step_source_status hs with h'' | h'' <;> simp [h'', Status.terminal] at this

/-- The state before an unstopped state is unstopped: a stop is never undone, and a step from a
    stopping state keeps the runs. -/
theorem unstopped_prev {op : Op} (hs : step p s op = .ok t) (ht : Unstopped t) : Unstopped s := by
  rcases step_source_status hs with h | h
  · exact Or.inl h
  · have hne : t.status ≠ .running := (step_status hs).1 h
    have done : Done t := ht.resolve_left hne
    obtain ⟨-, -, hcases⟩ := step_of_status_ne_running hs (by simp [h])
    have hruns : t.runs = s.runs := by
      rcases hcases with ⟨c, -, -, hf⟩ | ⟨c, -, -, ho⟩ | rfl | ⟨-, rfl⟩
      · exact failCall_runs hf
      · rw [(cancelOwner_update ho).runs, setCall_runs]
      · rfl
      · rfl
    refine Or.inr ?_
    unfold Done at done ⊢
    rwa [run?_eq_of_runs hruns] at done

/-- A step from a running state that stops without touching the runs leads to a state that is not
    unstopped. -/
theorem stop_excluded (h : Reachable p s) (running : s.status = .running) (us : Unstopped t)
    (hst : t.status = .stopping) (hruns : t.runs = s.runs) : False := by
  rcases us with h' | done
  · rw [hst] at h'
    cases h'
  · refine not_done_of_running h running ?_
    unfold Done at done ⊢
    rwa [run?_eq_of_runs hruns] at done

/-! ### What a step keeps of a call it does not touch -/

/-- The results and task results of `c` after a step are ones it had before, with the same values. -/
structure Frame (s t : State) (c : Call) : Prop where
  results : ∀ r ∈ t.results, ∀ k, r.id = Key.callResult c.id k → r ∈ s.results
  taskResults : ∀ name, c.task = some name → ∀ r ∈ t.taskResults, r.execution = c.owner → r.task = name →
    ∃ r₀ ∈ s.taskResults, r₀.execution = r.execution ∧ r₀.task = r.task ∧ r₀.index = r.index ∧ r₀.value = r.value

/-- The owner of `c` keeps what it had: its invocation, or its task in its execution. -/
structure OwnerKept (s t : State) (c : Call) : Prop where
  invocation : c.task = none → ∀ i, s.invocation? c.owner = some i → t.invocation? c.owner = some i
  execution : ∀ name, c.task = some name → ∀ e ts, s.execution? c.owner = some e →
    e.tasks.find? (·.name == name) = some ts →
      ∃ e', t.execution? c.owner = some e' ∧ e'.tasks.find? (·.name == name) = some ts

namespace Frame
variable {c : Call}

theorem trans (h₁ : Frame s u c) (h₂ : Frame u t c) : Frame s t c where
  results r hr k hk := h₁.results r (h₂.results r hr k hk) k hk
  taskResults name hn r hr he ht := by
    obtain ⟨r₁, hr₁, a1, a2, a3, a4⟩ := h₂.taskResults name hn r hr he ht
    obtain ⟨r₀, hr₀, b1, b2, b3, b4⟩ := h₁.taskResults name hn r₁ hr₁ (a1.trans he) (a2.trans ht)
    exact ⟨r₀, hr₀, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

theorem of_eq (hr : t.results = s.results) (htr : t.taskResults = s.taskResults) : Frame s t c where
  results _ h _ _ := hr ▸ h
  taskResults _ _ r h _ _ := ⟨r, htr ▸ h, rfl, rfl, rfl, rfl⟩

theorem setCall {c' : Call} : Frame s (s.setCall c') c := of_eq rfl rfl
theorem setInvocation {i : Invocation} : Frame s (s.setInvocation i) c := of_eq rfl rfl

theorem appendResult {x : Result} (hr : t.results = s.results ++ [x]) (hne : ∀ k, x.id ≠ Key.callResult c.id k)
    (htr : t.taskResults = s.taskResults) : Frame s t c where
  results r h k hk := by
    rw [hr, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact h
    · exact absurd hk (hne k)
  taskResults _ _ r h _ _ := ⟨r, htr ▸ h, rfl, rfl, rfl, rfl⟩

theorem appendTaskResult {x : TaskResult} (htr : t.taskResults = s.taskResults ++ [x])
    (hne : ∀ name, c.task = some name → x.execution = c.owner → x.task ≠ name) (hr : t.results = s.results) :
    Frame s t c where
  results r h _ _ := hr ▸ h
  taskResults name hn r h he ht := by
    rw [htr, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact ⟨r, h, rfl, rfl, rfl, rfl⟩
    · exact absurd ht (hne name hn he)

theorem setTaskResult {x : TaskResult} {o : TaskOutput} (hx : x ∈ s.taskResults) :
    Frame s (s.setTaskResult { x with output := o }) c where
  results r h _ _ := by simpa using h
  taskResults _ _ r h _ _ := by
    rcases mem_setTaskResult_taskResults h with rfl | h
    · exact ⟨x, hx, rfl, rfl, rfl, rfl⟩
    · exact ⟨r, h, rfl, rfl, rfl, rfl⟩

/-- Accepting a value of another call. -/
theorem accept {c₀ : Call} {index : Nat} {value : Value} {arm : Option String}
    (ha : s.accept c₀ index value arm = .ok t) (hid : c.id ≠ c₀.id) (hown : c.task = c₀.task → c.owner ≠ c₀.owner) :
    Frame s t c := by
  rcases accept_eq_ok.mp ha with ⟨-, i, -, -, rfl⟩ | ⟨name, hn, -, rfl⟩
  · exact appendResult rfl (fun k h => hid (callResult_inj h).1.symm) rfl
  · refine appendTaskResult rfl (fun name' hn' he ht => ?_) rfl
    simp only at he ht
    exact hown (by rw [hn', hn, ht]) he.symm

end Frame

namespace OwnerKept
variable {c : Call}

theorem trans (h₁ : OwnerKept s u c) (h₂ : OwnerKept u t c) : OwnerKept s t c where
  invocation hn i hi := h₂.invocation hn i (h₁.invocation hn i hi)
  execution name hn e ts he hts := by
    obtain ⟨e₁, he₁, hts₁⟩ := h₁.execution name hn e ts he hts
    exact h₂.execution name hn e₁ ts he₁ hts₁

theorem of_eq (hi : t.invocations = s.invocations) (he : t.executions = s.executions) : OwnerKept s t c where
  invocation _ i h := by simpa [State.invocation?, hi] using h
  execution _ _ e ts h hts := ⟨e, by simpa [State.execution?, he] using h, hts⟩

theorem setCall {c' : Call} : OwnerKept s (s.setCall c') c := of_eq rfl rfl
theorem setRun {r : Run} : OwnerKept s (s.setRun r) c := of_eq rfl rfl

theorem setInvocation {i : Invocation} (hne : c.task = none → i.id ≠ c.owner) :
    OwnerKept s (s.setInvocation i) c where
  invocation hn i' h := by
    rw [invocation?_setInvocation, ite_of_neg (hne hn), h]
  execution _ _ e ts h hts := ⟨e, h, hts⟩

theorem setExecution {e e' : Execution} (he : s.execution? e.id = some e) (hid : e'.id = e.id)
    (htasks : e'.tasks = e.tasks) : OwnerKept s (s.setExecution e') c where
  invocation _ i h := h
  execution name _ e₀ ts h hts := by
    rw [execution?_setExecution]
    by_cases hx : e'.id = c.owner
    · rw [ite_of_pos hx, h]
      have : e₀ = e := by
        rw [← hx, hid, he] at h
        exact (Option.some.inj h).symm
      subst this
      exact ⟨e', rfl, by rw [htasks]; exact hts⟩
    · rw [ite_of_neg hx]
      exact ⟨e₀, h, hts⟩

/-- Storing a task that is not the task of `c`. -/
theorem setTask {e : Execution} {ts : TaskState} (he : s.execution? e.id = some e)
    (hne : ∀ name, c.task = some name → e.id = c.owner → ts.name ≠ name) : OwnerKept s (s.setTask e ts) c where
  invocation _ i h := h
  execution name hn e₀ ts₀ h hts := by
    rw [execution?_setTask]
    by_cases hx : e.id = c.owner
    · rw [ite_of_pos hx, h]
      have : e₀ = e := by
        rw [← hx, he] at h
        exact (Option.some.inj h).symm
      subst this
      refine ⟨withTask e₀ ts, rfl, ?_⟩
      rw [Settle.withTask_find?, ite_of_neg (hne name hn hx)]
      exact hts
    · rw [ite_of_neg hx]
      exact ⟨e₀, h, hts⟩

/-- Steps that only append invocations and executions. -/
theorem append (hi : ∃ l, t.invocations = s.invocations ++ l) (he : ∃ l, t.executions = s.executions ++ l) :
    OwnerKept s t c where
  invocation _ i h := by
    obtain ⟨l, hl⟩ := hi
    simp only [State.invocation?, hl, List.find?_append] at h ⊢
    rw [h]
    rfl
  execution _ _ e ts h hts := by
    obtain ⟨l, hl⟩ := he
    refine ⟨e, ?_, hts⟩
    simp only [State.execution?, hl, List.find?_append] at h ⊢
    rw [h]
    rfl

end OwnerKept

/-! ### Transporting the call invariant across a frame -/

/-- An untouched call keeps conforming: the step kept its records and its results. -/
theorem callConform_frame {c : Call} (h : CallConform env s c) (K : Delivery.Kept s t) (wk : t.WellKeyed)
    (F : Frame s t c) : CallConform env t c where
  yields := h.yields
  single := h.single
  returned := h.returned
  failed := h.failed
  lost := h.lost
  cancelled := h.cancelled
  results k := by
    rw [← h.results k]
    constructor
    · rintro ⟨r, hr, hk⟩
      exact ⟨r, F.results r hr k hk, hk⟩
    · rintro ⟨r, hr, hk⟩
      exact ⟨r, K.mem_results hr, hk⟩
  values r hr k hk := by
    obtain ⟨hprod, i, hi, h1, h2, h3, h4, h5⟩ := h.values r (F.results r hr k hk) k hk
    obtain ⟨hmem, hid⟩ := invocation?_eq_some hi
    obtain ⟨i', hi', a1, a2, a3, -, a5⟩ := K.invocation i hmem
    refine ⟨hprod, i', ?_, h1.trans a2.symm, h2.trans a3.symm, h3, h4, fun a hs ha => ?_⟩
    · rw [← hid, ← a1]
      exact wk.invocation?_of_mem hi'
    · rw [a5]
      exact h5 a hs ha
  taskResults name hn k := by
    rw [← h.taskResults name hn k]
    constructor
    · rintro ⟨r, hr, he, ht, hk⟩
      obtain ⟨r₀, hr₀, a1, a2, a3, -⟩ := F.taskResults name hn r hr he ht
      exact ⟨r₀, hr₀, a1.trans he, a2.trans ht, a3.trans hk⟩
    · rintro ⟨r, hr, he, ht, hk⟩
      obtain ⟨r', hr', a1, a2, a3, -⟩ := K.taskResult r hr
      exact ⟨r', hr', a1.trans he, a2.trans ht, a3.trans hk⟩
  taskValues name hn r hr he ht := by
    obtain ⟨r₀, hr₀, a1, a2, a3, a4⟩ := F.taskResults name hn r hr he ht
    obtain ⟨b1, b2⟩ := h.taskValues name hn r₀ hr₀ (a1.trans he) (a2.trans ht)
    rw [a3, a4] at b1
    rw [a4] at b2
    exact ⟨b1, b2⟩

/-- An untouched call keeps its owner's status. -/
theorem ownerConform_frame {c : Call} (h : OwnerConform s c) (O : OwnerKept s t c) : OwnerConform t c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hst => ?_, fun hst => ?_⟩
  · have := h1 hst
    revert this
    rcases hn : c.task with _ | name
    · rintro ⟨i, hi, hs⟩
      exact ⟨i, O.invocation hn i hi, hs⟩
    · rintro ⟨e, ts, he, hts, hs⟩
      obtain ⟨e', he', hts'⟩ := O.execution name hn e ts he hts
      exact ⟨e', ts, he', hts', hs⟩
  · have := h2 hst
    revert this
    rcases hn : c.task with _ | name
    · rintro ⟨i, hi, hs⟩
      exact ⟨i, O.invocation hn i hi, hs⟩
    · rintro ⟨e, ts, he, hts, hs⟩
      obtain ⟨e', he', hts'⟩ := O.execution name hn e ts he hts
      exact ⟨e', ts, he', hts', hs⟩

end CallConformAux

end Suimon.Round3
