import Suimon.Theorems.Round3.Conformance

namespace Suimon.Round3
open State

/-! ## Helpers for [5] Round3/Fresh.lean — task B3: identities of results

Each kind of result identity starts with its own tag, so by `Key.kind?` an identity tells
which rule created the result. `ResultKeys` records, for every stored result, the record that
justifies its identity: the call of an invocation, the settlement, the transformed task result, the
complete execution or the complete sub-workflow run. It holds in every reachable state
(`reachable_resultKeys`), since the justifying records are never undone (`Delivery.Kept`). -/

namespace FreshAux

/-! ### Identities -/

theorem callResult_inj {a b : String} {m n : Nat} (h : Key.callResult a m = Key.callResult b n) :
    a = b ∧ m = n := Key.callResult_inj h

theorem aggregate_inj {a b : Path} {m n : String} (h : Key.aggregate a m = Key.aggregate b n) :
    a = b ∧ m = n := Key.aggregate_inj h

theorem taskOutput_inj {a b m n : String} {i j : Nat} (h : Key.taskOutput a m i = Key.taskOutput b n j) :
    a = b ∧ m = n ∧ i = j := Key.taskOutput_inj h

theorem list_inj {a b : String} (h : Key.list a = Key.list b) : a = b := Key.list_inj h

theorem returned_inj {a b : String} (h : Key.returned a = Key.returned b) : a = b := Key.returned_inj h

theorem task_inj {a b m n : String} (h : Key.task a m = Key.task b n) : a = b ∧ m = n := Key.task_inj h

theorem invocation_inj {a b : Path} {m n : String} {t t' : Option String}
    (h : Key.invocation a m t = Key.invocation b n t') : a = b ∧ m = n ∧ t = t' := Key.invocation_inj h

theorem invocation_ne_task {a : Path} {m b n : String} {t : Option String} :
    Key.invocation a m t ≠ Key.task b n := Key.invocation_ne_task

theorem aggregate_ne_callResult {path : Path} {name x : String} {k : Nat} :
    Key.aggregate path name ≠ Key.callResult x k := Key.aggregate_ne_callResult

theorem taskOutput_ne_callResult {e n x : String} {i k : Nat} : Key.taskOutput e n i ≠ Key.callResult x k :=
  Key.taskOutput_ne_callResult

theorem list_ne_callResult {e x : String} {k : Nat} : Key.list e ≠ Key.callResult x k := Key.list_ne_callResult

theorem returned_ne_callResult {o x : String} {k : Nat} : Key.returned o ≠ Key.callResult x k :=
  Key.returned_ne_callResult

/-! ### What a result identity says -/

/-- What the identity of a stored result says about its origin: a call result names a call of an
    invocation, an aggregate a settled placement, a task output a transformed task result, a list a
    complete execution, and a returned result a complete sub-workflow run of its owner. -/
def ResultKey (s : State) (r : Result) : Prop :=
  (∃ c ∈ s.calls, c.task = none ∧ ∃ k, r.id = Key.callResult c.id k) ∨
  (∃ path name, r.id = Key.aggregate path name ∧ (s.settled? path name).isSome) ∨
  (∃ tr ∈ s.taskResults, tr.output ≠ .pending ∧ r.id = Key.taskOutput tr.execution tr.task tr.index) ∨
  (∃ e ∈ s.executions, e.complete = true ∧ r.id = Key.list e.id) ∨
  (∃ run ∈ s.runs, ∃ o, run.owner = some o ∧ run.task = none ∧ run.complete = true ∧ r.id = Key.returned o)

/-- Every stored result is justified by its identity. -/
def ResultKeys (s : State) : Prop := ∀ r ∈ s.results, ResultKey s r

/-- The justifying records survive every step. -/
theorem ResultKey.kept {s t : State} {r : Result} (h : ResultKey s r) (K : Delivery.Kept s t) : ResultKey t r := by
  rcases h with ⟨c, hc, htask, k, hid⟩ | ⟨path, name, hid, hx⟩ | ⟨tr, htr, hout, hid⟩ | ⟨e, he, hcomp, hid⟩ |
      ⟨run, hrun, o, ho, htask, hcomp, hid⟩
  · obtain ⟨c', hc', h1, -, h3, -⟩ := K.call c hc
    exact Or.inl ⟨c', hc', h3.trans htask, k, by rw [h1]; exact hid⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hx
    exact Or.inr (Or.inl ⟨path, name, hid, by rw [K.settled? hx]; rfl⟩)
  · obtain ⟨tr', htr', h1, h2, h3, h4⟩ := K.taskResult tr htr
    exact Or.inr (Or.inr (Or.inl ⟨tr', htr', by rw [h4 hout]; exact hout, by rw [h1, h2, h3]; exact hid⟩))
  · obtain ⟨e', he', h1, -, -, -, h5⟩ := K.execution e he
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e', he', h5 hcomp, by rw [h1]; exact hid⟩)))
  · obtain ⟨run', hrun', -, -, -, h4, h5, h6⟩ := K.run run hrun
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨run', hrun', o, h4.trans ho, h5.trans htask, h6 hcomp, hid⟩)))

theorem ResultKey.callResult {s : State} {r : Result} (h : ResultKey s r) {x : String} {k : Nat}
    (hid : r.id = Key.callResult x k) : ∃ c ∈ s.calls, c.task = none ∧ c.id = x := by
  rcases h with ⟨c, hc, htask, k', h'⟩ | ⟨_, _, h', -⟩ | ⟨_, -, -, h'⟩ | ⟨_, -, -, h'⟩ | ⟨_, -, _, -, -, -, h'⟩
  · exact ⟨c, hc, htask, (callResult_inj (h'.symm.trans hid)).1⟩
  all_goals exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))

theorem ResultKey.aggregate {s : State} {r : Result} (h : ResultKey s r) {path : Path} {name : String}
    (hid : r.id = Key.aggregate path name) : (s.settled? path name).isSome := by
  rcases h with ⟨_, -, -, _, h'⟩ | ⟨path', name', h', hx⟩ | ⟨_, -, -, h'⟩ | ⟨_, -, -, h'⟩ | ⟨_, -, _, -, -, -, h'⟩
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · obtain ⟨rfl, rfl⟩ := aggregate_inj (h'.symm.trans hid)
    exact hx
  all_goals exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))

theorem ResultKey.taskOutput {s : State} {r : Result} (h : ResultKey s r) {e n : String} {i : Nat}
    (hid : r.id = Key.taskOutput e n i) :
    ∃ tr ∈ s.taskResults, tr.output ≠ .pending ∧ tr.execution = e ∧ tr.task = n ∧ tr.index = i := by
  rcases h with ⟨_, -, -, _, h'⟩ | ⟨_, _, h', -⟩ | ⟨tr, htr, hout, h'⟩ | ⟨_, -, -, h'⟩ | ⟨_, -, _, -, -, -, h'⟩
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · obtain ⟨h1, h2, h3⟩ := taskOutput_inj (h'.symm.trans hid)
    exact ⟨tr, htr, hout, h1, h2, h3⟩
  all_goals exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))

theorem ResultKey.list {s : State} {r : Result} (h : ResultKey s r) {e : String} (hid : r.id = Key.list e) :
    ∃ x ∈ s.executions, x.id = e ∧ x.complete = true := by
  rcases h with ⟨_, -, -, _, h'⟩ | ⟨_, _, h', -⟩ | ⟨_, -, -, h'⟩ | ⟨x, hx, hcomp, h'⟩ | ⟨_, -, _, -, -, -, h'⟩
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · exact ⟨x, hx, list_inj (h'.symm.trans hid), hcomp⟩
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))

theorem ResultKey.returned {s : State} {r : Result} (h : ResultKey s r) {o : String} (hid : r.id = Key.returned o) :
    ∃ run ∈ s.runs, run.owner = some o ∧ run.task = none ∧ run.complete = true := by
  rcases h with ⟨_, -, -, _, h'⟩ | ⟨_, _, h', -⟩ | ⟨_, -, -, h'⟩ | ⟨_, -, -, h'⟩ | ⟨run, hrun, o', ho, htask, hcomp, h'⟩
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · exact absurd (h'.symm.trans hid) (Key.ne_of_kind? (by simp))
  · obtain rfl := returned_inj (h'.symm.trans hid)
    exact ⟨run, hrun, ho, htask, hcomp⟩

/-! ### Every step keeps result identities justified -/

theorem settled?_isSome_of_mem {s : State} {x : Settled} (hx : x ∈ s.settled) :
    (s.settled? x.run x.placement).isSome := by
  unfold State.settled?
  exact List.find?_isSome.mpr ⟨x, hx, by simp⟩

theorem step_resultKeys {p : Definition} {s t : State} {op : Op} (h : Reachable p s) (hk : ResultKeys s)
    (hs : step p s op = .ok t) : ResultKeys t := by
  have wk := h.wellKeyed
  have K : Delivery.Kept s t :=
    Delivery.step_kept wk (h.eq_empty_or_started.imp (fun he => by rw [he]) id) hs
  intro r hr
  by_cases hold : r ∈ s.results
  · exact (hk r hold).kept K
  have hp := step_producer hs hr hold
  -- A result accepted from call `c` is identified by `Key.callResult c.id index`, for a call of an
  -- invocation.
  have accepted : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
      c ∈ s.calls → s.accept c index value arm = .ok s' → t.results = s'.results → ResultKey t r := by
    intro c index value arm s' hc ha ht
    rcases State.accept_eq_ok.mp ha with ⟨htask, i, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · rw [ht, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd hr hold
      · obtain ⟨c', hc', h1, -, h3, -⟩ := K.call c hc
        exact Or.inl ⟨c', hc', h3.trans htask, index, by rw [h1]⟩
    · exact absurd (ht ▸ hr) hold
  cases op
  case returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact accepted (call?_eq_some hc).1 hacc (by rw [(settleOwner_update hso).results, setCall_results])
  case judged id arm =>
    obtain ⟨-, -, c, _, _, _, _, _, s', hc, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact accepted (call?_eq_some hc).1 hacc (by rw [setInvocation_results, setCall_results])
  case yielded id value =>
    obtain ⟨-, -, c, s', hc, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact accepted (call?_eq_some hc).1 hacc (by rw [setCall_results])
  case taskOutput eid name index value =>
    obtain ⟨-, -, e, _, _, r0, -, -, -, -, hr0, -, hcases⟩ := Step.taskOutput_inv hs
    rcases hcases with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd (by simpa using hr) hold
      · -- The transformed task result is stored under the same key.
        have hkey := List.find?_some hr0
        simp only [Bool.and_eq_true, beq_iff_eq] at hkey
        obtain ⟨⟨h1, h2⟩, h3⟩ := hkey
        refine Or.inr (Or.inr (Or.inl ⟨{ r0 with output := .value value }, ?_, by simp, ?_⟩))
        · simp only [setTaskResult_taskResults]
          exact List.mem_map.mpr ⟨r0, List.mem_of_find?_eq_some hr0, by simp⟩
        · simp [h1, h2, h3]
    · exact absurd (by simpa using hr) hold
  case settle path name =>
    obtain ⟨-, -, _, _, pl, _, _, x, _, -, -, -, -, -, -, -, hout, hcases⟩ := Step.settle_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact absurd hr hold
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd hr hold
      · obtain ⟨-, hrun, hplace, hres⟩ := settleOutcome_some hout
        obtain ⟨-, hid, -⟩ := hres _ rfl
        refine Or.inr (Or.inl ⟨path, pl.name, hid, ?_⟩)
        have hmem : x ∈ ({ s with settled := s.settled ++ [x], results := s.results ++ [r] } : State).settled := by
          simp
        have := settled?_isSome_of_mem hmem
        rwa [hrun, hplace] at this
  case closeExecution eid =>
    obtain ⟨-, -, e, _, _, he, -, -, -, -, -, hcases⟩ := Step.closeExecution_inv hs
    rcases hcases with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact absurd (by simpa using hr) hold
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact absurd hr hold
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨{ e with complete := true }, ?_, rfl, ?_⟩)))
        · simp only [setInvocation_executions, setExecution_executions]
          exact List.mem_map.mpr ⟨e, (execution?_eq_some he).1, by simp⟩
        · simp [(execution?_eq_some he).2]
    · exact absurd (by simpa using hr) hold
  case closeRun path =>
    obtain ⟨-, -, r0, _, _, _, owner, hr0, -, -, -, -, -, -, howner, hcases⟩ := Step.closeRun_inv hs
    rcases hcases with ⟨htask, i, hi, hcases⟩ | ⟨_, _, _, -, -, -, hcases⟩
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact absurd hr hold
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨{ r0 with complete := true }, ?_, owner, howner, htask, rfl, ?_⟩)))
          · simp only [setInvocation_runs, setRun_runs]
            exact List.mem_map.mpr ⟨r0, (run?_eq_some hr0).1, by simp⟩
          · simp [(invocation?_eq_some hi).2]
      all_goals exact absurd (by simpa using hr) hold
    · rcases hcases with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact absurd (by simpa using hr) hold
  all_goals exact False.elim hp

theorem reachable_resultKeys {p : Definition} {s : State} (h : Reachable p s) : ResultKeys s := by
  induction h with
  | empty => intro r hr; simp at hr
  | step op hr hs ih => exact step_resultKeys hr ih hs

end FreshAux

end Suimon.Round3
