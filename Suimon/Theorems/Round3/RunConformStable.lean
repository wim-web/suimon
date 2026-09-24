import Suimon.Theorems.Round3.RunConformBase

/-! Helpers for [13] Round3/RunConform.lean — task E1: the input of an invocation stays available
    (`invocationInput_step`), and results with a task-output identity come only from `taskOutput`
    (`step_taskOutput_result`). -/

namespace Suimon.Round3
namespace RunConformAux
open State

variable {p : Definition} {s t : State} {op : Op}

/-! ### Invocation inputs -/

/-- The input an invocation took stays available: its run keeps its path and input, and deliveries are
    never withdrawn (a Single connection keeps its first delivery). -/
theorem invocationInput_step (h : Reachable p s) (hs : step p s op = .ok t) {path : Path} {r : Run}
    {w : Workflow} {name : String} {trigger : Option ResultId} {input : Option Value} (hr : s.run? path = some r)
    (hin : Step.invocationInput p s r w name trigger = .ok input) :
    ∃ r', t.run? path = some r' ∧ r'.workflow = r.workflow ∧ Step.invocationInput p t r' w name trigger = .ok input := by
  have g := step_grows hs
  obtain ⟨r', hr', hwf, hinp, -, -, -⟩ := ((Delivery.Reachable.inv h).kept hs).run? (step_wellKeyed h.wellKeyed hs) hr
  refine ⟨r', hr', hwf, ?_⟩
  have hpath : r'.path = r.path := by rw [(run?_eq_some hr').2, (run?_eq_some hr).2]
  rcases Step.invocationInput_inv hin with ⟨hsh, rfl, rfl⟩ | ⟨hsh, rfl, rfl⟩ | ⟨j, c, src, hsh, rfl, hres⟩ |
      ⟨j, c, src, d, hsh, rfl, hd, hout⟩
  · simp [Step.invocationInput, hsh, need]
  · simp [Step.invocationInput, hsh, need, hinp]
  · have hres' := Delivery.resolveSingle_value_kept g hres
    rw [← hpath] at hres'
    simp [Step.invocationInput, hsh, need, hres', require]
  · have hd' := g.delivery?_eq_some hd
    rw [← hpath] at hd'
    rcases hout with ⟨v, hv, rfl⟩ | ⟨hv, rfl⟩ <;> simp [Step.invocationInput, hsh, need, hd', hv]

/-! ### Task-output results -/

theorem callResult_ne_taskOutput {x e n : String} {k i : Nat} : Key.callResult x k ≠ Key.taskOutput e n i :=
  Key.ne_of_kind? (by simp)

theorem aggregate_ne_taskOutput {path : Path} {x e n : String} {i : Nat} :
    Key.aggregate path x ≠ Key.taskOutput e n i :=
  Key.ne_of_kind? (by simp)

theorem list_ne_taskOutput {x e n : String} {i : Nat} : Key.list x ≠ Key.taskOutput e n i :=
  Key.ne_of_kind? (by simp)

theorem returned_ne_taskOutput {x e n : String} {i : Nat} : Key.returned x ≠ Key.taskOutput e n i :=
  Key.ne_of_kind? (by simp)

theorem taskOutput_inj {a b m n : String} {i j : Nat} (h : Key.taskOutput a m i = Key.taskOutput b n j) :
    a = b ∧ m = n ∧ i = j := Key.taskOutput_inj h

/-- A result accepted from a call carries a call-result identity. -/
theorem accept_results {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State}
    (h : s.accept c index value arm = .ok s') {r : Result} (hr : r ∈ s'.results) :
    r ∈ s.results ∨ r.id = Key.callResult c.id index := by
  rcases accept_eq_ok.mp h with ⟨-, _, -, -, rfl⟩ | ⟨_, -, -, rfl⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact Or.inl hr
    · exact Or.inr rfl
  · exact Or.inl hr

/-- A result with a task-output identity after a step was there before, or `taskOutput` just added it
    together with the transformed task result. -/
theorem step_taskOutput_result (hs : step p s op = .ok t) {r : Result} (hr : r ∈ t.results) {eid name : String}
    {k : Nat} (hid : r.id = Key.taskOutput eid name k) :
    r ∈ s.results ∨ ∃ tr ∈ t.taskResults, tr.execution = eid ∧ tr.task = name ∧ tr.index = k ∧
      tr.output = .value r.value := by
  have same : t.results = s.results → r ∈ s.results ∨ ∃ tr ∈ t.taskResults, tr.execution = eid ∧ tr.task = name ∧
      tr.index = k ∧ tr.output = .value r.value := fun h => Or.inl (h ▸ hr)
  have acc : ∀ {c : Call} {index : Nat} {value : Value} {arm : Option String} {s' : State},
      s.accept c index value arm = .ok s' → t.results = s'.results →
      r ∈ s.results ∨ ∃ tr ∈ t.taskResults, tr.execution = eid ∧ tr.task = name ∧ tr.index = k ∧
        tr.output = .value r.value := by
    intro c index value arm s' hacc ht
    rw [ht] at hr
    rcases accept_results hacc hr with hr | hr
    · exact Or.inl hr
    · exact absurd (hr.symm.trans hid) callResult_ne_taskOutput
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
    exact acc hacc (by rw [(settleOwner_update hso).results, setCall_results])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact acc hacc (by rw [setInvocation_results, setCall_results])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact acc hacc (by rw [setCall_results])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact same (by rw [(settleOwner_update hso).results, setCall_results])
  | failed id =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.failed_inv hs
    obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact same (by simp [(settleOwner_update hso).results])
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, hf⟩ := Step.timedOut_inv hs
    obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
    exact same (by simp [(settleOwner_update hso).results])
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, hf⟩ | ⟨-, ho⟩⟩ := Step.lost_inv hs
    · obtain ⟨f, s', -, hso, rfl⟩ := failCall_eq_ok.mp hf
      exact same (by simp [(settleOwner_update hso).results])
    · exact same (by rw [(cancelOwner_update ho).results, setCall_results])
  | terminated id =>
    obtain ⟨-, -, _, -, -, ho⟩ := Step.terminated_inv hs
    exact same (by rw [(cancelOwner_update ho).results, setCall_results])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact same rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact same (by simp)
  | taskInput eid' name' value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact same rfl
  | taskInputFailed eid' name' =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact same (by simp)
  | beginTask eid' name' =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, -, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> exact same rfl
  | taskOutput eid' name' index value =>
    obtain ⟨-, -, e₁, c₁, spec₁, r₀, he₁, hc₁, hspec₁, hout₁, hr₀, hp, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · obtain ⟨h1, h2, h3⟩ := taskOutput_inj hid
        have hk : r₀.execution = eid' ∧ r₀.task = name' ∧ r₀.index = index := by
          simpa [and_assoc] using List.find?_some hr₀
        refine Or.inr ⟨{ r₀ with output := .value value }, ?_, hk.1.trans h1, hk.2.1.trans h2, hk.2.2.trans h3, rfl⟩
        simp only [setTaskResult_taskResults]
        exact List.mem_map.mpr ⟨r₀, List.mem_of_find?_eq_some hr₀, by simp⟩
    · exact same rfl
  | taskOutputFailed eid' name' index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact same (by simp)
  | settle path name' =>
    obtain ⟨-, -, _, _, pl, _, _, _, _, -, -, -, -, -, -, -, hout, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨res, rfl, -, rfl⟩
    · exact same rfl
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · have := ((settleOutcome_some hout).2.2.2 r rfl).2.1
        exact absurd (this.symm.trans hid) aggregate_ne_taskOutput
  | closeExecution eid' =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact same rfl
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact Or.inl hr
      · exact absurd hid list_ne_taskOutput
    · exact same rfl
  | closeRun path =>
    obtain ⟨-, -, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact Or.inl hr
        · exact absurd hid returned_ne_taskOutput
      all_goals exact same rfl
    · rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact same rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact same rfl
  | conclude =>
    obtain ⟨-, ⟨-, _, _, -, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs <;> exact same rfl

end RunConformAux
end Suimon.Round3
