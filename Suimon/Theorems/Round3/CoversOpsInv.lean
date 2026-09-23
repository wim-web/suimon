import Suimon.Theorems.Round3.CoversOpsFrame

/-! Helpers for [22] Round3/CoversOps.lean — task F4: `Created` holds in every reachable state.

Steps that create nothing keep it by the frame argument of `CoversOpsFrame`. The creating steps
(`start`, `invoke`, `beginTask`) add records whose fields they copy from their owner (`append*`). -/

namespace Suimon.Round3
namespace CoversOpsAux
open State

variable {p : Program} {s t u : State}

/-! ### Lookups -/

theorem workflow?_of_runs (h : t.runs = s.runs) {path : Path} : t.workflow? p path = s.workflow? p path := by
  simp [State.workflow?, State.run?, h]

theorem concurrencyOf_of_runs (h : t.runs = s.runs) {e : Execution} : t.concurrencyOf p e = s.concurrencyOf p e := by
  simp [State.concurrencyOf, State.placementOf, State.workflow?, State.run?, h]

/-- Appending a run with a new path keeps every lookup of an existing path. -/
theorem run?_append {x : Run} (h : t.runs = s.runs ++ [x]) {path : Path} (hp : (s.run? path).isSome) :
    t.run? path = s.run? path := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hp
  rw [hr]
  simp only [State.run?, h, List.find?_append] at hr ⊢
  rw [hr, Option.some_or]

theorem workflow?_append {x : Run} (h : t.runs = s.runs ++ [x]) {path : Path} (hp : (s.run? path).isSome) :
    t.workflow? p path = s.workflow? p path := by
  simp only [State.workflow?, run?_append h hp]

theorem concurrencyOf_append {x : Run} (h : t.runs = s.runs ++ [x]) {e : Execution} (hp : (s.run? e.run).isSome) :
    t.concurrencyOf p e = s.concurrencyOf p e := by
  simp only [State.concurrencyOf, State.placementOf, workflow?_append h hp]

theorem taskSpec_append {x : Run} (h : t.runs = s.runs ++ [x]) {e : Execution} (hp : (s.run? e.run).isSome)
    {name : String} : t.taskSpec p e name = s.taskSpec p e name := by
  simp only [State.taskSpec, concurrencyOf_append h hp]

/-- More calls and runs: a task that has not begun after had not begun before. -/
theorem notBegun_mono (hc : ∀ c ∈ s.calls, c ∈ t.calls) (hr : ∀ r ∈ s.runs, r ∈ t.runs) {e : Execution}
    {name : String} (h : NotBegun t e name) : NotBegun s e name := by
  refine ⟨?_, fun r hr' => h.2 r (hr r hr')⟩
  rcases hcs : s.call? (Key.task e.id name) with _ | c
  · rfl
  · obtain ⟨hcm, hcid⟩ := State.call?_eq_some hcs
    exact absurd h.1 fun h1 => State.call?_eq_none_iff.mp h1 (List.mem_map.mpr ⟨c, hc c hcm, hcid⟩)

/-! ### Same records -/

theorem Created.congr (hC : Created p s) (hc : t.calls = s.calls) (hi : t.invocations = s.invocations)
    (hr : t.runs = s.runs) (he : t.executions = s.executions) : Created p t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc' htask i hi'
    rw [hc] at hc'; rw [hi] at hi'
    simpa only [workflow?_of_runs hr] using h1 c hc' htask i hi'
  · intro c hc' name htask e he'
    rw [hc] at hc'; rw [he] at he'
    simpa only [taskSpec_of_runs hr] using h2 c hc' name htask e he'
  · intro r hr' htask i hi'
    rw [hr] at hr'; rw [hi] at hi'
    exact h3 r hr' htask i hi'
  · intro r hr' name htask e he'
    rw [hr] at hr'; rw [he] at he'
    simpa only [taskSpec_of_runs hr] using h4 r hr' name htask e he'
  · intro e he' i hi'
    rw [he] at he'; rw [hi] at hi'
    exact h5 e he' i hi'
  · intro e he' cc hcc
    rw [he] at he'
    rw [concurrencyOf_of_runs hr] at hcc
    exact h6 e he' cc hcc
  · intro e he' tk htk hp
    rw [he] at he'
    exact h7 e he' tk htk hp
  · intro e he' tk htk hf
    rw [he] at he'
    exact (h8 e he' tk htk hf).congr hc hr

theorem Created.empty : Created p {} :=
  ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-! ### Creating records -/

/-- An invocation that owns nothing yet. -/
theorem Created.appendInvocation (hC : Created p s) {i : Invocation}
    (hi : t.invocations = s.invocations ++ [i]) (hc : t.calls = s.calls) (hr : t.runs = s.runs)
    (he : t.executions = s.executions)
    (hcalls : ∀ c ∈ s.calls, c.task = none → c.owner ≠ i.id)
    (hruns : ∀ r ∈ s.runs, r.task = none → r.owner ≠ some i.id)
    (hexecs : ∀ e ∈ s.executions, e.id ≠ i.id) : Created p t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc' htask i' hi' hid
    rw [hc] at hc'
    rw [hi, List.mem_append, List.mem_singleton] at hi'
    rcases hi' with hi' | rfl
    · simpa only [workflow?_of_runs hr] using h1 c hc' htask i' hi' hid
    · exact absurd hid.symm (hcalls c hc' htask)
  · intro c hc' name htask e he'
    rw [hc] at hc'; rw [he] at he'
    simpa only [taskSpec_of_runs hr] using h2 c hc' name htask e he'
  · intro r hr' htask i' hi' ho
    rw [hr] at hr'
    rw [hi, List.mem_append, List.mem_singleton] at hi'
    rcases hi' with hi' | rfl
    · exact h3 r hr' htask i' hi' ho
    · exact absurd ho (hruns r hr' htask)
  · intro r hr' name htask e he'
    rw [hr] at hr'; rw [he] at he'
    simpa only [taskSpec_of_runs hr] using h4 r hr' name htask e he'
  · intro e he' i' hi' hid
    rw [he] at he'
    rw [hi, List.mem_append, List.mem_singleton] at hi'
    rcases hi' with hi' | rfl
    · exact h5 e he' i' hi' hid
    · exact absurd hid.symm (hexecs e he')
  · intro e he' cc hcc
    rw [he] at he'
    rw [concurrencyOf_of_runs hr] at hcc
    exact h6 e he' cc hcc
  · intro e he' tk htk hp
    rw [he] at he'
    exact h7 e he' tk htk hp
  · intro e he' tk htk hf
    rw [he] at he'
    exact (h8 e he' tk htk hf).congr hc hr

/-- A call that copies its fields from its owner. -/
theorem Created.appendCall (hC : Created p s) {c : Call}
    (hc : t.calls = s.calls ++ [c]) (hi : t.invocations = s.invocations) (hr : t.runs = s.runs)
    (he : t.executions = s.executions)
    (hinv : c.task = none → ∀ i ∈ s.invocations, i.id = c.owner → c.input = i.input ∧
      ∀ w pl, s.workflow? p i.run = some w → w.placement? i.placement = some pl →
        c.timeout = pl.timeout ∧ c.policy = pl.policy)
    (htask : ∀ name, c.task = some name → ∀ e ∈ s.executions, e.id = c.owner →
      (∀ tk ∈ e.tasks, tk.name = name → c.input = tk.input) ∧
      ∀ spec, s.taskSpec p e name = .ok spec → c.timeout = spec.timeout ∧ c.policy = spec.policy ∧
        ∃ f decl, spec.body = .function f ∧ p.function? f = some decl ∧ c.target = .function f ∧
          c.stream = (decl.output.kind == .stream)) : Created p t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc' htask' i hi'
    rw [hi] at hi'
    rw [hc, List.mem_append, List.mem_singleton] at hc'
    rw [workflow?_of_runs hr]
    rcases hc' with hc' | rfl
    · exact h1 c' hc' htask' i hi'
    · exact hinv htask' i hi'
  · intro c' hc' name htask' e he'
    rw [he] at he'
    rw [hc, List.mem_append, List.mem_singleton] at hc'
    rw [taskSpec_of_runs hr]
    rcases hc' with hc' | rfl
    · exact h2 c' hc' name htask' e he'
    · exact htask name htask' e he'
  · intro r hr' htask' i hi'
    rw [hr] at hr'; rw [hi] at hi'
    exact h3 r hr' htask' i hi'
  · intro r hr' name htask' e he'
    rw [hr] at hr'; rw [he] at he'
    simpa only [taskSpec_of_runs hr] using h4 r hr' name htask' e he'
  · intro e he' i hi'
    rw [he] at he'; rw [hi] at hi'
    exact h5 e he' i hi'
  · intro e he' cc hcc
    rw [he] at he'
    rw [concurrencyOf_of_runs hr] at hcc
    exact h6 e he' cc hcc
  · intro e he' tk htk hp
    rw [he] at he'
    exact h7 e he' tk htk hp
  · intro e he' tk htk hf
    rw [he] at he'
    rcases h8 e he' tk htk hf with hj | ⟨spec, tid, hspec, hin⟩
    · exact Or.inl fun hnb => hj (notBegun_mono (fun c' h' => by rw [hc]; exact List.mem_append_left _ h')
        (fun r h' => by rw [hr]; exact h') hnb)
    · exact Or.inr ⟨spec, tid, by rw [taskSpec_of_runs hr]; exact hspec, hin⟩

/-- A run with a new path that copies its input from its owner. -/
theorem Created.appendRun (hC : Created p s) {r : Run}
    (hr : t.runs = s.runs ++ [r]) (hc : t.calls = s.calls) (hi : t.invocations = s.invocations)
    (he : t.executions = s.executions)
    (hinvs : ∀ i ∈ s.invocations, (s.run? i.run).isSome) (hexecs : ∀ e ∈ s.executions, (s.run? e.run).isSome)
    (hinv : r.task = none → ∀ i ∈ s.invocations, r.owner = some i.id → r.input = i.input)
    (htask : ∀ name, r.task = some name → ∀ e ∈ s.executions, r.owner = some e.id →
      (∀ tk ∈ e.tasks, tk.name = name → r.input = tk.input) ∧
      ∀ spec, s.taskSpec p e name = .ok spec → ∃ out, spec.body = .workflow r.workflow out) :
    Created p t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc' htask' i hi'
    rw [hc] at hc'; rw [hi] at hi'
    rw [workflow?_append hr (hinvs i hi')]
    exact h1 c hc' htask' i hi'
  · intro c hc' name htask' e he'
    rw [hc] at hc'; rw [he] at he'
    rw [taskSpec_append hr (hexecs e he')]
    exact h2 c hc' name htask' e he'
  · intro r' hr' htask' i hi'
    rw [hi] at hi'
    rw [hr, List.mem_append, List.mem_singleton] at hr'
    rcases hr' with hr' | rfl
    · exact h3 r' hr' htask' i hi'
    · exact hinv htask' i hi'
  · intro r' hr' name htask' e he'
    rw [he] at he'
    rw [hr, List.mem_append, List.mem_singleton] at hr'
    rw [taskSpec_append hr (hexecs e he')]
    rcases hr' with hr' | rfl
    · exact h4 r' hr' name htask' e he'
    · exact htask name htask' e he'
  · intro e he' i hi'
    rw [he] at he'; rw [hi] at hi'
    exact h5 e he' i hi'
  · intro e he' cc hcc
    rw [he] at he'
    rw [concurrencyOf_append hr (hexecs e he')] at hcc
    exact h6 e he' cc hcc
  · intro e he' tk htk hp
    rw [he] at he'
    exact h7 e he' tk htk hp
  · intro e he' tk htk hf
    rw [he] at he'
    rcases h8 e he' tk htk hf with hj | ⟨spec, tid, hspec, hin⟩
    · exact Or.inl fun hnb => hj (notBegun_mono (fun c' h' => by rw [hc]; exact h')
        (fun r' h' => by rw [hr]; exact List.mem_append_left _ h') hnb)
    · exact Or.inr ⟨spec, tid, by rw [taskSpec_append hr (hexecs e he')]; exact hspec, hin⟩

/-- An execution with a new identity that copies its input from its owner, with waiting tasks. -/
theorem Created.appendExecution (hC : Created p s) {e : Execution}
    (he : t.executions = s.executions ++ [e]) (hc : t.calls = s.calls) (hi : t.invocations = s.invocations)
    (hr : t.runs = s.runs)
    (hcalls : ∀ c ∈ s.calls, ∀ name, c.task = some name → c.owner ≠ e.id)
    (hruns : ∀ r ∈ s.runs, ∀ name, r.task = some name → r.owner ≠ some e.id)
    (hinv : ∀ i ∈ s.invocations, i.id = e.id → e.input = i.input)
    (hnames : ∀ cc, s.concurrencyOf p e = .ok cc → e.tasks.map (·.name) = cc.tasks.map (·.name))
    (hpend : ∀ tk ∈ e.tasks, tk.status = .pending → tk.input = none)
    (hfail : ∀ tk ∈ e.tasks, tk.status ≠ .failed) : Created p t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc' htask' i hi'
    rw [hc] at hc'; rw [hi] at hi'
    simpa only [workflow?_of_runs hr] using h1 c hc' htask' i hi'
  · intro c hc' name htask' e' he'
    rw [hc] at hc'
    rw [he, List.mem_append, List.mem_singleton] at he'
    rw [taskSpec_of_runs hr]
    rcases he' with he' | rfl
    · exact h2 c hc' name htask' e' he'
    · exact fun hid => absurd hid.symm (hcalls c hc' name htask')
  · intro r hr' htask' i hi'
    rw [hr] at hr'; rw [hi] at hi'
    exact h3 r hr' htask' i hi'
  · intro r hr' name htask' e' he'
    rw [hr] at hr'
    rw [he, List.mem_append, List.mem_singleton] at he'
    rw [taskSpec_of_runs hr]
    rcases he' with he' | rfl
    · exact h4 r hr' name htask' e' he'
    · exact fun ho => absurd ho (hruns r hr' name htask')
  · intro e' he' i hi'
    rw [hi] at hi'
    rw [he, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact h5 e' he' i hi'
    · exact hinv i hi'
  · intro e' he' cc hcc
    rw [concurrencyOf_of_runs hr] at hcc
    rw [he, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact h6 e' he' cc hcc
    · exact hnames cc hcc
  · intro e' he' tk htk hp
    rw [he, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact h7 e' he' tk htk hp
    · exact hpend tk htk hp
  · intro e' he' tk htk hf
    rw [he, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact (h8 e' he' tk htk hf).congr hc hr
    · exact absurd hf (hfail tk htk)

/-! ### Every step keeps `Created` -/

theorem step_created (h : Reachable p s) (hC : Created p s) {op : Op} (hs : step p s op = .ok t) :
    Created p t := by
  have inv := Delivery.Reachable.inv h
  have lim := Limit.reachable_inv h
  have wk := inv.wk
  have wk' := step_wellKeyed wk hs
  have K := inv.kept hs
  have fr : Frame p s t → Created p t := fun F => hC.of_frame inv lim wk' F
  cases op with
  | start input =>
    obtain ⟨hst, -, _, -, -, rfl⟩ := Step.start_inv hs
    obtain rfl : s = {} := inv.fresh hst
    refine ⟨by simp, by simp, ?_, ?_, by simp, by simp, by simp, by simp⟩
    · intro r _ _ i hi
      simp at hi
    · intro r hr name htask
      simp only [List.mem_singleton] at hr
      subst hr
      simp at htask
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, -, rfl, -, hid', h⟩ := Step.invoke_inv hs
    have fresh : ∀ i ∈ s.invocations, i.id ≠ Key.invocation path name trigger := fun i hi hid =>
      State.invocation?_eq_none_iff.mp hid' (List.mem_map.mpr ⟨i, hi, hid⟩)
    have hcalls : ∀ c ∈ s.calls, c.task = none → c.owner ≠ Key.invocation path name trigger := by
      intro c hc htask ho
      rcases inv.own.calls c hc with ⟨-, -, i, hi, hio, -⟩ | ⟨name', htask', -⟩
      · exact fresh i hi (hio.trans ho)
      · rw [htask] at htask'; cases htask'
    have hruns : ∀ r' ∈ s.runs, r'.task = none → r'.owner ≠ some (Key.invocation path name trigger) := by
      intro r' hr' htask ho
      rcases inv.own.runs r' hr' with ⟨ho', -, -⟩ | ⟨-, i, hi, hio, -⟩ | ⟨name', htask', -⟩
      · rw [ho'] at ho; cases ho
      · rw [hio] at ho; exact fresh i hi (Option.some.inj ho)
      · rw [htask] at htask'; cases htask'
    have hexecs : ∀ e ∈ s.executions, e.id ≠ Key.invocation path name trigger := by
      intro e he hid
      obtain ⟨i, hi, hie, -⟩ := inv.own.executions e he
      exact fresh i hi (hie.trans hid)
    have hwf : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
    -- The new invocation, before its body.
    have hu : Created p { s with invocations := s.invocations ++
        [{ id := Key.invocation path name trigger, run := path, placement := name, trigger, input }] } :=
      hC.appendInvocation rfl rfl rfl rfl hcalls hruns hexecs
    -- Its only invocation with the new identity is the new one.
    have only : ∀ i ∈ s.invocations ++
        [{ id := Key.invocation path name trigger, run := path, placement := name, trigger, input }],
        i.id = Key.invocation path name trigger →
        i = { id := Key.invocation path name trigger, run := path, placement := name, trigger, input } := by
      intro i hi hid
      rcases List.mem_append.mp hi with hi | hi
      · exact absurd hid (fresh i hi)
      · exact List.mem_singleton.mp hi
    have callFields : ∀ (c : Call), c.owner = Key.invocation path name trigger → c.input = input →
        c.timeout = pl.timeout → c.policy = pl.policy → c.task = none →
        ∀ i ∈ s.invocations ++
          [{ id := Key.invocation path name trigger, run := path, placement := name, trigger, input }],
        i.id = c.owner → c.input = i.input ∧ ∀ w' pl', s.workflow? p i.run = some w' →
          w'.placement? i.placement = some pl' → c.timeout = pl'.timeout ∧ c.policy = pl'.policy := by
      intro c ho hin hto hpo _ i hi hid
      obtain rfl := only i hi (hid.trans ho)
      refine ⟨hin, fun w' pl' hw' hpl' => ?_⟩
      rw [hwf] at hw'
      cases hw'
      rw [hpl] at hpl'
      cases hpl'
      exact ⟨hto, hpo⟩
    rcases h with ⟨f, decl, hf, hdecl, -, rfl⟩ | ⟨judge, arms, hb, -, rfl⟩ | ⟨wf, out, hwf', -, rfl⟩ |
        ⟨cc, hcc, -, rfl⟩
    · exact hu.appendCall rfl rfl rfl rfl (callFields _ rfl rfl rfl rfl) fun _ h' => by cases h'
    · exact hu.appendCall rfl rfl rfl rfl (callFields _ rfl rfl rfl rfl) fun _ h' => by cases h'
    · refine hu.appendRun rfl rfl rfl rfl ?_ ?_ ?_ fun _ h' => by cases h'
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · obtain ⟨-, w₀, -, -, hw₀, -⟩ := inv.own.invocations i hi
          obtain ⟨r₀, hr₀, -⟩ := Delivery.workflow?_iff.mp hw₀
          show (s.run? i.run).isSome
          rw [hr₀]; rfl
        · rw [List.mem_singleton.mp hi]
          show (s.run? path).isSome
          rw [hr]; rfl
      · exact lim.execRuns
      · intro _ i hi ho
        rw [only i hi (Option.some.inj ho).symm]
    · refine hu.appendExecution rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
      · intro c hc name' htask ho
        obtain ⟨e, he, hid, -⟩ := lim.calls c hc name' htask
        exact hexecs e he (hid.trans ho)
      · intro r' hr' name' htask ho
        obtain ⟨e, he, hid, -⟩ := lim.runs r' hr' _ name' ho htask
        exact hexecs e he hid
      · intro i hi hid
        rw [only i hi hid]
      · intro cc' hcc'
        obtain ⟨w', pl', hw', hpl', hctl⟩ := Delivery.concurrencyOf_iff.mp hcc'
        change s.workflow? p path = some w' at hw'
        rw [hwf] at hw'
        cases hw'
        rw [hpl] at hpl'
        cases hpl'
        rw [hcc] at hctl
        cases hctl
        simp
      · intro tk htk _
        obtain ⟨ts, -, rfl⟩ := List.mem_map.mp htk
        rfl
      · intro tk htk hf
        obtain ⟨ts, -, rfl⟩ := List.mem_map.mp htk
        revert hf
        split <;> simp
  | fetch id =>
    obtain ⟨-, -, c, hc, -, h4, rfl⟩ := Step.fetch_inv hs
    exact fr (Frame.setCall (c' := { c with status := .fetching }) wk (State.call?_eq_some hc).1 rfl
      (Delivery.ended_of_running (Or.inl h4)))
  | returned id value =>
    obtain ⟨-, -, c, _, s', hc, -, h4, -, hacc, hso⟩ := Step.returned_inv hs
    have wk₁ := wk.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (State.call?_eq_some hc).1
    have wk₂ := wk₁.setCall { c with status := .returned }
    exact fr (((Frame.accept hacc).trans (Frame.setCall (c' := { c with status := .returned }) wk₁ hc' rfl
      (Delivery.ended_of_running (Or.inl h4))) wk₂).trans
      (Frame.settleOwner wk₂ hso (by simp) fun _ _ h => by cases h) wk')
  | judged id arm =>
    obtain ⟨-, -, c, _, i, _, _, _, s', hc, h3, -, -, hi, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    have wk₁ := wk.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (State.call?_eq_some hc).1
    have wk₂ := wk₁.setCall { c with status := .returned }
    have hi' : i ∈ (s'.setCall { c with status := .returned }).invocations := by
      rw [State.setCall_invocations, (accept_frame hacc).2.2.2.2.1]; exact (State.invocation?_eq_some hi).1
    exact fr (((Frame.accept hacc).trans (Frame.setCall (c' := { c with status := .returned }) wk₁ hc' rfl
      (Delivery.ended_of_running (Or.inl h3))) wk₂).trans
      (Frame.setInvocation (i' := { i with status := .succeeded, arm := some arm }) wk₂ hi' rfl rfl rfl rfl rfl) wk')
  | yielded id value =>
    obtain ⟨-, -, c, s', hc, -, h4, hacc, rfl⟩ := Step.yielded_inv hs
    have wk₁ := wk.accept hacc
    have hc' : c ∈ s'.calls := by rw [(accept_frame hacc).2.2.2.2.2.1]; exact (State.call?_eq_some hc).1
    exact fr ((Frame.accept hacc).trans (Frame.setCall (c' := { c with status := .running, yields := c.yields + 1 })
      wk₁ hc' rfl (Delivery.ended_of_running (Or.inr h4))) wk')
  | ended id =>
    obtain ⟨-, -, c, hc, -, h4, hso⟩ := Step.ended_inv hs
    have wk₁ := wk.setCall { c with status := .returned }
    exact fr ((Frame.setCall (c' := { c with status := .returned }) wk (State.call?_eq_some hc).1 rfl
      (Delivery.ended_of_running (Or.inr h4))).trans
      (Frame.settleOwner wk₁ hso (by simp) fun _ _ h => by cases h) wk')
  | failed id =>
    obtain ⟨-, -, c, hc, h3, hf⟩ := Step.failed_inv hs
    exact fr (Frame.failCall wk lim (State.call?_eq_some hc).1 (Delivery.ended_of_running h3) hf)
  | timedOut id element =>
    obtain ⟨-, -, c, hc, h3, hf⟩ := Step.timedOut_inv hs
    have hrun : c.status = .running ∨ c.status = .fetching := by
      rcases h3 with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact Or.inr h
      · exact h
    exact fr (Frame.failCall wk lim (State.call?_eq_some hc).1 (Delivery.ended_of_running hrun) hf)
  | lost id =>
    obtain ⟨-, -, c, hc, ⟨h3, hf⟩ | ⟨h3, ho⟩⟩ := Step.lost_inv hs
    · exact fr (Frame.failCall wk lim (State.call?_eq_some hc).1 (Delivery.ended_of_running h3) hf)
    · have wk₁ := wk.setCall { c with status := .cancelled }
      exact fr ((Frame.setCall (c' := { c with status := .cancelled }) wk (State.call?_eq_some hc).1 rfl
        (by simp [h3, CallStatus.ended])).trans (Frame.cancelOwner wk₁ ho) wk')
  | terminated id =>
    obtain ⟨-, -, c, hc, h3, ho⟩ := Step.terminated_inv hs
    have wk₁ := wk.setCall { c with status := .cancelled }
    exact fr ((Frame.setCall (c' := { c with status := .cancelled }) wk (State.call?_eq_some hc).1 rfl
      (by simp [h3, CallStatus.ended])).trans (Frame.cancelOwner wk₁ ho) wk')
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact fr (Frame.of_eq K rfl rfl rfl rfl)
  | transformFailed path index source =>
    obtain ⟨-, -, w, c, _, target, hdt, -, -, rfl⟩ := Step.transformFailed_inv hs
    have hfresh := (Step.deliveryTarget_eq_ok.mp hdt).2.2.2
    have wk₁ : ({ s with deliveries := s.deliveries ++
        [{ run := path, connection := index, source, outcome := .failed }] } : State).WellKeyed :=
      wk.appendDelivery hfresh
    have F₁ : Frame p s { s with deliveries := s.deliveries ++
        [{ run := path, connection := index, source, outcome := .failed }] } :=
      Frame.of_eq (Delivery.Kept.of_lists ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩ ⟨[], by simp⟩
        ⟨[], by simp⟩ ⟨_, rfl⟩ ⟨[], by simp⟩ ⟨[], by simp⟩) rfl rfl rfl rfl
    exact fr (F₁.trans (Frame.fail wk₁ _ _) wk')
  | taskInput eid name value =>
    obtain ⟨-, -, e, ts, spec, he, hts, hpend, -, -, rfl⟩ := Step.taskInput_inv hs
    refine fr (Frame.setTask wk (State.execution?_eq_some he).1 (List.mem_of_find?_eq_some hts) ?_)
    refine ⟨rfl, Or.inr hpend, ?_, ?_⟩ <;> intro h <;> cases h
  | taskInputFailed eid name =>
    obtain ⟨-, -, e, ts, spec, tid, he, hts, -, hspec, hin, rfl⟩ := Step.taskInputFailed_inv hs
    have hem := (State.execution?_eq_some he).1
    have hname := Delivery.find?_name_of_task hts
    have wk₁ := wk.setTask e { ts with status := .failed }
    have F₁ : Frame p s (s.setTask e { ts with status := .failed }) := by
      refine Frame.setTask wk hem (List.mem_of_find?_eq_some hts) ⟨rfl, Or.inl rfl, ?_, fun _ => ?_⟩
      · intro h; cases h
      refine Or.inr (Or.inr ⟨spec, tid, ?_, hin⟩)
      rw [taskSpec_of_runs rfl, Delivery.taskSpec_congr (withTask_run) (withTask_placement)]
      show s.taskSpec p e ts.name = .ok spec
      rw [hname]
      exact hspec
    exact fr (F₁.trans (Frame.fail wk₁ _ _) wk')
  | beginTask eid name =>
    obtain ⟨-, -, e, cc, ts, spec, he, -, -, hts, hready, -, hspec, h⟩ := Step.beginTask_inv hs
    obtain ⟨hem, heid⟩ := State.execution?_eq_some he
    have htsm := List.mem_of_find?_eq_some hts
    have hname := Delivery.find?_name_of_task hts
    have wku := wk.setTask e { ts with status := .active }
    have Fu : Frame p s (s.setTask e { ts with status := .active }) := by
      refine Frame.setTask wk hem htsm ⟨rfl, Or.inl rfl, ?_, ?_⟩ <;> intro h <;> cases h
    have hu : Created p (s.setTask e { ts with status := .active }) := hC.of_frame inv lim wku Fu
    have hmem : withTask e { ts with status := .active } ∈ (s.setTask e { ts with status := .active }).executions :=
      Delivery.mem_setTask_self hem
    have heu : ∀ e₁ ∈ (s.setTask e { ts with status := .active }).executions, e₁.id = e.id →
        e₁ = withTask e { ts with status := .active } := fun e₁ he₁ hid =>
      wku.execution_eq_of_id he₁ hmem hid
    have htk : ∀ tk ∈ (withTask e { ts with status := .active }).tasks, tk.name = name →
        tk = { ts with status := .active } := by
      intro tk htk hn
      rcases Delivery.mem_withTask htk with rfl | ⟨-, hne⟩
      · rfl
      · exact absurd (hn.trans hname.symm) hne
    have hspecu : (s.setTask e { ts with status := .active }).taskSpec p (withTask e { ts with status := .active }) name =
        .ok spec := by
      rw [taskSpec_of_runs rfl, Delivery.taskSpec_congr (withTask_run) (withTask_placement)]
      exact hspec
    rcases h with ⟨f, decl, hf, hdecl, -, rfl⟩ | ⟨wf, out, hwf, -, rfl⟩
    · refine hu.appendCall rfl rfl rfl rfl (fun h => by cases h) fun name' h' e₁ he₁ hid => ?_
      cases h'
      obtain rfl := heu e₁ he₁ hid
      refine ⟨fun tk htk' hn => by rw [htk tk htk' hn], fun sp hsp => ?_⟩
      rw [hspecu] at hsp
      cases hsp
      exact ⟨rfl, rfl, f, decl, hf, hdecl, rfl, rfl⟩
    · refine hu.appendRun rfl rfl rfl rfl ?_ ?_ (fun h => by cases h) fun name' h' e₁ he₁ ho => ?_
      · intro i hi
        obtain ⟨-, w₀, -, -, hw₀, -⟩ := inv.own.invocations i hi
        obtain ⟨r₀, hr₀, -⟩ := Delivery.workflow?_iff.mp hw₀
        show (s.run? i.run).isSome
        rw [hr₀]; rfl
      · intro e₁ he₁
        rcases State.mem_setTask_executions he₁ with rfl | he₁
        · exact lim.execRuns e hem
        · exact lim.execRuns e₁ he₁
      · cases h'
        obtain rfl := heu e₁ he₁ (Option.some.inj ho).symm
        refine ⟨fun tk htk' hn => by rw [htk tk htk' hn], fun sp hsp => ?_⟩
        rw [hspecu] at hsp
        cases hsp
        exact ⟨out, hwf⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact fr (Frame.of_eq K rfl rfl rfl rfl)
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, e, spec, r, -, -, -, hr, hpend, rfl⟩ := Step.taskOutputFailed_inv hs
    have hrm := List.mem_of_find?_eq_some hr
    have wk₁ := wk.setTaskResult { r with output := .failed }
    have F₁ : Frame p s (s.setTaskResult { r with output := .failed }) :=
      Frame.of_eq (Delivery.Kept.setTaskResult .failed wk hrm hpend) rfl rfl rfl rfl
    exact fr (F₁.trans (Frame.fail wk₁ _ _) wk')
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact fr (Frame.of_eq K rfl rfl rfl rfl)
  | closeExecution eid =>
    obtain ⟨-, -, e, _, i, he, hc, -, -, -, hi, h⟩ := Step.closeExecution_inv hs
    have hem := (State.execution?_eq_some he).1
    have wk₁ := wk.setExecution { e with complete := true }
    have hi' : i ∈ (s.setExecution { e with complete := true }).invocations := (State.invocation?_eq_some hi).1
    have F : ∀ st : InvocationStatus, Frame p s
        ((s.setExecution { e with complete := true }).setInvocation { i with status := st }) := fun st =>
      (Frame.setExecution wk hem true fun _ => rfl).trans (Frame.setInvocation wk₁ hi' rfl rfl rfl rfl rfl)
        (wk₁.setInvocation _)
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact fr (F _)
    · exact fr ((F .succeeded).congr K rfl rfl rfl rfl)
    · exact fr (F _)
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, owner, hr, -, -, -, -, -, -, ho, h⟩ := Step.closeRun_inv hs
    have hrm := (State.run?_eq_some hr).1
    have wk₁ := wk.setRun { r with complete := true }
    have F₁ : Frame p s (s.setRun { r with complete := true }) := Frame.setRun wk hrm true fun _ => rfl
    rcases h with ⟨-, i, hi, h⟩ | ⟨name, e, ts, htask, he, hts, h⟩
    · have hi' : i ∈ (s.setRun { r with complete := true }).invocations := (State.invocation?_eq_some hi).1
      have F : ∀ st : InvocationStatus, Frame p s
          ((s.setRun { r with complete := true }).setInvocation { i with status := st }) := fun st =>
        F₁.trans (Frame.setInvocation wk₁ hi' rfl rfl rfl rfl rfl) (wk₁.setInvocation _)
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact fr ((F .succeeded).congr K rfl rfl rfl rfl)
      all_goals exact fr (F _)
    · obtain ⟨hem, heid⟩ := State.execution?_eq_some he
      have hem' : e ∈ (s.setRun { r with complete := true }).executions := hem
      have hname := Delivery.find?_name_of_task hts
      -- The task's run is in the state, so a failed task began.
      have F : ∀ st : TaskStatus, st ≠ .pending → Frame p s
          ((s.setRun { r with complete := true }).setTask e { ts with status := st }) := by
        intro st hst
        refine F₁.trans (Frame.setTask wk₁ hem' (List.mem_of_find?_eq_some hts)
          ⟨rfl, Or.inl rfl, fun h => absurd h hst, fun _ => Or.inr ?_⟩) (wk₁.setTask _ _)
        refine justified_of_run (r := { r with complete := true }) ?_ ?_ ?_
        · show { r with complete := true } ∈ (s.setRun { r with complete := true }).runs
          exact List.mem_map.mpr ⟨r, hrm, by simp⟩
        · rw [withTask_id, heid]; exact ho
        · rw [htask]; exact congrArg some hname.symm
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact fr ((F .succeeded (by simp)).congr K rfl rfl rfl rfl)
      all_goals exact fr (F _ (by simp))
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs
    · exact fr (Frame.stop.congr K rfl rfl rfl rfl)
    · exact fr (Frame.of_eq K rfl rfl rfl rfl)
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · exact fr ((Frame.setRun wk (State.run?_eq_some hr).1 true fun _ => rfl).congr K rfl rfl rfl rfl)
    · exact fr (Frame.of_eq K rfl rfl rfl rfl)

/-- `Created` in every reachable state. -/
theorem Reachable.created (h : Reachable p s) : Created p s := by
  induction h with
  | empty => exact Created.empty
  | step _ hr hs ih => exact step_created hr ih hs

/-! ### The root run -/

/-- Only `start` is accepted before the start. -/
theorem step_not_started {op : Op} (hs : step p s op = .ok t) (h : s.started = false) :
    ∃ input, op = .start input ∧
      t = { s with started := true, runs := [{ path := [], workflow := p.main, input }] } := by
  have no : s.started = true → False := fun h' => by rw [h] at h'; cases h'
  cases op with
  | start input =>
    obtain ⟨-, -, _, -, -, rfl⟩ := Step.start_inv hs
    exact ⟨input, rfl, rfl⟩
  | invoke => exact (no (Step.invoke_inv hs).1).elim
  | fetch => exact (no (Step.fetch_inv hs).1).elim
  | returned => exact (no (Step.returned_inv hs).1).elim
  | judged => exact (no (Step.judged_inv hs).1).elim
  | yielded => exact (no (Step.yielded_inv hs).1).elim
  | ended => exact (no (Step.ended_inv hs).1).elim
  | failed => exact (no (Step.failed_inv hs).1).elim
  | timedOut => exact (no (Step.timedOut_inv hs).1).elim
  | lost => exact (no (Step.lost_inv hs).1).elim
  | terminated => exact (no (Step.terminated_inv hs).1).elim
  | deliver => exact (no (Step.deliver_inv hs).1).elim
  | transformFailed => exact (no (Step.transformFailed_inv hs).1).elim
  | taskInput => exact (no (Step.taskInput_inv hs).1).elim
  | taskInputFailed => exact (no (Step.taskInputFailed_inv hs).1).elim
  | beginTask => exact (no (Step.beginTask_inv hs).1).elim
  | taskOutput => exact (no (Step.taskOutput_inv hs).1).elim
  | taskOutputFailed => exact (no (Step.taskOutputFailed_inv hs).1).elim
  | settle => exact (no (Step.settle_inv hs).1).elim
  | closeExecution => exact (no (Step.closeExecution_inv hs).1).elim
  | closeRun => exact (no (Step.closeRun_inv hs).1).elim
  | cancel => exact (no (Step.cancel_inv hs).1).elim
  | conclude => exact (no (Step.conclude_inv hs).1).elim

/-- The root run of a conforming execution runs the main workflow on the caller's input. -/
theorem Conforming.root {env : Env} {tr : List Op} (h : Conforming p env tr s) :
    ∀ r ∈ s.runs, r.path = [] → r.workflow = p.main ∧ r.input = env.input ∧ r.owner = none ∧ r.task = none := by
  induction h with
  | nil => intro r hr; cases hr
  | @snoc tr s₀ s₁ op h₀ hc hs _ ih =>
    intro r hr hpath
    by_cases hst : s₀.started = true
    · rcases Delivery.step_runs_back (Or.inr hst) hs r hr with ⟨r₀, hr₀, a1, a2, a3, a4, a5, -⟩ | ⟨-, -, hnew⟩
      · obtain ⟨b1, b2, b3, b4⟩ := ih r₀ hr₀ (a1.trans hpath)
        exact ⟨a2 ▸ b1, a3 ▸ b2, a4 ▸ b3, a5 ▸ b4⟩
      · rcases hnew with ⟨hst', -⟩ | ⟨-, i, -, -, -, hp, -⟩ | ⟨name, e, -, -, -, -, -, -, -, -, -, -, -, -, hp, -⟩
        · rw [hst] at hst'; cases hst'
        · rw [hpath] at hp; simp at hp
        · rw [hpath] at hp; simp at hp
    · obtain ⟨input, rfl, rfl⟩ := step_not_started hs (by simpa using hst)
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨rfl, hc, rfl, rfl⟩

end CoversOpsAux
end Suimon.Round3
