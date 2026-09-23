import Suimon.Theorems.Round3.ProgressEasy
import Suimon.Theorems.Round3.SettledValue
import Suimon.Theorems.Round3.ShapeFits
import Suimon.Theorems.Round3.ProgressCalmStatic
import Suimon.Theorems.Round3.ProgressCalmTaskRun

/-! The moves of the deepest open run in a calm state (task C2, §4 step 4 of the Round 3 plan): a task
    begins or an execution closes, the first unsettled placement is invoked or settles, or the run
    closes. -/

namespace Suimon.Round3.CalmAux
open State

variable {p : Program} {s : State}

/-! ### Small facts -/

theorem workflow_mem {path : Path} {w : Workflow} (hw : s.workflow? p path = some w) : w ∈ p.workflows := by
  obtain ⟨_, -, hwf⟩ := Routing.workflow?_eq_some.mp hw
  exact (Program.workflow?_eq_some hwf).1

/-- A run below the deepest open run is complete. -/
theorem below_complete {r : Run} (hr : DeepestOpen s r) {r' : Run} (hr' : r' ∈ s.runs)
    (hlen : r.path.length < r'.path.length) : r'.complete = true := by
  cases hc : r'.complete with
  | true => rfl
  | false =>
    have := hr.2.2 r' hr' hc
    omega

/-- A nonempty list has an element of minimal measure. -/
theorem exists_min_mem {α : Type} (f : α → Nat) {l : List α} {a : α} (ha : a ∈ l) :
    ∃ x ∈ l, ∀ y ∈ l, f x ≤ f y := by
  suffices ∀ n, ∀ a ∈ l, f a ≤ n → ∃ x ∈ l, ∀ y ∈ l, f x ≤ f y from this _ a ha (Nat.le_refl _)
  intro n
  induction n with
  | zero => exact fun a ha h0 => ⟨a, ha, fun y _ => by omega⟩
  | succ n ih =>
    intro a ha hn
    by_cases hlt : ∃ y ∈ l, f y < f a
    · obtain ⟨y, hy, hy'⟩ := hlt
      exact ih y hy (by omega)
    · exact ⟨a, ha, fun y hy => Nat.le_of_not_lt fun h' => hlt ⟨y, hy, h'⟩⟩

/-- The shapes other than Merge and a waitStream's Stream belong to invoked controls. -/
theorem invocable_of_fits {ctrl : Control} {sh : Workflow.Shape} (hfit : ShapeFits ctrl sh)
    (hw : ∀ e, ctrl ≠ .waitStream e) (hm : ∀ cs, sh ≠ .merge cs) :
    (∃ b, ctrl = .call b) ∨ (∃ j arms, ctrl = .branch j arms) ∨ (∃ cc, ctrl = .concurrency cc) := by
  cases ctrl with
  | call b => exact Or.inl ⟨b, rfl⟩
  | branch j arms => exact Or.inr (Or.inl ⟨j, arms, rfl⟩)
  | concurrency cc => exact Or.inr (Or.inr ⟨cc, rfl⟩)
  | waitStream e => exact absurd rfl (hw e)
  | merge e =>
    cases sh with
    | merge cs => exact absurd rfl (hm cs)
    | _ => simp [ShapeFits] at hfit

/-! ### Settling -/

/-- A placement whose invocations ended and whose input is used up settles. -/
theorem settleOutcome_of_inputDone {path : Path} {pl : Placement} {shape : Workflow.Shape} {kind : Kind}
    (hended : ∀ i ∈ s.invocationsOf path pl.name, s.invocationEnded i = true)
    (hfit : ShapeFits pl.control shape) (hdone : Delivery.InputDone s path pl shape) :
    ∃ x agg, s.settleOutcome path pl shape kind = some (x, agg) := by
  have hall : (s.invocationsOf path pl.name).all s.invocationEnded = true := List.all_eq_true.mpr hended
  have hfind : ∀ tr : Option ResultId, (∃ i ∈ s.invocationsOf path pl.name, i.trigger = tr) →
      ∃ j, (s.invocationsOf path pl.name).find? (fun x => x.trigger == tr) = some j := by
    intro tr ⟨i, hi, ht⟩
    exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨i, hi, by simp [ht]⟩)
  have hfind0 : (∃ i ∈ s.invocationsOf path pl.name, i.trigger = none) →
      ∃ j, (s.invocationsOf path pl.name).find? (fun x => x.trigger.isNone) = some j := by
    intro ⟨i, hi, ht⟩
    exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨i, hi, by simp [ht]⟩)
  have hstream : ∀ j c, (s.settled? path c.source).isSome →
      (∀ r ∈ s.eligible path c, (s.delivery? path j r.id).isSome) → ∃ o, s.streamEnd? path j c = some o := by
    intro j c hset hall'
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hset
    exact ⟨_, Delivery.streamEnd?_eq_some.mpr ⟨x, hx, hall', rfl⟩⟩
  have htrig : ∀ j, (∀ d ∈ s.deliveriesOn path j, d.outcome ≠ .failed →
      ∃ i ∈ s.invocationsOf path pl.name, i.trigger = some d.source) →
      ((s.deliveriesOn path j).all fun d => d.outcome == .failed ||
        (s.invocationsOf path pl.name).any (·.trigger == some d.source)) = true := by
    intro j h
    refine List.all_eq_true.mpr fun d hd => ?_
    by_cases hf : d.outcome = .failed
    · simp [hf]
    · obtain ⟨i, hi, ht⟩ := h d hd hf
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
      exact Or.inr ⟨i, hi, by simp [ht]⟩
  rcases pl with ⟨name, control, policy, timeout⟩
  cases control <;> cases shape <;> simp only [ShapeFits] at hfit <;> simp only [Delivery.InputDone] at hdone
  -- A call: by its invocation, by its Single input, or after its Stream input ended.
  · obtain ⟨j, hj⟩ := hfind0 hdone
    unfold State.settleOutcome
    simp [hall, guard, hj]
  · obtain ⟨j, hj⟩ := hfind0 hdone
    unfold State.settleOutcome
    simp [hall, guard, hj]
  · rename_i body idx c
    obtain ⟨hne, hval⟩ := hdone
    unfold State.settleOutcome
    cases hres : s.resolveSingle path idx c with
    | pending => exact absurd hres hne
    | value src inp =>
      obtain ⟨j, hj⟩ := hfind (some src) (hval src inp hres)
      simp [hall, guard, hres, hj]
    | transformFailed => simp [hall, guard, hres]
    | skipped => simp [hall, guard, hres]
    | failure => simp [hall, guard, hres]
  · rename_i body idx c
    obtain ⟨hset, hdel, htr⟩ := hdone
    obtain ⟨o, ho⟩ := hstream idx c hset hdel
    have ht := htrig idx (htr fun e he => nomatch he)
    unfold State.settleOutcome
    simp only [hall, guard, ho, ht]
    simp
    split <;> simp
  -- A branch.
  · obtain ⟨j, hj⟩ := hfind0 hdone
    unfold State.settleOutcome
    simp only [hall, guard, hj]
    simp
    split <;> simp
  · rename_i jj arms idx c
    obtain ⟨hne, hval⟩ := hdone
    unfold State.settleOutcome
    cases hres : s.resolveSingle path idx c with
    | pending => exact absurd hres hne
    | value src inp =>
      obtain ⟨j, hj⟩ := hfind (some src) (hval src inp hres)
      simp only [hall, guard, hres, hj]
      simp
      split <;> simp
    | transformFailed => simp [hall, guard, hres]
    | skipped => simp [hall, guard, hres]
    | failure => simp [hall, guard, hres]
  · rename_i jj arms idx c
    obtain ⟨hset, hdel, htr⟩ := hdone
    obtain ⟨o, ho⟩ := hstream idx c hset hdel
    have ht := htrig idx (htr fun e he => nomatch he)
    unfold State.settleOutcome
    simp only [hall, guard, ho, ht]
    simp
    split <;> simp
  -- A waitStream.
  · rename_i el idx c
    obtain ⟨hset, hdel, -⟩ := hdone
    obtain ⟨o, ho⟩ := hstream idx c hset hdel
    unfold State.settleOutcome
    simp only [hall, guard, ho]
    simp
    split <;> simp
  -- A Merge.
  · rename_i el cs
    have hres : (cs.map fun (x : Nat × Connection) => s.resolveSingle path x.1 x.2).all (· != .pending) = true := by
      refine List.all_eq_true.mpr fun r hr => ?_
      obtain ⟨jc, hjc, rfl⟩ := List.mem_map.mp hr
      simpa using hdone jc hjc
    unfold State.settleOutcome
    simp only [hall, guard, hres]
    simp
    split <;> simp
  -- A concurrency.
  · obtain ⟨j, hj⟩ := hfind0 hdone
    unfold State.settleOutcome
    simp [hall, guard, hj]
  · obtain ⟨j, hj⟩ := hfind0 hdone
    unfold State.settleOutcome
    simp [hall, guard, hj]
  · rename_i cc idx c
    obtain ⟨hne, hval⟩ := hdone
    unfold State.settleOutcome
    cases hres : s.resolveSingle path idx c with
    | pending => exact absurd hres hne
    | value src inp =>
      obtain ⟨j, hj⟩ := hfind (some src) (hval src inp hres)
      simp [hall, guard, hres, hj]
    | transformFailed => simp [hall, guard, hres]
    | skipped => simp [hall, guard, hres]
    | failure => simp [hall, guard, hres]
  · rename_i cc idx c
    obtain ⟨hset, hdel, htr⟩ := hdone
    obtain ⟨o, ho⟩ := hstream idx c hset hdel
    have ht := htrig idx (htr fun e he => nomatch he)
    unfold State.settleOutcome
    simp only [hall, guard, ho, ht]
    simp
    split <;> simp

/-! ### Inputs in a calm state -/

/-- In a calm state every eligible result of a connection was delivered. -/
theorem all_delivered (calm : Calm p s) {path : Path} {w : Workflow} (hw : s.workflow? p path = some w)
    {j : Nat} {c : Connection} (hc : w.connections[j]? = some c) :
    ∀ res ∈ s.eligible path c, (s.delivery? path j res.id).isSome := by
  intro res hres
  obtain ⟨hresm, hresr, hresp, hresa⟩ := Delivery.mem_eligible.mp hres
  have := calm.delivered res hresm w (by rw [hresr]; exact hw) j c hc hresp.symm (hresa.imp id Eq.symm)
  rwa [hresr] at this

/-- In a calm state a Single connection from a settled source is resolved: a normal arm has an
    eligible result (`settled_value`), which was delivered. -/
theorem single_resolved (valid : p.validate = .ok ()) (h : Reachable p s) (calm : Calm p s)
    {path : Path} {w : Workflow} (hw : s.workflow? p path = some w) {j : Nat} {c : Connection}
    (hc : w.connections[j]? = some c) (hk : w.outputKind? p c.source = some .single)
    (hsettled : (s.settled? path c.source).isSome) : s.resolveSingle path j c ≠ .pending := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsettled
  rcases hd : s.deliveriesOn path j with _ | ⟨d, rest⟩
  · rw [Delivery.resolveSingle_of_nil hd, hx]
    cases harm : armOutcome x c.arm with
    | normal =>
      exfalso
      obtain ⟨hxm, hxr, hxp⟩ := State.settled?_eq_some hx
      have hne := (settled_value valid h x hxm w (by rw [hxr]; exact hw) (by rw [hxp]; exact hk)).2 j c hc
        hxp.symm harm
      obtain ⟨res, hres⟩ := List.exists_mem_of_ne_nil _ hne
      rw [hxr] at hres
      obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp (all_delivered calm hw hc res hres)
      obtain ⟨hdm, hdr, hdc, -⟩ := State.delivery?_eq_some hd'
      have : d' ∈ s.deliveriesOn path j := Delivery.mem_deliveriesOn.mpr ⟨hdm, hdr, hdc⟩
      rw [hd] at this
      cases this
    | skipped => simp [harm]
    | failed => simp [harm]
    | upstreamFailed => simp [harm]
  · rw [Delivery.resolveSingle_of_cons hd]
    split <;> simp

/-! ### Executions -/

/-- An open execution of the deepest open run in a calm state begins a ready task or closes. No task
    holds a slot: an active task would have an unended call or an open run below the deepest one, and
    no call is cancelling. -/
theorem exec_step (valid : p.validate = .ok ()) (h : Reachable p s) (started : s.started = true)
    (running : s.status = .running) (calm : Calm p s) {r : Run} (hr : DeepestOpen s r)
    {e : Execution} (he : e ∈ s.executions) (herun : e.run = r.path) (hopen : e.complete = false) :
    ∃ op t, ((∃ e, op = .closeExecution e) ∨ (∃ e n, op = .beginTask e n)) ∧
      step p s op = .ok t ∧ t ≠ s := by
  have wk := h.wellKeyed
  obtain ⟨own, -, -, -⟩ := Settle.reachable h
  obtain ⟨i, hi, hie, -, -, pl, cc, hpl, hctrl, hnames⟩ := own.execOwner e he
  obtain ⟨w, hw, hplw⟩ := Option.bind_eq_some_iff.mp hpl
  have hcc : s.concurrencyOf p e = .ok cc :=
    State.concurrencyOf_eq_ok.mpr ⟨pl, State.placementOf_eq_ok.mpr ⟨w, hw, hplw⟩, hctrl⟩
  have hwm := workflow_mem hw
  have hplm := (Workflow.placement?_eq_some hplw).1
  obtain ⟨hnodup, hlimit⟩ := concurrency_settings valid w hwm pl hplm cc hctrl
  have hnotactive : ∀ t ∈ e.tasks, t.status ≠ .active := by
    intro t ht hact
    rcases active_task_body h e he t ht hact with ⟨c, hc, -, -, -, hcend⟩ | ⟨r', hr', hpath, -, -, hrc⟩
    · rw [calm.calls c hc] at hcend
      cases hcend
    · have := hr.2.2 r' hr' hrc
      rw [hpath, herun, List.length_append, List.length_singleton] at this
      omega
  have hnocan : ∀ c ∈ s.calls, c.status ≠ .cancelling := by
    intro c hc hcan
    have := calm.calls c hc
    rw [hcan] at this
    cases this
  have hnoslot : ∀ t ∈ e.tasks, s.holdsSlot e t = false := fun t ht =>
    Delivery.holdsSlot_eq_false.mpr ⟨hnotactive t ht, fun c hc _ _ => hnocan c hc⟩
  by_cases hready : ∃ t ∈ e.tasks, t.status = .ready
  · obtain ⟨t, ht, htr⟩ := hready
    have hname : t.name ∈ cc.tasks.map (·.name) := by
      rw [← hnames]
      exact List.mem_map_of_mem ht
    obtain ⟨spec, hspecm, hsn⟩ := List.mem_map.mp hname
    have hspec : s.taskSpec p e t.name = .ok spec :=
      State.taskSpec_eq_ok.mpr ⟨cc, hcc, find?_eq_some_of_nodup hnodup hspecm (fun y => by simp [hsn])⟩
    have hts : e.tasks.find? (·.name == t.name) = some t :=
      find?_eq_some_of_nodup (h.taskNames valid e he) ht (fun y => by simp)
    have hslot : (e.tasks.filter (s.holdsSlot e)).length < cc.limit := by
      have hnil : e.tasks.filter (s.holdsSlot e) = [] :=
        List.filter_eq_nil_iff.mpr fun t ht => by simp [hnoslot t ht]
      rw [hnil]
      exact hlimit
    have hfresh := (Reachable.fresh h).taskBody e he t ht (Or.inr htr)
    obtain ⟨at_, hbv⟩ := (body_valid valid hwm hplm).2 cc hctrl spec hspecm
    have hfun : ∀ f, spec.body = .function f →
        (p.function? f).isSome ∧ s.call? (Key.task e.id t.name) = none := by
      intro f hf
      rw [hf] at hbv
      exact ⟨function_of_validateBody hbv, hfresh.1⟩
    obtain ⟨t', hs, hne⟩ := beginTask_enabled started running (wk.execution?_of_mem he) hopen hcc hts htr hslot
      hspec hfun (fun _ _ _ => hfresh.2)
    exact ⟨_, t', Or.inr ⟨_, _, rfl⟩, hs, hne⟩
  · have hended : ∀ t ∈ e.tasks, s.taskEnded e t = true := by
      intro t ht
      refine Delivery.taskEnded_iff.mpr ⟨?_, hnotactive t ht, fun c hc _ _ => hnocan c hc, ?_⟩
      · have hp := calm.inputs e he t ht
        have hr' : t.status ≠ .ready := fun h' => hready ⟨t, ht, h'⟩
        have ha := hnotactive t ht
        cases hst : t.status <;> simp_all [TaskStatus.ended]
      · intro r' hr' ho htk
        obtain ⟨e', he', heo, hpath, -⟩ := own.runTask r' hr' t.name htk
        have : e' = e := wk.execution_eq_of_id he' he (Option.some.inj (heo.symm.trans ho))
        subst this
        exact below_complete hr hr' (by rw [hpath, herun]; simp)
    have houts : ∀ x ∈ s.taskResults, x.execution = e.id →
        ((cc.tasks.filter (·.output.isSome)).map (·.name)).contains x.task = true → x.output ≠ .pending := by
      intro x hx hxe hcont
      refine calm.outputs e he cc hcc x hx hxe ?_
      obtain ⟨spec, hspec, hsn⟩ := List.mem_map.mp (List.contains_iff_mem.mp hcont)
      obtain ⟨hspecm, hso⟩ := List.mem_filter.mp hspec
      exact ⟨spec, hspecm, hsn, hso⟩
    have hi' : s.invocation? e.id = some i := by
      rw [← hie]
      exact wk.invocation?_of_mem hi
    obtain ⟨t', hs, hne⟩ := closeExecution_enabled started running (wk.execution?_of_mem he) hopen hcc hended houts
      hi' (fun _ => (Reachable.fresh h).list e he hopen)
    exact ⟨_, t', Or.inl ⟨_, rfl⟩, hs, hne⟩

/-! ### Invocations -/

/-- Once every execution of the deepest open run completed, each of its invocations ended: its calls
    ended (calm), its sub-run is complete (below the deepest open run), its execution completed, and
    so its status is no longer active (`owner_closed`). -/
theorem inv_ended (h : Reachable p s) (calm : Calm p s) {r : Run} (hr : DeepestOpen s r)
    (hexec : ∀ e ∈ s.executions, e.run = r.path → e.complete = true)
    {i : Invocation} (hi : i ∈ s.invocations) (hir : i.run = r.path) : s.invocationEnded i = true := by
  have wk := h.wellKeyed
  obtain ⟨own, -, -, -⟩ := Settle.reachable h
  have hruns : ∀ r' ∈ s.runs, r'.owner = some i.id → r'.task = none → r'.complete = true := by
    intro r' hr' ho ht
    obtain ⟨i', hi', hio, hpath, -⟩ := own.runNone r' hr' i.id ho ht
    have : i' = i := wk.invocation_eq_of_id hi' hi hio
    subst this
    exact below_complete hr hr' (by rw [hpath, hir]; simp)
  have hexecs : ∀ e ∈ s.executions, e.id = i.id → e.complete = true := by
    intro e he hid
    obtain ⟨i', hi', hie, hir', -⟩ := own.execOwner e he
    have : i' = i := wk.invocation_eq_of_id hi' hi (hie.trans hid)
    subst this
    exact hexec e he (hir'.symm.trans hir)
  have hstatus : i.status ≠ .active := by
    obtain ⟨w, pl, hw, hpl, hinv⟩ := own.invPlaced i hi
    obtain ⟨hcall, hrun, hexe⟩ := invocation_body h i hi w pl hw hpl
    obtain ⟨oc1, -, oc3, -, oc5⟩ := owner_closed h
    cases hc : pl.control with
    | call body =>
      cases body with
      | function f =>
        obtain ⟨c, hc', -, hco, hct⟩ := hcall (Or.inl ⟨f, hc⟩)
        exact oc1 c hc' (calm.calls c hc') hct i hi hco.symm
      | workflow wf out =>
        obtain ⟨r', hr', -, ho, ht, -⟩ := hrun wf out hc
        exact oc3 r' hr' (hruns r' hr' ho ht) ht i hi ho
    | branch j arms =>
      obtain ⟨c, hc', -, hco, hct⟩ := hcall (Or.inr ⟨j, arms, hc⟩)
      exact oc1 c hc' (calm.calls c hc') hct i hi hco.symm
    | concurrency cc =>
      obtain ⟨e, he, hid⟩ := hexe cc hc
      exact oc5 e he (hexecs e he hid) i hi hid.symm
    | waitStream _ => simp [Settle.invocable, hc] at hinv
    | merge _ => simp [Settle.invocable, hc] at hinv
  exact Delivery.invocationEnded_iff.mpr ⟨hstatus, fun c hc _ _ => calm.calls c hc, hruns, hexecs⟩

/-! ### Placements -/

/-- An unsettled placement of minimal rank: every source of its input connections settled. -/
theorem min_unsettled (valid : p.validate = .ok ()) {w : Workflow} (hwm : w ∈ p.workflows) {path : Path}
    (hnot : ¬ ∀ pl ∈ w.placements, (s.settled? path pl.name).isSome) :
    ∃ pl ∈ w.placements, s.settled? path pl.name = none ∧
      ∀ c ∈ w.connections, c.target = pl.name → (s.settled? path c.source).isSome := by
  obtain ⟨rank, -, hedge⟩ := placement_rank valid w hwm
  obtain ⟨pl₀, hpl₀, hun₀⟩ : ∃ pl ∈ w.placements, s.settled? path pl.name = none := by
    refine Classical.byContradiction fun hno => hnot fun pl hpl => ?_
    cases hs : s.settled? path pl.name with
    | none => exact absurd ⟨pl, hpl, hs⟩ hno
    | some x => rfl
  have hmem : pl₀ ∈ w.placements.filter fun pl => (s.settled? path pl.name).isNone :=
    List.mem_filter.mpr ⟨hpl₀, by simp [hun₀]⟩
  obtain ⟨pl, hplU, hmin⟩ := exists_min_mem (fun pl : Placement => rank pl.name) hmem
  obtain ⟨hpl, hun⟩ := List.mem_filter.mp hplU
  refine ⟨pl, hpl, by simpa using hun, fun c hc htgt => ?_⟩
  obtain ⟨src, -, hsrc, -, -⟩ := typedConnections_of_validate valid w hwm c hc
  obtain ⟨hsrcm, hsrcn⟩ := Workflow.placement?_eq_some hsrc
  have hlt := hedge c hc
  cases hs : s.settled? path c.source with
  | some x => rfl
  | none =>
    exfalso
    have := hmin src (List.mem_filter.mpr ⟨hsrcm, by simp [hsrcn, hs]⟩)
    simp only [hsrcn, ← htgt] at this
    omega

/-- The first unsettled placement of the deepest open run moves, once its invocations ended and its
    sources settled: it settles if its input is used up, and otherwise it is invoked for the input it
    has not taken. -/
theorem placement_step (valid : p.validate = .ok ()) (h : Reachable p s) (started : s.started = true)
    (running : s.status = .running) (calm : Calm p s) {r : Run} (hr : r ∈ s.runs) (hopen : r.complete = false)
    {w : Workflow} (hw : p.workflow? r.workflow = some w) {pl : Placement} (hpl : pl ∈ w.placements)
    (hunset : s.settled? r.path pl.name = none)
    (hsrc : ∀ c ∈ w.connections, c.target = pl.name → (s.settled? r.path c.source).isSome)
    (hended : ∀ i ∈ s.invocationsOf r.path pl.name, s.invocationEnded i = true) :
    ∃ op t, ((∃ n, op = .settle r.path n) ∨ (∃ n tr, op = .invoke r.path n tr)) ∧
      step p s op = .ok t ∧ t ≠ s := by
  have wk := h.wellKeyed
  have hrr : s.run? r.path = some r := wk.run?_of_mem hr
  have hsw : s.workflow? p r.path = some w := Settle.workflow?_of_run hrr hw
  have hwm : w ∈ p.workflows := (Program.workflow?_eq_some hw).1
  have hwc := (Program.validate_ok valid).workflows w hwm
  have hplw : w.placement? pl.name = some pl := Workflow.placement?_of_mem hwc.names hpl
  obtain ⟨sh, k, hsh, hk, hfit, hsingle, hstream, hmerge⟩ := shape_fits valid w hwm pl hpl
  have fresh := Reachable.fresh h
  have settle : Delivery.InputDone s r.path pl sh →
      ∃ op t, ((∃ n, op = .settle r.path n) ∨ (∃ n tr, op = .invoke r.path n tr)) ∧
        step p s op = .ok t ∧ t ≠ s := by
    intro hdone
    obtain ⟨x, agg, hout⟩ := settleOutcome_of_inputDone (kind := k) hended hfit hdone
    have hfree : ∀ res, agg = some res → s.result? res.id = none := by
      intro res hres
      subst hres
      rw [((State.settleOutcome_some hout).2.2.2 res rfl).2.1]
      exact fresh.aggregate r.path pl.name hunset
    obtain ⟨t, hs, hne⟩ := settle_enabled started running hrr hopen hw hplw hunset hsh hk hout hfree
    exact ⟨_, t, Or.inl ⟨_, rfl⟩, hs, hne⟩
  have invoke : ∀ tr, (∀ i ∈ s.invocationsOf r.path pl.name, i.trigger ≠ tr) →
      (∃ input, Step.invocationInput p s r w pl.name tr = .ok input) →
      ((∃ b, pl.control = .call b) ∨ (∃ j arms, pl.control = .branch j arms) ∨
        (∃ cc, pl.control = .concurrency cc)) →
      ∃ op t, ((∃ n, op = .settle r.path n) ∨ (∃ n tr, op = .invoke r.path n tr)) ∧
        step p s op = .ok t ∧ t ≠ s := by
    intro tr hnew ⟨input, hinput⟩ hctrl
    obtain ⟨hinv, hcall, hexe, hrun⟩ := fresh.invocation r.path pl.name tr hnew
    have hbody : match pl.control with
        | .call (.function f) => (p.function? f).isSome ∧ s.call? (Key.invocation r.path pl.name tr) = none
        | .branch _ _ => s.call? (Key.invocation r.path pl.name tr) = none
        | .call (.workflow _ _) => s.run? (r.path ++ [Key.invocation r.path pl.name tr]) = none
        | .concurrency _ => s.execution? (Key.invocation r.path pl.name tr) = none
        | _ => False := by
      rcases hctrl with ⟨b, hb⟩ | ⟨j, arms, hb⟩ | ⟨cc, hb⟩
      · rw [hb]
        cases b with
        | function f =>
          obtain ⟨at_, hbv⟩ := (body_valid valid hwm hpl).1 _ hb
          exact ⟨function_of_validateBody hbv, hcall⟩
        | workflow wf out => exact hrun
      · rw [hb]
        exact hcall
      · rw [hb]
        exact hexe
    obtain ⟨t, hs, hne⟩ := invoke_enabled started running hrr hopen hw hplw hinput hnew hinv hbody
    exact ⟨_, t, Or.inr ⟨_, _, rfl⟩, hs, hne⟩
  -- Controls that take their input from an invocation are invocable.
  have hctrl : (∀ e, pl.control ≠ .waitStream e) → (∀ cs, sh ≠ .merge cs) →
      (∃ b, pl.control = .call b) ∨ (∃ j arms, pl.control = .branch j arms) ∨
        (∃ cc, pl.control = .concurrency cc) :=
    invocable_of_fits hfit
  cases sh with
  | none =>
    by_cases hex : ∃ i ∈ s.invocationsOf r.path pl.name, i.trigger = none
    · exact settle hex
    · exact invoke none (fun i hi ht => hex ⟨i, hi, ht⟩)
        (invocationInput_enabled (Or.inl ⟨hsh, rfl⟩))
        (hctrl (fun e he => by rw [he] at hfit; simp [ShapeFits] at hfit) (by simp))
  | entry =>
    by_cases hex : ∃ i ∈ s.invocationsOf r.path pl.name, i.trigger = none
    · exact settle hex
    · exact invoke none (fun i hi ht => hex ⟨i, hi, ht⟩)
        (invocationInput_enabled (Or.inr (Or.inl ⟨hsh, rfl⟩)))
        (hctrl (fun e he => by rw [he] at hfit; simp [ShapeFits] at hfit) (by simp))
  | single j c =>
    obtain ⟨hkc, hjc⟩ := hsingle j c rfl
    obtain ⟨hcj, hct⟩ := Delivery.mem_inputs.mp hjc
    have hne := single_resolved valid h calm hsw hcj hkc (hsrc c (List.mem_of_getElem? hcj) hct)
    cases hres : s.resolveSingle r.path j c with
    | pending => exact absurd hres hne
    | value src inp =>
      by_cases hex : ∃ i ∈ s.invocationsOf r.path pl.name, i.trigger = some src
      · refine settle ⟨hne, fun src' inp' h' => ?_⟩
        rw [hres] at h'
        cases h'
        exact hex
      · exact invoke (some src) (fun i hi ht => hex ⟨i, hi, ht⟩)
          (invocationInput_enabled (Or.inr (Or.inr (Or.inl ⟨j, c, src, inp, hsh, rfl, hres⟩))))
          (hctrl (fun e he => by rw [he] at hfit; simp [ShapeFits] at hfit) (by simp))
    | transformFailed => exact settle ⟨hne, fun _ _ h' => by rw [hres] at h'; cases h'⟩
    | skipped => exact settle ⟨hne, fun _ _ h' => by rw [hres] at h'; cases h'⟩
    | failure => exact settle ⟨hne, fun _ _ h' => by rw [hres] at h'; cases h'⟩
  | stream j c =>
    obtain ⟨-, hjc⟩ := hstream j c rfl
    obtain ⟨hcj, hct⟩ := Delivery.mem_inputs.mp hjc
    have hset := hsrc c (List.mem_of_getElem? hcj) hct
    have hdel := all_delivered calm hsw hcj
    by_cases hex : ∃ d ∈ s.deliveriesOn r.path j, d.outcome ≠ .failed ∧
        ¬ ∃ i ∈ s.invocationsOf r.path pl.name, i.trigger = some d.source
    · by_cases hwait : ∃ e, pl.control = .waitStream e
      · obtain ⟨e, he⟩ := hwait
        exact settle ⟨hset, hdel, fun hne => absurd he (hne e)⟩
      · obtain ⟨d, hd, hdf, hno⟩ := hex
        obtain ⟨hdm, hdr, hdc⟩ := Delivery.mem_deliveriesOn.mp hd
        have hd' : s.delivery? r.path j d.source = some d := by
          rw [← hdr, ← hdc]
          exact wk.delivery?_of_mem hdm
        exact invoke (some d.source) (fun i hi ht => hno ⟨i, hi, ht⟩)
          (invocationInput_enabled (Or.inr (Or.inr (Or.inr ⟨j, c, d.source, d, hsh, rfl, hd', hdf⟩))))
          (hctrl (fun e he => hwait ⟨e, he⟩) (by simp))
    · refine settle ⟨hset, hdel, fun _ d hd hdf => ?_⟩
      exact Classical.byContradiction fun hno => hex ⟨d, hd, hdf, hno⟩
  | merge cs =>
    obtain ⟨rfl, hks⟩ := hmerge cs rfl
    refine settle fun jc hjc => ?_
    obtain ⟨hcj, hct⟩ := Delivery.mem_inputs.mp hjc
    exact single_resolved valid h calm hsw hcj (hks jc hjc) (hsrc jc.2 (List.mem_of_getElem? hcj) hct)

/-! ### Closing the run -/

/-- Once every placement of the deepest open run settled, the root concludes or the run closes. The
    designated output is a placement of the run's workflow (a sub-workflow run by `invocation_body`,
    a task run by `TaskRunWf`), an endpoint, hence Single, so a normal settlement has its result
    (`settled_value`); the result the step adds is fresh (`Fresh`). -/
theorem close_step (valid : p.validate = .ok ()) (h : Reachable p s) (started : s.started = true)
    (running : s.status = .running) {r : Run} (hr : r ∈ s.runs) (hopen : r.complete = false)
    {w : Workflow} (hw : p.workflow? r.workflow = some w)
    (hall : ∀ pl ∈ w.placements, (s.settled? r.path pl.name).isSome) :
    ∃ op t, (op = .conclude ∨ op = .closeRun r.path) ∧ step p s op = .ok t ∧ t ≠ s := by
  have wk := h.wellKeyed
  have hrr : s.run? r.path = some r := wk.run?_of_mem hr
  by_cases hroot : r.path = []
  · rw [hroot] at hrr hall
    obtain ⟨t, hs, hne⟩ := conclude_running_enabled started running hrr hw hall
    exact ⟨_, t, Or.inl rfl, hs, hne⟩
  have hsw : s.workflow? p r.path = some w := Settle.workflow?_of_run hrr hw
  have hwm : w ∈ p.workflows := (Program.workflow?_eq_some hw).1
  have fresh := Reachable.fresh h
  -- What closing needs once the designated output is known to be an endpoint of `w`.
  have close : ∀ out, s.designatedOutput p r = .ok out → (w.placement? out).isSome = true →
      w.isEndpoint out = true →
      (match r.task with
        | none => ∃ o i, r.owner = some o ∧ s.invocation? o = some i ∧ s.result? (Key.returned i.id) = none
        | some name => ∃ o e ts, r.owner = some o ∧ s.execution? o = some e ∧
            e.tasks.find? (·.name == name) = some ts ∧
            (s.taskResults.any fun y => y.execution == e.id && y.task == name && y.index == 0) = false) →
      ∃ op t, (op = .conclude ∨ op = .closeRun r.path) ∧ step p s op = .ok t ∧ t ≠ s := by
    intro out hout hplo hend howner
    obtain ⟨plo, hplo'⟩ := Option.isSome_iff_exists.mp hplo
    obtain ⟨hplom, hplon⟩ := Workflow.placement?_eq_some hplo'
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hall plo hplom)
    rw [hplon] at hx
    obtain ⟨hxm, hxr, hxp⟩ := State.settled?_eq_some hx
    have hkind : w.outputKind? p x.placement = some .single := by
      rw [hxp, ← hplon]
      exact (kinds_of_validate valid w hwm plo hplom).2.1 (by rw [hplon]; exact hend)
    have hvalue : x.outcome = .normal → s.resultsOf r.path out ≠ [] := by
      intro hn
      have := (settled_value valid h x hxm w (by rw [hxr]; exact hsw) hkind).1 hn
      rwa [hxr, hxp] at this
    obtain ⟨t, hs, hne⟩ := closeRun_enabled started running hrr hopen hroot hw hall hout hx hvalue howner
    exact ⟨_, t, Or.inr rfl, hs, hne⟩
  obtain ⟨own, -, -, -⟩ := Settle.reachable h
  rcases (Delivery.Reachable.inv h).own.runs r hr with ⟨-, -, hpath⟩ |
      ⟨htask, i, hi, ho, hpath, w', pl, wf, out, hw', hpl, hctrl⟩ |
      ⟨name, htask, e, he, ho, -, ⟨tk, htk, htkn⟩, spec, wf, out, hspec, hbody⟩
  · exact absurd hpath hroot
  · -- A sub-workflow call: its run is the run of the call's workflow.
    obtain ⟨r', hr', hpath', -, -, hwf⟩ := (invocation_body h i hi w' pl hw' hpl).2.1 wf out hctrl
    have : r' = r := wk.run_eq_of_path hr' hr (hpath'.trans hpath.symm)
    subst this
    have hout : s.designatedOutput p r' = .ok out :=
      State.designatedOutput_eq_ok.mpr ⟨i.id, ho, Or.inl ⟨htask, i, pl, wf, wk.invocation?_of_mem hi,
        State.placementOf_eq_ok.mpr ⟨w', hw', hpl⟩, hctrl⟩⟩
    obtain ⟨at_, hbv⟩ := (body_valid valid (workflow_mem hw') (Workflow.placement?_eq_some hpl).1).1 _ hctrl
    obtain ⟨w'', hw'', hplo, hend⟩ := workflow_of_validateBody hbv
    rw [← hwf, hw] at hw''
    cases hw''
    refine close out hout hplo hend ?_
    rw [htask]
    exact ⟨i.id, i, ho, wk.invocation?_of_mem hi, fresh.returned r' hr i.id ho htask hopen⟩
  · -- A task run: its run is the run of the task's workflow.
    obtain ⟨e', he', heo', spec', out', hspec', hbody'⟩ := Reachable.taskRunWf h r hr name htask
    have : e' = e := wk.execution_eq_of_id he' he (Option.some.inj (heo'.symm.trans ho))
    subst this
    have : spec' = spec := Settle.taskSpec_det hspec' hspec
    subst this
    rw [hbody] at hbody'
    cases hbody'
    have hout : s.designatedOutput p r = .ok out :=
      State.designatedOutput_eq_ok.mpr ⟨e'.id, ho, Or.inr ⟨name, e', spec', r.workflow, htask,
        wk.execution?_of_mem he', hspec', hbody⟩⟩
    obtain ⟨cc, hcc, hfind⟩ := State.taskSpec_eq_ok.mp hspec'
    obtain ⟨plc, hplc, hctrl⟩ := State.concurrencyOf_eq_ok.mp hcc
    obtain ⟨we, hwe, hplce⟩ := State.placementOf_eq_ok.mp hplc
    obtain ⟨at_, hbv⟩ := (body_valid valid (workflow_mem hwe) (Workflow.placement?_eq_some hplce).1).2 cc hctrl
      spec' (List.mem_of_find?_eq_some hfind)
    rw [hbody] at hbv
    obtain ⟨w'', hw'', hplo, hend⟩ := workflow_of_validateBody hbv
    rw [hw] at hw''
    cases hw''
    refine close out hout hplo hend ?_
    rw [htask]
    obtain ⟨ts, hts⟩ : ∃ ts, e'.tasks.find? (·.name == name) = some ts :=
      Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨tk, htk, by simp [htkn]⟩)
    refine ⟨e'.id, e', ts, ho, wk.execution?_of_mem he', hts, ?_⟩
    refine List.any_eq_false.mpr fun y hy hyes => ?_
    simp only [Bool.and_eq_true, beq_iff_eq] at hyes
    exact fresh.taskRun r hr e'.id name ho htask hopen y hy ⟨hyes.1.1, hyes.1.2⟩

end Suimon.Round3.CalmAux
