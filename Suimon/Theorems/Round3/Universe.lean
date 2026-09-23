import Suimon.Theorems.Round3.Work
import Suimon.Theorems.Round3.ShapeFits
import Suimon.Theorems.Round3.UniverseInv

namespace Suimon.Round3
open State

/-! ## [11] Round3/Universe.lean — task D2

Identities never contain values, so the records a conforming execution can create are bounded by a
finite set computed from the program and the behavior alone: every source result may trigger every
target (arms and transform failures are ignored), and every call may yield all its elements. -/

section UniverseSection
variable {p : Program} {env : Env} {s : State}

/-- Result identities a placement of the run at `path` can produce, over-approximated. The fuel bounds
    connection paths, as for `Workflow.kind?`; `w.placements.length + 1` suffices in an acyclic workflow. -/
def possibleResults (p : Program) (B : Behavior) (path : Path) (w : Workflow) : Nat → String → List ResultId
  | 0, _ => []
  | fuel + 1, name =>
    match w.placement? name with
    | none => []
    | some pl =>
      let triggers : List (Option ResultId) :=
        if w.isEntry name then [none]
        else match w.incoming name with
          | [] => [none]
          | cs => cs.flatMap fun c => (possibleResults p B path w fuel c.source).map some
      let steps (id : String) : List Nat := List.range (max 1 (B.script id).yields.length)
      match pl.control with
      | .call (.function _) => triggers.flatMap fun t =>
          let id := Key.invocation path name t
          (steps id).map (Key.callResult id)
      | .branch .. => triggers.map fun t => Key.callResult (Key.invocation path name t) 0
      | .call (.workflow ..) => triggers.map fun t => Key.returned (Key.invocation path name t)
      | .concurrency cc => triggers.flatMap fun t =>
          let id := Key.invocation path name t
          Key.list id :: cc.tasks.flatMap fun task => (steps (Key.task id task.name)).map (Key.taskOutput id task.name)
      | .waitStream _ | .merge _ => [Key.aggregate path name]

/-- Keys of the records an execution can create. -/
structure Universe where
  runs : List Path := []
  invocations : List String := []
  calls : List String := []
  executions : List String := []
  tasks : List (String × String) := []
  results : List ResultId := []
  taskResults : List (String × String × Nat) := []
  deliveries : List (Path × Nat × ResultId) := []
  settled : List (Path × String) := []

instance : Append Universe where
  append a b := {
    runs := a.runs ++ b.runs, invocations := a.invocations ++ b.invocations, calls := a.calls ++ b.calls
    executions := a.executions ++ b.executions, tasks := a.tasks ++ b.tasks, results := a.results ++ b.results
    taskResults := a.taskResults ++ b.taskResults, deliveries := a.deliveries ++ b.deliveries
    settled := a.settled ++ b.settled }

def Universe.join (us : List Universe) : Universe := us.foldr (· ++ ·) {}

/-- The records of one run of `w` at `path` and of the runs it calls. `depth` bounds the nesting of
    workflow calls; `p.depth` suffices when calls are acyclic (`call_rank`). -/
def runUniverse (p : Program) (B : Behavior) : Nat → Path → Workflow → Universe
  | 0, _, _ => {}
  | depth + 1, path, w =>
    let results := possibleResults p B path w (w.placements.length + 1)
    let triggersOf (name : String) : List (Option ResultId) :=
      if w.isEntry name then [none]
      else match w.incoming name with
        | [] => [none]
        | cs => cs.flatMap fun c => (results c.source).map some
    let steps (id : String) : List Nat := List.range (max 1 (B.script id).yields.length)
    let child (childPath : Path) (wf : String) : Universe :=
      match p.workflow? wf with
      | some cw => runUniverse p B depth childPath cw
      | none => {}
    let perPlacement (pl : Placement) : Universe :=
      let ids := (triggersOf pl.name).map (Key.invocation path pl.name)
      let own : Universe := {
        settled := [(path, pl.name)], results := results pl.name
        deliveries := (w.inputs pl.name).flatMap fun (j, c) => (results c.source).map fun r => (path, j, r) }
      match pl.control with
      | .call (.function _) | .branch .. => own ++ { invocations := ids, calls := ids }
      | .call (.workflow wf _) =>
        own ++ { invocations := ids } ++ Universe.join (ids.map fun id => child (path ++ [id]) wf)
      | .concurrency cc =>
        own ++ { invocations := ids, executions := ids } ++ Universe.join (ids.map fun id =>
          ({ tasks := cc.tasks.map fun t => (id, t.name)
             calls := cc.tasks.filterMap fun t => match t.body with
               | .function _ => some (Key.task id t.name)
               | .workflow .. => none
             taskResults := cc.tasks.flatMap fun t => (steps (Key.task id t.name)).map fun j => (id, t.name, j) } :
            Universe) ++
          Universe.join (cc.tasks.map fun t => match t.body with
            | .workflow wf _ => child (path ++ [Key.task id t.name]) wf
            | .function _ => {}))
      | .waitStream _ | .merge _ => own
    ({ runs := [path] } : Universe) ++ Universe.join (w.placements.map perPlacement)

/-- The universe of a program under a behavior. It does not depend on the input value. -/
def universeOf (p : Program) (B : Behavior) : Universe :=
  match p.workflow? p.main with
  | some w => runUniverse p B p.depth [] w
  | none => {}

/-- The universe contains the key of every record of `s`. -/
structure Universe.Covers (u : Universe) (s : State) : Prop where
  runs : ∀ r ∈ s.runs, r.path ∈ u.runs
  invocations : ∀ i ∈ s.invocations, i.id ∈ u.invocations
  calls : ∀ c ∈ s.calls, c.id ∈ u.calls
  executions : ∀ e ∈ s.executions, e.id ∈ u.executions
  tasks : ∀ e ∈ s.executions, ∀ t ∈ e.tasks, (e.id, t.name) ∈ u.tasks
  results : ∀ r ∈ s.results, r.id ∈ u.results
  taskResults : ∀ r ∈ s.taskResults, (r.execution, r.task, r.index) ∈ u.taskResults
  deliveries : ∀ d ∈ s.deliveries, (d.run, d.connection, d.source) ∈ u.deliveries
  settled : ∀ x ∈ s.settled, (x.run, x.placement) ∈ u.settled

/-- The largest `work` a state covered by `u` can have when its calls follow `B`: each key is charged
    the largest progress of its record. -/
def Universe.weight (B : Behavior) (u : Universe) : Nat :=
  4 + 2 * u.runs.length + 2 * u.invocations.length +
    (u.calls.map fun id => 5 + 2 * (B.script id).yields.length).sum +
    2 * u.executions.length + 3 * u.tasks.length + u.results.length + 2 * u.taskResults.length +
    u.deliveries.length + u.settled.length

def workBound (p : Program) (B : Behavior) : Nat := (universeOf p B).weight B

namespace UniverseProof

/-! ### Proof of `universe_covers` and `work_le_bound`

`possibleResults` and `runUniverse` are unfolded into named parts (`resultsFor`, `triggersBy`,
`perPlacement`, `execU`, `childU`). Every result is allowed by the universe of its run
(`results_allowed`, by induction on the placement rank, from the result shapes of `UniverseInv.lean`),
hence so is every available trigger (`trigger_allowed`); the universe of every run is part of the
program's universe (`RunU`, by induction over the execution, with `call_rank` bounding the depth). Each
record's key is then found in the part of its placement (`covers_of_conforming`), and unique keys give
the bound (`work_le_weight`).

### Universes as key sets -/

theorem append_runs (a b : Universe) : (a ++ b).runs = a.runs ++ b.runs := rfl
theorem append_invocations (a b : Universe) : (a ++ b).invocations = a.invocations ++ b.invocations := rfl
theorem append_calls (a b : Universe) : (a ++ b).calls = a.calls ++ b.calls := rfl
theorem append_executions (a b : Universe) : (a ++ b).executions = a.executions ++ b.executions := rfl
theorem append_tasks (a b : Universe) : (a ++ b).tasks = a.tasks ++ b.tasks := rfl
theorem append_results (a b : Universe) : (a ++ b).results = a.results ++ b.results := rfl
theorem append_taskResults (a b : Universe) : (a ++ b).taskResults = a.taskResults ++ b.taskResults := rfl
theorem append_deliveries (a b : Universe) : (a ++ b).deliveries = a.deliveries ++ b.deliveries := rfl
theorem append_settled (a b : Universe) : (a ++ b).settled = a.settled ++ b.settled := rfl

attribute [local simp] append_runs append_invocations append_calls append_executions append_tasks append_results
  append_taskResults append_deliveries append_settled

/-- Every key of `u` is a key of `v`. -/
structure Sub (u v : Universe) : Prop where
  runs : ∀ x ∈ u.runs, x ∈ v.runs
  invocations : ∀ x ∈ u.invocations, x ∈ v.invocations
  calls : ∀ x ∈ u.calls, x ∈ v.calls
  executions : ∀ x ∈ u.executions, x ∈ v.executions
  tasks : ∀ x ∈ u.tasks, x ∈ v.tasks
  results : ∀ x ∈ u.results, x ∈ v.results
  taskResults : ∀ x ∈ u.taskResults, x ∈ v.taskResults
  deliveries : ∀ x ∈ u.deliveries, x ∈ v.deliveries
  settled : ∀ x ∈ u.settled, x ∈ v.settled

theorem Sub.refl (u : Universe) : Sub u u :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => h, fun _ h => h⟩

theorem Sub.trans {u v w : Universe} (h₁ : Sub u v) (h₂ : Sub v w) : Sub u w :=
  ⟨fun x h => h₂.runs x (h₁.runs x h), fun x h => h₂.invocations x (h₁.invocations x h),
    fun x h => h₂.calls x (h₁.calls x h), fun x h => h₂.executions x (h₁.executions x h),
    fun x h => h₂.tasks x (h₁.tasks x h), fun x h => h₂.results x (h₁.results x h),
    fun x h => h₂.taskResults x (h₁.taskResults x h), fun x h => h₂.deliveries x (h₁.deliveries x h),
    fun x h => h₂.settled x (h₁.settled x h)⟩

theorem Sub.left (u v : Universe) : Sub u (u ++ v) :=
  ⟨fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h],
    fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h],
    fun _ h => by simp [h]⟩

theorem Sub.right (u v : Universe) : Sub v (u ++ v) :=
  ⟨fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h],
    fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h], fun _ h => by simp [h],
    fun _ h => by simp [h]⟩

theorem Sub.join {u : Universe} : ∀ {us : List Universe}, u ∈ us → Sub u (Universe.join us)
  | _ :: _, List.Mem.head _ => Sub.left _ _
  | v :: _, List.Mem.tail _ h => (Sub.join h).trans (Sub.right v _)

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' fun x hx => h x (List.mem_cons_of_mem a hx)]

/-! ### Unfolding `possibleResults` and `runUniverse` -/

/-- The element indices the universe allows for the call `id`. -/
def stepsOf (B : Behavior) (id : String) : List Nat := List.range (max 1 (B.script id).yields.length)

/-- The results of a placement with control `ctrl`, given the triggers it may take. -/
def resultsFor (B : Behavior) (path : Path) (name : String) (ctrl : Control)
    (triggers : List (Option ResultId)) : List ResultId :=
  match ctrl with
  | .call (.function _) => triggers.flatMap fun t =>
      let id := Key.invocation path name t
      (stepsOf B id).map (Key.callResult id)
  | .branch .. => triggers.map fun t => Key.callResult (Key.invocation path name t) 0
  | .call (.workflow ..) => triggers.map fun t => Key.returned (Key.invocation path name t)
  | .concurrency cc => triggers.flatMap fun t =>
      let id := Key.invocation path name t
      Key.list id :: cc.tasks.flatMap fun task => (stepsOf B (Key.task id task.name)).map (Key.taskOutput id task.name)
  | .waitStream _ | .merge _ => [Key.aggregate path name]

/-- The triggers of a placement, from its sources' results under `res`. -/
def triggersBy (w : Workflow) (name : String) (res : String → List ResultId) : List (Option ResultId) :=
  if w.isEntry name then [none]
  else match w.incoming name with
    | [] => [none]
    | cs => cs.flatMap fun c => (res c.source).map some

/-- One unfolding of `possibleResults`. -/
theorem possibleResults_succ {p : Program} {B : Behavior} {path : Path} {w : Workflow} {fuel : Nat}
    {name : String} :
    possibleResults p B path w (fuel + 1) name = match w.placement? name with
      | none => []
      | some pl => resultsFor B path name pl.control (triggersBy w name (possibleResults p B path w fuel)) := by
  rw [possibleResults]
  rfl

/-- The results function of `runUniverse`. -/
def resultsIn (p : Program) (B : Behavior) (path : Path) (w : Workflow) : String → List ResultId :=
  possibleResults p B path w (w.placements.length + 1)

/-- The triggers function of `runUniverse`. -/
def triggersIn (p : Program) (B : Behavior) (path : Path) (w : Workflow) (name : String) : List (Option ResultId) :=
  triggersBy w name (resultsIn p B path w)

/-- A child run's universe. -/
def childU (p : Program) (B : Behavior) (depth : Nat) (childPath : Path) (wf : String) : Universe :=
  match p.workflow? wf with
  | some cw => runUniverse p B depth childPath cw
  | none => {}

/-- The records the universe keeps for one invocation of a concurrency. -/
def execU (p : Program) (B : Behavior) (depth : Nat) (path : Path) (cc : Concurrency) (id : String) : Universe :=
  ({ tasks := cc.tasks.map fun t => (id, t.name)
     calls := cc.tasks.filterMap fun t => match t.body with
       | .function _ => some (Key.task id t.name)
       | .workflow .. => none
     taskResults := cc.tasks.flatMap fun t => (stepsOf B (Key.task id t.name)).map fun j => (id, t.name, j) } :
    Universe) ++
  Universe.join (cc.tasks.map fun t => match t.body with
    | .workflow wf _ => childU p B depth (path ++ [Key.task id t.name]) wf
    | .function _ => {})

/-- The part of a run's universe every placement has, whatever its control: its settlement, its
    results and the deliveries on its input connections. -/
def ownU (p : Program) (B : Behavior) (path : Path) (w : Workflow) (pl : Placement) : Universe := {
    settled := [(path, pl.name)], results := resultsIn p B path w pl.name
    deliveries := (w.inputs pl.name).flatMap fun (j, c) => (resultsIn p B path w c.source).map fun r => (path, j, r) }

/-- The records the universe keeps for one placement of a run. -/
def perPlacement (p : Program) (B : Behavior) (depth : Nat) (path : Path) (w : Workflow) (pl : Placement) :
    Universe :=
  let ids := (triggersIn p B path w pl.name).map (Key.invocation path pl.name)
  match pl.control with
  | .call (.function _) | .branch .. => ownU p B path w pl ++ { invocations := ids, calls := ids }
  | .call (.workflow wf _) =>
    ownU p B path w pl ++ { invocations := ids } ++
      Universe.join (ids.map fun id => childU p B depth (path ++ [id]) wf)
  | .concurrency cc =>
    ownU p B path w pl ++ { invocations := ids, executions := ids } ++ Universe.join (ids.map (execU p B depth path cc))
  | .waitStream _ | .merge _ => ownU p B path w pl

/-- One unfolding of `runUniverse`. -/
theorem runUniverse_succ {p : Program} {B : Behavior} {depth : Nat} {path : Path} {w : Workflow} :
    runUniverse p B (depth + 1) path w =
      ({ runs := [path] } : Universe) ++ Universe.join (w.placements.map (perPlacement p B depth path w)) := by
  rw [runUniverse]
  rfl

/-! ### Fuel stability of `possibleResults` -/

theorem possibleResults_of_not_mem {p : Program} {B : Behavior} {path : Path} {w : Workflow} {name : String}
    (h : name ∉ w.placements.map (·.name)) : ∀ fuel, possibleResults p B path w fuel name = []
  | 0 => rfl
  | _ + 1 => by rw [possibleResults_succ, Workflow.placement?_eq_none h]

theorem triggersBy_congr {w : Workflow} {name : String} {res res' : String → List ResultId}
    (h : ∀ c ∈ w.incoming name, res c.source = res' c.source) : triggersBy w name res = triggersBy w name res' := by
  unfold triggersBy
  split
  · rfl
  · generalize w.incoming name = cs at h
    cases cs with
    | nil => rfl
    | cons c cs =>
      show (c :: cs).flatMap _ = (c :: cs).flatMap _
      exact flatMap_congr' fun x hx => by rw [h x hx]

/-- `possibleResults` stops depending on the fuel once the fuel exceeds the rank of the placement, for
    any rank that increases along connections (the model is `Workflow.kind?_fuel_stable`). -/
theorem possibleResults_fuel_stable {p : Program} {B : Behavior} {path : Path} {w : Workflow} {rank : String → Nat}
    (hrank : ∀ c ∈ w.connections, c.source ∈ w.placements.map (·.name) →
      c.target ∈ w.placements.map (·.name) → rank c.source < rank c.target) :
    ∀ m name f g, (name ∈ w.placements.map (·.name) → rank name < m) → m ≤ f → m ≤ g →
      possibleResults p B path w f name = possibleResults p B path w g name := by
  intro m
  induction m with
  | zero =>
    intro name f g hv _ _
    have hn : name ∉ w.placements.map (·.name) := fun h => by have := hv h; omega
    rw [possibleResults_of_not_mem hn, possibleResults_of_not_mem hn]
  | succ m ih =>
    intro name f g hv hf hg
    by_cases hn : name ∈ w.placements.map (·.name)
    · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [possibleResults_succ, possibleResults_succ,
        triggersBy_congr (res' := possibleResults p B path w g) ?_]
      intro c hc
      simp only [Workflow.incoming, List.mem_filter, beq_iff_eq] at hc
      apply ih c.source f g _ (by omega) (by omega)
      intro hs
      have := hrank c hc.1 hs (hc.2 ▸ hn)
      have := hv hn
      rw [hc.2] at *
      omega
    · rw [possibleResults_of_not_mem hn, possibleResults_of_not_mem hn]

/-- In an acyclic workflow, `resultsIn` is the rule applied to `triggersIn`. -/
theorem resultsIn_eq {p : Program} {B : Behavior} {path : Path} {w : Workflow} {name : String}
    (hacyc : w.acyclic = true) :
    resultsIn p B path w name = match w.placement? name with
      | none => []
      | some pl => resultsFor B path name pl.control (triggersIn p B path w name) := by
  obtain ⟨rank, hlt, hedge⟩ := acyclic_rank hacyc
  have hrank : ∀ c ∈ w.connections, c.source ∈ w.placements.map (·.name) →
      c.target ∈ w.placements.map (·.name) → rank c.source < rank c.target :=
    fun c hc hs ht => hedge (c.source, c.target) (List.mem_map.2 ⟨c, hc, rfl⟩) hs ht
  unfold triggersIn resultsIn
  rw [possibleResults_succ]
  cases hpl : w.placement? name with
  | none => rfl
  | some pl =>
    show resultsFor B path name pl.control _ = resultsFor B path name pl.control _
    have hn : name ∈ w.placements.map (·.name) :=
      List.mem_map.2 ⟨pl, (Workflow.placement?_eq_some hpl).1, (Workflow.placement?_eq_some hpl).2⟩
    have hle : rank name < w.placements.length := by simpa using hlt name hn
    rw [triggersBy_congr (res' := possibleResults p B path w (w.placements.length + 1)) ?_]
    intro c hc
    simp only [Workflow.incoming, List.mem_filter, beq_iff_eq] at hc
    refine possibleResults_fuel_stable hrank (rank name) c.source _ _ (fun hs => ?_) (by omega) (by omega)
    have := hrank c hc.1 hs (hc.2 ▸ hn)
    rwa [hc.2] at this

/-! ### Membership in the rule -/

theorem mem_triggersBy_none {w : Workflow} {name : String} {res : String → List ResultId}
    (h : w.isEntry name = true ∨ w.incoming name = []) : none ∈ triggersBy w name res := by
  unfold triggersBy
  rcases h with h | h
  · simp [h]
  · split
    · exact List.mem_singleton_self _
    · rw [h]; exact List.mem_singleton_self _

theorem mem_triggersBy_some {w : Workflow} {name : String} {res : String → List ResultId} {c : Connection}
    {src : ResultId} (hentry : w.isEntry name = false) (hc : c ∈ w.incoming name) (hsrc : src ∈ res c.source) :
    some src ∈ triggersBy w name res := by
  unfold triggersBy
  simp only [hentry, Bool.false_eq_true, ↓reduceIte]
  generalize w.incoming name = cs at hc
  cases cs with
  | nil => cases hc
  | cons c' cs =>
    show some src ∈ (c' :: cs).flatMap _
    exact List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨src, hsrc, rfl⟩⟩

theorem mem_stepsOf {B : Behavior} {id : String} {j : Nat} (h : j < max 1 (B.script id).yields.length) :
    j ∈ stepsOf B id :=
  List.mem_range.2 h

/-- A result identity of the shape an invocation with an allowed trigger produces is allowed. -/
theorem mem_resultsFor {B : Behavior} {path : Path} {name : String} {ctrl : Control}
    {triggers : List (Option ResultId)} {trig : Option ResultId} {rid : ResultId} (ht : trig ∈ triggers)
    (h : IdShape B ctrl (Key.invocation path name trig) rid) : rid ∈ resultsFor B path name ctrl triggers := by
  unfold IdShape at h
  unfold resultsFor
  split at h
  · obtain ⟨idx, hidx, rfl⟩ := h
    exact List.mem_flatMap.2 ⟨trig, ht, List.mem_map.2 ⟨idx, mem_stepsOf hidx, rfl⟩⟩
  · subst h; exact List.mem_map.2 ⟨trig, ht, rfl⟩
  · subst h; exact List.mem_map.2 ⟨trig, ht, rfl⟩
  · rcases h with rfl | ⟨spec, hspec, idx, hidx, rfl⟩
    · exact List.mem_flatMap.2 ⟨trig, ht, List.mem_cons_self⟩
    · exact List.mem_flatMap.2 ⟨trig, ht, List.mem_cons_of_mem _
        (List.mem_flatMap.2 ⟨spec, hspec, List.mem_map.2 ⟨idx, mem_stepsOf hidx, rfl⟩⟩)⟩
  · exact h.elim
  · exact h.elim

theorem mem_resultsFor_aggregate {B : Behavior} {path : Path} {name : String} {ctrl : Control}
    {triggers : List (Option ResultId)} (h : ∃ e, ctrl = .waitStream e ∨ ctrl = .merge e) :
    Key.aggregate path name ∈ resultsFor B path name ctrl triggers := by
  obtain ⟨e, rfl | rfl⟩ := h <;> exact List.mem_singleton_self _

/-! ### Every result and every trigger is allowed -/

/-- An available trigger is allowed once the results of the placement's sources are. -/
theorem trigAvail_mem {p : Program} {B : Behavior} {s : State} (inv : Delivery.Inv p s) {path : Path}
    {w : Workflow} {name : String} {trig : Option ResultId} (hw : s.workflow? p path = some w)
    (h : TrigAvail s path w name trig)
    (hsrc : ∀ r ∈ s.results, ∀ c ∈ w.connections, c.target = name → r.run = path → r.placement = c.source →
      r.id ∈ resultsIn p B path w c.source) :
    trig ∈ triggersIn p B path w name := by
  rcases h with ⟨rfl, h⟩ | ⟨src, rfl, hentry, d, hd, hdrun, hdsrc, c, hc, htgt⟩
  · exact mem_triggersBy_none h
  · obtain ⟨w₁, c₁, r₁, hw₁, hc₁, hr₁, hid, hrun, hpl, -⟩ := inv.own.deliveries d hd
    rw [hdrun, hw] at hw₁
    have hww : w₁ = w := (Option.some.inj hw₁).symm
    rw [hww, hc] at hc₁
    have hcc : c₁ = c := (Option.some.inj hc₁).symm
    rw [hcc] at hpl
    have hcm : c ∈ w.connections := List.mem_of_getElem? hc
    refine mem_triggersBy_some hentry (List.mem_filter.2 ⟨hcm, by simp [htgt]⟩) ?_
    rw [← hdsrc, ← hid]
    exact hsrc r₁ hr₁ c hcm htgt (hrun.trans hdrun) hpl

/-- Every result of a conforming execution is allowed by the universe of its run. By induction on the
    rank of its placement: the trigger of the invocation it comes from is a result of a source, which
    has a lower rank. -/
theorem results_allowed {p : Program} {B : Behavior} {s : State} (valid : p.validate = .ok ()) (reach : Reachable p s)
    (hshape : ∀ r ∈ s.results, ResultShape p B s r) :
    ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → r.id ∈ resultsIn p B r.run w r.placement := by
  have inv := Delivery.Reachable.inv reach
  intro r hr w hw
  obtain ⟨run, -, hwf⟩ := Delivery.workflow?_iff.mp hw
  have hwm : w ∈ p.workflows := (Program.workflow?_eq_some hwf).1
  obtain ⟨rank, -, hedge⟩ := placement_rank valid w hwm
  have hacyc := ((Program.validate_ok valid).workflows w hwm).acyclic
  suffices H : ∀ n, ∀ r' ∈ s.results, r'.run = r.run → rank r'.placement < n →
      r'.id ∈ resultsIn p B r.run w r'.placement from H _ r hr rfl (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro r' _ _ h; omega
  | succ n ih =>
    intro r' hr' hrun hlt
    obtain ⟨w', pl, hw', hpl, hcase⟩ := hshape r' hr'
    rw [hrun, hw] at hw'
    have hww : w' = w := (Option.some.inj hw').symm
    rw [hww] at hpl
    rw [resultsIn_eq hacyc, hpl]
    rcases hcase with ⟨trig, htrig, hid⟩ | ⟨hctrl, hid⟩
    · rw [hrun, hww] at htrig
      rw [hrun] at hid
      refine mem_resultsFor (trigAvail_mem inv hw htrig ?_) hid
      -- A source has a lower rank than its target.
      intro r'' hr'' c hc htgt hrun'' hpl''
      have hlt' : rank r''.placement < n := by
        have := hedge c hc
        rw [hpl'']
        rw [htgt] at this
        omega
      rw [← hpl'']
      exact ih r'' hr'' hrun'' hlt'
    · rw [hid, hrun]
      exact mem_resultsFor_aggregate hctrl

/-- Every available trigger is allowed. -/
theorem trigger_allowed {p : Program} {B : Behavior} {s : State} (reach : Reachable p s)
    (hres : ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → r.id ∈ resultsIn p B r.run w r.placement)
    {path : Path} {w : Workflow} {name : String} {trig : Option ResultId} (hw : s.workflow? p path = some w)
    (h : TrigAvail s path w name trig) : trig ∈ triggersIn p B path w name :=
  trigAvail_mem (Delivery.Reachable.inv reach) hw h fun r hr _ _ _ hrun hpl => by
    have := hres r hr w (hrun ▸ hw)
    rwa [hrun, hpl] at this

/-! ### The parts of a run's universe -/

/-- A run's universe has its path. -/
theorem path_mem_runUniverse {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow} :
    path ∈ (runUniverse p B (d + 1) path w).runs := by
  rw [runUniverse_succ]; simp

/-- A run's universe has the part of each placement. -/
theorem sub_perPlacement {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow} {pl : Placement}
    (hpl : pl ∈ w.placements) : Sub (perPlacement p B d path w pl) (runUniverse p B (d + 1) path w) := by
  rw [runUniverse_succ]
  exact (Sub.join (List.mem_map.2 ⟨pl, hpl, rfl⟩)).trans (Sub.right _ _)

theorem sub_ownU {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow} {pl : Placement} :
    Sub (ownU p B path w pl) (perPlacement p B d path w pl) := by
  rcases pl with ⟨name, control, policy, timeout⟩
  cases control with
  | call body =>
    cases body with
    | function f => exact Sub.left _ _
    | workflow wf out => exact (Sub.left _ _).trans (Sub.left _ _)
  | branch j arms => exact Sub.left _ _
  | concurrency cc => exact (Sub.left _ _).trans (Sub.left _ _)
  | waitStream e => exact Sub.refl _
  | merge e => exact Sub.refl _

theorem ownU_settled {p : Program} {B : Behavior} {path : Path} {w : Workflow} {pl : Placement} :
    (path, pl.name) ∈ (ownU p B path w pl).settled := List.mem_singleton_self _

theorem ownU_results {p : Program} {B : Behavior} {path : Path} {w : Workflow} {pl : Placement} {rid : ResultId}
    (h : rid ∈ resultsIn p B path w pl.name) : rid ∈ (ownU p B path w pl).results := h

theorem ownU_deliveries {p : Program} {B : Behavior} {path : Path} {w : Workflow} {pl : Placement} {j : Nat}
    {c : Connection} {rid : ResultId} (hjc : (j, c) ∈ w.inputs pl.name) (h : rid ∈ resultsIn p B path w c.source) :
    (path, j, rid) ∈ (ownU p B path w pl).deliveries :=
  List.mem_flatMap.2 ⟨(j, c), hjc, List.mem_map.2 ⟨rid, h, rfl⟩⟩

/-- An invocable placement has the invocations of its allowed triggers. -/
theorem perPlacement_invocations {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow}
    {pl : Placement} {trig : Option ResultId} (hinv : Delivery.Invocable pl.control)
    (ht : trig ∈ triggersIn p B path w pl.name) :
    Key.invocation path pl.name trig ∈ (perPlacement p B d path w pl).invocations := by
  have hid : Key.invocation path pl.name trig ∈ (triggersIn p B path w pl.name).map (Key.invocation path pl.name) :=
    List.mem_map.2 ⟨trig, ht, rfl⟩
  rcases pl with ⟨name, control, policy, timeout⟩
  cases control with
  | call body =>
    cases body with
    | function f => simp only [perPlacement, append_invocations]; exact List.mem_append_right _ hid
    | workflow wf out =>
      simp only [perPlacement, append_invocations]
      exact List.mem_append_left _ (List.mem_append_right _ hid)
  | branch j arms => simp only [perPlacement, append_invocations]; exact List.mem_append_right _ hid
  | concurrency cc =>
    simp only [perPlacement, append_invocations]
    exact List.mem_append_left _ (List.mem_append_right _ hid)
  | waitStream e => exact hinv.elim
  | merge e => exact hinv.elim

/-- A function call or branch has the calls of its invocations. -/
theorem perPlacement_calls {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow}
    {pl : Placement} {trig : Option ResultId}
    (hctrl : (∃ f, pl.control = .call (.function f)) ∨ (∃ j arms, pl.control = .branch j arms))
    (ht : trig ∈ triggersIn p B path w pl.name) :
    Key.invocation path pl.name trig ∈ (perPlacement p B d path w pl).calls := by
  have hid : Key.invocation path pl.name trig ∈ (triggersIn p B path w pl.name).map (Key.invocation path pl.name) :=
    List.mem_map.2 ⟨trig, ht, rfl⟩
  rcases pl with ⟨name, control, policy, timeout⟩
  rcases hctrl with ⟨f, hf⟩ | ⟨j, arms, hb⟩
  · dsimp only at hf; subst hf
    simp only [perPlacement, append_calls]; exact List.mem_append_right _ hid
  · dsimp only at hb; subst hb
    simp only [perPlacement, append_calls]; exact List.mem_append_right _ hid

/-- A concurrency has the executions of its invocations. -/
theorem perPlacement_executions {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow}
    {pl : Placement} {trig : Option ResultId} {cc : Concurrency} (hctrl : pl.control = .concurrency cc)
    (ht : trig ∈ triggersIn p B path w pl.name) :
    Key.invocation path pl.name trig ∈ (perPlacement p B d path w pl).executions := by
  have hid : Key.invocation path pl.name trig ∈ (triggersIn p B path w pl.name).map (Key.invocation path pl.name) :=
    List.mem_map.2 ⟨trig, ht, rfl⟩
  rcases pl with ⟨name, control, policy, timeout⟩
  dsimp only at hctrl; subst hctrl
  simp only [perPlacement, append_executions]
  exact List.mem_append_left _ (List.mem_append_right _ hid)

/-- A concurrency has the tasks, task calls, task results and task runs of its invocations. -/
theorem sub_execU {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow}
    {pl : Placement} {trig : Option ResultId} {cc : Concurrency} (hctrl : pl.control = .concurrency cc)
    (ht : trig ∈ triggersIn p B path w pl.name) :
    Sub (execU p B d path cc (Key.invocation path pl.name trig)) (perPlacement p B d path w pl) := by
  have hid : Key.invocation path pl.name trig ∈ (triggersIn p B path w pl.name).map (Key.invocation path pl.name) :=
    List.mem_map.2 ⟨trig, ht, rfl⟩
  rcases pl with ⟨name, control, policy, timeout⟩
  dsimp only at hctrl; subst hctrl
  exact (Sub.join (List.mem_map.2 ⟨_, hid, rfl⟩)).trans (Sub.right _ _)

/-- A sub-workflow call has the runs of its invocations. -/
theorem sub_childU_call {p : Program} {B : Behavior} {d : Nat} {path : Path} {w : Workflow}
    {pl : Placement} {trig : Option ResultId} {wf out : String} (hctrl : pl.control = .call (.workflow wf out))
    (ht : trig ∈ triggersIn p B path w pl.name) :
    Sub (childU p B d (path ++ [Key.invocation path pl.name trig]) wf) (perPlacement p B d path w pl) := by
  have hid : Key.invocation path pl.name trig ∈ (triggersIn p B path w pl.name).map (Key.invocation path pl.name) :=
    List.mem_map.2 ⟨trig, ht, rfl⟩
  have hmem : childU p B d (path ++ [Key.invocation path pl.name trig]) wf ∈
      ((triggersIn p B path w pl.name).map (Key.invocation path pl.name)).map
        (fun id => childU p B d (path ++ [id]) wf) :=
    List.mem_map_of_mem (f := fun id => childU p B d (path ++ [id]) wf) hid
  rcases pl with ⟨name, control, policy, timeout⟩
  dsimp only at hctrl; subst hctrl
  exact (Sub.join hmem).trans (Sub.right _ _)

theorem execU_tasks {p : Program} {B : Behavior} {d : Nat} {path : Path} {cc : Concurrency} {id : String}
    {task : TaskSpec} (htask : task ∈ cc.tasks) : (id, task.name) ∈ (execU p B d path cc id).tasks := by
  simp only [execU, append_tasks]
  exact List.mem_append_left _ (List.mem_map.2 ⟨task, htask, rfl⟩)

theorem execU_calls {p : Program} {B : Behavior} {d : Nat} {path : Path} {cc : Concurrency} {id : String}
    {task : TaskSpec} (htask : task ∈ cc.tasks) {f : String} (hbody : task.body = .function f) :
    Key.task id task.name ∈ (execU p B d path cc id).calls := by
  simp only [execU, append_calls]
  exact List.mem_append_left _ (List.mem_filterMap.2 ⟨task, htask, by rw [hbody]⟩)

theorem execU_taskResults {p : Program} {B : Behavior} {d : Nat} {path : Path} {cc : Concurrency} {id : String}
    {task : TaskSpec} (htask : task ∈ cc.tasks) {j : Nat}
    (hj : j < max 1 (B.script (Key.task id task.name)).yields.length) :
    (id, task.name, j) ∈ (execU p B d path cc id).taskResults := by
  simp only [execU, append_taskResults]
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨task, htask, List.mem_map.2 ⟨j, mem_stepsOf hj, rfl⟩⟩)

/-- A workflow task has its run. -/
theorem sub_childU_task {p : Program} {B : Behavior} {d : Nat} {path : Path} {cc : Concurrency} {id : String}
    {task : TaskSpec} (htask : task ∈ cc.tasks) {wf out : String} (hbody : task.body = .workflow wf out) :
    Sub (childU p B d (path ++ [Key.task id task.name]) wf) (execU p B d path cc id) := by
  have hmem := List.mem_map_of_mem (f := fun t : TaskSpec => match t.body with
    | .workflow wf _ => childU p B d (path ++ [Key.task id t.name]) wf
    | .function _ => ({} : Universe)) htask
  simp only [hbody] at hmem
  exact (Sub.join hmem).trans (Sub.right _ _)

/-- The universe of a child run whose workflow exists. -/
theorem childU_eq {p : Program} {B : Behavior} {d : Nat} {childPath : Path} {wf : String} {cw : Workflow}
    (h : p.workflow? wf = some cw) : childU p B d childPath wf = runUniverse p B d childPath cw := by
  simp only [childU, h]

/-! ### Every run's universe is part of the program's -/

/-- The universe of every run is part of the program's universe, at a depth that leaves room for the
    sub-workflow and workflow-task runs below it (`call_rank`). -/
def RunU (p : Program) (B : Behavior) (rank : String → Nat) (s : State) : Prop :=
  ∀ r ∈ s.runs, ∃ w d, p.workflow? r.workflow = some w ∧ p.workflows.length - rank w.id ≤ d ∧
    Sub (runUniverse p B (d + 1) r.path w) (universeOf p B)

/-- `RunU` depends only on the paths and workflows of the runs. -/
theorem RunU.of_old {p : Program} {B : Behavior} {rank : String → Nat} {s t : State} (h : RunU p B rank s)
    (ht : ∀ r ∈ t.runs, ∃ r₀ ∈ s.runs, r₀.path = r.path ∧ r₀.workflow = r.workflow) : RunU p B rank t := by
  intro r hr
  obtain ⟨r₀, hr₀, hpath, hwf⟩ := ht r hr
  obtain ⟨w, d, hw, hd, hsub⟩ := h r₀ hr₀
  exact ⟨w, d, hwf ▸ hw, hd, hpath ▸ hsub⟩

/-- The universe of the run at a path. -/
theorem RunU.ctx {p : Program} {B : Behavior} {rank : String → Nat} {s : State} (h : RunU p B rank s) {path : Path}
    {w : Workflow} (hw : s.workflow? p path = some w) :
    ∃ d, p.workflows.length - rank w.id ≤ d ∧ Sub (runUniverse p B (d + 1) path w) (universeOf p B) := by
  obtain ⟨R, hR, hRw⟩ := Delivery.workflow?_iff.mp hw
  obtain ⟨hRm, hRp⟩ := run?_eq_some hR
  obtain ⟨w', d, hw', hd, hsub⟩ := h R hRm
  rw [hRw] at hw'
  have hww : w = w' := Option.some.inj hw'
  subst hww
  exact ⟨d, hd, hRp ▸ hsub⟩

/-- A run called from a placement of a run gets the child universe, one level down. -/
theorem child_ctx {p : Program} {B : Behavior} {rank : String → Nat}
    (hlt : ∀ w ∈ p.workflows, rank w.id < p.workflows.length)
    (hedge : ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ wf ∈ pl.control.workflowRefs, ∀ w' ∈ p.workflows,
      w'.id = wf → rank w.id < rank w'.id)
    {w : Workflow} {d : Nat} (hwm : w ∈ p.workflows) (hd : p.workflows.length - rank w.id ≤ d)
    {pl : Placement} (hpl : pl ∈ w.placements) {wf : String} (hwf : wf ∈ pl.control.workflowRefs) {cw : Workflow}
    (hcw : p.workflow? wf = some cw) {childPath : Path} (hsub : Sub (childU p B d childPath wf) (universeOf p B)) :
    ∃ d', p.workflows.length - rank cw.id ≤ d' ∧ Sub (runUniverse p B (d' + 1) childPath cw) (universeOf p B) := by
  obtain ⟨hcwm, hcwid⟩ := Program.workflow?_eq_some hcw
  have h1 := hlt w hwm
  have h2 := hlt cw hcwm
  have h3 := hedge w hwm pl hpl wf hwf cw hcwm hcwid
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine ⟨d', by omega, ?_⟩
  rw [childU_eq hcw] at hsub
  exact hsub

/-- Every step keeps `RunU`: `start` creates the root with the whole universe, and `invoke` and
    `beginTask` create child runs inside the universe of their parent, for an allowed trigger. -/
theorem step_runU {p : Program} {B : Behavior} {s t : State} {op : Op} (valid : p.validate = .ok ())
    {rank : String → Nat} (hlt : ∀ w ∈ p.workflows, rank w.id < p.workflows.length)
    (hedge : ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ wf ∈ pl.control.workflowRefs, ∀ w' ∈ p.workflows,
      w'.id = wf → rank w.id < rank w'.id)
    (reach : Reachable p s)
    (hres : ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → r.id ∈ resultsIn p B r.run w r.placement)
    (hs : step p s op = .ok t) (ih : RunU p B rank s) : RunU p B rank t := by
  have old : ∀ {u : State}, u.runs = s.runs → RunU p B rank u := fun hu =>
    ih.of_old fun r hr => ⟨r, hu ▸ hr, rfl, rfl⟩
  have added : ∀ {u : State} (x : Run), u.runs = s.runs ++ [x] →
      (∃ w d, p.workflow? x.workflow = some w ∧ p.workflows.length - rank w.id ≤ d ∧
        Sub (runUniverse p B (d + 1) x.path w) (universeOf p B)) → RunU p B rank u := by
    intro u x hu hx r hr
    rw [hu, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact ih r hr
    · exact hx
  have setRun : ∀ {u : State} {r : Run}, s.run? r.path = some r →
      u.runs = (s.setRun { r with complete := true }).runs → RunU p B rank u := by
    intro u r hr hu
    refine ih.of_old fun x hx => ?_
    rw [hu] at hx
    obtain ⟨r₀, hr₀, hp, hw, -⟩ := Delivery.runOld_setRun (run?_eq_some hr).1 hx
    exact ⟨r₀, hr₀, hp, hw⟩
  cases op with
  | start input =>
    obtain ⟨-, -, w, hw, -, rfl⟩ := Step.start_inv hs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨w, p.workflows.length, hw, by omega, ?_⟩
    unfold universeOf
    rw [hw]
    exact Sub.refl _
  | invoke path name trigger =>
    obtain ⟨-, -, r, w, pl, input, id, hr, -, hw, hpl, hinput, hid, -, -, h⟩ := Step.invoke_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨wf, out, hctrl, -, rfl⟩ | ⟨_, -, -, rfl⟩
    · exact old rfl
    · exact old rfl
    · refine added _ rfl ?_
      have hpath := (run?_eq_some hr).2
      have hwp : s.workflow? p path = some w := Delivery.workflow?_iff.mpr ⟨r, hr, hw⟩
      obtain ⟨d, hd, hsub⟩ := ih.ctx hwp
      have hwm := (Program.workflow?_eq_some hw).1
      obtain ⟨hplm, hname⟩ := Workflow.placement?_eq_some hpl
      obtain ⟨cw, hcw⟩ := call_workflow_exists valid hwm hplm hctrl
      have htrig : trigger ∈ triggersIn p B path w pl.name := by
        rw [hname]
        have := trigAvail_of_input hinput
        rw [hpath] at this
        exact trigger_allowed reach hres hwp this
      have hsubC := (sub_childU_call hctrl htrig).trans ((sub_perPlacement hplm).trans hsub)
      rw [hname, ← hid] at hsubC
      obtain ⟨d', hd', hsub'⟩ := child_ctx hlt hedge hwm hd hplm (by rw [hctrl]; exact List.mem_singleton_self _)
        hcw hsubC
      exact ⟨cw, d', hcw, hd', hsub'⟩
    · exact old rfl
  | fetch id =>
    obtain ⟨-, -, _, -, -, -, rfl⟩ := Step.fetch_inv hs
    exact old rfl
  | returned id value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, hacc, hso⟩ := Step.returned_inv hs
    exact old (by rw [(settleOwner_update hso).runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | judged id arm =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hacc, rfl⟩ := Step.judged_inv hs
    exact old (by rw [setInvocation_runs, setCall_runs, (accept_frame hacc).2.2.2.1])
  | yielded id value =>
    obtain ⟨-, -, _, _, -, -, -, hacc, rfl⟩ := Step.yielded_inv hs
    exact old (by rw [setCall_runs, (accept_frame hacc).2.2.2.1])
  | ended id =>
    obtain ⟨-, -, _, -, -, -, hso⟩ := Step.ended_inv hs
    exact old (by rw [(settleOwner_update hso).runs, setCall_runs])
  | failed id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.failed_inv hs
    exact old (failCall_runs h)
  | timedOut id element =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.timedOut_inv hs
    exact old (failCall_runs h)
  | lost id =>
    obtain ⟨-, -, _, -, ⟨-, h⟩ | ⟨-, h⟩⟩ := Step.lost_inv hs
    · exact old (failCall_runs h)
    · exact old (by rw [(cancelOwner_update h).runs, setCall_runs])
  | terminated id =>
    obtain ⟨-, -, _, -, -, h⟩ := Step.terminated_inv hs
    exact old (by rw [(cancelOwner_update h).runs, setCall_runs])
  | deliver path index source value =>
    obtain ⟨-, -, _, _, _, -, -, rfl⟩ := Step.deliver_inv hs
    exact old rfl
  | transformFailed path index source =>
    obtain ⟨-, -, _, _, _, _, -, -, -, rfl⟩ := Step.transformFailed_inv hs
    exact old (by simp)
  | taskInput eid name value =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInput_inv hs
    exact old rfl
  | taskInputFailed eid name =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskInputFailed_inv hs
    exact old (by simp)
  | beginTask eid name =>
    obtain ⟨-, -, e, cc, ts, spec, he, -, hcc, -, -, -, hspec, h⟩ := Step.beginTask_inv hs
    rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨wf, out, hbody, -, rfl⟩
    · exact old rfl
    · refine added _ rfl ?_
      have inv := Delivery.Reachable.inv reach
      obtain ⟨hem, -⟩ := execution?_eq_some he
      obtain ⟨i, hi, hie, hir, hip, -⟩ := inv.own.executions e hem
      obtain ⟨hid, w, pl, hw, hpl, -, htrigA⟩ := trigAvail_of_placed (inv.own.invocations i hi)
      rw [hir] at hw htrigA hid
      rw [hip] at hpl htrigA hid
      obtain ⟨pl', hpl', hctrl⟩ := State.concurrencyOf_eq_ok.mp hcc
      obtain ⟨w', hw', hpl''⟩ := State.placementOf_eq_ok.mp hpl'
      have hww : w = w' := Option.some.inj (hw.symm.trans hw')
      rw [← hww, hpl] at hpl''
      have hpp : pl = pl' := Option.some.inj hpl''
      rw [← hpp] at hctrl
      obtain ⟨d, hd, hsub⟩ := ih.ctx hw
      have hwm : w ∈ p.workflows := by
        obtain ⟨R, -, hRw⟩ := Delivery.workflow?_iff.mp hw
        exact (Program.workflow?_eq_some hRw).1
      obtain ⟨hplm, hname⟩ := Workflow.placement?_eq_some hpl
      have htrig : i.trigger ∈ triggersIn p B e.run w pl.name := by
        rw [hname]; exact trigger_allowed reach hres hw htrigA
      have hsubE := (sub_execU (d := d) hctrl htrig).trans ((sub_perPlacement hplm).trans hsub)
      obtain ⟨cc', hcc', hfind⟩ := State.taskSpec_eq_ok.mp hspec
      have hcc'' : cc = cc' := Settle.concurrencyOf_det hcc hcc'
      rw [← hcc''] at hfind
      have hspecm : spec ∈ cc.tasks := List.mem_of_find?_eq_some hfind
      have hsname : spec.name = name := by simpa using List.find?_some hfind
      have hsubC := (sub_childU_task hspecm hbody).trans hsubE
      rw [hname, ← hid, hie, hsname] at hsubC
      obtain ⟨cw, hcw⟩ := task_workflow_exists valid hwm hplm hctrl hspecm hbody
      have hwf : wf ∈ pl.control.workflowRefs := by
        rw [hctrl]
        exact List.mem_filterMap.2 ⟨spec, hspecm, by rw [hbody]; rfl⟩
      obtain ⟨d', hd', hsub'⟩ := child_ctx hlt hedge hwm hd hplm hwf hcw hsubC
      exact ⟨cw, d', hcw, hd', hsub'⟩
  | taskOutput eid name index value =>
    obtain ⟨-, -, _, _, _, _, -, -, -, -, -, -, h⟩ := Step.taskOutput_inv hs
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact old rfl
  | taskOutputFailed eid name index =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, rfl⟩ := Step.taskOutputFailed_inv hs
    exact old (by simp)
  | settle path name =>
    obtain ⟨-, -, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, h⟩ := Step.settle_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨_, -, -, rfl⟩ <;> exact old rfl
  | closeExecution eid =>
    obtain ⟨-, -, _, _, _, -, -, -, -, -, -, h⟩ := Step.closeExecution_inv hs
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact old rfl
  | closeRun path =>
    obtain ⟨-, -, r, _, _, _, _, hr, -, -, -, -, -, -, -, h⟩ := Step.closeRun_inv hs
    have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
    rcases h with ⟨-, _, -, h⟩ | ⟨_, _, _, -, -, -, h⟩ <;>
      rcases h with ⟨-, _, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact setRun hr' rfl
  | cancel =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := Step.cancel_inv hs <;> exact old rfl
  | conclude =>
    obtain ⟨-, ⟨-, r, _, hr, -, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := Step.conclude_inv hs
    · have hr' : s.run? r.path = some r := by rw [(run?_eq_some hr).2]; exact hr
      exact setRun hr' rfl
    · exact old rfl

/-- `RunU` holds along a conforming execution. -/
theorem conforming_runU {p : Program} {env : Env} {tr : List Op} {s : State} (valid : p.validate = .ok ())
    {rank : String → Nat} (hlt : ∀ w ∈ p.workflows, rank w.id < p.workflows.length)
    (hedge : ∀ w ∈ p.workflows, ∀ pl ∈ w.placements, ∀ wf ∈ pl.control.workflowRefs, ∀ w' ∈ p.workflows,
      w'.id = wf → rank w.id < rank w'.id)
    (h : Conforming p env tr s) : RunU p env.behavior rank s := by
  induction h with
  | nil => intro r hr; cases hr
  | snoc hex _ hs _ ih =>
    have reach := hex.reachable
    exact step_runU valid hlt hedge reach (results_allowed valid reach (conforming_resultShape hex)) hs ih

/-! ### Every record is covered -/

section Cover
variable {p : Program} {B : Behavior} {rank : String → Nat} {s : State}

/-- The universe part of a placement of an existing run. -/
theorem placement_ctx (hrun : RunU p B rank s) {path : Path} {w : Workflow} {name : String} {pl : Placement}
    (hw : s.workflow? p path = some w) (hpl : w.placement? name = some pl) :
    ∃ d, Sub (perPlacement p B d path w pl) (universeOf p B) := by
  obtain ⟨d, -, hsub⟩ := hrun.ctx hw
  exact ⟨d, (sub_perPlacement (Workflow.placement?_eq_some hpl).1).trans hsub⟩

/-- An invocation's identity is allowed in the universe part of its placement. -/
theorem invocation_ctx (reach : Reachable p s)
    (hres : ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → r.id ∈ resultsIn p B r.run w r.placement)
    (hrun : RunU p B rank s) {i : Invocation} (hi : i ∈ s.invocations) :
    ∃ w pl d, s.workflow? p i.run = some w ∧ w.placement? i.placement = some pl ∧ Delivery.Invocable pl.control ∧
      i.trigger ∈ triggersIn p B i.run w pl.name ∧ i.id = Key.invocation i.run pl.name i.trigger ∧
      Sub (perPlacement p B d i.run w pl) (universeOf p B) := by
  obtain ⟨hid, w, pl, hw, hpl, hinv, htrig⟩ := trigAvail_of_placed ((Delivery.Reachable.inv reach).own.invocations i hi)
  obtain ⟨d, hsub⟩ := placement_ctx hrun hw hpl
  have hname := (Workflow.placement?_eq_some hpl).2
  refine ⟨w, pl, d, hw, hpl, hinv, ?_, by rw [hname]; exact hid, hsub⟩
  rw [hname]
  exact trigger_allowed reach hres hw htrig

/-- An execution's identity and records are allowed in the universe part of its concurrency. -/
theorem execution_ctx (reach : Reachable p s)
    (hres : ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → r.id ∈ resultsIn p B r.run w r.placement)
    (hrun : RunU p B rank s) {e : Execution} (he : e ∈ s.executions) :
    ∃ cc d, s.concurrencyOf p e = .ok cc ∧ e.id ∈ (universeOf p B).executions ∧
      Sub (execU p B d e.run cc e.id) (universeOf p B) := by
  obtain ⟨i, hi, hie, hir, hip, cc, hcc⟩ := (Delivery.Reachable.inv reach).own.executions e he
  obtain ⟨w, pl, d, hw, hpl, -, htrig, hid, hsub⟩ := invocation_ctx reach hres hrun hi
  obtain ⟨pl', hpl', hctrl⟩ := State.concurrencyOf_eq_ok.mp hcc
  obtain ⟨w', hw', hpl''⟩ := State.placementOf_eq_ok.mp hpl'
  rw [← hir] at hw'
  have hww : w = w' := Option.some.inj (hw.symm.trans hw')
  rw [← hww, ← hip, hpl] at hpl''
  have hpp : pl = pl' := Option.some.inj hpl''
  rw [← hpp] at hctrl
  have hkey : Key.invocation i.run pl.name i.trigger = e.id := hid.symm.trans hie
  refine ⟨cc, d, hcc, ?_, ?_⟩
  · have := hsub.executions _ (perPlacement_executions hctrl htrig)
    rwa [hkey] at this
  · have := (sub_execU hctrl htrig).trans hsub
    rwa [hkey, hir] at this

/-- The task names of an execution are those of its concurrency. -/
theorem execution_names (reach : Reachable p s) {e : Execution} (he : e ∈ s.executions) {cc : Concurrency}
    (hcc : s.concurrencyOf p e = .ok cc) : e.tasks.map (·.name) = cc.tasks.map (·.name) := by
  obtain ⟨-, -, -, -, -, pl, cc', hpl, hctrl, hnames⟩ := (Settle.reachable reach).1.execOwner e he
  obtain ⟨pl', hpl', hctrl'⟩ := State.concurrencyOf_eq_ok.mp hcc
  obtain ⟨w, hw, hpl''⟩ := State.placementOf_eq_ok.mp hpl'
  rw [Settle.placementAt_eq hw, hpl''] at hpl
  have hpp : pl' = pl := Option.some.inj hpl
  rw [hpp, hctrl] at hctrl'
  have : cc' = cc := by cases hctrl'; rfl
  rw [hnames, this]

end Cover

/-- Every record's key lies in the universe part of its placement (`universe_covers`). -/
theorem covers_of_conforming {p : Program} {env : Env} {tr : List Op} {s : State} (valid : p.validate = .ok ())
    (h : Conforming p env tr s) : (universeOf p env.behavior).Covers s := by
  obtain ⟨rank, hlt, hedge⟩ := call_rank valid
  have reach := h.reachable
  have inv := Delivery.Reachable.inv reach
  have hrun := conforming_runU valid hlt hedge h
  have hres := results_allowed valid reach (conforming_resultShape h)
  have hidx := conforming_taskIndex h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- runs
    intro r hr
    obtain ⟨w, d, -, -, hsub⟩ := hrun r hr
    exact hsub.runs _ path_mem_runUniverse
  · -- invocations
    intro i hi
    obtain ⟨w, pl, d, -, -, hinv, htrig, hid, hsub⟩ := invocation_ctx reach hres hrun hi
    rw [hid]
    exact hsub.invocations _ (perPlacement_invocations hinv htrig)
  · -- calls
    intro c hc
    rcases inv.own.calls c hc with ⟨-, hco, i, hi, hio, w, pl, hw, hpl, hctrl⟩ |
        ⟨name, -, hkey, e, he, heo, -, spec, f, hspec, hbody⟩
    · obtain ⟨w', pl', d, hw', hpl', -, htrig, hid, hsub⟩ := invocation_ctx reach hres hrun hi
      rw [hw] at hw'
      have hww : w = w' := Option.some.inj hw'
      rw [← hww, hpl] at hpl'
      have hpp : pl = pl' := Option.some.inj hpl'
      rw [← hpp] at htrig hid hsub
      have hctrl' : (∃ f, pl.control = .call (.function f)) ∨ (∃ j arms, pl.control = .branch j arms) := by
        rcases hctrl with ⟨f, -, hf, -⟩ | ⟨j, arms, hb, -⟩
        · exact Or.inl ⟨f, hf⟩
        · exact Or.inr ⟨j, arms, hb⟩
      rw [hco, ← hio, hid]
      exact hsub.calls _ (perPlacement_calls hctrl' htrig)
    · obtain ⟨cc, d, hcc, -, hsub⟩ := execution_ctx reach hres hrun he
      obtain ⟨cc', hcc', hfind⟩ := State.taskSpec_eq_ok.mp hspec
      have hcc'' : cc = cc' := Settle.concurrencyOf_det hcc hcc'
      rw [← hcc''] at hfind
      have hspecm : spec ∈ cc.tasks := List.mem_of_find?_eq_some hfind
      have hsname : spec.name = name := by simpa using List.find?_some hfind
      have := hsub.calls _ (execU_calls hspecm hbody)
      rwa [hsname, heo, ← hkey] at this
  · -- executions
    intro e he
    obtain ⟨cc, d, -, hmem, -⟩ := execution_ctx reach hres hrun he
    exact hmem
  · -- tasks
    intro e he ts hts
    obtain ⟨cc, d, hcc, -, hsub⟩ := execution_ctx reach hres hrun he
    have hn : ts.name ∈ cc.tasks.map (·.name) := by
      rw [← execution_names reach he hcc]; exact List.mem_map_of_mem hts
    obtain ⟨spec, hspecm, hsname⟩ := List.mem_map.1 hn
    have := hsub.tasks _ (execU_tasks (id := e.id) hspecm)
    rwa [hsname] at this
  · -- results
    intro r hr
    obtain ⟨w, pl, hw, hpl, -⟩ := conforming_resultShape h r hr
    obtain ⟨d, hsub⟩ := placement_ctx hrun hw hpl
    have hname := (Workflow.placement?_eq_some hpl).2
    refine hsub.results _ (sub_ownU.results _ (ownU_results ?_))
    rw [hname]
    exact hres r hr w hw
  · -- task results
    intro tr htr
    obtain ⟨e, he, heid, ts, hts, htsn⟩ := Reachable.taskResultsOwned reach tr htr
    obtain ⟨cc, d, hcc, -, hsub⟩ := execution_ctx reach hres hrun he
    have hn : ts.name ∈ cc.tasks.map (·.name) := by
      rw [← execution_names reach he hcc]; exact List.mem_map_of_mem hts
    obtain ⟨spec, hspecm, hsname⟩ := List.mem_map.1 hn
    have hj := hidx tr htr
    unfold TaskIndexOk at hj
    rw [← heid, ← htsn, ← hsname] at hj
    have := hsub.taskResults _ (execU_taskResults hspecm hj)
    rwa [hsname, htsn, heid] at this
  · -- deliveries
    intro dl hdl
    obtain ⟨w, c, r, hw, hc, hr, hid, hrun', hpl, -⟩ := inv.own.deliveries dl hdl
    obtain ⟨R, -, hRw⟩ := Delivery.workflow?_iff.mp hw
    have hwm : w ∈ p.workflows := (Program.workflow?_eq_some hRw).1
    obtain ⟨-, dst, -, hdst, -⟩ := typedConnections_of_validate valid w hwm c (List.mem_of_getElem? hc)
    obtain ⟨d, hsub⟩ := placement_ctx hrun hw hdst
    have hdname := (Workflow.placement?_eq_some hdst).2
    have hjc : (dl.connection, c) ∈ w.inputs dst.name := Delivery.mem_inputs.2 ⟨hc, hdname.symm⟩
    refine hsub.deliveries _ (sub_ownU.deliveries _ (ownU_deliveries hjc ?_))
    rw [← hid, ← hpl, ← hrun']
    exact hres r hr w (hrun' ▸ hw)
  · -- settlements
    intro x hx
    obtain ⟨w, pl, sh, hw, hpl, -⟩ := inv.sett.input x hx
    obtain ⟨d, hsub⟩ := placement_ctx hrun hw hpl
    have hname := (Workflow.placement?_eq_some hpl).2
    have := hsub.settled _ (sub_ownU.settled _ ownU_settled)
    rwa [hname] at this

/-! ### Counting the records -/

theorem sum_le_sum {α : Type} {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a List.mem_cons_self
    have := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    omega

theorem length_le_of_nodup_map {α β : Type} [BEq β] [LawfulBEq β] {l : List α} {k : α → β} {l' : List β}
    (hn : (l.map k).Nodup) (hsub : ∀ x ∈ l, k x ∈ l') : l.length ≤ l'.length := by
  have := List.Nodup.length_le_of_subset hn fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hsub x hx
  simpa using this

theorem callProgress_le (c : Call) : callProgress c ≤ 2 * c.yields + 4 := by
  unfold callProgress; split <;> omega

theorem taskProgress_le_three (x : TaskState) : taskProgress x ≤ 3 := by
  unfold taskProgress; split <;> omega

theorem statusProgress_le_two (st : Status) : statusProgress st ≤ 2 := by
  unfold statusProgress; split <;> omega

theorem tasks_sum_le (l : List TaskState) : (l.map taskProgress).sum ≤ 3 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := taskProgress_le_three a
    omega

theorem execs_sum_le (es : List Execution) :
    (es.map fun e => (e.tasks.map taskProgress).sum).sum ≤
      3 * (es.flatMap fun e => e.tasks.map fun t => (e.id, t.name)).length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.length_map]
    have := tasks_sum_le e.tasks
    omega

theorem nodup_pairs {a : String} : ∀ {l : List TaskState}, (l.map (·.name)).Nodup →
    (l.map fun t => (a, t.name)).Nodup
  | [], _ => List.nodup_nil
  | t :: l, hn => by
    rw [List.map_cons, List.nodup_cons] at hn ⊢
    refine ⟨fun hmem => hn.1 ?_, nodup_pairs hn.2⟩
    obtain ⟨t', ht', heq⟩ := List.mem_map.1 hmem
    simp only [Prod.mk.injEq] at heq
    exact List.mem_map.2 ⟨t', ht', heq.2⟩

/-- The keys of the tasks of all executions are distinct. -/
theorem taskKeys_nodup : ∀ {es : List Execution}, (es.map (·.id)).Nodup → (∀ e ∈ es, (e.tasks.map (·.name)).Nodup) →
    (es.flatMap fun e => e.tasks.map fun t => (e.id, t.name)).Nodup
  | [], _, _ => List.nodup_nil
  | e :: es, hn, ht => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_pairs (ht e List.mem_cons_self),
      taskKeys_nodup hn.2 fun e' he' => ht e' (List.mem_cons_of_mem e he'), ?_⟩
    intro x hx y hy hxy
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e', he', hy'⟩ := List.mem_flatMap.1 hy
    obtain ⟨t', -, rfl⟩ := List.mem_map.1 hy'
    simp only [Prod.mk.injEq] at hxy
    exact hn.1 (List.mem_map.2 ⟨e', he', hxy.1.symm⟩)

/-- `work` is at most the weight of any universe that covers the state, when keys are unique, task
    names are distinct and every call's elements are bounded by its script. -/
theorem work_le_weight {B : Behavior} {u : Universe} {s : State} (wk : s.WellKeyed) (cov : u.Covers s)
    (hnames : ∀ e ∈ s.executions, (e.tasks.map (·.name)).Nodup)
    (hy : ∀ c ∈ s.calls, c.yields ≤ (B.script c.id).yields.length) : work s ≤ u.weight B := by
  have h1 : (if s.started then 1 else 0) + (if s.cancelled then 1 else 0) + statusProgress s.status ≤ 4 := by
    have := statusProgress_le_two s.status
    split <;> split <;> omega
  have h2 : s.runs.length ≤ u.runs.length := length_le_of_nodup_map wk.runs cov.runs
  have h2' := List.length_filter_le (·.complete) s.runs
  have h3 : s.invocations.length ≤ u.invocations.length := length_le_of_nodup_map wk.invocations cov.invocations
  have h3' := List.length_filter_le (fun i => i.status != .active) s.invocations
  have h4 : (s.calls.map fun c => 1 + callProgress c).sum ≤
      (u.calls.map fun id => 5 + 2 * (B.script id).yields.length).sum := by
    calc (s.calls.map fun c => 1 + callProgress c).sum
        ≤ (s.calls.map fun c => 5 + 2 * (B.script c.id).yields.length).sum :=
          sum_le_sum fun c hc => by have := callProgress_le c; have := hy c hc; omega
      _ = ((s.calls.map (·.id)).map fun id => 5 + 2 * (B.script id).yields.length).sum := by
          rw [List.map_map]; rfl
      _ ≤ (u.calls.map fun id => 5 + 2 * (B.script id).yields.length).sum :=
          sum_map_le_of_nodup _ wk.calls fun x hx => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
            exact cov.calls c hc
  have h5 : s.executions.length ≤ u.executions.length := length_le_of_nodup_map wk.executions cov.executions
  have h5' := List.length_filter_le (·.complete) s.executions
  have h6 : (s.executions.map fun e => (e.tasks.map taskProgress).sum).sum ≤ 3 * u.tasks.length := by
    refine Nat.le_trans (execs_sum_le s.executions) (Nat.mul_le_mul_left 3 ?_)
    refine List.Nodup.length_le_of_subset (taskKeys_nodup wk.executions hnames) fun x hx => ?_
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact cov.tasks e he t ht
  have h7 : s.results.length ≤ u.results.length := length_le_of_nodup_map wk.results cov.results
  have h8 : s.taskResults.length ≤ u.taskResults.length := length_le_of_nodup_map wk.taskResults cov.taskResults
  have h8' := List.length_filter_le (fun r => r.output != .pending) s.taskResults
  have h9 : s.deliveries.length ≤ u.deliveries.length := length_le_of_nodup_map wk.deliveries cov.deliveries
  have h10 : s.settled.length ≤ u.settled.length := length_le_of_nodup_map wk.settled cov.settled
  unfold work Universe.weight
  omega

end UniverseProof

/-- Every record of a conforming execution has its key in the universe. By induction over the
    execution: each new record's identity is built from records already present (Round 2
    `Delivery.step_*_back`, `Delivery.Own`, `Settle.Prov`); `placement_rank` bounds the fuel of
    `possibleResults`, `call_rank` bounds `p.depth`, and `Conforming.yields_le` bounds element indices. -/
theorem universe_covers (valid : p.validate = .ok ()) {tr : List Op} (h : Conforming p env tr s) :
    (universeOf p env.behavior).Covers s := by
  exact UniverseProof.covers_of_conforming valid h

/-- With keys unique (`WellKeyed`, task names by Round 2 `Reachable.taskNames`) and inside the universe,
    and each call's elements bounded by its script, `work` is at most `workBound`. -/
theorem work_le_bound (valid : p.validate = .ok ()) {tr : List Op} (h : Conforming p env tr s) :
    work s ≤ workBound p env.behavior := by
  exact UniverseProof.work_le_weight h.reachable.wellKeyed (universe_covers valid h)
    (Reachable.taskNames valid h.reachable) h.yields_le

/-- **Bounded executions.** No execution conforming to a behavior is longer than `workBound`, for any
    behavior, fitting or not, and any scheduler. -/
theorem bounded (valid : p.validate = .ok ()) {tr : List Op} (h : Conforming p env tr s) :
    tr.length ≤ workBound p env.behavior :=
  Nat.le_trans h.length_le_work (work_le_bound valid h)

end UniverseSection

end Suimon.Round3
