import Suimon.Theorems.Round3.Enabled
import Suimon.Theorems.Round3.FreshIndex

namespace Suimon.Round3
open State

/-! ## [5] Round3/Fresh.lean — task B3 -/

section FreshSection
variable {p : Definition} {s : State}

/-- (N5) Every identity a step creates is free until that step, so no `DUPLICATE_*` guard blocks an
    operation the engine or a call needs. -/
structure Fresh (s : State) : Prop where
  /-- The invocation of an unused trigger, its call, its execution and its run are all free. -/
  invocation : ∀ path name trigger, (∀ i ∈ s.invocationsOf path name, i.trigger ≠ trigger) →
    s.invocation? (Key.invocation path name trigger) = none ∧ s.call? (Key.invocation path name trigger) = none ∧
    s.execution? (Key.invocation path name trigger) = none ∧
    s.run? (Key.child (Key.invocation path name trigger)) = none
  /-- A task that has not begun owns neither its call nor its run. -/
  taskBody : ∀ e ∈ s.executions, ∀ t ∈ e.tasks, (t.status = .pending ∨ t.status = .ready) →
    s.call? (Key.task e.id t.name) = none ∧ s.run? (Key.child (Key.task e.id t.name)) = none
  /-- The aggregate of an unsettled placement. -/
  aggregate : ∀ path name, s.settled? path name = none → s.result? (Key.aggregate path name) = none
  /-- The list of an open execution. -/
  list : ∀ e ∈ s.executions, e.complete = false → s.result? (Key.list e.id) = none
  /-- The result an open sub-workflow run returns. -/
  returned : ∀ r ∈ s.runs, ∀ o, r.owner = some o → r.task = none → r.complete = false →
    s.result? (Key.returned o) = none
  /-- The result of a task output that is not yet transformed. -/
  taskOutput : ∀ tr ∈ s.taskResults, tr.output = .pending →
    s.result? (Key.taskOutput tr.execution tr.task tr.index) = none
  /-- A workflow task has no task result while its run is open (`closeRun` adds index 0). -/
  taskRun : ∀ r ∈ s.runs, ∀ o name, r.owner = some o → r.task = some name → r.complete = false →
    ∀ tr ∈ s.taskResults, ¬ (tr.execution = o ∧ tr.task = name)
  /-- A running or fetching call has accepted exactly the indices below its count. -/
  callIndex : ∀ c ∈ s.calls, (c.status = .running ∨ c.status = .fetching) → ∀ k, c.yields ≤ k → IndexFree s c k

theorem Reachable.fresh (h : Reachable p s) : Fresh s := by
  have wk := h.wellKeyed
  have keys := Calls.reachable_keys h
  obtain ⟨own, -, prov, -⟩ := Settle.reachable h
  have downs := (Delivery.Reachable.inv h).own
  have linv := Limit.reachable_inv h
  have rk := FreshAux.reachable_resultKeys h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, FreshAux.reachable_callIndex h⟩
  · -- An invocation is stored under the identity of its run, placement and trigger; calls,
    -- executions and runs take their identities from invocations.
    intro path name trigger hfree
    have hinv : s.invocation? (Key.invocation path name trigger) = none := by
      rw [invocation?_eq_none_iff]
      intro hmem
      obtain ⟨i, hi, hid⟩ := List.mem_map.mp hmem
      obtain ⟨h1, h2, h3⟩ := FreshAux.invocation_inj ((own.invId i hi).symm.trans hid)
      exact hfree i (List.mem_filter.mpr ⟨hi, by simp [h1, h2]⟩) h3
    have hnotmem := invocation?_eq_none_iff.mp hinv
    obtain ⟨hcalls, hexec, -⟩ := keys.fresh hnotmem ⟨path, name, trigger, rfl⟩
    refine ⟨hinv, ?_, execution?_eq_none_iff.mpr hexec, ?_⟩
    · rw [call?_eq_none_iff]
      intro hmem
      obtain ⟨c, hc, hid⟩ := List.mem_map.mp hmem
      exact hcalls c hc hid
    · rw [run?_eq_none_iff]
      intro hmem
      obtain ⟨r, hr, hpath⟩ := List.mem_map.mp hmem
      rcases downs.runs r hr with ⟨-, -, hroot⟩ | ⟨-, i, hi, -, hrp, -⟩ | ⟨tname, -, e, -, -, hrp, -⟩
      · rw [hroot] at hpath
        exact Key.child_ne_nil _ hpath.symm
      · rw [hrp, own.invId i hi] at hpath
        have hlast : i.id = Key.invocation path name trigger := by
          rw [own.invId i hi]
          exact Key.child_inj (Key.within_invocation _ _ _) (Key.within_invocation _ _ _) hpath
        exact hnotmem (List.mem_map.mpr ⟨i, hi, hlast⟩)
      · rw [hrp] at hpath
        exact Key.child_invocation_ne_task hpath.symm
  · -- A call or run of a task names its execution and task, and needs the task to have begun.
    intro e he ts hts hst
    have hb : ¬ Limit.Begun ts.status := fun hb => by
      rcases hst with h' | h'
      · exact hb.1 h'
      · exact hb.2 h'
    refine ⟨?_, ?_⟩
    · rw [call?_eq_none_iff]
      intro hmem
      obtain ⟨c, hc, hid⟩ := List.mem_map.mp hmem
      rcases hct : c.task with _ | name
      · obtain ⟨path, pname, trig, hkey⟩ := keys.invocations c.id (keys.calls c hc hct)
        exact FreshAux.invocation_ne_task (hkey.symm.trans hid)
      · obtain ⟨h1, h2⟩ := FreshAux.task_inj ((linv.keys c hc name hct).symm.trans hid)
        exact linv.no_call he hts hb c hc (by rw [hct, h2]) h1
    · rw [run?_eq_none_iff]
      intro hmem
      obtain ⟨r, hr, hpath⟩ := List.mem_map.mp hmem
      rcases downs.runs r hr with ⟨-, -, hroot⟩ | ⟨-, i, hi, -, hrp, -⟩ | ⟨tname, htname, e', -, hro, hrp, -⟩
      · rw [hroot] at hpath
        exact Key.child_ne_nil _ hpath.symm
      · rw [hrp, own.invId i hi] at hpath
        exact Key.child_invocation_ne_task hpath
      · rw [hrp] at hpath
        obtain ⟨h1, h2⟩ := Key.child_task_inj hpath
        exact linv.no_run he hts hb r hr (by rw [htname, h2]) (by rw [hro, h1])
  · -- An aggregate is stored only together with its settlement.
    intro path name hnone
    rw [result?_eq_none_iff]
    intro hmem
    obtain ⟨r, hr, hid⟩ := List.mem_map.mp hmem
    have hsome := (rk r hr).aggregate hid
    rw [hnone] at hsome
    simp at hsome
  · -- A list is stored only by a complete execution.
    intro e he hcomp
    rw [result?_eq_none_iff]
    intro hmem
    obtain ⟨r, hr, hid⟩ := List.mem_map.mp hmem
    obtain ⟨x, hx, hxid, hxc⟩ := (rk r hr).list hid
    rw [wk.execution_eq_of_id hx he hxid, hcomp] at hxc
    cases hxc
  · -- A returned result is stored only by the complete run of its owner, which is this run.
    intro r hr o ho htask hcomp
    rw [result?_eq_none_iff]
    intro hmem
    obtain ⟨x, hx, hid⟩ := List.mem_map.mp hmem
    obtain ⟨run, hrun, hro, hrt, hrc⟩ := (rk x hx).returned hid
    rw [← own.run_unique wk hr hrun ho hro htask hrt, hcomp] at hrc
    cases hrc
  · -- A task output is stored only once its task result is transformed.
    intro tr htr hpend
    rw [result?_eq_none_iff]
    intro hmem
    obtain ⟨x, hx, hid⟩ := List.mem_map.mp hmem
    obtain ⟨tr', htr', hout, h1, h2, h3⟩ := (rk x hx).taskOutput hid
    have heq : tr' = tr := Limit.eq_of_key wk.taskResults htr' htr (by simp only [h1, h2, h3])
    exact hout (heq ▸ hpend)
  · -- A task result comes from a call of the task, which a workflow task lacks, or from its
    -- completed run, which is this run.
    intro r hr o name ho htask hcomp tr htr ⟨hte, htt⟩
    rcases prov.taskResultSrc tr htr with ⟨c, hc, hco, hct⟩ | ⟨r', hr', hro, hrt, hrc⟩
    · exact own.taskCall_not_run wk hc (by rw [hct, htt]) hr htask (by rw [ho, ← hte, hco])
    · rw [← own.taskRun_unique wk hr hr' htask (by rw [hrt, htt]) (by rw [ho, hro, hte]), hcomp] at hrc
      cases hrc

end FreshSection

end Suimon.Round3
