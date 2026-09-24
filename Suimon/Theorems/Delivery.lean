import Suimon.Theorems.Basic
import Suimon.Theorems.Static
import Suimon.Theorems.DeliveryDeliv

namespace Suimon

/-- In a workflow that finished without a stop, every accepted result reached every connection that
    carries it (§6, §15.2 受け渡し); with `WellKeyed.deliveries`, it reached each of them once.
    Each connection must target a placement of its workflow, as in a valid definition: a connection to
    an unknown placement is never waited for, so nothing obliges its delivery. --/
theorem Reachable.delivered {p : Definition} {s : State}
    (targets : ∀ w ∈ p.workflows, ∀ c ∈ w.connections, (w.placement? c.target).isSome)
    (h : Reachable p s) (done : (s.run? []).any (·.complete) = true) :
    ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → ∀ i c, w.connections[i]? = some c →
      c.source = r.placement → (c.arm = none ∨ c.arm = r.arm) → (s.delivery? r.run i r.id).isSome := by
  intro r hr w hw i c hc hsrc harm
  have inv := Delivery.Reachable.inv h
  obtain ⟨root, hroot, hrc⟩ := Delivery.root_of_done done
  obtain ⟨hruns, -, -⟩ := Delivery.all_done inv hroot hrc
  -- The run of the result completed, so the target of the connection settled.
  obtain ⟨run, hrun, hwf⟩ := Delivery.workflow?_iff.mp hw
  obtain ⟨hrunm, hrunp⟩ := State.run?_eq_some hrun
  have hsettled := (inv.sett.runs run hrunm (hruns run hrunm)).2 w hwf
  obtain ⟨dst, hdst⟩ := Option.isSome_iff_exists.mp
    (targets w (Definition.workflow?_eq_some hwf).1 c (List.mem_of_getElem? hc))
  obtain ⟨hdstm, hdstn⟩ := Workflow.placement?_eq_some hdst
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hsettled dst hdstm)
  obtain ⟨hxm, hxr, hxp⟩ := State.settled?_eq_some hx
  -- A settled placement received every result its input connections carry.
  have hdel := ((Delivery.Reachable.deliv h).delivered x hxm w (by rw [hxr, hrunp]; exact hw) i c hc
    (by rw [hxp, hdstn])).1 r (Delivery.mem_eligible.mpr ⟨hr, by rw [hxr, hrunp], hsrc.symm, harm.imp id Eq.symm⟩)
  rwa [hxr, hrunp] at hdel

/-- `Reachable.delivered` for a valid definition. --/
theorem Reachable.delivered_of_validate {p : Definition} {s : State} (valid : p.validate = .ok ()) (h : Reachable p s)
    (done : (s.run? []).any (·.complete) = true) :
    ∀ r ∈ s.results, ∀ w, s.workflow? p r.run = some w → ∀ i c, w.connections[i]? = some c →
      c.source = r.placement → (c.arm = none ∨ c.arm = r.arm) → (s.delivery? r.run i r.id).isSome := by
  refine Reachable.delivered (fun w hw c hc => ?_) h done
  obtain ⟨-, dst, -, hdst, -⟩ := typedConnections_of_validate valid w hw c hc
  rw [hdst]
  rfl

/-- In a workflow that finished without a stop, every run and every concurrency execution completed,
    and no call is still running (§13.3). --/
theorem Reachable.done_complete {p : Definition} {s : State} (h : Reachable p s) (done : (s.run? []).any (·.complete) = true) :
    (∀ r ∈ s.runs, r.complete = true) ∧ (∀ e ∈ s.executions, e.complete = true) ∧ (∀ c ∈ s.calls, c.status.ended = true) := by
  obtain ⟨root, hroot, hrc⟩ := Delivery.root_of_done done
  exact Delivery.all_done (Delivery.Reachable.inv h) hroot hrc

/-- In a completed execution, every result of a task in the output went through its output
    transform (§8.3). --/
theorem Reachable.execution_outputs {p : Definition} {s : State} (h : Reachable p s) :
    ∀ e ∈ s.executions, e.complete = true → ∀ c, s.concurrencyOf p e = .ok c →
      ∀ r ∈ s.taskResults, r.execution = e.id → (∃ spec ∈ c.tasks, spec.name = r.task ∧ spec.output.isSome) →
        r.output ≠ .pending :=
  fun e he hc => ((Delivery.Reachable.inv h).dyn.execDone e he hc).2.2

end Suimon
