import Suimon.Theorems.Basic
import Suimon.Theorems.SettleStep

/-! Settlement ordering (§4.5, §9.1, §10.3, §13.3). The proofs rest on the invariants of
    `Suimon.Settle`: ownership of records (`Own`), what keeps owners active (`Active`), where results
    come from (`Prov`), and what a settled placement keeps (`SettledInv`), which hold in every
    reachable state (`Settle.reachable`). -/

namespace Suimon

/-- A settled placement had all its invocations ended, and they stay ended (§10.3). --/
theorem Reachable.settled_invocations_ended {p : Definition} {s : State} (h : Reachable p s) :
    ∀ x ∈ s.settled, ∀ i ∈ s.invocationsOf x.run x.placement, s.invocationEnded i = true :=
  (Settle.reachable h).2.2.2.ended

/-- A placement with a Stream input settles only after the stream ended: its source settled and every
    result the connection carries was delivered, which stays true (§10.3). --/
theorem Reachable.settled_stream {p : Definition} {s : State} (h : Reachable p s) :
    ∀ x ∈ s.settled, ∀ w i c, s.workflow? p x.run = some w → w.shape? p x.placement = some (.stream i c) →
      (s.settled? x.run c.source).isSome ∧ ∀ r ∈ s.eligible x.run c, (s.delivery? x.run i r.id).isSome := by
  intro x hx w i c hw hshape
  obtain ⟨w', pl, hw', -, hclosed⟩ := (Settle.reachable h).2.2.2.closed x hx
  rw [hw] at hw'
  cases hw'
  unfold Settle.Closed at hclosed
  rw [hshape] at hclosed
  exact ⟨hclosed.1, hclosed.2.1⟩

/-- A waitStream result lists exactly the values delivered on its input, which ended (§9.1). --/
theorem Reachable.waitStream_result {p : Definition} {s : State} (h : Reachable p s) :
    ∀ r ∈ s.results, ∀ w pl i c, s.workflow? p r.run = some w → w.placement? r.placement = some pl →
      (∃ e, pl.control = .waitStream e) → w.shape? p r.placement = some (.stream i c) →
        r.value = listValue ((s.deliveriesOn r.run i).filterMap fun d => match d.outcome with
          | .value v => some v
          | _ => none) :=
  (Settle.reachable h).2.2.2.waitValue

/-- A sub-workflow call returns its result only after its run completed (§4.5). --/
theorem Reachable.call_returns_after_run {p : Definition} {s : State} (h : Reachable p s) :
    ∀ i ∈ s.invocations, i.status = .succeeded → ∀ pl, (s.workflow? p i.run).bind (·.placement? i.placement) = some pl →
      (∃ wf out, pl.control = .call (.workflow wf out)) →
        ∃ r ∈ s.runs, r.owner = some i.id ∧ r.task = none ∧ r.complete = true :=
  (Settle.reachable h).2.2.1.callRun

/-- A completed run, including every sub-workflow call, has settled all its placements (§4.5, §13.3). --/
theorem Reachable.complete_run_settled {p : Definition} {s : State} (h : Reachable p s) :
    ∀ r ∈ s.runs, r.complete = true → ∀ w, p.workflow? r.workflow = some w →
      ∀ pl ∈ w.placements, (s.settled? r.path pl.name).isSome :=
  (Settle.reachable h).2.2.1.completeSettled

end Suimon
