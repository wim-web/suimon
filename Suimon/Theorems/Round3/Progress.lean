import Suimon.Theorems.Round3.ProgressCalm

namespace Suimon.Round3
open State

/-! ## [9] Round3/Progress.lean — proven assembly

A valid definition never waits on the engine side: in a reachable, started, non-final state where no
call waits for the outside world, some engine operation is accepted and changes the state, and it can
be chosen to conform to any environment. -/

section Progress
variable {p : Definition} {s : State}

/-- Stopping: `Quiet` leaves no call running or fetching, and not waiting leaves none cancelling, so
    every call ended and the conclusion is accepted (§11.3). -/
theorem progress_stopping (h : Reachable p s) (stopping : s.status = .stopping) (idle : ¬ Waiting s) :
    ∃ t, step p s .conclude = .ok t ∧ t ≠ s := by
  have started : s.started = true := by
    rcases h.eq_empty_or_started with rfl | hs
    · simp at stopping
    · exact hs
  refine conclude_stopping_enabled started stopping fun c hc => ?_
  obtain ⟨hr, hf⟩ := h.quiet stopping c hc
  have hcan : c.status ≠ .cancelling := fun hcan => idle ⟨c, hc, Or.inr (Or.inl hcan)⟩
  cases hst : c.status <;> simp_all [CallStatus.ended]

theorem progress_running (valid : p.validate = .ok ()) (h : Reachable p s) (started : s.started = true)
    (running : s.status = .running) (idle : ¬ Waiting s) (env : Env) :
    ∃ op t, engine op = true ∧ Conforms env s op ∧ step p s op = .ok t ∧ t ≠ s := by
  rcases easy_or_calm valid h running idle env with hop | calm
  · exact hop
  · obtain ⟨r, hr⟩ := exists_deepestOpen h started running
    obtain ⟨op, t, he, hop, hs, hne⟩ := calm_progress valid h running calm hr
    refine ⟨op, t, he, ?_, hs, hne⟩
    rcases hop with rfl | rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

/-- **Progress (進行, §15.2).** In a valid definition, a reachable, started, non-final state in which no
    call waits for the outside world accepts an engine operation that changes the state, and the
    operation conforms to any given environment. -/
theorem progress (valid : p.validate = .ok ()) (h : Reachable p s) (started : s.started = true)
    (live : s.status.terminal = false) (idle : ¬ Waiting s) (env : Env) :
    ∃ op t, engine op = true ∧ Conforms env s op ∧ step p s op = .ok t ∧ t ≠ s := by
  cases hst : s.status with
  | running => exact progress_running valid h started hst idle env
  | stopping =>
    obtain ⟨t, ht, hne⟩ := progress_stopping h hst idle
    exact ⟨.conclude, t, rfl, trivial, ht, hne⟩
  | _ => simp [hst, Status.terminal] at live

end Progress

end Suimon.Round3
