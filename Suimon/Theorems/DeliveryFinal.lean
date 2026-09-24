import Suimon.Theorems.DeliverySett

/-! The invariant holds in every reachable state; consequences for a workflow that finished without a
    stop: everything completed and every call ended. -/

namespace Suimon.Delivery
open State

theorem Inv.empty (p : Definition) : Inv p {} where
  wk := State.WellKeyed.empty
  fresh _ := rfl
  own := ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩
  dyn := ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  sett := ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

theorem Reachable.inv {p : Definition} {s : State} (h : Reachable p s) : Inv p s := by
  induction h with
  | empty => exact Inv.empty p
  | step op _ hs ih => exact step_inv ih hs

section Final
variable {p : Definition} {s : State}

/-- The run of an invocation exists. --/
theorem run_of_invocation (inv : Inv p s) {i : Invocation} (hi : i ∈ s.invocations) :
    ∃ r ∈ s.runs, r.path = i.run := by
  obtain ⟨-, w, -, -, hw, -⟩ := inv.own.invocations i hi
  obtain ⟨r, hr, -⟩ := workflow?_iff.mp hw
  exact ⟨r, (run?_eq_some hr).1, (run?_eq_some hr).2⟩

/-- Once the root run completed, every run completed: a sub-run belongs to an invocation or a task of
    a run with a shorter path, which ended when that run completed. --/
theorem all_runs_complete (inv : Inv p s) {root : Run} (hroot : s.run? [] = some root) (hc : root.complete = true) :
    ∀ r ∈ s.runs, r.complete = true := by
  suffices h : ∀ n, ∀ r ∈ s.runs, r.path.length = n → r.complete = true from fun r hr => h _ r hr rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro r hr hlen
    rcases inv.own.runs r hr with ⟨-, -, hp⟩ | ⟨ht, i, hi, ho, hp, -⟩ | ⟨name, ht, e, he, ho, hp, -⟩
    · obtain rfl : r = root := Option.some.inj ((inv.wk.run?_of_mem hr).symm.trans (hp ▸ hroot))
      exact hc
    · obtain ⟨r', hr', hr'p⟩ := run_of_invocation inv hi
      have hlt : r'.path.length < n := by rw [← hlen, hp, hr'p]; simp
      have hc' := ih _ hlt r' hr' rfl
      have hend := (inv.sett.runs r' hr' hc').1 i hi hr'p.symm
      exact (invocationEnded_iff.mp hend).2.2.1 r hr ho ht
    · obtain ⟨i, hi, hiid, hir, -, -⟩ := inv.own.executions e he
      obtain ⟨r', hr', hr'p⟩ := run_of_invocation inv hi
      have hlt : r'.path.length < n := by rw [← hlen, hp, hr'p, hir]; simp
      have hc' := ih _ hlt r' hr' rfl
      have hend := (inv.sett.runs r' hr' hc').1 i hi hr'p.symm
      have hec := (invocationEnded_iff.mp hend).2.2.2 e he hiid.symm
      exact (inv.dyn.execDone e he hec).2.1 r hr ho (by rw [ht]; simp)

theorem invocation_ended (inv : Inv p s) (hall : ∀ r ∈ s.runs, r.complete = true) {i : Invocation}
    (hi : i ∈ s.invocations) : s.invocationEnded i = true := by
  obtain ⟨r, hr, hrp⟩ := run_of_invocation inv hi
  exact (inv.sett.runs r hr (hall r hr)).1 i hi hrp.symm

theorem all_done (inv : Inv p s) {root : Run} (hroot : s.run? [] = some root) (hc : root.complete = true) :
    (∀ r ∈ s.runs, r.complete = true) ∧ (∀ e ∈ s.executions, e.complete = true) ∧
      (∀ c ∈ s.calls, c.status.ended = true) := by
  have hruns := all_runs_complete inv hroot hc
  have hexecs : ∀ e ∈ s.executions, e.complete = true := by
    intro e he
    obtain ⟨i, hi, hiid, -, -, -⟩ := inv.own.executions e he
    exact (invocationEnded_iff.mp (invocation_ended inv hruns hi)).2.2.2 e he hiid.symm
  refine ⟨hruns, hexecs, fun c hc => ?_⟩
  rcases inv.own.calls c hc with ⟨ht, -, i, hi, hio, -⟩ | ⟨name, ht, -, e, he, heo, -⟩
  · exact (invocationEnded_iff.mp (invocation_ended inv hruns hi)).2.1 c hc hio.symm ht
  · exact (inv.dyn.execDone e he (hexecs e he)).1 c hc heo.symm (by rw [ht]; simp)

theorem root_of_done (done : (s.run? []).any (·.complete) = true) :
    ∃ root, s.run? [] = some root ∧ root.complete = true := by
  cases hr : s.run? [] with
  | none => rw [hr] at done; cases done
  | some root =>
    rw [hr] at done
    exact ⟨root, rfl, by simpa using done⟩

end Final

end Suimon.Delivery
