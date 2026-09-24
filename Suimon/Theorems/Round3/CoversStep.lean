import Suimon.Theorems.Round3.CoversOps
import Suimon.Theorems.Round3.CoversReports
import Suimon.Theorems.Round3.CoversClose

namespace Suimon.Round3
open State

/-! ## [25] Round3/CoversStep.lean — proven assembly -/

section CoversStep
variable {p : Definition} {env : Env} {s s' T : State}

theorem covers_step {op : Op} (h : StepCtx p env T s op s') : Covers p T s' := by
  cases op with
  | start input => exact covers_start h
  | invoke path name trigger => exact covers_invoke h
  | fetch id => exact covers_fetch h
  | returned id value => exact covers_returned h
  | judged id arm => exact covers_judged h
  | yielded id value => exact covers_yielded h
  | ended id => exact covers_ended h
  | failed id => exact covers_failed h
  | timedOut id element => exact covers_timedOut h
  | lost id => exact covers_lost h
  | terminated id => exact covers_terminated h
  | deliver path index source value => exact covers_deliver h
  | transformFailed path index source => exact covers_transformFailed h
  | taskInput eid name value => exact covers_taskInput h
  | taskInputFailed eid name => exact covers_taskInputFailed h
  | beginTask eid name => exact covers_beginTask h
  | taskOutput eid name index value => exact covers_taskOutput h
  | taskOutputFailed eid name index => exact covers_taskOutputFailed h
  | settle path name => exact covers_settle h
  | closeExecution eid => exact covers_closeExecution h
  | closeRun path => exact covers_closeRun h
  | cancel => exact covers_cancel h
  | conclude => exact covers_conclude h

/-- Every unstopped state of a conforming execution is contained in the final state of a complete
    execution of the same environment. -/
theorem covers_of_execution {tr tr₂ : List Op} (valid : p.validate = .ok ()) (h₂ : Conforming p env tr₂ T)
    (done : Done T) (h : Conforming p env tr s) (us : Unstopped s) : Covers p T s := by
  revert us
  induction h with
  | nil => intro _; exact covers_empty p T
  | @snoc tr s₀ s₁ op h₀ hc hs hne ih =>
    intro us
    have us₀ : Unstopped s₀ := unstopped_of_step h₀.reachable hs us
    exact covers_step ⟨valid, ⟨tr, h₀⟩, hc, hs, hne, us, ⟨tr₂, h₂⟩, done, ih us₀⟩

end CoversStep

end Suimon.Round3
