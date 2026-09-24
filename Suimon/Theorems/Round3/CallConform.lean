import Suimon.Theorems.Round3.RunConform
import Suimon.Theorems.Round3.CallConformStep

namespace Suimon.Round3
open State

/-! ## [14] Round3/CallConform.lean — task E2

Every state of a conforming execution before it stops keeps `CallConformAux.CallInv`: each step from
the empty state is taken from a running state (a `Done` state takes no step), and a step that stops
would not lead to an unstopped state. The helpers are in `CallConformBase`, `CallConformReports` and
`CallConformStep`. -/

section CallConformSection
variable {p : Definition} {env : Env} {s : State}

/-- In a conforming execution that has not stopped, every call stands where its script puts it and its
    owner carries its end. -/
theorem callConform (valid : p.validate = .ok ()) {tr : List Op} (h : Conforming p env tr s) (us : Unstopped s) :
    ∀ c ∈ s.calls, CallConform env s c ∧ OwnerConform s c := by
  -- Validity is not needed: the Round 2 invariants used hold in every reachable state.
  have _ := valid
  exact (CallConformAux.conforming_callInv h us).calls

/-- The single-run invariants hold along a conforming execution until it stops. Proven. -/
theorem runConform (valid : p.validate = .ok ()) {tr : List Op} (h : Conforming p env tr s) (us : Unstopped s) :
    RunConform p env s :=
  ⟨callConform valid h us, deliveryConform h, taskConform valid h us, policyConform h.reachable us⟩

end CallConformSection

end Suimon.Round3
