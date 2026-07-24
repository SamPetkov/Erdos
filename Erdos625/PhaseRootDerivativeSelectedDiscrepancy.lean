import Erdos625.PhaseRootFiniteCommon
import Mathlib.Tactic

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The selected partition/tilt contribution appearing in the derivative. -/
noncomputable def phaseRootDerivativeSelectedTerm (n : ℕ) : ℝ :=
  Real.log
      (profileDeficitPartition (phaseNat n)
        (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))) -
    profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
      (phaseNat n : ℝ)

/--
Exact discrepancy between the derivative-selected term and the objective's
deficit-selected term.
-/
theorem phaseRootDerivativeSelectedTerm_eq :
    ∀ n : ℕ,
      phaseRootDerivativeSelectedTerm n =
        phaseRootSelectedDeficitTerm n -
          profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
            ((n : ℝ) / phaseRootCenter n) := by
  intro n
  unfold phaseRootDerivativeSelectedTerm phaseRootSelectedDeficitTerm
    phaseRootDeficitTarget
  ring

end

end Erdos625
