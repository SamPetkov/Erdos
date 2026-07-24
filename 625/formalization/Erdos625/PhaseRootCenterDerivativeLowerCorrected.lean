Exit code: 0
Wall time: 0.3 seconds
Output:
Exit code: 0
Wall time: 0.2 seconds
Output:
import Erdos625.DerivativeAffineCoreError
import Erdos625.PhaseRootFiniteCommon
import Mathlib.Tactic

namespace Erdos625

open Set

noncomputable section

set_option autoImplicit false

/--
Correct finite lower bound at the reference center, using the derivative's
actual affine coefficient `phaseNat n` in the selected tilt term.
-/
theorem unrestrictedPhaseObjective_deriv_center_lower_corrected
    {n : ℕ}
    (hT : profileDeficitTarget (phaseNat n) (n : ℝ)
        (phaseRootCenter n) ∈
      Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1)) :
    q / 2 * (phaseNat n : ℝ) ^ 2 + (phaseNat n : ℝ) -
          profileDeficitTilt (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ)
                (phaseRootCenter n)) *
            (phaseNat n : ℝ) +
          Real.log
            (profileDeficitPartition (phaseNat n)
              (profileDeficitTilt (phaseNat n)
                (profileDeficitTarget (phaseNat n) (n : ℝ)
                  (phaseRootCenter n)))) -
          Real.log (phaseRootCenter n) -
          factorialLogErrorBound (phaseNat n) ≤
      deriv (unrestrictedPhaseObjective n) (phaseRootCenter n) := by
  have h := abs_unrestrictedPhaseObjective_deriv_sub_deficitMain_le hT
  rw [abs_le] at h
  linarith [h.1]

end

end Erdos625


