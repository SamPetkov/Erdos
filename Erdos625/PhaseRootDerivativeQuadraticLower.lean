import Erdos625.PhaseRootCenterOpenCorridor
import Erdos625.PhaseRootCenterDerivativeLowerCorrected
import Erdos625.PhaseRootDerivativeSelectedQuadratic
import Erdos625.PhaseRootCenterLogQuadratic
import Erdos625.PhaseFactorialErrorQuadratic
import Erdos625.QuadraticSlopeAssemblyArithmetic
import Mathlib.Tactic

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/--
At the reference center, the unrestricted phase objective eventually has a
strictly positive derivative of explicit quadratic size.
-/
theorem eventually_unrestrictedPhaseObjective_deriv_center_ge_quadratic :
    ∀ᶠ n : ℕ in atTop,
      q / 4 * (phaseNat n : ℝ) ^ 2 ≤
        deriv (unrestrictedPhaseObjective n) (phaseRootCenter n) := by
  filter_upwards [eventually_phaseRootCenter_deficitTarget_mem_open,
    eventually_abs_phaseRootDerivativeSelectedTerm_le_quadratic,
    eventually_abs_log_phaseRootCenter_le_quadratic,
    eventually_factorialLogErrorBound_phaseNat_le_quadratic] with n hT hsel hcen hfac
  have hlb := unrestrictedPhaseObjective_deriv_center_lower_corrected hT
  have heq : profileDeficitTarget (phaseNat n) (n : ℝ) (phaseRootCenter n)
      = phaseRootDeficitTarget n := rfl
  rw [heq] at hlb
  have hkey := quadraticMain_sub_three_errors_ge_quarter
    (a := (phaseNat n : ℝ))
    (selected := Real.log
        (profileDeficitPartition (phaseNat n)
          (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))) -
      profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
        (phaseNat n : ℝ))
    (centerLog := Real.log (phaseRootCenter n))
    (factorialError := factorialLogErrorBound (phaseNat n))
    (Nat.cast_nonneg _) hsel hcen
    (factorialLogErrorBound_nonneg _) hfac
  linarith [hkey, hlb]

end

end Erdos625
