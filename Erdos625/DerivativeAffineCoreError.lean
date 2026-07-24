import Erdos625.DeficitDerivativeComposition
import Erdos625.ColoringProfilePhaseDerivativeAffineCore
import Mathlib.Tactic

namespace Erdos625

open Set

noncomputable section

set_option autoImplicit false

/--
After converting the unrestricted phase derivative to deficit coordinates,
the only error in replacing its affine factorial-log core by the quadratic
main term is the explicit `factorialLogErrorBound`.
-/
theorem abs_unrestrictedPhaseObjective_deriv_sub_deficitMain_le
    {n : ℕ} {k : ℝ}
    (hT : profileDeficitTarget (phaseNat n) (n : ℝ) k ∈
      Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1)) :
    |deriv (unrestrictedPhaseObjective n) k -
      (q / 2 * (phaseNat n : ℝ) ^ 2 + (phaseNat n : ℝ) -
        profileDeficitTilt (phaseNat n)
            (profileDeficitTarget (phaseNat n) (n : ℝ) k) *
          (phaseNat n : ℝ) +
        Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) k))) -
        Real.log k)| ≤ factorialLogErrorBound (phaseNat n) := by
  rw [unrestrictedPhaseObjective_deriv_eq_deficitCoordinates_of_deficitTarget hT]
  obtain ⟨_, h2⟩ := phaseDeficitTarget_domain_coordinates hT
  have hpn : 0 < phaseNat n := by omega
  have key := abs_profileDeficitAffineCore_sub_quadratic_le (phaseNat n) hpn
  convert key using 2
  ring

end

end Erdos625
