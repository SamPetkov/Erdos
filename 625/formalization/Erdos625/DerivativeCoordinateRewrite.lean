import Erdos625.ColoringProfilePhaseRootCenter
import Erdos625.ColoringProfilePhaseDerivative
import Erdos625.ColoringProfileDeficitTilt
import Mathlib.Tactic

namespace Erdos625

open Set

noncomputable section

set_option autoImplicit false

/-- Once the size coordinate is in the admissible corridor, the derivative
of the unrestricted phase objective has the exact deficit-coordinate form. -/
theorem unrestrictedPhaseObjective_deriv_eq_deficitCoordinates_of_sizeTarget
    {n : ℕ} {k : ℝ} (hk : 0 < k)
    (hsize : (n : ℝ) / k ∈
      Ioo (1 : ℝ) ((((phaseNat n) + 1 : ℕ) : ℝ))) :
    deriv (unrestrictedPhaseObjective n) k =
      profileDeficitAffineA (phaseNat n) +
        profileDeficitAffineB (phaseNat n) * (phaseNat n : ℝ) -
        profileDeficitTilt (phaseNat n)
            (profileDeficitTarget (phaseNat n) (n : ℝ) k) *
          (phaseNat n : ℝ) +
        Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) k))) -
        Real.log k := by
  have hbReal : (1 : ℝ) < (((phaseNat n) + 1 : ℕ) : ℝ) :=
    lt_trans hsize.1 hsize.2
  have hb : 2 ≤ phaseNat n + 1 := by exact_mod_cast hbReal
  have htilt :
      profileDeficitAffineB (phaseNat n) -
          profileDeficitTilt (phaseNat n)
            (profileDeficitTarget (phaseNat n) (n : ℝ) k) =
        profileDualTilt (phaseNat n + 1) ((n : ℝ) / k) := by
    rw [profileDeficitAffineB_sub_profileDeficitTilt]
    congr 1
    simp only [profileDeficitTarget]
    ring
  show deriv (fun k ↦ profileDualOptimalValue (phaseNat n + 1) (n : ℝ) k) k = _
  rw [deriv_profileDualOptimalValue_parts hb hk hsize, ← htilt,
    log_profileDualPartition_eq_deficitCentered]
  ring

end

end Erdos625
