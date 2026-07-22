import Erdos625.ColoringProfilePhaseRootCenter
import Erdos625.ColoringProfileDeficitTilt
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem unrestrictedPhaseObjective_div_eq_deficitCentered
    (n : ℕ) {parts : ℝ} (hparts : parts ≠ 0) :
    unrestrictedPhaseObjective n parts / parts =
      (n : ℝ) * Real.log (n : ℝ) / parts - (n : ℝ) / parts + 1 -
        Real.log parts +
        (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) *
            profileDeficitTarget (phaseNat n) (n : ℝ) parts +
          Real.log
            (profileDeficitPartition (phaseNat n)
              (profileDeficitTilt (phaseNat n)
                (profileDeficitTarget (phaseNat n) (n : ℝ) parts))) -
          profileDeficitTilt (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) parts) *
            profileDeficitTarget (phaseNat n) (n : ℝ) parts) := by
  rw [unrestrictedPhaseObjective,
    profileDualOptimalValue_eq_profileDualUpper (phaseNat n + 1) hparts]
  have htilt :
      profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts) =
        profileDeficitAffineB (phaseNat n) -
          profileDeficitTilt (phaseNat n)
            (profileDeficitTarget (phaseNat n) (n : ℝ) parts) := by
    rw [profileDeficitAffineB_sub_profileDeficitTilt]
    congr 1
    unfold profileDeficitTarget
    ring
  rw [htilt, profileDualUpper_eq_deficitCentered (phaseNat n) hparts]
  field_simp

end

end Erdos625
