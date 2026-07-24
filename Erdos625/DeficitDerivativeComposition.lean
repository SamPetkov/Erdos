import Erdos625.DerivativeCoordinateRewrite
import Erdos625.DeficitTargetDomain
import Mathlib.Tactic

namespace Erdos625

open Set

noncomputable section

set_option autoImplicit false

/-- A deficit-target corridor alone supplies both the admissible size
coordinate and the positivity of the class-count variable, so the exact
deficit-coordinate derivative formula applies without a separate `0 < k`
hypothesis. -/
theorem unrestrictedPhaseObjective_deriv_eq_deficitCoordinates_of_deficitTarget
    {n : ℕ} {k : ℝ}
    (hT : profileDeficitTarget (phaseNat n) (n : ℝ) k ∈
      Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1)) :
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
  obtain ⟨hsize, _⟩ := phaseDeficitTarget_domain_coordinates hT
  have hk : 0 < k := by
    rw [Set.mem_Ioo] at hsize
    by_contra h
    have hkle : k ≤ 0 := not_lt.mp h
    have hle : (n : ℝ) / k ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hkle
    linarith [hsize.1]
  exact unrestrictedPhaseObjective_deriv_eq_deficitCoordinates_of_sizeTarget hk hsize

end

end Erdos625
