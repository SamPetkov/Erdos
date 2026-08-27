import Erdos625.PhaseSignedFourSizeTiltLinearQuadratic
import Erdos625.PhaseRootCenterLogQuadratic
import Mathlib.Tactic

/-!
# Uniform logarithm control on the signed four-size gap corridor

This module bounds the explicit `Real.log parts` remainder left by the exact
signed four-size derivative lower envelope.  The corridor radius is a
`phaseNat⁻²` fraction of the reference center, so every corridor point is
within a fixed multiplicative factor of that center.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- The logarithmic remainder is uniformly negligible on the native
phase-root gap corridor. -/
theorem eventually_abs_phaseRootGapCorridor_log_le_quadratic :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n - phaseRootGapRadius n)
          (phaseRootCenter n + phaseRootGapRadius n),
        |Real.log s| ≤ q / 8 * (phaseNat n : Real) ^ 2 := by
  filter_upwards
    [eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_abs_log_phaseRootCenter_le_quadratic,
      eventually_five_lt_phaseNat] with n hcenter hlogCenter hphase
  intro s hs
  obtain ⟨hn, hs0Pos, _⟩ := hcenter
  set a : Real := (phaseNat n : Real) with ha
  set c : Real := phaseRootCenter n with hc
  set gap : Real := phaseRootGapRadius n with hgap
  have haSix : (6 : Real) ≤ a := by
    rw [ha]
    exact_mod_cast hphase
  have haSq : (2 : Real) ≤ a ^ 2 := by nlinarith
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn.1)
  have hcPos : 0 < c := by
    rw [hc]
    unfold phaseRootCenter
    exact div_pos hnPos hs0Pos
  have hgapEq : gap = c / a ^ 2 := by
    rw [hgap, hc, ha]
    rfl
  have hgapNonneg : 0 ≤ gap := by
    rw [hgapEq]
    positivity
  have hgapLeHalf : gap ≤ c / 2 := by
    rw [hgapEq,
      div_le_div_iff₀ (by positivity : 0 < a ^ 2)
        (by norm_num : (0 : Real) < 2)]
    nlinarith [hcPos]
  rw [mem_Icc] at hs
  have hsPos : 0 < s := by linarith [hs.1, hcPos]
  have hsUpper : s ≤ 2 * c := by linarith [hs.2, hgapLeHalf, hcPos]
  have hcUpper : c ≤ 2 * s := by linarith [hs.1, hgapLeHalf, hcPos]
  have hlogUpper : Real.log s ≤ Real.log (2 * c) :=
    Real.log_le_log hsPos hsUpper
  have hlogLower : Real.log c ≤ Real.log (2 * s) :=
    Real.log_le_log hcPos hcUpper
  have hlogTwoCenter : Real.log (2 * c) = q + Real.log c := by
    rw [Real.log_mul (by norm_num) hcPos.ne']
    rfl
  have hlogTwoS : Real.log (2 * s) = q + Real.log s := by
    rw [Real.log_mul (by norm_num) hsPos.ne']
    rfl
  rw [hlogTwoCenter] at hlogUpper
  rw [hlogTwoS] at hlogLower
  have haSqSixteen : (16 : Real) ≤ a ^ 2 := by nlinarith
  have hqSq : 16 * q ≤ a ^ 2 * q :=
    mul_le_mul_of_nonneg_right haSqSixteen q_pos.le
  have hbudget :
      q + q / 16 * a ^ 2 ≤ q / 8 * a ^ 2 := by
    nlinarith
  rw [hc, ha] at hlogCenter
  rw [abs_le] at hlogCenter ⊢
  constructor
  · linarith [hlogLower, hlogCenter.1, hbudget]
  · linarith [hlogUpper, hlogCenter.2, hbudget]

end

#print axioms eventually_abs_phaseRootGapCorridor_log_le_quadratic

end Erdos625
