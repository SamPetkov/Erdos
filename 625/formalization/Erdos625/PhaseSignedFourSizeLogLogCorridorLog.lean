import Erdos625.PhaseSignedFourSizeLogLogCorridorDomain
import Erdos625.PhaseRootCenterLogQuadratic
import Mathlib.Tactic

/-!
# Logarithm control on the logarithmic-logarithmic root corridor

The enlarged radius is still an `o(1)` fraction of the reference
center because `logLogOrder = o(logOrder)` and `phaseNat` dominates
`logOrder`.  Thus every corridor point remains within a fixed multiplicative
factor of the center, allowing the existing center logarithm bound to be
transported uniformly.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

private theorem eventually_logLogCorridor_multiplier_le_phaseNat_div_sixty_four
    (C : Real) (hC : 0 ≤ C) :
    ∀ᶠ n : Nat in atTop,
      C * logLogOrder n ≤ (phaseNat n : Real) / 64 := by
  have hOneC : 0 < 1 + C := by linarith
  have hEps : (0 : Real) < 1 / (64 * (1 + C)) := by positivity
  have hLittle := logLogOrder_isLittleO_logOrder.bound hEps
  have hLogPos : ∀ᶠ n : Nat in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hLogLogNonneg : ∀ᶠ n : Nat in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ hn ↦ hn.le
  filter_upwards [hLittle, hLogPos, hLogLogNonneg,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hsmall hlog hloglog hphase
  rw [Real.norm_eq_abs, abs_of_nonneg hloglog,
    Real.norm_eq_abs, abs_of_pos hlog] at hsmall
  have hCLe : C ≤ 1 + C := by linarith
  have hmul : C * logLogOrder n ≤ (1 + C) * logLogOrder n :=
    mul_le_mul_of_nonneg_right hCLe hloglog
  have hscaled :
      (1 + C) * logLogOrder n ≤ logOrder n / 64 := by
    calc
      (1 + C) * logLogOrder n ≤
          (1 + C) * ((1 / (64 * (1 + C))) * logOrder n) :=
        mul_le_mul_of_nonneg_left hsmall hOneC.le
      _ = logOrder n / 64 := by field_simp
  exact hmul.trans (hscaled.trans (by linarith [hphase.1]))

/-- The explicit logarithmic derivative remainder is uniformly negligible on
every fixed nonnegative logarithmic-logarithmic root-search corridor. -/
theorem eventually_abs_phaseRootLogLogCorridor_log_le_quadratic
    (C : Real) (hC : 0 ≤ C) :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        |Real.log s| ≤ q / 8 * (phaseNat n : Real) ^ 2 := by
  filter_upwards
    [eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_abs_log_phaseRootCenter_le_quadratic,
      eventually_five_lt_phaseNat,
      eventually_logLogCorridor_multiplier_le_phaseNat_div_sixty_four C hC]
      with n hcenter hlogCenter hphase hscale
  intro s hs
  obtain ⟨hn, hs0Pos, _⟩ := hcenter
  set a : Real := (phaseNat n : Real) with ha
  set c : Real := phaseRootCenter n with hc
  set gap : Real := phaseRootGapRadius n with hgap
  set wide : Real := C * logLogOrder n * gap with hwide
  have haSix : (6 : Real) ≤ a := by
    rw [ha]
    exact_mod_cast hphase
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn.1)
  have hcPos : 0 < c := by
    rw [hc]
    unfold phaseRootCenter
    exact div_pos hnPos hs0Pos
  have hgapEq : gap = c / a ^ 2 := by
    rw [hgap, hc, ha]
    rfl
  have hscale' : C * logLogOrder n ≤ a / 64 := by
    simpa [ha] using hscale
  have hfrac : C * logLogOrder n / a ^ 2 ≤ (1 / 2 : Real) := by
    rw [div_le_iff₀ haSqPos]
    nlinarith [hscale']
  have hwideEq : wide = c * (C * logLogOrder n / a ^ 2) := by
    rw [hwide, hgapEq]
    ring
  have hwideLeHalf : wide ≤ c / 2 := by
    rw [hwideEq]
    nlinarith [mul_le_mul_of_nonneg_left hfrac hcPos.le]
  rw [mem_Icc] at hs
  have hsPos : 0 < s := by linarith [hs.1, hcPos]
  have hsUpper : s ≤ 2 * c := by linarith [hs.2, hwideLeHalf, hcPos]
  have hcUpper : c ≤ 2 * s := by linarith [hs.1, hwideLeHalf, hcPos]
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

#print axioms eventually_abs_phaseRootLogLogCorridor_log_le_quadratic

end Erdos625
