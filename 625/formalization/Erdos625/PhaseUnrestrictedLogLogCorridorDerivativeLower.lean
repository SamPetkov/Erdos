import Erdos625.PhaseSignedFourSizeLogLogCorridorTarget
import Erdos625.PhaseSignedFourSizeLogLogCorridorLog
import Erdos625.PhaseRootDerivativeUnitCorridor
import Erdos625.PhaseFactorialErrorQuadratic
import Mathlib.Tactic

/-!
# Positive unrestricted derivative on the logarithmic-logarithmic corridor

This module supplies a prerequisite for constructing the ordinary unrestricted
phase root in the same corridor as the signed finite-four root. It proves only
a derivative lower bound; it does not assert another
root, compare roots, or choose an integer selector.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- The unrestricted phase objective has a uniform positive quadratic
derivative throughout every fixed nonnegative logarithmic-logarithmic
root-search corridor. -/
theorem eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower
    (C : Real) (hC : 0 ≤ C) :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        q / 8 * (phaseNat n : Real) ^ 2 ≤
          deriv (unrestrictedPhaseObjective n) s := by
  have hAlow : (-1 : Real) < 2 / q - 1 := by
    have : (0 : Real) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hAB : (2 / q - 1 : Real) ≤ 2 + 2 / q := by
    have : (0 : Real) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hqLower : (2 / 3 : Real) < q := by
    exact (by norm_num : (2 / 3 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hqUpper : q < (4 / 5 : Real) := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hTwoDivQLower : (5 / 2 : Real) < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    nlinarith
  have hTwoDivQUpper : 2 / q < (3 : Real) := by
    rw [div_lt_iff₀ q_pos]
    nlinarith
  filter_upwards
    [eventually_forall_mem_Icc_abs_selectedTerm_le_quadratic hAlow hAB,
      eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
      eventually_abs_phaseRootLogLogCorridor_log_le_quadratic C hC,
      eventually_factorialLogErrorBound_phaseNat_le_quadratic] with
      n hsel htarget hlog hfac
  intro s hs
  have hFour : fourSizeTarget n (phaseNat n) s ∈
      Icc (9 / 4 : Real) (17 / 4 : Real) := htarget s hs
  have hTargetEq :
      profileDeficitTarget (phaseNat n) (n : Real) s =
        fourSizeTarget n (phaseNat n) s := by
    rfl
  have hTIcc : profileDeficitTarget (phaseNat n) (n : Real) s ∈
      Icc (2 / q - 1) (2 + 2 / q) := by
    rw [hTargetEq, mem_Icc] at ⊢
    rw [mem_Icc] at hFour
    constructor <;> linarith
  obtain ⟨hTopen, hselbound⟩ :=
    hsel (profileDeficitTarget (phaseNat n) (n : Real) s) hTIcc
  have hderiv := abs_unrestrictedPhaseObjective_deriv_sub_deficitMain_le
    (n := n) (k := s) hTopen
  rw [abs_le] at hderiv
  have hlogbound : |Real.log s| ≤ q / 8 * (phaseNat n : Real) ^ 2 :=
    hlog s hs
  have hselle := abs_le.mp hselbound
  have hloge := abs_le.mp hlogbound
  have hanonneg : (0 : Real) ≤ (phaseNat n : Real) := Nat.cast_nonneg _
  nlinarith [hderiv.1, hselle.1, hselle.2, hloge.1, hloge.2, hfac,
    hanonneg, mul_nonneg (le_of_lt q_pos) (sq_nonneg (phaseNat n : Real))]

end

#print axioms eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower

end Erdos625
