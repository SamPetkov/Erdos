import Erdos625.PhaseSignedFourSizeGapCorridorLog
import Erdos625.PhaseFactorialErrorQuadratic
import Mathlib.Tactic

/-!
# Positive signed four-size derivative on the native gap corridor

This module combines the exact derivative lower envelope with the separately
proved finite-entropy, logarithm, tilt-linear, and factorial-error bounds.
It proves only the uniform derivative lower bound; root existence and center
location remain downstream.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- The exact signed four-size objective has a uniform positive quadratic
derivative throughout the manuscript-scale phase-root gap corridor. -/
theorem eventually_signedFourSizeObjectiveDerivative_gapCorridor_lower :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n - phaseRootGapRadius n)
          (phaseRootCenter n + phaseRootGapRadius n),
        q / 8 * (phaseNat n : Real) ^ 2 ≤
          signedFourSizeObjectiveDerivative n (phaseNat n) s := by
  have hphaseReal :
      Tendsto (fun n : Nat ↦ (phaseNat n : Real)) atTop atTop :=
    tendsto_atTop_mono' atTop
      (show (logOrder : Nat → Real) ≤ᶠ[atTop]
        fun n : Nat ↦ (phaseNat n : Real) by
        filter_upwards
          [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
        exact hn.1)
      tendsto_logOrder_atTop
  have hphaseNat : Tendsto phaseNat atTop atTop := by
    rwa [tendsto_natCast_atTop_iff] at hphaseReal
  have hentropyN :=
    hphaseNat.eventually
      eventually_fourSizeFiniteEntropy_ge_neg_twenty_five_q_div_two_sub_one
  have hphaseHundred : ∀ᶠ n : Nat in atTop, 100 ≤ phaseNat n :=
    hphaseNat.eventually_ge_atTop 100
  filter_upwards
    [eventually_factorialLogErrorBound_phaseNat_le_quadratic,
      hentropyN,
      eventually_abs_phaseRootGapCorridor_log_le_quadratic,
      eventually_abs_phaseRootGapCorridor_fourSize_tilt_linear_le_quadratic,
      eventually_phaseRootGapCorridor_fourSize_target_mem_Icc,
      hphaseHundred] with n hfactorial hentropy hlog htilt htarget hhundred
  intro s hs
  have halpha : 0 < phaseNat n := by omega
  have hbase :=
    signedFourSizeObjectiveDerivative_quadratic_lower_envelope
      n (phaseNat n) s halpha
  have hEntropy :=
    hentropy (fourSizeTarget n (phaseNat n) s) (htarget s hs)
  have hLog := hlog s hs
  have hTilt := htilt s hs
  rw [abs_le] at hLog hTilt
  have haHundred : (100 : Real) ≤ (phaseNat n : Real) := by
    exact_mod_cast hhundred
  have haSq : (10000 : Real) ≤ (phaseNat n : Real) ^ 2 := by
    nlinarith
  have hqLower : (0.6931471803 : Real) < q := Real.log_two_gt_d9
  have hproduct :
      0 ≤ (q - 0.6931471803) *
        ((phaseNat n : Real) ^ 2 - 10000) :=
    mul_nonneg (by linarith) (by linarith)
  have hconstant :
      25 * q / 2 + 1 ≤
        5 * q / 32 * (phaseNat n : Real) ^ 2 := by
    nlinarith
  have halphaNonneg : (0 : Real) ≤ (phaseNat n : Real) :=
    Nat.cast_nonneg _
  nlinarith [hbase, hEntropy, hfactorial, hLog.1, hLog.2,
    hTilt.1, hTilt.2, hconstant, q_pos]

end

#print axioms eventually_signedFourSizeObjectiveDerivative_gapCorridor_lower

end Erdos625
