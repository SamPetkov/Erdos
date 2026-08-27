import Erdos625.PhaseSignedFourSizeLogLogCorridorLog
import Erdos625.PhaseSignedFourSizeLogLogCorridorTiltLinear
import Erdos625.PhaseSignedFourSizeDerivativeRewrite
import Erdos625.PhaseFactorialErrorQuadratic
import Erdos625.FourDeficitGaussianBound
import Mathlib.Tactic

/-!
# Upper bound for the signed derivative on the logarithmic-logarithmic corridor

The finite four-size entropy is first bounded above by comparison with the
uniform distribution on the four deficit coordinates.  The exact affine-core
rewrite then combines that bound with the already established factorial,
logarithmic, and tilt-linear corridor estimates.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- The exact finite four-size entropy is no larger than the entropy of the
uniform distribution.  The exact finite residual scores only decrease the
optimized value. -/
theorem fourSizeFiniteEntropy_le_two_q
    (alpha : Nat) {target : Real}
    (hAlpha : 5 < alpha) (htarget : target ∈ Set.Ioo (2 : Real) 5) :
    fourSizeFiniteEntropy alpha target ≤ 2 * q := by
  let p : Fin 4 → Real :=
    ProfileEntropyS4.optimizer (fourDeficitScore alpha) target
  let u : Fin 4 → Real := fun _ ↦ 1 / 4
  have hp_nonneg (i : Fin 4) : 0 ≤ p i := by
    exact ProfileEntropyS4.optimizer_nonneg (fourDeficitScore alpha) target i
  have hp_sum : ∑ i : Fin 4, p i = 1 := by
    exact ProfileEntropyS4.sum_optimizer (fourDeficitScore alpha) target
  have hu_pos (i : Fin 4) : 0 < u i := by
    norm_num [u]
  have hu_sum : ∑ i : Fin 4, u i = 1 := by
    norm_num [u, Fin.sum_univ_succ]
  have hrelative :=
    ProfileEntropyS4.sum_neg_mul_log_add_mul_log_le_zero
      p u hp_nonneg hu_pos hp_sum hu_sum
  have hlogFour : Real.log (4 : Real) = 2 * q := by
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
    simp [q]
  have hlogUniform (i : Fin 4) : Real.log (u i) = -(2 * q) := by
    dsimp [u]
    rw [Real.log_div (by norm_num : (1 : Real) ≠ 0)
      (by norm_num : (4 : Real) ≠ 0), Real.log_one, hlogFour]
    ring
  have hentropy :
      -(∑ i : Fin 4, p i * Real.log (p i)) ≤ 2 * q := by
    have hrelativeForm :
        -(∑ i : Fin 4, p i * Real.log (p i)) - 2 * q ≤ 0 := by
      calc
        -(∑ i : Fin 4, p i * Real.log (p i)) - 2 * q =
            ∑ i : Fin 4,
              (-p i * Real.log (p i) + p i * (-(2 * q))) := by
                rw [Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
                  ← Finset.sum_mul, hp_sum]
                ring
        _ = ∑ i : Fin 4,
              (-p i * Real.log (p i) + p i * Real.log (u i)) := by
                apply Finset.sum_congr rfl
                intro i _hi
                rw [hlogUniform i]
        _ ≤ 0 := hrelative
    linarith
  have hGaussianScore (i : Fin 4) : fourGaussianScore i ≤ 0 := by
    unfold fourGaussianScore
    have hsquare : 0 ≤ ProfileEntropyS4.support i ^ 2 := sq_nonneg _
    nlinarith [q_pos]
  have hFiniteScore (i : Fin 4) : fourDeficitScore alpha i ≤ 0 :=
    (fourDeficitScore_le_fourGaussianScore alpha hAlpha i).trans
      (hGaussianScore i)
  have hweightedScore :
      ∑ i : Fin 4, p i * fourDeficitScore alpha i ≤ 0 := by
    calc
      ∑ i : Fin 4, p i * fourDeficitScore alpha i ≤
          ∑ _i : Fin 4, (0 : Real) := by
            exact Finset.sum_le_sum fun i _hi ↦
              mul_nonpos_of_nonneg_of_nonpos (hp_nonneg i) (hFiniteScore i)
      _ = 0 := by simp
  rw [fourSizeFiniteEntropy_eq_gibbs alpha htarget]
  unfold fourSizeGibbsEntropy
  change
    -(∑ i : Fin 4, p i * Real.log (p i)) +
        ∑ i : Fin 4, p i * fourDeficitScore alpha i ≤ 2 * q
  linarith

/-- On every fixed nonnegative logarithmic-logarithmic root-search corridor,
the exact signed four-size derivative is eventually at most its explicit
`q * phaseNat^2` ceiling. -/
theorem eventually_signedFourSizeObjectiveDerivative_logLogCorridor_upper
    (C : Real) (hC : 0 ≤ C) :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Set.Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤
          q * (phaseNat n : Real) ^ 2 := by
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
  have hphaseSix : ∀ᶠ n : Nat in atTop, 5 < phaseNat n :=
    hphaseNat.eventually_gt_atTop 5
  have hphaseHundred : ∀ᶠ n : Nat in atTop, 100 ≤ phaseNat n :=
    hphaseNat.eventually_ge_atTop 100
  filter_upwards
    [eventually_factorialLogErrorBound_phaseNat_le_quadratic,
      eventually_abs_phaseRootLogLogCorridor_log_le_quadratic C hC,
      eventually_abs_phaseRootLogLogCorridor_fourSize_tilt_linear_le_quadratic
        C hC,
      eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
      hphaseSix, hphaseHundred] with
      n hfactorial hlog htilt htarget hsix hhundred
  intro s hs
  have halpha : 0 < phaseNat n := by omega
  have hcore :=
    abs_profileDeficitAffineCore_sub_quadratic_le (phaseNat n) halpha
  rw [abs_le] at hcore
  have hTargetClosed := htarget s hs
  have hTargetOpen :
      fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (2 : Real) 5 := by
    constructor <;> linarith [hTargetClosed.1, hTargetClosed.2]
  have hEntropy :=
    fourSizeFiniteEntropy_le_two_q (phaseNat n) hsix hTargetOpen
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
      (phaseNat n : Real) + 3 * q ≤
        9 * q / 32 * (phaseNat n : Real) ^ 2 := by
    nlinarith
  rw [signedFourSizeObjectiveDerivative_eq_affineCore_sub_tiltTerm]
  nlinarith [hcore.2, hfactorial, hEntropy, hLog.1, hTilt.1,
    hconstant, q_pos]

end

#print axioms fourSizeFiniteEntropy_le_two_q
#print axioms eventually_signedFourSizeObjectiveDerivative_logLogCorridor_upper

end Erdos625
