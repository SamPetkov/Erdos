import Erdos625.ColoringProfileDeficitUniformMomentConvergence

/-!
# Uniform convergence of the normalized finite deficit mean

This module passes the uniform first-numerator and partition limits through
the normalized quotient.  The finite denominator is bounded below by one
for every positive support; the single initial support value is replaced and
then restored by eventual equality.
-/

namespace Erdos625

open Filter Set
open scoped BigOperators Topology

noncomputable section

/-- The normalized finite deficit mean converges uniformly to the extended
Gaussian mean on every bounded tilt interval.  To keep the generic quotient
wrapper's denominator hypothesis valid even at `alpha = 0`, the proof changes
that single initial value to the `alpha = 1` value and then transfers back by
eventual equality. -/
theorem tendstoUniformlyOn_profileDeficitMean (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦ profileDeficitMean alpha lambda)
      (fun lambda ↦ extendedGaussianMean (Real.log 2) lambda)
      atTop (Icc (-M) M) := by
  let A : ℕ → ℝ → ℝ := fun alpha lambda ↦
    if alpha = 0 then profileDeficitFirstNumerator 1 lambda
    else profileDeficitFirstNumerator alpha lambda
  let B : ℕ → ℝ → ℝ := fun alpha lambda ↦
    if alpha = 0 then profileDeficitPartition 1 lambda
    else profileDeficitPartition alpha lambda
  let C : ℝ :=
    Real.exp M +
      ∑' d : ℕ,
        (d : ℝ) * extendedGaussianNaturalTerm (Real.log 2) M d
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (Real.exp_pos M).le
      (tsum_nonneg fun d ↦ mul_nonneg (Nat.cast_nonneg d)
        (extendedGaussianNaturalTerm_pos (Real.log 2) M d).le)
  have hA :
      TendstoUniformlyOn A
        (fun lambda ↦
          extendedGaussianFirstNumerator (Real.log 2) lambda)
        atTop (Icc (-M) M) := by
    apply (tendstoUniformlyOn_profileDeficitFirstNumerator M).congr
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    intro lambda _
    simp [A, (Nat.ne_of_gt halpha)]
  have hB :
      TendstoUniformlyOn B
        (fun lambda ↦ extendedGaussianPartition (Real.log 2) lambda)
        atTop (Icc (-M) M) := by
    apply (tendstoUniformlyOn_profileDeficitPartition M).congr
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    intro lambda _
    simp [B, (Nat.ne_of_gt halpha)]
  have hden : ∀ alpha lambda, lambda ∈ Icc (-M) M →
      1 ≤ B alpha lambda := by
    intro alpha lambda _
    by_cases halpha : alpha = 0
    · simp [B, halpha,
        one_le_profileDeficitPartition 1 (by omega) lambda]
    · simp [B, halpha,
        one_le_profileDeficitPartition alpha
          (Nat.pos_of_ne_zero halpha) lambda]
  have hdenlim : ∀ lambda, lambda ∈ Icc (-M) M →
      1 ≤ extendedGaussianPartition (Real.log 2) lambda := by
    intro lambda _
    exact one_le_extendedGaussianPartition
      (show 0 < Real.log 2 by positivity)
  have hnum : ∀ lambda, lambda ∈ Icc (-M) M →
      |extendedGaussianFirstNumerator (Real.log 2) lambda| ≤ C := by
    intro lambda hlambda
    exact abs_extendedGaussianFirstNumerator_le_upper_tilt hlambda
  have hquot :
      TendstoUniformlyOn
        (fun alpha lambda ↦ A alpha lambda / B alpha lambda)
        (fun lambda ↦
          extendedGaussianFirstNumerator (Real.log 2) lambda /
            extendedGaussianPartition (Real.log 2) lambda)
        atTop (Icc (-M) M) :=
    tendstoUniformlyOn_div_of_denominator_ge
      (z := 1) (M := C) zero_lt_one hC hA hB hden hdenlim hnum
  have hquotActual :
      TendstoUniformlyOn
        (fun alpha lambda ↦
          profileDeficitFirstNumerator alpha lambda /
            profileDeficitPartition alpha lambda)
        (fun lambda ↦
          extendedGaussianFirstNumerator (Real.log 2) lambda /
            extendedGaussianPartition (Real.log 2) lambda)
        atTop (Icc (-M) M) := by
    apply hquot.congr
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    intro lambda _
    simp [A, B, (Nat.ne_of_gt halpha)]
  refine (hquotActual.congr ?_).congr_right ?_
  · exact Filter.Eventually.of_forall fun alpha lambda _ ↦
      (profileDeficitMean_eq_firstNumerator_div alpha lambda).symm
  · exact fun lambda _ ↦ rfl

end

end Erdos625
