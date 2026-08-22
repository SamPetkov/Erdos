import Erdos625.SignedFourMidpointObjectiveAsymptotic
import Mathlib.Tactic

/-!
# Consequences of the normalized signed four-size part-count limit

The midpoint objective asymptotic consumes a natural part-count sequence
`K_n` through the single manuscript-scale statement

`K_n / (n / log n) -> q / 2`.

This module proves that the auxiliary hypotheses used by the finite and
asymptotic transport layers are consequences of that limit:

* the natural scale `n / log n` is eventually positive;
* `K_n` is eventually positive;
* `n / log n = O(K_n)`;
* `(log n)^2 <= K_n` eventually.

It then packages objective and exact-first-moment wrappers which no longer
ask separately for positivity or a scale big-O hypothesis.

No root existence, root-gap estimate, derivative estimate, admissibility
certificate, chromatic lower tail, partial diagonal, second moment, or final
Erdős theorem is proved here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The natural manuscript part-count scale is eventually strictly positive. -/
theorem eventually_signedFourNaturalPartScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < signedFourNaturalPartScale n := by
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnNat : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hlog : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
  exact div_pos hnReal hlog

/-- Convergence of the normalized part count to `q/2` makes the normalized
count eventually positive. -/
theorem eventually_signedFourNormalizedPartCount_pos_of_tendsto
    (K : ℕ → ℕ)
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop, 0 < signedFourNormalizedPartCount K n := by
  have hLimitPos : (0 : ℝ) < q / 2 :=
    div_pos q_pos (by norm_num)
  simpa only [mem_Ioi] using hParts.eventually (Ioi_mem_nhds hLimitPos)

/-- The natural part count itself is eventually positive. -/
theorem eventually_signedFourPartCount_pos_of_normalized_tendsto
    (K : ℕ → ℕ)
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop, 0 < K n := by
  have hNormalizedPos :=
    eventually_signedFourNormalizedPartCount_pos_of_tendsto K hParts
  filter_upwards [hNormalizedPos, eventually_signedFourNaturalPartScale_pos] with
    n hNormalized hScale
  have hProduct :
      0 < signedFourNormalizedPartCount K n *
        signedFourNaturalPartScale n :=
    mul_pos hNormalized hScale
  have hIdentity :
      signedFourNormalizedPartCount K n *
          signedFourNaturalPartScale n =
        (K n : ℝ) := by
    unfold signedFourNormalizedPartCount
    exact div_mul_cancel₀ _ hScale.ne'
  rw [hIdentity] at hProduct
  exact_mod_cast hProduct

/-- The normalized part-count limit gives the scale domination required by
the normalized finite first-moment error theorem. -/
theorem signedFourNaturalPartScale_isBigO_parts_of_normalized_tendsto
    (K : ℕ → ℕ)
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦ (K n : ℝ)) := by
  have hQuarterLtHalf : q / 4 < q / 2 := by
    have hq := q_pos
    linarith
  have hNormalizedLower :
      ∀ᶠ n : ℕ in atTop, q / 4 < signedFourNormalizedPartCount K n := by
    simpa only [mem_Ioi] using
      hParts.eventually (Ioi_mem_nhds hQuarterLtHalf)
  apply IsBigO.of_bound (4 / q)
  filter_upwards [hNormalizedLower, eventually_signedFourNaturalPartScale_pos] with
    n hNormalized hScale
  have hIdentity :
      signedFourNormalizedPartCount K n *
          signedFourNaturalPartScale n =
        (K n : ℝ) := by
    unfold signedFourNormalizedPartCount
    exact div_mul_cancel₀ _ hScale.ne'
  have hScaled :
      q / 4 * signedFourNaturalPartScale n ≤ (K n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hNormalized.le hScale.le
    rw [hIdentity] at h
    exact h
  have hQuarterPos : 0 < q / 4 :=
    div_pos q_pos (by norm_num)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hScale, abs_of_nonneg (Nat.cast_nonneg (K n))]
  calc
    signedFourNaturalPartScale n ≤ (K n : ℝ) / (q / 4) := by
      apply (le_div_iff₀ hQuarterPos).2
      simpa only [mul_comm] using hScaled
    _ = (4 / q) * (K n : ℝ) := by
      field_simp [q_ne_zero]

/-- The same normalized limit is already strong enough for the weaker
square-logarithmic lower bound used by the finite error layer. -/
theorem eventually_logOrder_sq_le_parts_of_normalized_tendsto
    (K : ℕ → ℕ)
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop, (logOrder n) ^ 2 ≤ (K n : ℝ) := by
  have hQuarterPos : 0 < q / 4 :=
    div_pos q_pos (by norm_num)
  have hSmall : ∀ᶠ n : ℕ in atTop,
      (logOrder n) ^ 2 / signedFourNaturalPartScale n < q / 4 := by
    simpa only [mem_Iio] using
      tendsto_logOrder_sq_div_signedFourNaturalPartScale_zero.eventually
        (Iio_mem_nhds hQuarterPos)
  have hQuarterLtHalf : q / 4 < q / 2 := by
    have hq := q_pos
    linarith
  have hNormalizedLower :
      ∀ᶠ n : ℕ in atTop, q / 4 < signedFourNormalizedPartCount K n := by
    simpa only [mem_Ioi] using
      hParts.eventually (Ioi_mem_nhds hQuarterLtHalf)
  filter_upwards [hSmall, hNormalizedLower,
    eventually_signedFourNaturalPartScale_pos] with n hSmallN hLowerN hScale
  have hLowerN' :
      q / 4 < (K n : ℝ) / signedFourNaturalPartScale n := by
    simpa only [signedFourNormalizedPartCount] using hLowerN
  have hRatio :
      (logOrder n) ^ 2 / signedFourNaturalPartScale n <
        (K n : ℝ) / signedFourNaturalPartScale n :=
    hSmallN.trans hLowerN'
  exact ((div_lt_div_iff_of_pos_right hScale).mp hRatio).le

/-- Objective wrapper in which positivity of the midpoint count is derived
from its normalized manuscript-scale limit. -/
theorem
    tendsto_phaseSignedFourSizeObjective_rootMidpoint_div_parts_sub_margin_half_of_partCountAsymptotic
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hObjectiveBounds : ∀ᶠ n : ℕ in atTop,
      slopeLower n * ((rPlus n - rCo n) / 2) ≤
          phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ∧
      phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ≤
          slopeUpper n * ((rPlus n - rCo n) / 2 + 1))
    (hSlopeLower : Tendsto (signedFourNormalizedSlope slopeLower)
      atTop (𝓝 (2 / q)))
    (hSlopeUpper : Tendsto (signedFourNormalizedSlope slopeUpper)
      atTop (𝓝 (2 / q)))
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0))
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2))) :
    Tendsto
      (fun n : ℕ ↦
        phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) /
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
        signedFourPhaseMargin n / 2)
      atTop (𝓝 0) := by
  have hKPos :=
    eventually_signedFourPartCount_pos_of_normalized_tendsto
      (signedFourRootMidpointPartCount rCo rPlus) hParts
  exact
    tendsto_phaseSignedFourSizeObjective_rootMidpoint_div_parts_sub_margin_half
      rCo rPlus slopeLower slopeUpper hKPos hObjectiveBounds
      hSlopeLower hSlopeUpper hRootGap hParts

/-- Exact-first-moment wrapper in which both positivity and the scale big-O
hypothesis are derived from the normalized midpoint part-count asymptotic. -/
theorem
    tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half_of_partCountAsymptotic
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hObjectiveBounds : ∀ᶠ n : ℕ in atTop,
      slopeLower n * ((rPlus n - rCo n) / 2) ≤
          phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ∧
      phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ≤
          slopeUpper n * ((rPlus n - rCo n) / 2 + 1))
    (hSlopeLower : Tendsto (signedFourNormalizedSlope slopeLower)
      atTop (𝓝 (2 / q)))
    (hSlopeUpper : Tendsto (signedFourNormalizedSlope slopeUpper)
      atTop (𝓝 (2 / q)))
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0))
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2)))
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (signedFourRootMidpointPartCount rCo rPlus n)) :
    Tendsto
      (fun n : ℕ ↦
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) /
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0) := by
  let K := signedFourRootMidpointPartCount rCo rPlus
  have hKPos : ∀ᶠ n : ℕ in atTop, 0 < K n :=
    eventually_signedFourPartCount_pos_of_normalized_tendsto K hParts
  have hScaleToParts : signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦ (K n : ℝ)) :=
    signedFourNaturalPartScale_isBigO_parts_of_normalized_tendsto K hParts
  exact
    tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half
      rCo rPlus slopeLower slopeUpper hKPos hObjectiveBounds
      hSlopeLower hSlopeUpper hRootGap hParts hAdmissible hScaleToParts

#print axioms eventually_signedFourNaturalPartScale_pos
#print axioms eventually_signedFourNormalizedPartCount_pos_of_tendsto
#print axioms eventually_signedFourPartCount_pos_of_normalized_tendsto
#print axioms signedFourNaturalPartScale_isBigO_parts_of_normalized_tendsto
#print axioms eventually_logOrder_sq_le_parts_of_normalized_tendsto
#print axioms tendsto_phaseSignedFourSizeObjective_rootMidpoint_div_parts_sub_margin_half_of_partCountAsymptotic
#print axioms tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half_of_partCountAsymptotic

end

end Erdos625
