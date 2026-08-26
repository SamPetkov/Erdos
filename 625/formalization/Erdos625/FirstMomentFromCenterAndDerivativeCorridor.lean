import Erdos625.RootGapFromCenterAndDerivativeCorridor
import Erdos625.RootCorridorFromNormalizedGap
import Mathlib.Tactic

/-!
# E625-10 from the right-root center and signed derivative corridor

The preceding root-gap assembly still exposed five consequences as independent
hypotheses of its first-moment endpoint:

* `O(log log n)` localization of the rounded root midpoint;
* eventual nonnegativity of the signed root;
* a literal signed/unrestricted root gap of at least two;
* eventual nonnegativity of the lower derivative bound;
* eventual nonnegativity of the upper derivative bound.

None is independent. The first three follow from right-root center localization
and the normalized root-gap expansion. The last two follow from convergence of
the normalized derivative bounds to the positive coefficient `2/q`.

This module removes those five hypotheses. It does not construct the roots,
prove their equations, establish the center-localization estimate, prove the
finite derivative corridor, prove the normalized derivative limits, or address
the chromatic lower tail, partial diagonals, skeletons, second moments, or the
final Erdős statement.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A slope whose normalization by `(log n)^2` tends to the positive
coefficient `2/q` is eventually strictly positive. -/
theorem eventually_signedFourSlope_pos_of_normalized_tendsto
    (slope : ℕ → ℝ)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q))) :
    ∀ᶠ n : ℕ in atTop, 0 < slope n := by
  have hLimitPos : 0 < 2 / q := div_pos (by norm_num) q_pos
  have hNormalizedPos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourNormalizedSlope slope n :=
    hSlope.eventually (Ioi_mem_nhds hLimitPos)
  filter_upwards [hNormalizedPos, eventually_gt_atTop (1 : ℕ)] with
      n hnNormalized hn
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hdenomPos : 0 < (logOrder n) ^ 2 := pow_pos hlogPos 2
  unfold signedFourNormalizedSlope at hnNormalized
  rcases div_pos_iff.mp hnNormalized with h | h
  · exact h.1
  · exact (not_lt_of_ge hdenomPos.le h.2).elim

/-- Manuscript-facing E625-10 endpoint using only a positive root order,
root equations, right-root center localization, and the concrete derivative
corridor with its normalized limits. Midpoint localization, the finite root
corridor, and slope nonnegativity are derived internally. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_positiveGap_rootEquations_centerLocalization_and_derivativeCorridor
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hRightCenter : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hGap : ∀ᶠ n : ℕ in atTop, 0 < rPlus n - rCo n)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        slopeLower n ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper n)
    (hCoRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hPlusRoot : ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (rPlus n) = 0)
    (hSlopeLower : Tendsto (signedFourNormalizedSlope slopeLower)
      atTop (𝓝 (2 / q)))
    (hSlopeUpper : Tendsto (signedFourNormalizedSlope slopeUpper)
      atTop (𝓝 (2 / q))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) <
        signedFourRootMidpointFirstMoment rCo rPlus n := by
  have hRootGap :=
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_derivativeCorridor
      rCo rPlus slopeLower slopeUpper
      hRightCenter hGap hCoRoot hPlusRoot
      hFeasible hDerivLower hDerivUpper
      hSlopeLower hSlopeUpper
  have hMidpointCenter :=
    signedFourNormalizedRootMidpointCenterDisplacement_isBigO_logLogOrder_of_right_and_rootGap
      rCo rPlus hRightCenter hRootGap
  have hCo : ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n :=
    eventually_signedFour_leftRoot_nonneg
      rCo rPlus hRightCenter hRootGap
  have hGapTwo : ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n :=
    eventually_two_le_signedFourRootGap rCo rPlus hRootGap
  have hSlopeLowerNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeLower n :=
    (eventually_signedFourSlope_pos_of_normalized_tendsto
      slopeLower hSlopeLower).mono fun _ hn ↦ hn.le
  have hSlopeUpperNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeUpper n :=
    (eventually_signedFourSlope_pos_of_normalized_tendsto
      slopeUpper hSlopeUpper).mono fun _ hn ↦ hn.le
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootEquations_centerLocalization_and_derivativeCorridor
      rCo rPlus slopeLower slopeUpper
      hRightCenter hMidpointCenter hCo hGapTwo
      hSlopeLowerNonneg hSlopeUpperNonneg
      hFeasible hDerivLower hDerivUpper
      hCoRoot hPlusRoot hSlopeLower hSlopeUpper

#print axioms eventually_signedFourSlope_pos_of_normalized_tendsto
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_positiveGap_rootEquations_centerLocalization_and_derivativeCorridor

end

end Erdos625