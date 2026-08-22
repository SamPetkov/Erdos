import Erdos625.LimitingMarginTargetTransport
import Erdos625.SignedFourMidpointObjectiveCorridor
import Mathlib.Tactic

/-!
# Signed-root secant slope from derivative corridors

The normalized root-gap assembly consumes the signed-objective secant slope
between the signed and unrestricted roots.  That secant limit is not an
independent analytic theorem once lower and upper derivative corridors have
already been proved on the full root interval.

This module first integrates the exact finite derivative bounds and divides by
the positive root gap.  It then normalizes by `(log n)^2` and squeezes the
secant between the normalized lower and upper slope sequences.

No root existence, derivative estimate, target transport, root-gap asymptotic,
first moment, chromatic lower tail, partial diagonal, skeleton, second moment,
or final Erdős statement is supplied here.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Finite secant-slope envelope for the signed four-size objective. -/
theorem phaseSignedFourRootSecantSlope_bounds
    (n : ℕ) (rCo rPlus slopeLower slopeUpper : ℝ)
    (hGap : 0 < rPlus - rCo)
    (hFeasible : ∀ s ∈ Icc rCo rPlus,
      0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ s ∈ Ioo rCo rPlus,
      slopeLower ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ s ∈ Ioo rCo rPlus,
      signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper) :
    slopeLower ≤ phaseSignedFourRootSecantSlope n rCo rPlus ∧
      phaseSignedFourRootSecantSlope n rCo rPlus ≤ slopeUpper := by
  have hOrder : rCo ≤ rPlus := by linarith
  have hCont : ContinuousOn (phaseSignedFourSizeObjective n)
      (Icc rCo rPlus) := by
    intro s hs
    exact (continuousAt_phaseSignedFourSizeObjective n
      (hFeasible s hs).1 (hFeasible s hs).2).continuousWithinAt
  have hDiff : DifferentiableOn ℝ (phaseSignedFourSizeObjective n)
      (Ioo rCo rPlus) := by
    intro s hs
    have hsClosed : s ∈ Icc rCo rPlus := Ioo_subset_Icc_self hs
    exact (hasDerivAt_phaseSignedFourSizeObjective n
      (hFeasible s hsClosed).1
      (hFeasible s hsClosed).2).differentiableAt.differentiableWithinAt
  have hLower : ∀ s ∈ Ioo rCo rPlus,
      slopeLower ≤ deriv (phaseSignedFourSizeObjective n) s := by
    intro s hs
    have hsClosed : s ∈ Icc rCo rPlus := Ioo_subset_Icc_self hs
    rw [(hasDerivAt_phaseSignedFourSizeObjective n
      (hFeasible s hsClosed).1 (hFeasible s hsClosed).2).deriv]
    exact hDerivLower s hs
  have hUpper : ∀ s ∈ Ioo rCo rPlus,
      deriv (phaseSignedFourSizeObjective n) s ≤ slopeUpper := by
    intro s hs
    have hsClosed : s ∈ Icc rCo rPlus := Ioo_subset_Icc_self hs
    rw [(hasDerivAt_phaseSignedFourSizeObjective n
      (hFeasible s hsClosed).1 (hFeasible s hsClosed).2).deriv]
    exact hDerivUpper s hs
  have hLowerIncrement :
      slopeLower * (rPlus - rCo) ≤
        phaseSignedFourSizeObjective n rPlus -
          phaseSignedFourSizeObjective n rCo :=
    derivative_lower_bound_mul_sub_le_sub hOrder hCont hDiff hLower
  have hUpperIncrement :
      phaseSignedFourSizeObjective n rPlus -
          phaseSignedFourSizeObjective n rCo ≤
        slopeUpper * (rPlus - rCo) :=
    sub_le_derivative_upper_bound_mul_sub hOrder hCont hDiff hUpper
  unfold phaseSignedFourRootSecantSlope
  constructor
  · exact (le_div_iff₀ hGap).2 hLowerIncrement
  · exact (div_le_iff₀ hGap).2 hUpperIncrement

/-- Eventual normalized secant bounds obtained from the finite derivative
corridor. -/
theorem eventually_signedFourNormalizedRootSecantSlope_bounds
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hGap : ∀ᶠ n : ℕ in atTop, 0 < rPlus n - rCo n)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        slopeLower n ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper n) :
    ∀ᶠ n : ℕ in atTop,
      signedFourNormalizedSlope slopeLower n ≤
          signedFourNormalizedRootSecantSlope rCo rPlus n ∧
        signedFourNormalizedRootSecantSlope rCo rPlus n ≤
          signedFourNormalizedSlope slopeUpper n := by
  filter_upwards [hGap, hFeasible, hDerivLower, hDerivUpper,
    eventually_gt_atTop (1 : ℕ)] with
    n hnGap hnFeasible hnLower hnUpper hn
  have hBounds := phaseSignedFourRootSecantSlope_bounds
    n (rCo n) (rPlus n) (slopeLower n) (slopeUpper n)
    hnGap hnFeasible hnLower hnUpper
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hlogSqPos : 0 < (logOrder n) ^ 2 := pow_pos hlogPos 2
  unfold signedFourNormalizedSlope signedFourNormalizedRootSecantSlope
  constructor
  · exact (div_le_div_iff_of_pos_right hlogSqPos).2 hBounds.1
  · exact (div_le_div_iff_of_pos_right hlogSqPos).2 hBounds.2

/-- Matching normalized derivative asymptotics squeeze the normalized root
secant slope to the same coefficient `2/q`. -/
theorem tendsto_signedFourNormalizedRootSecantSlope_of_derivativeCorridor
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
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
    (hSlopeLower : Tendsto (signedFourNormalizedSlope slopeLower)
      atTop (𝓝 (2 / q)))
    (hSlopeUpper : Tendsto (signedFourNormalizedSlope slopeUpper)
      atTop (𝓝 (2 / q))) :
    Tendsto (signedFourNormalizedRootSecantSlope rCo rPlus)
      atTop (𝓝 (2 / q)) := by
  have hBounds :=
    eventually_signedFourNormalizedRootSecantSlope_bounds
      rCo rPlus slopeLower slopeUpper
      hGap hFeasible hDerivLower hDerivUpper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hSlopeLower hSlopeUpper
    (hBounds.mono fun _ hn ↦ hn.1)
    (hBounds.mono fun _ hn ↦ hn.2)

/-- Root-gap wrapper with the secant asymptotic discharged internally from the
finite derivative corridor and its lower/upper normalized limits. -/
theorem
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_target_and_derivativeCorridor
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5)
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hPhase : Tendsto phaseNat atTop atTop)
    (hTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (rPlus n) ∈ Icc A B)
    (hPhaseTarget : ∀ᶠ n : ℕ in atTop,
      signedFourPhaseTarget n ∈ Icc A B)
    (hTargetTransport : Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (rPlus n) -
          signedFourPhaseTarget n)
      atTop (𝓝 0))
    (hGap : ∀ᶠ n : ℕ in atTop, 0 < rPlus n - rCo n)
    (hCoRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hPlusRoot : ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (rPlus n) = 0)
    (hRightParts : Tendsto
      (signedFourNormalizedRightRootPartCount rPlus)
      atTop (𝓝 (q / 2)))
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        slopeLower n ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper n)
    (hSlopeLower : Tendsto (signedFourNormalizedSlope slopeLower)
      atTop (𝓝 (2 / q)))
    (hSlopeUpper : Tendsto (signedFourNormalizedSlope slopeUpper)
      atTop (𝓝 (2 / q))) :
    Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  have hSecant :=
    tendsto_signedFourNormalizedRootSecantSlope_of_derivativeCorridor
      rCo rPlus slopeLower slopeUpper
      hGap hFeasible hDerivLower hDerivUpper
      hSlopeLower hSlopeUpper
  have hGapNe : ∀ᶠ n : ℕ in atTop, rPlus n - rCo n ≠ 0 :=
    hGap.mono fun _ hn ↦ hn.ne'
  have hPlus : ∀ᶠ n : ℕ in atTop, rPlus n ≠ 0 := by
    filter_upwards [hFeasible, hGap] with n hnFeasible hnGap
    exact
      (hnFeasible (rPlus n)
        (right_mem_Icc.mpr hnGap.le)).1.ne'
  exact
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_target_and_secant
      hA hAB hB rCo rPlus hPhase hTarget hPhaseTarget
      hTargetTransport hGapNe hPlus hCoRoot hPlusRoot
      hRightParts hSecant

#print axioms phaseSignedFourRootSecantSlope_bounds
#print axioms eventually_signedFourNormalizedRootSecantSlope_bounds
#print axioms tendsto_signedFourNormalizedRootSecantSlope_of_derivativeCorridor
#print axioms tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_target_and_derivativeCorridor

end

end Erdos625