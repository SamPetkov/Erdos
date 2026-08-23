import Erdos625.UnrestrictedRootTargetFromCenter
import Erdos625.RootSecantSlopeFromDerivativeCorridor
import Mathlib.Tactic

/-!
# Root-gap and first-moment assembly from center localization and derivative corridors

The preceding packages independently remove the right-root target data and the
signed secant slope from the normalized root-gap interface.  This module joins
them.

The normalized root gap is now derived from:

* `O(log log n)` localization of the unrestricted root about the exact phase
  center;
* the exact signed and unrestricted root equations;
* a positive signed/unrestricted root gap;
* a full admissible inter-root corridor;
* matching lower and upper derivative asymptotics.

A second theorem inserts the derived root-gap expansion into the existing
E625-10 first-moment package.  Thus the first-moment endpoint no longer accepts
a root-gap asymptotic as an independent hypothesis.

No root selector, root equation, center-localization estimate, derivative
corridor, chromatic lower tail, partial diagonal, skeleton, second moment, or
final Erdős statement is constructed here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Center localization of the unrestricted root and matching derivative
corridors imply the phase-varying normalized signed/unrestricted root gap. -/
theorem
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_derivativeCorridor
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hCenter : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hGap : ∀ᶠ n : ℕ in atTop, 0 < rPlus n - rCo n)
    (hCoRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hPlusRoot : ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (rPlus n) = 0)
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
  have hGapNe : ∀ᶠ n : ℕ in atTop,
      rPlus n - rCo n ≠ 0 :=
    hGap.mono fun _ hn ↦ hn.ne'
  exact
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_secant
      rCo rPlus hCenter hGapNe hCoRoot hPlusRoot hSecant

/-- Manuscript-facing E625-10 endpoint with the normalized root-gap estimate
discharged internally from unrestricted-root center localization and the
signed-objective derivative corridor.  The midpoint has its own explicit
`O(log log n)` center-displacement input because its rounding profile is a
separate finite object. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootEquations_centerLocalization_and_derivativeCorridor
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hRightCenter : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hMidpointCenter :
      signedFourNormalizedCenterDisplacement
          (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
        logLogOrder)
    (hCo : ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n)
    (hGap : ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n)
    (hSlopeLowerNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeLower n)
    (hSlopeUpperNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeUpper n)
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
  have hGapPos : ∀ᶠ n : ℕ in atTop,
      0 < rPlus n - rCo n :=
    hGap.mono fun _ hn ↦ by linarith
  have hRootGap :=
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_derivativeCorridor
      rCo rPlus slopeLower slopeUpper
      hRightCenter hGapPos hCoRoot hPlusRoot
      hFeasible hDerivLower hDerivUpper
      hSlopeLower hSlopeUpper
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_logLogCenterDisplacement
      rCo rPlus slopeLower slopeUpper
      hMidpointCenter hCo hGap
      hSlopeLowerNonneg hSlopeUpperNonneg
      hFeasible hDerivLower hDerivUpper hCoRoot
      hSlopeLower hSlopeUpper hRootGap

#print axioms tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_derivativeCorridor
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootEquations_centerLocalization_and_derivativeCorridor

end

end Erdos625