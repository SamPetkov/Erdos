import Erdos625.SignedFourMidpointObjectiveCorridor
import Erdos625.SignedFourPartCountScaleAdapter
import Erdos625.MidpointRoundedSignedFourSizeObjectiveBridge
import Erdos625.RootSeparationRoundingNatAdapter
import Mathlib.Tactic

/-!
# The abstract-root finite E625-10 sandwich

This module joins the exact rounded-root objective corridor with the exact
factorial first-moment bridge.  It defines the natural midpoint part count
attached to arbitrary signed and unrestricted root sequences and proves:

* safe `Int.toNat` transport under the root corridor hypotheses;
* the finite signed-objective lower and upper envelope at that natural count;
* the exact logarithmic first-moment error bound at the same count;
* the normalized vanishing of that finite error at manuscript part-count
  scale.

The roots and their derivative data remain explicit inputs.  The module does
not manufacture the concrete E625-08 analytic estimates and does not assume a
first-moment conclusion.

No chromatic lower tail, partial diagonal, skeleton, second moment, or final
Erdős statement is used.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Natural part count obtained from the exact ceiling midpoint of two real
root sequences. -/
noncomputable def signedFourRootMidpointPartCount
    (rCo rPlus : ℕ → ℝ) (n : ℕ) : ℕ :=
  (rootCochromaticIndex (rCo n) (rPlus n)).toNat

/-- The exact real factorial first moment attached to the root-midpoint part
count and the tangent-corrected four-size profile. -/
noncomputable def signedFourRootMidpointFirstMoment
    (rCo rPlus : ℕ → ℝ) (n : ℕ) : ℝ :=
  partialSignedFirstMoment n
    (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
    (midpointMultiplicity n (phaseNat n)
      (signedFourRootMidpointPartCount rCo rPlus n))

/-- Nonnegative left root and a gap of at least two make the integer ceiling
midpoint nonnegative. -/
theorem rootCochromaticIndex_nonneg_of_left_nonneg_gap
    {rCo rPlus : ℝ} (hCo : 0 ≤ rCo) (hGap : 2 ≤ rPlus - rCo) :
    0 ≤ rootCochromaticIndex rCo rPlus := by
  have hPlus : 0 ≤ rPlus := by linarith
  exact rootCochromaticIndex_nonneg_of_nonneg_roots hCo hPlus

/-- Safe cast of the natural midpoint count back to the exact integer ceiling
midpoint. -/
theorem signedFourRootMidpointPartCount_cast_eq
    (rCo rPlus : ℕ → ℝ) (n : ℕ)
    (hCo : 0 ≤ rCo n) (hGap : 2 ≤ rPlus n - rCo n) :
    (signedFourRootMidpointPartCount rCo rPlus n : ℝ) =
      ((rootCochromaticIndex (rCo n) (rPlus n) : ℤ) : ℝ) := by
  unfold signedFourRootMidpointPartCount
  exact rootCochromaticIndex_toNat_cast
    (rootCochromaticIndex_nonneg_of_left_nonneg_gap hCo hGap)

/-- Signed-objective bounds at the natural root-midpoint part count. -/
theorem phaseSignedFourSizeObjective_at_rootMidpointPartCount_bounds
    (n : ℕ) (rCo rPlus : ℕ → ℝ)
    (slopeLower slopeUpper : ℝ)
    (hCo : 0 ≤ rCo n)
    (hGap : 2 ≤ rPlus n - rCo n)
    (hSlopeLower : 0 ≤ slopeLower)
    (hSlopeUpper : 0 ≤ slopeUpper)
    (hFeasible : ∀ s ∈ Icc (rCo n) (rPlus n),
      0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ s ∈ Ioo (rCo n) (rPlus n),
      slopeLower ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ s ∈ Ioo (rCo n) (rPlus n),
      signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper)
    (hRoot : phaseSignedFourSizeObjective n (rCo n) = 0) :
    slopeLower * ((rPlus n - rCo n) / 2) ≤
        phaseSignedFourSizeObjective n
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ∧
    phaseSignedFourSizeObjective n
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ≤
        slopeUpper * ((rPlus n - rCo n) / 2 + 1) := by
  have hBounds :=
    phaseSignedFourSizeObjective_at_rootCochromaticIndex_bounds
      n (rCo n) (rPlus n) slopeLower slopeUpper hGap
      hSlopeLower hSlopeUpper hFeasible hDerivLower hDerivUpper hRoot
  rw [signedFourRootMidpointPartCount_cast_eq rCo rPlus n hCo hGap]
  exact hBounds

/-- Exact finite first-moment/objective comparison at the root-midpoint part
count. -/
theorem abs_log_signedFourRootMidpointFirstMoment_sub_objective_le
    (rCo rPlus : ℕ → ℝ) (n : ℕ)
    (hAdmissible : MidpointRoundingAdmissible n (phaseNat n)
      (signedFourRootMidpointPartCount rCo rPlus n)) :
    |Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) -
        phaseSignedFourSizeObjective n
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ)| ≤
      4 * factorialLogErrorBound n + 50 / 7 := by
  unfold signedFourRootMidpointFirstMoment phaseSignedFourSizeObjective
  exact
    abs_log_midpointPartialSignedFirstMoment_sub_signedFourSizeObjective_le
      n (phaseNat n) (signedFourRootMidpointPartCount rCo rPlus n)
      hAdmissible

/-- The exact finite first-moment error at the root midpoint is negligible at
manuscript part-count scale. -/
theorem tendsto_signedFourRootMidpointFirstMomentLogError_div_parts_zero
    (rCo rPlus : ℕ → ℝ)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (signedFourRootMidpointPartCount rCo rPlus n))
    (hScaleToParts : signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦
        (signedFourRootMidpointPartCount rCo rPlus n : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        (Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) -
          phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) /
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ))
      atTop (𝓝 0) := by
  have h :=
    tendsto_midpointPartialSignedFirstMomentLogError_div_parts_zero_of_naturalScale
      phaseNat (signedFourRootMidpointPartCount rCo rPlus)
      hAdmissible hScaleToParts
  simpa [midpointPartialSignedFirstMomentLogError,
    signedFourRootMidpointFirstMoment, phaseSignedFourSizeObjective] using h

/-- Eventual finite objective envelope for root and derivative sequences. -/
theorem eventually_phaseSignedFourSizeObjective_rootMidpoint_bounds
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hCo : ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n)
    (hGap : ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n)
    (hSlopeLower : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeLower n)
    (hSlopeUpper : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeUpper n)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        slopeLower n ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper n)
    (hRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0) :
    ∀ᶠ n : ℕ in atTop,
      slopeLower n * ((rPlus n - rCo n) / 2) ≤
          phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ∧
      phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ≤
          slopeUpper n * ((rPlus n - rCo n) / 2 + 1) := by
  filter_upwards [hCo, hGap, hSlopeLower, hSlopeUpper, hFeasible,
    hDerivLower, hDerivUpper, hRoot] with
    n hnCo hnGap hnSlopeLower hnSlopeUpper hnFeasible
      hnDerivLower hnDerivUpper hnRoot
  exact phaseSignedFourSizeObjective_at_rootMidpointPartCount_bounds
    n rCo rPlus (slopeLower n) (slopeUpper n)
    hnCo hnGap hnSlopeLower hnSlopeUpper hnFeasible
    hnDerivLower hnDerivUpper hnRoot

/-- Complete eventual finite sandwich: objective corridor plus exact
factorial/rounding error at the same natural midpoint part count. -/
theorem eventually_signedFourRootMidpointFirstMoment_sandwich
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hCo : ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n)
    (hGap : ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n)
    (hSlopeLower : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeLower n)
    (hSlopeUpper : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeUpper n)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        slopeLower n ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper n)
    (hRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hAdmissible : ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (signedFourRootMidpointPartCount rCo rPlus n)) :
    ∀ᶠ n : ℕ in atTop,
      slopeLower n * ((rPlus n - rCo n) / 2) ≤
          phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ∧
      phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ≤
          slopeUpper n * ((rPlus n - rCo n) / 2 + 1) ∧
      |Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) -
          phaseSignedFourSizeObjective n
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)| ≤
        4 * factorialLogErrorBound n + 50 / 7 := by
  have hObjective :=
    eventually_phaseSignedFourSizeObjective_rootMidpoint_bounds
      rCo rPlus slopeLower slopeUpper hCo hGap hSlopeLower hSlopeUpper
      hFeasible hDerivLower hDerivUpper hRoot
  filter_upwards [hObjective, hAdmissible] with n hnObjective hnAdmissible
  exact ⟨hnObjective.1, hnObjective.2,
    abs_log_signedFourRootMidpointFirstMoment_sub_objective_le
      rCo rPlus n hnAdmissible⟩

#print axioms rootCochromaticIndex_nonneg_of_left_nonneg_gap
#print axioms signedFourRootMidpointPartCount_cast_eq
#print axioms phaseSignedFourSizeObjective_at_rootMidpointPartCount_bounds
#print axioms abs_log_signedFourRootMidpointFirstMoment_sub_objective_le
#print axioms tendsto_signedFourRootMidpointFirstMomentLogError_div_parts_zero
#print axioms eventually_phaseSignedFourSizeObjective_rootMidpoint_bounds
#print axioms eventually_signedFourRootMidpointFirstMoment_sandwich

end

end Erdos625
