import Erdos625.SignedFourPartCountAsymptoticConsequences
import Mathlib.Tactic

/-!
# Explicit positive rate for the signed four-size first moment

The preceding modules prove that concrete root-corridor asymptotics imply

`log M_n / K_n - signedFourPhaseMargin n / 2 -> 0`,

where `M_n` is the exact tangent-rounded signed four-size first moment and
`K_n` is the ceiling midpoint of the signed and unrestricted roots.

The uniform entropy certificate gives

`log (200 / 153) < signedFourPhaseMargin n`

for every phase.  This module converts those two facts into a fixed positive
rate and then exponentiates it:

`exp (c * K_n) < M_n`

with `c = log (200 / 153) / 4` eventually.

The rate loses a factor two only to absorb the vanishing asymptotic error.  No
first-moment lower bound is assumed.  Root existence, derivative estimates,
root-gap asymptotics, part-count asymptotics, and admissibility remain explicit
inputs in the manuscript-facing wrapper.

No chromatic lower tail, partial diagonal, skeleton, second moment, or final
Erdős statement is used.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A fixed positive rate safely below one half of every phase margin. -/
noncomputable def signedFourCertifiedFirstMomentRate : ℝ :=
  Real.log ((200 : ℝ) / 153) / 4

/-- The certified first-moment rate is strictly positive. -/
theorem signedFourCertifiedFirstMomentRate_pos :
    0 < signedFourCertifiedFirstMomentRate := by
  unfold signedFourCertifiedFirstMomentRate
  exact div_pos log_200_div_153_pos (by norm_num)

/-- Package the finite root corridor with the asymptotic transport theorem.
Every input is a root, derivative, scale, or admissibility statement; none is
a first-moment estimate. -/
theorem
    tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half_of_rootCorridor
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
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
    (hRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
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
  have hObjectiveBounds :=
    eventually_phaseSignedFourSizeObjective_rootMidpoint_bounds
      rCo rPlus slopeLower slopeUpper hCo hGap
      hSlopeLowerNonneg hSlopeUpperNonneg hFeasible
      hDerivLower hDerivUpper hRoot
  exact
    tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half_of_partCountAsymptotic
      rCo rPlus slopeLower slopeUpper hObjectiveBounds
      hSlopeLower hSlopeUpper hRootGap hParts hAdmissible

/-- Any normalized first-moment asymptotic with the certified phase margin is
eventually bounded below by the fixed positive rate. -/
theorem eventually_signedFourCertifiedFirstMomentRate_lt_normalized_log
    (rCo rPlus : ℕ → ℝ)
    (hLimit : Tendsto
      (fun n : ℕ ↦
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) /
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      signedFourCertifiedFirstMomentRate <
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) /
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ) := by
  let L : ℝ := Real.log ((200 : ℝ) / 153)
  have hL : 0 < L := by
    simpa only [L] using log_200_div_153_pos
  have hNegative : -L / 4 < (0 : ℝ) := by linarith
  have hError : ∀ᶠ n : ℕ in atTop,
      -L / 4 <
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) /
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseMargin n / 2 := by
    simpa only [mem_Ioi] using
      hLimit.eventually (Ioi_mem_nhds hNegative)
  filter_upwards [hError] with n hn
  have hMargin : L < signedFourPhaseMargin n := by
    simpa only [L] using log_200_div_153_lt_signedFourPhaseMargin n
  unfold signedFourCertifiedFirstMomentRate
  dsimp only [L] at hn hMargin
  linarith

/-- Exponentiating the normalized lower rate gives an exact eventual lower
bound for the positive real first moment. -/
theorem eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment
    (rCo rPlus : ℕ → ℝ)
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2)))
    (hLimit : Tendsto
      (fun n : ℕ ↦
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) /
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) <
        signedFourRootMidpointFirstMoment rCo rPlus n := by
  have hKPos :=
    eventually_signedFourPartCount_pos_of_normalized_tendsto
      (signedFourRootMidpointPartCount rCo rPlus) hParts
  have hRate :=
    eventually_signedFourCertifiedFirstMomentRate_lt_normalized_log
      rCo rPlus hLimit
  filter_upwards [hKPos, hRate] with n hnK hnRate
  have hnKReal :
      0 < (signedFourRootMidpointPartCount rCo rPlus n : ℝ) := by
    exact_mod_cast hnK
  have hLog :
      signedFourCertifiedFirstMomentRate *
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ) <
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) :=
    (lt_div_iff₀ hnKReal).mp hnRate
  have hMomentPos :
      0 < signedFourRootMidpointFirstMoment rCo rPlus n := by
    unfold signedFourRootMidpointFirstMoment
    exact partialSignedFirstMoment_pos _ _ _
  exact (Real.exp_lt_exp.mpr hLog).trans_eq (Real.exp_log hMomentPos)

/-- In particular, the exact signed four-size first moment is eventually
strictly larger than one. -/
theorem eventually_one_lt_signedFourRootMidpointFirstMoment
    (rCo rPlus : ℕ → ℝ)
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2)))
    (hLimit : Tendsto
      (fun n : ℕ ↦
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) /
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      1 < signedFourRootMidpointFirstMoment rCo rPlus n := by
  have hExponential :=
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment
      rCo rPlus hParts hLimit
  have hKPos :=
    eventually_signedFourPartCount_pos_of_normalized_tendsto
      (signedFourRootMidpointPartCount rCo rPlus) hParts
  filter_upwards [hExponential, hKPos] with n hExp hnK
  have hnKReal :
      0 < (signedFourRootMidpointPartCount rCo rPlus n : ℝ) := by
    exact_mod_cast hnK
  have hExponent :
      0 < signedFourCertifiedFirstMomentRate *
        (signedFourRootMidpointPartCount rCo rPlus n : ℝ) :=
    mul_pos signedFourCertifiedFirstMomentRate_pos hnKReal
  have hOneExp :
      1 < Real.exp
        (signedFourCertifiedFirstMomentRate *
          (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) := by
    have h := Real.exp_lt_exp.mpr hExponent
    simpa using h
  exact hOneExp.trans hExp

/-- Manuscript-facing exponential lower bound obtained directly from the
root corridor, the three analytic scale limits, and midpoint admissibility. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
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
    (hRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
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
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) <
        signedFourRootMidpointFirstMoment rCo rPlus n := by
  have hLimit :=
    tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half_of_rootCorridor
      rCo rPlus slopeLower slopeUpper hCo hGap
      hSlopeLowerNonneg hSlopeUpperNonneg hFeasible
      hDerivLower hDerivUpper hRoot hSlopeLower hSlopeUpper
      hRootGap hParts hAdmissible
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment
      rCo rPlus hParts hLimit

#print axioms signedFourCertifiedFirstMomentRate_pos
#print axioms tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half_of_rootCorridor
#print axioms eventually_signedFourCertifiedFirstMomentRate_lt_normalized_log
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment
#print axioms eventually_one_lt_signedFourRootMidpointFirstMoment
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor

end

end Erdos625
