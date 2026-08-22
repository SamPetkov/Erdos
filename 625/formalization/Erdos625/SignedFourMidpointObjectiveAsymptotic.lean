import Erdos625.SignedFourPhaseMargin
import Erdos625.SignedFourRootMidpointFirstMomentSandwich
import Mathlib.Tactic

/-!
# Phase-varying asymptotic assembly at the signed root midpoint

This module performs the deterministic asymptotic squeeze left after the
finite E625-10 sandwich.  It keeps the phase margin as the varying sequence

`A_n = signedFourPhaseMargin n`

and consumes separate asymptotics for:

* the derivative corridor bounds, normalized by `(log n)^2`;
* the signed/unrestricted root gap, normalized by `n/(log n)^3`;
* the midpoint part count, normalized by `n/log n`.

From these inputs and the finite objective corridor it proves

`phaseSignedFourSizeObjective n K_n / K_n - A_n/2 -> 0`.

Combining the result with the already-proved factorial/rounding error gives
the corresponding exact first-moment limit.  No hypothesis is an expectation
or first-moment estimate.

No chromatic lower tail, partial diagonal, skeleton, second moment, or final
Erdős statement is used.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Natural real scale of the signed/unrestricted root gap. -/
noncomputable def signedFourNaturalRootGapScale (n : ℕ) : ℝ :=
  (n : ℝ) / (logOrder n) ^ 3

/-- Derivative normalized by its manuscript scale `(log n)^2`. -/
noncomputable def signedFourNormalizedSlope
    (slope : ℕ → ℝ) (n : ℕ) : ℝ :=
  slope n / (logOrder n) ^ 2

/-- Root gap normalized by its manuscript scale `n/(log n)^3`. -/
noncomputable def signedFourNormalizedRootGap
    (rCo rPlus : ℕ → ℝ) (n : ℕ) : ℝ :=
  (rPlus n - rCo n) / signedFourNaturalRootGapScale n

/-- A natural part-count sequence normalized by `n/log n`. -/
noncomputable def signedFourNormalizedPartCount
    (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  (K n : ℝ) / signedFourNaturalPartScale n

/-- Fully normalized multiplicative core of the midpoint objective. -/
noncomputable def signedFourNormalizedMidpointCore
    (rCo rPlus slope : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  signedFourNormalizedSlope slope n *
      signedFourNormalizedRootGap rCo rPlus n / 2 *
    (signedFourNormalizedPartCount K n)⁻¹

/-- The cubic logarithmic scale is negligible relative to the vertex count. -/
theorem signedFour_logOrder_cubed_isLittleO_natCast :
    (fun n : ℕ ↦ (logOrder n) ^ 3) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  simpa only [logOrder, Function.comp_def, id_eq] using
    (Real.isLittleO_pow_log_id_atTop (n := 3)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Equivalently, `(log n)^2` is negligible compared with the natural part
scale `n/log n`. -/
theorem tendsto_logOrder_sq_div_signedFourNaturalPartScale_zero :
    Tendsto
      (fun n : ℕ ↦
        (logOrder n) ^ 2 / signedFourNaturalPartScale n)
      atTop (𝓝 0) := by
  have hRaw : Tendsto
      (fun n : ℕ ↦ (logOrder n) ^ 3 / (n : ℝ))
      atTop (𝓝 0) :=
    signedFour_logOrder_cubed_isLittleO_natCast.tendsto_div_nhds_zero
  refine hRaw.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hnReal : (n : ℝ) ≠ 0 := by positivity
  unfold signedFourNaturalPartScale
  field_simp [hlog, hnReal]

/-- Inversion of the normalized part-count asymptotic. -/
theorem tendsto_inv_signedFourNormalizedPartCount
    (K : ℕ → ℕ)
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    Tendsto
      (fun n : ℕ ↦ (signedFourNormalizedPartCount K n)⁻¹)
      atTop (𝓝 (2 / q)) := by
  have hne : q / 2 ≠ 0 := div_ne_zero q_ne_zero (by norm_num)
  have h := hParts.inv₀ hne
  have hlimit : (q / 2)⁻¹ = 2 / q := by
    field_simp [q_ne_zero]
  simpa only [hlimit] using h

/-- The normalized multiplicative core converges to one half of the varying
phase margin.  The root-gap input is an error relative to the actual sequence
`signedFourPhaseMargin n`, not a fixed phase. -/
theorem tendsto_signedFourNormalizedMidpointCore_sub_margin_half
    (rCo rPlus slope : ℕ → ℝ) (K : ℕ → ℕ)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q)))
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0))
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedMidpointCore rCo rPlus slope K n -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0) := by
  have hConstSlope : Tendsto (fun _n : ℕ ↦ (2 / q : ℝ))
      atTop (𝓝 (2 / q)) := tendsto_const_nhds
  have hSlopeErr : Tendsto
      (fun n : ℕ ↦ signedFourNormalizedSlope slope n - 2 / q)
      atTop (𝓝 0) := by
    simpa using hSlope.sub hConstSlope
  have hMarginSlopeErr : Tendsto
      (fun n : ℕ ↦ signedFourPhaseMargin n *
        (signedFourNormalizedSlope slope n - 2 / q))
      atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero (b := 0) (B := q)
    · exact Filter.Eventually.of_forall fun n ↦
        (signedFourPhaseMargin_mem_Icc n).1
    · exact Filter.Eventually.of_forall fun n ↦
        (signedFourPhaseMargin_mem_Icc n).2
    · exact hSlopeErr
  have hSlopeGapErr : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedSlope slope n *
          (signedFourNormalizedRootGap rCo rPlus n -
            q ^ 2 / 4 * signedFourPhaseMargin n))
      atTop (𝓝 0) := by
    simpa using hSlope.mul hRootGap
  have hProductErr : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedSlope slope n *
            signedFourNormalizedRootGap rCo rPlus n -
          q / 2 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
    have h := hSlopeGapErr.add
      (hMarginSlopeErr.const_mul (q ^ 2 / 4))
    convert h using 1
    · funext n
      field_simp [q_ne_zero]
      ring
    · ring
  have hNumeratorErr : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedSlope slope n *
            signedFourNormalizedRootGap rCo rPlus n / 2 -
          q / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
    have h := hProductErr.const_mul (1 / 2 : ℝ)
    convert h using 1
    · funext n
      ring
    · ring
  have hPartsInv := tendsto_inv_signedFourNormalizedPartCount K hParts
  have hConstInv : Tendsto (fun _n : ℕ ↦ (2 / q : ℝ))
      atTop (𝓝 (2 / q)) := tendsto_const_nhds
  have hPartsInvErr : Tendsto
      (fun n : ℕ ↦
        (signedFourNormalizedPartCount K n)⁻¹ - 2 / q)
      atTop (𝓝 0) := by
    simpa using hPartsInv.sub hConstInv
  have hMarginInvErr : Tendsto
      (fun n : ℕ ↦ signedFourPhaseMargin n *
        ((signedFourNormalizedPartCount K n)⁻¹ - 2 / q))
      atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero (b := 0) (B := q)
    · exact Filter.Eventually.of_forall fun n ↦
        (signedFourPhaseMargin_mem_Icc n).1
    · exact Filter.Eventually.of_forall fun n ↦
        (signedFourPhaseMargin_mem_Icc n).2
    · exact hPartsInvErr
  have hFirst := hNumeratorErr.mul hPartsInv
  have hSecond := hMarginInvErr.const_mul (q / 4)
  have h := hFirst.add hSecond
  convert h using 1
  · funext n
    unfold signedFourNormalizedMidpointCore
    field_simp [q_ne_zero]
    ring
  · ring

/-- Exact conversion of the normalized core to the literal objective lower
corridor term. -/
theorem tendsto_signedFourMidpointCore_div_parts_sub_margin_half
    (rCo rPlus slope : ℕ → ℝ) (K : ℕ → ℕ)
    (hKPos : ∀ᶠ n : ℕ in atTop, 0 < K n)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q)))
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0))
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    Tendsto
      (fun n : ℕ ↦
        slope n * ((rPlus n - rCo n) / 2) / (K n : ℝ) -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0) := by
  have hCore :=
    tendsto_signedFourNormalizedMidpointCore_sub_margin_half
      rCo rPlus slope K hSlope hRootGap hParts
  refine hCore.congr' ?_
  filter_upwards [hKPos, eventually_gt_atTop (1 : ℕ)] with n hKn hn
  have hKReal : (K n : ℝ) ≠ 0 := by exact_mod_cast hKn.ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hnReal : (n : ℝ) ≠ 0 := by positivity
  unfold signedFourNormalizedMidpointCore signedFourNormalizedSlope
    signedFourNormalizedRootGap signedFourNormalizedPartCount
    signedFourNaturalRootGapScale signedFourNaturalPartScale
  field_simp [hKReal, hlog, hnReal]

/-- The additive ceiling unit contributes negligibly after normalization by
an `n/log n` part count. -/
theorem tendsto_signedFourSlope_div_parts_zero
    (slope : ℕ → ℝ) (K : ℕ → ℕ)
    (hKPos : ∀ᶠ n : ℕ in atTop, 0 < K n)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q)))
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    Tendsto (fun n : ℕ ↦ slope n / (K n : ℝ)) atTop (𝓝 0) := by
  have hPartsInv := tendsto_inv_signedFourNormalizedPartCount K hParts
  have hProduct :=
    (hSlope.mul tendsto_logOrder_sq_div_signedFourNaturalPartScale_zero).mul
      hPartsInv
  simp only [mul_zero, zero_mul] at hProduct
  refine hProduct.congr' ?_
  filter_upwards [hKPos, eventually_gt_atTop (1 : ℕ)] with n hKn hn
  have hKReal : (K n : ℝ) ≠ 0 := by exact_mod_cast hKn.ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hnReal : (n : ℝ) ≠ 0 := by positivity
  unfold signedFourNormalizedSlope signedFourNormalizedPartCount
    signedFourNaturalPartScale
  field_simp [hKReal, hlog, hnReal]

/-- Upper corridor term, including the exact ceiling `+1`, has the same
phase-varying normalized limit. -/
theorem tendsto_signedFourMidpointUpper_div_parts_sub_margin_half
    (rCo rPlus slope : ℕ → ℝ) (K : ℕ → ℕ)
    (hKPos : ∀ᶠ n : ℕ in atTop, 0 < K n)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q)))
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0))
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    Tendsto
      (fun n : ℕ ↦
        slope n * ((rPlus n - rCo n) / 2 + 1) / (K n : ℝ) -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0) := by
  have hCore := tendsto_signedFourMidpointCore_div_parts_sub_margin_half
    rCo rPlus slope K hKPos hSlope hRootGap hParts
  have hCeiling := tendsto_signedFourSlope_div_parts_zero
    slope K hKPos hSlope hParts
  have h := hCore.add hCeiling
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards with n
  ring

/-- Separate derivative, root-gap, and part-count asymptotics squeeze the
signed objective to one half of the varying phase margin. -/
theorem tendsto_phaseSignedFourSizeObjective_rootMidpoint_div_parts_sub_margin_half
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hKPos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourRootMidpointPartCount rCo rPlus n)
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
  let K := signedFourRootMidpointPartCount rCo rPlus
  have hLower := tendsto_signedFourMidpointCore_div_parts_sub_margin_half
    rCo rPlus slopeLower K hKPos hSlopeLower hRootGap hParts
  have hUpper := tendsto_signedFourMidpointUpper_div_parts_sub_margin_half
    rCo rPlus slopeUpper K hKPos hSlopeUpper hRootGap hParts
  apply hLower.squeeze' hUpper
  · filter_upwards [hObjectiveBounds, hKPos] with n hnBounds hnK
    have hnKReal : 0 < (K n : ℝ) := by exact_mod_cast hnK
    have hDiv := (div_le_div_iff_of_pos_right hnKReal).2 hnBounds.1
    linarith
  · filter_upwards [hObjectiveBounds, hKPos] with n hnBounds hnK
    have hnKReal : 0 < (K n : ℝ) := by exact_mod_cast hnK
    have hDiv := (div_le_div_iff_of_pos_right hnKReal).2 hnBounds.2
    linarith

/-- Exact factorial first moment: add the already-proved normalized finite
error to the normalized objective limit. -/
theorem tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hKPos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourRootMidpointPartCount rCo rPlus n)
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
        (signedFourRootMidpointPartCount rCo rPlus n))
    (hScaleToParts : signedFourNaturalPartScale =O[atTop]
      (fun n : ℕ ↦
        (signedFourRootMidpointPartCount rCo rPlus n : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        Real.log (signedFourRootMidpointFirstMoment rCo rPlus n) /
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseMargin n / 2)
      atTop (𝓝 0) := by
  have hFinite :=
    tendsto_signedFourRootMidpointFirstMomentLogError_div_parts_zero
      rCo rPlus hAdmissible hScaleToParts
  have hObjective :=
    tendsto_phaseSignedFourSizeObjective_rootMidpoint_div_parts_sub_margin_half
      rCo rPlus slopeLower slopeUpper hKPos hObjectiveBounds
      hSlopeLower hSlopeUpper hRootGap hParts
  have h := hFinite.add hObjective
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards with n
  ring

#print axioms signedFour_logOrder_cubed_isLittleO_natCast
#print axioms tendsto_logOrder_sq_div_signedFourNaturalPartScale_zero
#print axioms tendsto_inv_signedFourNormalizedPartCount
#print axioms tendsto_signedFourNormalizedMidpointCore_sub_margin_half
#print axioms tendsto_signedFourMidpointCore_div_parts_sub_margin_half
#print axioms tendsto_signedFourSlope_div_parts_zero
#print axioms tendsto_signedFourMidpointUpper_div_parts_sub_margin_half
#print axioms tendsto_phaseSignedFourSizeObjective_rootMidpoint_div_parts_sub_margin_half
#print axioms tendsto_signedFourRootMidpointFirstMoment_div_parts_sub_margin_half

end

end Erdos625
