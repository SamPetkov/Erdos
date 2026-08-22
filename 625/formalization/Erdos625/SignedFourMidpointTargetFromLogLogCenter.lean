import Erdos625.SignedFourMidpointTargetFromCenter
import Mathlib.Tactic

/-!
# Midpoint target convergence from `O(log log n)` center displacement

The raw unrestricted objective at the manuscript phase center is only known
at the `O(log log n)` scale.  Consequently, the natural concrete root
localization may have the form

`(K_n - phaseRootCenter n) / (n/(log n)^3) = O(log log n)`

rather than a uniformly bounded normalized displacement.

This module proves that the weaker and more realistic input is still fully
sufficient for E625-10.  Indeed,

* relative to the part-count scale, the correction is
  `O(log log n / (log n)^2) = o(1)`;
* in the deficit target, the correction is
  `O(log log n / log n) = o(1)`.

Thus the midpoint part-count asymptotic, target convergence, compact target
corridor, and tangent-rounding admissibility all survive unchanged.

No root existence, derivative estimate, root-gap coefficient, first-moment
estimate, chromatic lower tail, partial diagonal, second moment, or final
Erdős statement is assumed or proved here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The logarithmic-logarithmic scale is negligible relative to the
logarithmic scale. -/
theorem tendsto_signedFour_logLogOrder_div_logOrder_zero :
    Tendsto
      (fun n : ℕ ↦ logLogOrder n / logOrder n)
      atTop (𝓝 0) :=
  logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero

/-- Multiplicative form used in the target-displacement argument. -/
theorem tendsto_signedFour_logLogOrder_mul_inv_logOrder_zero :
    Tendsto
      (fun n : ℕ ↦ logLogOrder n * (logOrder n)⁻¹)
      atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv] using
    tendsto_signedFour_logLogOrder_div_logOrder_zero

/-- The `O(log log n)` displacement is still negligible after changing from
the root-gap scale to the part-count scale. -/
theorem
    tendsto_signedFour_logLogOrder_mul_rootGapScale_div_partScale_zero :
    Tendsto
      (fun n : ℕ ↦
        logLogOrder n *
          (signedFourNaturalRootGapScale n /
            signedFourNaturalPartScale n))
      atTop (𝓝 0) := by
  have h := tendsto_signedFour_logLogOrder_div_logOrder_zero.mul
    tendsto_signedFour_inv_logOrder_zero
  simp only [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNaturalRootGapScale signedFourNaturalPartScale
  field_simp [hnReal, hlog]

/-- A center displacement of size `O(log log n)` on the root-gap scale still
implies the ordinary midpoint part-count asymptotic. -/
theorem
    tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO_logLogOrder
    (K : ℕ → ℕ)
    (hDisplacement : signedFourNormalizedCenterDisplacement K =O[atTop]
      logLogOrder) :
    Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2)) := by
  let scaleRatio : ℕ → ℝ := fun n ↦
    signedFourNaturalRootGapScale n /
      signedFourNaturalPartScale n
  have hVanishing : Tendsto
      (fun n : ℕ ↦ logLogOrder n * scaleRatio n)
      atTop (𝓝 0) := by
    simpa only [scaleRatio] using
      tendsto_signedFour_logLogOrder_mul_rootGapScale_div_partScale_zero
  have hProductBigO :
      (fun n : ℕ ↦
        signedFourNormalizedCenterDisplacement K n * scaleRatio n) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n * scaleRatio n) := by
    simpa using hDisplacement.mul (isBigO_refl scaleRatio atTop)
  have hProduct : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedCenterDisplacement K n * scaleRatio n)
      atTop (𝓝 0) :=
    hProductBigO.trans_tendsto hVanishing
  have hCenter := tendsto_signedFourNormalizedPhaseRootCenter
  have hSum := hCenter.add hProduct
  simp only [add_zero] at hSum
  refine hSum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hRootScale : signedFourNaturalRootGapScale n ≠ 0 := by
    unfold signedFourNaturalRootGapScale
    exact div_ne_zero hnReal (pow_ne_zero 3 hlog)
  have hPartScale : signedFourNaturalPartScale n ≠ 0 := by
    unfold signedFourNaturalPartScale
    exact div_ne_zero hnReal hlog
  unfold signedFourNormalizedPartCount
    signedFourNormalizedPhaseRootCenter
    signedFourNormalizedCenterDisplacement scaleRatio
  field_simp [hRootScale, hPartScale]
  ring

/-- An `O(log log n)` center displacement also forces the exact four-size
target to converge to the phase target. -/
theorem
    tendsto_fourSizeTarget_sub_phaseTarget_of_centerDisplacement_isBigO_logLogOrder
    (K : ℕ → ℕ)
    (hDisplacement : signedFourNormalizedCenterDisplacement K =O[atTop]
      logLogOrder) :
    Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (K n : ℝ) -
          signedFourPhaseTarget n)
      atTop (𝓝 0) := by
  have hParts :=
    tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO_logLogOrder
      K hDisplacement
  have hCenterInvRaw :=
    tendsto_signedFourNormalizedPhaseRootCenter.inv₀
      (div_ne_zero q_ne_zero (by norm_num))
  have hHalfInv : (q / 2)⁻¹ = 2 / q := by
    field_simp [q_ne_zero]
  have hCenterInv : Tendsto
      (fun n : ℕ ↦ (signedFourNormalizedPhaseRootCenter n)⁻¹)
      atTop (𝓝 (2 / q)) := by
    simpa only [hHalfInv] using hCenterInvRaw
  have hPartsInv := tendsto_inv_signedFourNormalizedPartCount K hParts
  have hDisplacementInvLogBigO :
      (fun n : ℕ ↦
        signedFourNormalizedCenterDisplacement K n *
          (logOrder n)⁻¹) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n * (logOrder n)⁻¹) := by
    simpa using hDisplacement.mul
      (isBigO_refl (fun n : ℕ ↦ (logOrder n)⁻¹) atTop)
  have hDisplacementInvLog : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedCenterDisplacement K n *
          (logOrder n)⁻¹)
      atTop (𝓝 0) :=
    hDisplacementInvLogBigO.trans_tendsto
      tendsto_signedFour_logLogOrder_mul_inv_logOrder_zero
  have hCore := (hDisplacementInvLog.mul hCenterInv).mul hPartsInv
  simp only [zero_mul] at hCore
  refine hCore.congr' ?_
  have hKPos :=
    eventually_signedFourPartCount_pos_of_normalized_tendsto K hParts
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_phaseRootCenter_pos, hKPos,
    eventually_gt_atTop (1 : ℕ)] with n hnRoot hCenterPos hnK hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hCenter : phaseRootCenter n ≠ 0 := hCenterPos.ne'
  have hKReal : (K n : ℝ) ≠ 0 := by exact_mod_cast hnK.ne'
  have hRootScale : signedFourNaturalRootGapScale n ≠ 0 := by
    unfold signedFourNaturalRootGapScale
    exact div_ne_zero hnReal (pow_ne_zero 3 hlog)
  have hPartScale : signedFourNaturalPartScale n ≠ 0 := by
    unfold signedFourNaturalPartScale
    exact div_ne_zero hnReal hlog
  have hTargetIdentity :
      signedFourPhaseTarget n =
        (phaseNat n : ℝ) - (n : ℝ) / phaseRootCenter n := by
    simpa only [signedFourPhaseTarget] using
      (phaseRoot_target_identity hnRoot.1).symm
  rw [hTargetIdentity]
  unfold fourSizeTarget signedFourNormalizedCenterDisplacement
    signedFourNormalizedPhaseRootCenter signedFourNormalizedPartCount
    signedFourNaturalRootGapScale signedFourNaturalPartScale
  field_simp [hnReal, hlog, hCenter, hKReal, hRootScale, hPartScale]
  ring

/-- Canonical root-midpoint target convergence under the realistic
`O(log log n)` center-displacement hypothesis. -/
theorem
    tendsto_rootMidpointTarget_sub_phaseTarget_of_centerDisplacement_isBigO_logLogOrder
    (rCo rPlus : ℕ → ℝ)
    (hDisplacement :
      signedFourNormalizedCenterDisplacement
          (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
        logLogOrder) :
    Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n)
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseTarget n)
      atTop (𝓝 0) :=
  tendsto_fourSizeTarget_sub_phaseTarget_of_centerDisplacement_isBigO_logLogOrder
    (signedFourRootMidpointPartCount rCo rPlus) hDisplacement

/-- Canonical root-midpoint part-count asymptotic under the same realistic
center-displacement hypothesis. -/
theorem
    tendsto_rootMidpointNormalizedPartCount_of_centerDisplacement_isBigO_logLogOrder
    (rCo rPlus : ℕ → ℝ)
    (hDisplacement :
      signedFourNormalizedCenterDisplacement
          (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
        logLogOrder) :
    Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2)) :=
  tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO_logLogOrder
    (signedFourRootMidpointPartCount rCo rPlus) hDisplacement

/-- Manuscript-facing exponential E625-10 endpoint under an
`O(log log n)` root-midpoint displacement from the exact phase center. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_logLogCenterDisplacement
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hDisplacement :
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
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) <
        signedFourRootMidpointFirstMoment rCo rPlus n := by
  have hTargetApprox :=
    tendsto_rootMidpointTarget_sub_phaseTarget_of_centerDisplacement_isBigO_logLogOrder
      rCo rPlus hDisplacement
  have hParts :=
    tendsto_rootMidpointNormalizedPartCount_of_centerDisplacement_isBigO_logLogOrder
      rCo rPlus hDisplacement
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_target_tendsto
      rCo rPlus slopeLower slopeUpper hTargetApprox
      hCo hGap hSlopeLowerNonneg hSlopeUpperNonneg hFeasible
      hDerivLower hDerivUpper hRoot hSlopeLower hSlopeUpper
      hRootGap hParts

#print axioms tendsto_signedFour_logLogOrder_div_logOrder_zero
#print axioms tendsto_signedFour_logLogOrder_mul_inv_logOrder_zero
#print axioms tendsto_signedFour_logLogOrder_mul_rootGapScale_div_partScale_zero
#print axioms tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO_logLogOrder
#print axioms tendsto_fourSizeTarget_sub_phaseTarget_of_centerDisplacement_isBigO_logLogOrder
#print axioms tendsto_rootMidpointTarget_sub_phaseTarget_of_centerDisplacement_isBigO_logLogOrder
#print axioms tendsto_rootMidpointNormalizedPartCount_of_centerDisplacement_isBigO_logLogOrder
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_logLogCenterDisplacement

end

end Erdos625
