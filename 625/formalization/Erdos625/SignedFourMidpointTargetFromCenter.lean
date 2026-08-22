import Erdos625.SignedFourMidpointTargetCorridor
import Erdos625.PhaseRootPartGeometry
import Mathlib.Tactic

/-!
# Midpoint target convergence from displacement about the phase center

The exact phase center satisfies

`phaseRootCenter n ~ (q/2) * n/log n`.

Suppose a natural part-count sequence differs from that center by at most the
root-gap scale `n/(log n)^3`, uniformly up to a constant.  Then two consequences
follow automatically:

* the part count has the manuscript asymptotic `K_n/(n/log n) -> q/2`;
* its exact deficit target converges to
  `1 + 2/q - phaseDelta n`.

The second conclusion uses the exact identity at `phaseRootCenter` and the
extra factor `1/log n` obtained when a root-gap-scale displacement is converted
into a target displacement.

For the canonical ceiling midpoint, this removes both the part-count
asymptotic and midpoint-target convergence as independent E625-10 inputs.  The
remaining input is the geometrically natural statement that the midpoint lies
within `O(n/(log n)^3)` of the phase center.

No root existence, derivative estimate, root-gap coefficient, first-moment
estimate, chromatic lower tail, partial diagonal, second moment, or final
Erdős statement is assumed or proved here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The phase root center normalized by the natural part-count scale. -/
noncomputable def signedFourNormalizedPhaseRootCenter (n : ℕ) : ℝ :=
  phaseRootCenter n / signedFourNaturalPartScale n

/-- Displacement of a natural part count from the phase center, normalized by
the root-gap scale. -/
noncomputable def signedFourNormalizedCenterDisplacement
    (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((K n : ℝ) - phaseRootCenter n) /
    signedFourNaturalRootGapScale n

/-- The phase center is eventually strictly positive. -/
theorem eventually_phaseRootCenter_pos :
    ∀ᶠ n : ℕ in atTop, 0 < phaseRootCenter n := by
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor] with n hn
  unfold phaseRootCenter
  have hnPos : 0 < n := Nat.zero_lt_of_lt hn.1.1
  exact div_pos (by exact_mod_cast hnPos) hn.2.1

/-- The phase center has the manuscript part-count asymptotic. -/
theorem tendsto_signedFourNormalizedPhaseRootCenter :
    Tendsto signedFourNormalizedPhaseRootCenter atTop (𝓝 (q / 2)) := by
  have hScaleNe : ∀ᶠ n : ℕ in atTop,
      (2 / q) * logOrder n ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact mul_ne_zero (div_ne_zero (by norm_num) q_ne_zero)
      (Real.log_pos (by exact_mod_cast hn)).ne'
  have hRatio : Tendsto
      (fun n : ℕ ↦
        phaseRootS0 n / ((2 / q) * logOrder n))
      atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hScaleNe).1
      phaseRootS0_isEquivalent_scaled_logOrder
  have hInv : Tendsto
      (fun n : ℕ ↦
        (phaseRootS0 n / ((2 / q) * logOrder n))⁻¹)
      atTop (𝓝 1) := by
    simpa using hRatio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hScaled : Tendsto
      (fun n : ℕ ↦
        (q / 2) *
          (phaseRootS0 n / ((2 / q) * logOrder n))⁻¹)
      atTop (𝓝 (q / 2)) := by
    simpa using hInv.const_mul (q / 2)
  refine hScaled.congr' ?_
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_gt_atTop (1 : ℕ)] with n hnRoot hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hs0 : phaseRootS0 n ≠ 0 := hnRoot.2.1.ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedPhaseRootCenter phaseRootCenter
    signedFourNaturalPartScale
  field_simp [hnReal, hs0, hlog, q_ne_zero]

/-- The root-gap scale is negligible relative to the part-count scale. -/
theorem tendsto_signedFourNaturalRootGapScale_div_partScale_zero :
    Tendsto
      (fun n : ℕ ↦
        signedFourNaturalRootGapScale n /
          signedFourNaturalPartScale n)
      atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹)
      atTop (𝓝 0) :=
    tendsto_logOrder_atTop.inv_tendsto_atTop
  have hInvSq : Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹ ^ 2)
      atTop (𝓝 0) := by
    simpa using hInv.pow 2
  refine hInvSq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNaturalRootGapScale signedFourNaturalPartScale
  field_simp [hnReal, hlog]

/-- A root-gap-scale `O(1)` displacement from the phase center already
implies the ordinary midpoint part-count asymptotic. -/
theorem tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO
    (K : ℕ → ℕ)
    (hDisplacement : signedFourNormalizedCenterDisplacement K =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ))) :
    Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2)) := by
  let scaleRatio : ℕ → ℝ := fun n ↦
    signedFourNaturalRootGapScale n /
      signedFourNaturalPartScale n
  have hRatio : Tendsto scaleRatio atTop (𝓝 0) := by
    simpa only [scaleRatio] using
      tendsto_signedFourNaturalRootGapScale_div_partScale_zero
  have hProductBigO :
      (fun n : ℕ ↦
        signedFourNormalizedCenterDisplacement K n * scaleRatio n) =O[atTop]
        scaleRatio := by
    have h := hDisplacement.mul (isBigO_refl scaleRatio atTop)
    exact h.congr_right fun n ↦ by simp
  have hProduct : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedCenterDisplacement K n * scaleRatio n)
      atTop (𝓝 0) :=
    hProductBigO.trans_tendsto hRatio
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

/-- The reciprocal logarithmic scale tends to zero. -/
theorem tendsto_signedFour_inv_logOrder_zero :
    Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹) atTop (𝓝 0) :=
  tendsto_logOrder_atTop.inv_tendsto_atTop

/-- A root-gap-scale bounded displacement from the phase center forces the
exact four-size target to converge to the phase target. -/
theorem tendsto_fourSizeTarget_sub_phaseTarget_of_centerDisplacement_isBigO
    (K : ℕ → ℕ)
    (hDisplacement : signedFourNormalizedCenterDisplacement K =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (K n : ℝ) -
          signedFourPhaseTarget n)
      atTop (𝓝 0) := by
  have hParts :=
    tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO
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
        (fun n : ℕ ↦ (logOrder n)⁻¹) := by
    have h := hDisplacement.mul
      (isBigO_refl (fun n : ℕ ↦ (logOrder n)⁻¹) atTop)
    exact h.congr_right fun n ↦ by simp
  have hDisplacementInvLog : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedCenterDisplacement K n *
          (logOrder n)⁻¹)
      atTop (𝓝 0) :=
    hDisplacementInvLogBigO.trans_tendsto
      tendsto_signedFour_inv_logOrder_zero
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

/-- Canonical root-midpoint specialization of the displacement-to-target
bridge. -/
theorem tendsto_rootMidpointTarget_sub_phaseTarget_of_centerDisplacement_isBigO
    (rCo rPlus : ℕ → ℝ)
    (hDisplacement :
      signedFourNormalizedCenterDisplacement
          (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
        (fun _n : ℕ ↦ (1 : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n)
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseTarget n)
      atTop (𝓝 0) :=
  tendsto_fourSizeTarget_sub_phaseTarget_of_centerDisplacement_isBigO
    (signedFourRootMidpointPartCount rCo rPlus) hDisplacement

/-- Canonical root-midpoint part-count asymptotic derived from the same center
 displacement bound. -/
theorem tendsto_rootMidpointNormalizedPartCount_of_centerDisplacement_isBigO
    (rCo rPlus : ℕ → ℝ)
    (hDisplacement :
      signedFourNormalizedCenterDisplacement
          (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
        (fun _n : ℕ ↦ (1 : ℝ))) :
    Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2)) :=
  tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO
    (signedFourRootMidpointPartCount rCo rPlus) hDisplacement

/-- Manuscript-facing exponential E625-10 endpoint in which both the midpoint
part-count asymptotic and target convergence are derived from one natural
center-displacement estimate. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_centerDisplacement
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hDisplacement :
      signedFourNormalizedCenterDisplacement
          (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
        (fun _n : ℕ ↦ (1 : ℝ)))
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
    tendsto_rootMidpointTarget_sub_phaseTarget_of_centerDisplacement_isBigO
      rCo rPlus hDisplacement
  have hParts :=
    tendsto_rootMidpointNormalizedPartCount_of_centerDisplacement_isBigO
      rCo rPlus hDisplacement
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_target_tendsto
      rCo rPlus slopeLower slopeUpper hTargetApprox
      hCo hGap hSlopeLowerNonneg hSlopeUpperNonneg hFeasible
      hDerivLower hDerivUpper hRoot hSlopeLower hSlopeUpper
      hRootGap hParts

#print axioms eventually_phaseRootCenter_pos
#print axioms tendsto_signedFourNormalizedPhaseRootCenter
#print axioms tendsto_signedFourNaturalRootGapScale_div_partScale_zero
#print axioms tendsto_signedFourNormalizedPartCount_of_centerDisplacement_isBigO
#print axioms tendsto_signedFour_inv_logOrder_zero
#print axioms tendsto_fourSizeTarget_sub_phaseTarget_of_centerDisplacement_isBigO
#print axioms tendsto_rootMidpointTarget_sub_phaseTarget_of_centerDisplacement_isBigO
#print axioms tendsto_rootMidpointNormalizedPartCount_of_centerDisplacement_isBigO
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_centerDisplacement

end

end Erdos625
