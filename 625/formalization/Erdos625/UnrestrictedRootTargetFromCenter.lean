import Erdos625.LimitingMarginTargetTransport
import Erdos625.SignedFourMidpointTargetFromLogLogCenter
import Mathlib.Tactic

/-!
# Unrestricted-root target and scale data from center localization

The unrestricted-root localization theorem controls

`(rPlus_n - phaseRootCenter n)/(n/(log n)^3)`

at the `O(log log n)` scale.  The normalized root-gap assembly consumes three
consequences of that estimate:

* `rPlus_n/(n/log n) -> q/2`;
* convergence of the exact unrestricted-root target to the manuscript phase
  target;
* eventual containment of that target in one explicit compact subinterval of
  `(2,5)`.

This module proves all three directly.  No root equation, derivative estimate,
secant-slope estimate, signed root, first moment, chromatic lower tail, partial
diagonal, skeleton, second moment, or final Erdős statement is used.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- `O(log log n)` right-root displacement from the exact phase center implies
the ordinary unrestricted-root part-count asymptotic. -/
theorem
    tendsto_signedFourNormalizedRightRootPartCount_of_centerLocalization
    (rPlus : ℕ → ℝ)
    (hDisplacement : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder) :
    Tendsto (signedFourNormalizedRightRootPartCount rPlus)
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
        signedFourNormalizedRightRootCenterDisplacement rPlus n *
          scaleRatio n) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n * scaleRatio n) := by
    simpa using hDisplacement.mul (isBigO_refl scaleRatio atTop)
  have hProduct : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRightRootCenterDisplacement rPlus n *
          scaleRatio n)
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
  unfold signedFourNormalizedRightRootPartCount
    signedFourNormalizedPhaseRootCenter
    signedFourNormalizedRightRootCenterDisplacement scaleRatio
  field_simp [hRootScale, hPartScale]
  ring

/-- The unrestricted-root part-count asymptotic forces eventual positivity of
the actual real root. -/
theorem eventually_unrestrictedRoot_pos_of_centerLocalization
    (rPlus : ℕ → ℝ)
    (hDisplacement : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder) :
    ∀ᶠ n : ℕ in atTop, 0 < rPlus n := by
  have hParts :=
    tendsto_signedFourNormalizedRightRootPartCount_of_centerLocalization
      rPlus hDisplacement
  have hNormPos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourNormalizedRightRootPartCount rPlus n :=
    hParts.eventually
      (Ioi_mem_nhds (div_pos q_pos (by norm_num : (0 : ℝ) < 2)))
  filter_upwards [hNormPos, eventually_gt_atTop (1 : ℕ)] with n hnNorm hn
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hPartPos : 0 < signedFourNaturalPartScale n := by
    unfold signedFourNaturalPartScale
    exact div_pos hnPos hlogPos
  unfold signedFourNormalizedRightRootPartCount at hnNorm
  rcases div_pos_iff.mp hnNorm with h | h
  · exact h.1
  · exact (not_lt_of_ge hPartPos.le h.2).elim

/-- `O(log log n)` center localization forces the exact unrestricted-root
deficit target to converge to the phase-varying manuscript target. -/
theorem
    tendsto_unrestrictedRootTarget_sub_phaseTarget_of_centerLocalization
    (rPlus : ℕ → ℝ)
    (hDisplacement : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder) :
    Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (rPlus n) -
          signedFourPhaseTarget n)
      atTop (𝓝 0) := by
  have hParts :=
    tendsto_signedFourNormalizedRightRootPartCount_of_centerLocalization
      rPlus hDisplacement
  have hCenterInvRaw :=
    tendsto_signedFourNormalizedPhaseRootCenter.inv₀
      (div_ne_zero q_ne_zero (by norm_num))
  have hHalfInv : (q / 2)⁻¹ = 2 / q := by
    field_simp [q_ne_zero]
  have hCenterInv : Tendsto
      (fun n : ℕ ↦ (signedFourNormalizedPhaseRootCenter n)⁻¹)
      atTop (𝓝 (2 / q)) := by
    simpa only [hHalfInv] using hCenterInvRaw
  have hPartsInvRaw := hParts.inv₀
    (div_ne_zero q_ne_zero (by norm_num))
  have hPartsInv : Tendsto
      (fun n : ℕ ↦
        (signedFourNormalizedRightRootPartCount rPlus n)⁻¹)
      atTop (𝓝 (2 / q)) := by
    simpa only [hHalfInv] using hPartsInvRaw
  have hDisplacementInvLogBigO :
      (fun n : ℕ ↦
        signedFourNormalizedRightRootCenterDisplacement rPlus n *
          (logOrder n)⁻¹) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n * (logOrder n)⁻¹) := by
    simpa using hDisplacement.mul
      (isBigO_refl (fun n : ℕ ↦ (logOrder n)⁻¹) atTop)
  have hDisplacementInvLog : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRightRootCenterDisplacement rPlus n *
          (logOrder n)⁻¹)
      atTop (𝓝 0) :=
    hDisplacementInvLogBigO.trans_tendsto
      tendsto_signedFour_logLogOrder_mul_inv_logOrder_zero
  have hCore := (hDisplacementInvLog.mul hCenterInv).mul hPartsInv
  simp only [zero_mul] at hCore
  refine hCore.congr' ?_
  have hRightPos :=
    eventually_unrestrictedRoot_pos_of_centerLocalization
      rPlus hDisplacement
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_phaseRootCenter_pos, hRightPos,
    eventually_gt_atTop (1 : ℕ)] with
    n hnRoot hCenterPos hnPlus hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hCenter : phaseRootCenter n ≠ 0 := hCenterPos.ne'
  have hPlus : rPlus n ≠ 0 := hnPlus.ne'
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
  unfold fourSizeTarget
    signedFourNormalizedRightRootCenterDisplacement
    signedFourNormalizedPhaseRootCenter
    signedFourNormalizedRightRootPartCount
    signedFourNaturalRootGapScale signedFourNaturalPartScale
  field_simp [hnReal, hlog, hCenter, hPlus, hRootScale, hPartScale]
  ring

/-- The unrestricted-root target is eventually contained in the same explicit
compact corridor used by the midpoint rounding and limiting-margin packages. -/
theorem eventually_unrestrictedRootTarget_mem_admissibilityCorridor
    (rPlus : ℕ → ℝ)
    (hDisplacement : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder) :
    ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (rPlus n) ∈
        signedFourAdmissibilityTargetCorridor := by
  have hTarget :=
    tendsto_unrestrictedRootTarget_sub_phaseTarget_of_centerLocalization
      rPlus hDisplacement
  have hError : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (rPlus n) -
          signedFourPhaseTarget n ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    hTarget.eventually
      (Ioo_mem_nhds (by norm_num : (-(1 / 4 : ℝ)) < 0)
        (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hError] with n hn
  have hPhase := signedFourPhaseTarget_mem_explicit_Icc n
  unfold signedFourAdmissibilityTargetCorridor
  constructor <;> linarith [hn.1, hn.2, hPhase.1, hPhase.2]

/-- The manuscript phase target lies pointwise in the explicit compact
corridor used above. -/
theorem signedFourPhaseTarget_mem_admissibilityCorridor_pointwise
    (n : ℕ) :
    signedFourPhaseTarget n ∈ signedFourAdmissibilityTargetCorridor :=
  signedFourPhaseTarget_mem_admissibilityTargetCorridor n

/-- Root-gap assembly with all right-root scale and target data derived from a
single center-localization estimate.  The remaining analytic inputs are the
concrete root equations, nonzero gap, and normalized signed secant slope. -/
theorem
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_secant
    (rCo rPlus : ℕ → ℝ)
    (hCenter : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hGap : ∀ᶠ n : ℕ in atTop, rPlus n - rCo n ≠ 0)
    (hCoRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hPlusRoot : ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (rPlus n) = 0)
    (hSecant : Tendsto
      (signedFourNormalizedRootSecantSlope rCo rPlus)
      atTop (𝓝 (2 / q))) :
    Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  have hTarget :=
    eventually_unrestrictedRootTarget_mem_admissibilityCorridor
      rPlus hCenter
  have hTargetTransport :=
    tendsto_unrestrictedRootTarget_sub_phaseTarget_of_centerLocalization
      rPlus hCenter
  have hRightParts :=
    tendsto_signedFourNormalizedRightRootPartCount_of_centerLocalization
      rPlus hCenter
  have hPlus :=
    (eventually_unrestrictedRoot_pos_of_centerLocalization
      rPlus hCenter).mono fun _ hn ↦ hn.ne'
  exact
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_target_and_secant
      (A := 5 / 2) (B := 9 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      rCo rPlus tendsto_phaseNat_atTop_nat
      hTarget
      (Filter.Eventually.of_forall
        signedFourPhaseTarget_mem_admissibilityCorridor_pointwise)
      hTargetTransport hGap hPlus hCoRoot hPlusRoot
      hRightParts hSecant

#print axioms tendsto_signedFourNormalizedRightRootPartCount_of_centerLocalization
#print axioms eventually_unrestrictedRoot_pos_of_centerLocalization
#print axioms tendsto_unrestrictedRootTarget_sub_phaseTarget_of_centerLocalization
#print axioms eventually_unrestrictedRootTarget_mem_admissibilityCorridor
#print axioms signedFourPhaseTarget_mem_admissibilityCorridor_pointwise
#print axioms tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_secant

end

end Erdos625