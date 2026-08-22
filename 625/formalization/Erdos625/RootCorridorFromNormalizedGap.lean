import Erdos625.RootMidpointCenterLocalization
import Erdos625.Section10AmplificationScales
import Mathlib.Tactic

/-!
# Deriving the finite root corridor from normalized root data

The root-midpoint localization theorem currently accepts eventual
nonnegativity of the signed root and a literal gap of at least two.  These are
not independent analytic inputs.  This module derives both from the same two
asymptotic statements already needed downstream:

* `O(log log n)` localization of the unrestricted root about the phase center;
* the phase-varying normalized signed/unrestricted root-gap expansion.

First, any real sequence with `O(log log n)` center displacement on the
`n/(log n)^3` scale has normalized part-count limit `q/2`.  Applying this to
the signed root gives eventual positivity.  Second, the uniform positive
phase margin forces a fixed positive normalized root gap, while the natural
root-gap scale tends to infinity; hence the actual gap eventually exceeds
two.

No root existence, derivative estimate, root-gap coefficient proof, first
moment, chromatic lower tail, partial diagonal, skeleton, second moment, or
final Erdős statement is supplied here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A real-valued part-count sequence normalized by the natural `n/log n`
scale. -/
noncomputable def signedFourNormalizedRealPartCount
    (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  r n / signedFourNaturalPartScale n

/-- A real sequence with `O(log log n)` displacement from the exact phase
center has the ordinary normalized part-count limit `q/2`. -/
theorem
    tendsto_signedFourNormalizedRealPartCount_of_centerDisplacement_isBigO_logLogOrder
    (r : ℕ → ℝ)
    (hDisplacement :
      (fun n : ℕ ↦
        (r n - phaseRootCenter n) /
          signedFourNaturalRootGapScale n) =O[atTop]
        logLogOrder) :
    Tendsto (signedFourNormalizedRealPartCount r)
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
        ((r n - phaseRootCenter n) /
            signedFourNaturalRootGapScale n) * scaleRatio n) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n * scaleRatio n) := by
    simpa using hDisplacement.mul (isBigO_refl scaleRatio atTop)
  have hProduct : Tendsto
      (fun n : ℕ ↦
        ((r n - phaseRootCenter n) /
            signedFourNaturalRootGapScale n) * scaleRatio n)
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
  unfold signedFourNormalizedRealPartCount
    signedFourNormalizedPhaseRootCenter scaleRatio
  field_simp [hRootScale, hPartScale]
  ring

/-- The signed-root center displacement is the right-root center displacement
minus the normalized root gap. -/
theorem signedFour_leftRoot_centerDisplacement_eq
    (rCo rPlus : ℕ → ℝ) (n : ℕ) :
    (rCo n - phaseRootCenter n) /
        signedFourNaturalRootGapScale n =
      signedFourNormalizedRightRootCenterDisplacement rPlus n -
        signedFourNormalizedRootGap rCo rPlus n := by
  unfold signedFourNormalizedRightRootCenterDisplacement
    signedFourNormalizedRootGap
  ring

/-- Right-root center localization and the normalized gap expansion imply the
same `O(log log n)` center localization for the signed root. -/
theorem signedFour_leftRoot_centerDisplacement_isBigO_logLogOrder
    (rCo rPlus : ℕ → ℝ)
    (hRight : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    (fun n : ℕ ↦
      (rCo n - phaseRootCenter n) /
        signedFourNaturalRootGapScale n) =O[atTop]
      logLogOrder := by
  have hGap :=
    signedFourNormalizedRootGap_isBigO_logLogOrder
      rCo rPlus hRootGap
  have hSub := hRight.sub hGap
  apply hSub.congr'
  · filter_upwards with n
    exact (signedFour_leftRoot_centerDisplacement_eq rCo rPlus n).symm
  · exact Filter.EventuallyEq.rfl

/-- Consequently the signed root itself has normalized part-count limit
`q/2`. -/
theorem tendsto_signedFourNormalizedLeftRootPartCount
    (rCo rPlus : ℕ → ℝ)
    (hRight : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    Tendsto (signedFourNormalizedRealPartCount rCo)
      atTop (𝓝 (q / 2)) :=
  tendsto_signedFourNormalizedRealPartCount_of_centerDisplacement_isBigO_logLogOrder
    rCo
    (signedFour_leftRoot_centerDisplacement_isBigO_logLogOrder
      rCo rPlus hRight hRootGap)

/-- The signed-root part-count asymptotic forces eventual nonnegativity of the
actual real root. -/
theorem eventually_signedFour_leftRoot_nonneg
    (rCo rPlus : ℕ → ℝ)
    (hRight : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n := by
  have hLimit :=
    tendsto_signedFourNormalizedLeftRootPartCount
      rCo rPlus hRight hRootGap
  have hNormPos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourNormalizedRealPartCount rCo n :=
    hLimit.eventually
      (Ioi_mem_nhds (div_pos q_pos (by norm_num : (0 : ℝ) < 2)))
  filter_upwards [hNormPos, eventually_gt_atTop (1 : ℕ)] with n hnNorm hn
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hPartPos : 0 < signedFourNaturalPartScale n := by
    unfold signedFourNaturalPartScale
    exact div_pos hnPos hlogPos
  unfold signedFourNormalizedRealPartCount at hnNorm
  rcases div_pos_iff.mp hnNorm with h | h
  · exact h.1.le
  · exact (not_lt_of_ge hPartPos.le h.2).elim

/-- A fixed positive lower coefficient inherited from the welded phase-margin
certificate. -/
noncomputable def signedFourRootGapUniformLower : ℝ :=
  q ^ 2 / 8 * Real.log ((200 : ℝ) / 153)

/-- The uniform normalized root-gap lower coefficient is positive. -/
theorem signedFourRootGapUniformLower_pos :
    0 < signedFourRootGapUniformLower := by
  unfold signedFourRootGapUniformLower
  exact mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
    log_200_div_153_pos

/-- The phase-varying normalized root-gap expansion gives an eventual fixed
positive normalized gap. -/
theorem eventually_signedFourRootGapUniformLower_lt_normalizedGap
    (rCo rPlus : ℕ → ℝ)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      signedFourRootGapUniformLower <
        signedFourNormalizedRootGap rCo rPlus n := by
  have hc : 0 < signedFourRootGapUniformLower :=
    signedFourRootGapUniformLower_pos
  have hError : ∀ᶠ n : ℕ in atTop,
      -signedFourRootGapUniformLower <
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n :=
    hRootGap.eventually (Ioi_mem_nhds (neg_lt_zero.mpr hc))
  filter_upwards [hError] with n hn
  have hMargin := log_200_div_153_lt_signedFourPhaseMargin n
  unfold signedFourRootGapUniformLower at hn ⊢
  have hqSq : 0 < q ^ 2 := sq_pos_of_pos q_pos
  nlinarith

/-- The natural root-gap scale is eventually large enough that the fixed
positive normalized coefficient contributes at least two actual classes. -/
theorem eventually_two_le_signedFourRootGapUniformLower_mul_scale :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ signedFourRootGapUniformLower *
        signedFourNaturalRootGapScale n := by
  have hc : 0 < signedFourRootGapUniformLower :=
    signedFourRootGapUniformLower_pos
  have hOne :
      (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop]
        signedFourNaturalRootGapScale := by
    change (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / (Real.log (n : ℝ)) ^ 3)
    exact one_isLittleO_gapScale
  have hBound := hOne.bound
    (div_pos hc (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hBound, eventually_gt_atTop (1 : ℕ)] with n hnBound hn
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hScalePos : 0 < signedFourNaturalRootGapScale n := by
    unfold signedFourNaturalRootGapScale
    exact div_pos hnPos (pow_pos hlogPos 3)
  rw [norm_one, Real.norm_eq_abs, abs_of_pos hScalePos] at hnBound
  nlinarith

/-- The normalized root-gap expansion alone forces the literal finite corridor
condition `2 ≤ rPlus-rCo` eventually. -/
theorem eventually_two_le_signedFourRootGap
    (rCo rPlus : ℕ → ℝ)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n := by
  have hNorm :=
    eventually_signedFourRootGapUniformLower_lt_normalizedGap
      rCo rPlus hRootGap
  filter_upwards [hNorm,
    eventually_two_le_signedFourRootGapUniformLower_mul_scale,
    eventually_gt_atTop (1 : ℕ)] with n hnNorm hnTwo hn
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hScalePos : 0 < signedFourNaturalRootGapScale n := by
    unfold signedFourNaturalRootGapScale
    exact div_pos hnPos (pow_pos hlogPos 3)
  unfold signedFourNormalizedRootGap at hnNorm
  have hActual :
      signedFourRootGapUniformLower *
          signedFourNaturalRootGapScale n <
        rPlus n - rCo n :=
    (lt_div_iff₀ hScalePos).mp hnNorm
  exact hnTwo.trans hActual.le

/-- Strengthened root-midpoint localization wrapper: the finite sign and gap
corridor hypotheses are derived internally from right-root localization and
the normalized root-gap asymptotic. -/
theorem
    signedFourNormalizedRootMidpointCenterDisplacement_isBigO_logLogOrder_of_right_and_rootGap
    (rCo rPlus : ℕ → ℝ)
    (hRight : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    signedFourNormalizedCenterDisplacement
        (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
      logLogOrder := by
  exact
    signedFourNormalizedRootMidpointCenterDisplacement_isBigO_logLogOrder
      rCo rPlus hRight
      (eventually_signedFour_leftRoot_nonneg rCo rPlus hRight hRootGap)
      (eventually_two_le_signedFourRootGap rCo rPlus hRootGap)
      hRootGap

#print axioms tendsto_signedFourNormalizedRealPartCount_of_centerDisplacement_isBigO_logLogOrder
#print axioms signedFour_leftRoot_centerDisplacement_eq
#print axioms signedFour_leftRoot_centerDisplacement_isBigO_logLogOrder
#print axioms tendsto_signedFourNormalizedLeftRootPartCount
#print axioms eventually_signedFour_leftRoot_nonneg
#print axioms signedFourRootGapUniformLower_pos
#print axioms eventually_signedFourRootGapUniformLower_lt_normalizedGap
#print axioms eventually_two_le_signedFourRootGapUniformLower_mul_scale
#print axioms eventually_two_le_signedFourRootGap
#print axioms signedFourNormalizedRootMidpointCenterDisplacement_isBigO_logLogOrder_of_right_and_rootGap

end

end Erdos625