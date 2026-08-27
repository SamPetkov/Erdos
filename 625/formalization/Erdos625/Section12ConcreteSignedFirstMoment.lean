import Erdos625.Section8ConcretePhaseInputs
import Erdos625.SignedFourFirstMomentFiniteErrorAsymptotic
import Erdos625.PhaseSignedFourSizeLogLogCorridorCompactControl
import Erdos625.PhaseSignedFourSizeLogLogCorridorDerivativeLower
import Erdos625.PhaseRootLogLogCorridorScale
import Erdos625.Section11AsymptoticAssembly
import Erdos625.PartialDiagonalCentralLogEnvelope
import Erdos625.FullCornerWeights
import Mathlib.Tactic

/-!
# Concrete midpoint signed first moment

This module proves the signed first-moment estimate at the midpoint selected
from the two phase roots.
The proof has four steps: put the rounded selector in one enlarged common
corridor, derive its finite rounding side conditions, integrate the positive
signed-objective derivative from the exact signed root, and pay the explicit
finite logarithmic error.  A positive multiple of `baseScale` survives and
diverges; the exact midpoint vertex-mass identity then identifies the partial
and complete signed moments.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

private theorem tendsto_baseScale_atTop :
    Tendsto baseScale atTop atTop := by
  let d : ℝ :=
    (Real.log 2) ^ 2 / 32 * Real.log (200 / 153 : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hScaled : Tendsto (fun n : ℕ ↦ d * baseScale n) atTop atTop := by
    simpa only [d, baseScale, mul_div_assoc] using
      tendsto_explicit_gap_scale_atTop
  have h := hScaled.const_mul_atTop (inv_pos.mpr hd)
  simpa only [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul] using h

private structure PhaseCochromaticMidpointGeometry (n : ℕ) : Prop where
  index_pos : 0 < phaseCochromaticMidpointIndex n
  index_mem :
    (phaseCochromaticMidpointIndex n : ℝ) ∈
      Icc
        (phaseRootCenter n -
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)
  signed_le_index :
    phaseSignedFourSizeRootSelected n ≤
      (phaseCochromaticMidpointIndex n : ℝ)
  gap_lower :
    q ^ 2 / 16 * Real.log (200 / 153 : ℝ) * baseScale n ≤
      (phaseCochromaticMidpointIndex n : ℝ) -
        phaseSignedFourSizeRootSelected n
  width_pos : 0 < logLogOrder n * phaseRootGapRadius n
  index_scale_lower :
    q ^ 2 / 16 * Real.log (200 / 153 : ℝ) * baseScale n ≤
      (phaseCochromaticMidpointIndex n : ℝ)

private theorem eventually_phaseCochromaticMidpointIndex_geometry :
    ∀ᶠ n : ℕ in atTop, PhaseCochromaticMidpointGeometry n := by
  let c : ℝ := q ^ 2 / 8 * Real.log (200 / 153 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
      log_200_div_153_pos
  have hLogLogLarge : ∀ᶠ n : ℕ in atTop,
      8 / q ^ 3 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop (8 / q ^ 3)
  have hBaseOne : ∀ᶠ n : ℕ in atTop, 1 ≤ baseScale n :=
    tendsto_baseScale_atTop.eventually_ge_atTop 1
  have hScale :=
    eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower
      0 (by norm_num)
  filter_upwards
    [eventually_selected_phase_roots_separated,
      eventually_phaseSignedFourSizeRootSelected_spec_unique,
      eventually_unrestrictedPhaseRootSelected_spec_unique,
      hLogLogLarge, hBaseOne, hScale] with
      n hGap hSigned hUnrestricted hLogLogLargeN hBaseOneN hScaleN
  let rCo : ℝ := phaseSignedFourSizeRootSelected n
  let rPlus : ℝ := unrestrictedPhaseRootSelected n
  let width : ℝ := logLogOrder n * phaseRootGapRadius n
  let midpoint : ℝ := (rCo + rPlus) / 2
  let z : ℤ := rootCochromaticIndex rCo rPlus
  have hRCoPos : 0 < rCo := hSigned.1.2.1
  have hGap' : c * baseScale n ≤ rPlus - rCo := by
    simpa [c, rPlus, rCo] using hGap
  have hRPlusPos : 0 < rPlus := by
    have hBasePos : 0 < baseScale n :=
      lt_of_lt_of_le (by norm_num) hBaseOneN
    nlinarith [mul_pos hc hBasePos]
  have hScaleAtCenter : q ^ 3 / 8 * baseScale n ≤
      phaseRootGapRadius n := by
    have h := hScaleN (phaseRootCenter n) (by simp)
    simpa [phaseRootGapRadius] using h
  have hQCubePos : 0 < q ^ 3 := pow_pos q_pos 3
  have hCoeffLogLog : 1 ≤ q ^ 3 / 8 * logLogOrder n := by
    rw [div_le_iff₀ hQCubePos] at hLogLogLargeN
    nlinarith
  have hLogLogPos : 0 < logLogOrder n := by
    have : 0 < 8 / q ^ 3 := div_pos (by norm_num) hQCubePos
    linarith
  have hBaseNonneg : 0 ≤ baseScale n :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans hBaseOneN
  have hWidthOne : 1 ≤ width := by
    calc
      1 ≤ baseScale n := hBaseOneN
      _ ≤ (q ^ 3 / 8 * logLogOrder n) * baseScale n :=
        by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hCoeffLogLog hBaseNonneg
      _ = logLogOrder n * (q ^ 3 / 8 * baseScale n) := by ring
      _ ≤ logLogOrder n * phaseRootGapRadius n :=
        mul_le_mul_of_nonneg_left hScaleAtCenter hLogLogPos.le
      _ = width := by rfl
  have hWidthPos : 0 < width := lt_of_lt_of_le (by norm_num) hWidthOne
  have hSignedCoeffLe :
      phaseSignedFourSizeRootCorridorCoefficient ≤
        phaseRootCommonCorridorCoefficient := by
    unfold phaseRootCommonCorridorCoefficient
    linarith [unrestrictedPhaseRootCorridorCoefficient_pos]
  have hUnrestrictedCoeffLe :
      unrestrictedPhaseRootCorridorCoefficient ≤
        phaseRootCommonCorridorCoefficient := by
    unfold phaseRootCommonCorridorCoefficient
    linarith [phaseSignedFourSizeRootCorridorCoefficient_pos]
  have hSignedCommon : rCo ∈ Icc
      (phaseRootCenter n - phaseRootCommonCorridorCoefficient * width)
      (phaseRootCenter n + phaseRootCommonCorridorCoefficient * width) := by
    have hOwn := hSigned.1.1
    rw [mem_Ioo] at hOwn
    rw [mem_Icc]
    dsimp [rCo, width] at hOwn ⊢
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_right hSignedCoeffLe hWidthPos.le]
  have hUnrestrictedCommon : rPlus ∈ Icc
      (phaseRootCenter n - phaseRootCommonCorridorCoefficient * width)
      (phaseRootCenter n + phaseRootCommonCorridorCoefficient * width) := by
    have hOwn := hUnrestricted.1.1
    rw [mem_Ioo] at hOwn
    rw [mem_Icc]
    dsimp [rPlus, width] at hOwn ⊢
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_right hUnrestrictedCoeffLe hWidthPos.le]
  have hMidpointMem : midpoint ∈ Icc
      (phaseRootCenter n - phaseRootCommonCorridorCoefficient * width)
      (phaseRootCenter n + phaseRootCommonCorridorCoefficient * width) := by
    dsimp [midpoint]
    constructor <;> nlinarith [hSignedCommon.1, hSignedCommon.2,
      hUnrestrictedCommon.1, hUnrestrictedCommon.2]
  have hMidpointPos : 0 < midpoint := by
    dsimp [midpoint]
    positivity
  have hZNonneg : 0 ≤ z := by
    dsimp [z, rootCochromaticIndex]
    exact Int.ceil_nonneg hMidpointPos.le
  have hIndexCast : (phaseCochromaticMidpointIndex n : ℝ) = (z : ℝ) := by
    rw [phaseCochromaticMidpointIndex]
    norm_cast
    simpa [z, rCo, rPlus, rootCochromaticIndex] using
      Int.toNat_of_nonneg hZNonneg
  have hMidpointLeZ : midpoint ≤ (z : ℝ) := by
    dsimp [z, rootCochromaticIndex, midpoint]
    exact_mod_cast Int.le_ceil ((rCo + rPlus) / 2)
  have hZLt : (z : ℝ) < midpoint + 1 := by
    dsimp [z, rootCochromaticIndex, midpoint]
    exact Int.ceil_lt_add_one ((rCo + rPlus) / 2)
  have hIndexPos : 0 < phaseCochromaticMidpointIndex n := by
    exact_mod_cast (show (0 : ℝ) < (phaseCochromaticMidpointIndex n : ℝ) by
      rw [hIndexCast]
      exact hMidpointPos.trans_le hMidpointLeZ)
  have hIndexMem : (phaseCochromaticMidpointIndex n : ℝ) ∈
      Icc
        (phaseRootCenter n -
          (phaseRootCommonCorridorCoefficient + 1) * width)
        (phaseRootCenter n +
          (phaseRootCommonCorridorCoefficient + 1) * width) := by
    rw [hIndexCast, mem_Icc]
    constructor
    · nlinarith [hMidpointMem.1, hMidpointLeZ]
    · nlinarith [hMidpointMem.2, hZLt, hWidthOne]
  have hSignedLe : rCo ≤ (phaseCochromaticMidpointIndex n : ℝ) := by
    rw [hIndexCast]
    dsimp [midpoint] at hMidpointLeZ
    nlinarith [hRCoPos, hRPlusPos, hGap']
  have hGapLower : c / 2 * baseScale n ≤
      (phaseCochromaticMidpointIndex n : ℝ) - rCo := by
    rw [hIndexCast]
    dsimp [midpoint] at hMidpointLeZ
    nlinarith [hGap', hMidpointLeZ]
  have hIndexScale : c / 2 * baseScale n ≤
      (phaseCochromaticMidpointIndex n : ℝ) := by
    linarith
  refine
    { index_pos := hIndexPos
      index_mem := ?_
      signed_le_index := ?_
      gap_lower := ?_
      width_pos := ?_
      index_scale_lower := ?_ }
  · simpa [width, mul_assoc] using hIndexMem
  · simpa [rCo] using hSignedLe
  · dsimp [c, rCo] at hGapLower ⊢
    convert hGapLower using 1; ring
  · simpa [width] using hWidthPos
  · dsimp [c] at hIndexScale ⊢
    convert hIndexScale using 1; ring

private theorem tendsto_phaseCochromaticMidpointIndex_real_atTop :
    Tendsto (fun n : ℕ ↦ (phaseCochromaticMidpointIndex n : ℝ))
      atTop atTop := by
  let c : ℝ := q ^ 2 / 16 * Real.log (200 / 153 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
      log_200_div_153_pos
  have hLower : Tendsto (fun n : ℕ ↦ c * baseScale n) atTop atTop :=
    tendsto_baseScale_atTop.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop
    (eventually_phaseCochromaticMidpointIndex_geometry.mono
      fun n hn ↦ by simpa [c] using hn.index_scale_lower)
    hLower

/-- The root-midpoint ceiling eventually satisfies every finite four-size
rounding and optimizer condition required by the exact factorial bridge. -/
theorem eventually_phaseCochromaticMidpointIndex_rounding_admissible :
    ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (phaseCochromaticMidpointIndex n) := by
  let C : ℝ := phaseRootCommonCorridorCoefficient + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [phaseRootCommonCorridorCoefficient_pos]
  obtain ⟨c, hc, hCompact⟩ :=
    exists_pos_eventually_phaseRootLogLogCorridor_fourSize_compact_control C hC
  have hControl := hCompact 1 (by norm_num)
  have hLarge : ∀ᶠ n : ℕ in atTop,
      14 / c ≤ (phaseCochromaticMidpointIndex n : ℝ) :=
    tendsto_phaseCochromaticMidpointIndex_real_atTop.eventually_ge_atTop
      (14 / c)
  have hDomain := eventually_phaseRootLogLogCorridor_fourSize_domain C hC
  filter_upwards
    [eventually_phaseCochromaticMidpointIndex_geometry,
      eventually_five_lt_phaseNat, hControl, hLarge, hDomain] with
      n hGeom hPhase hControlN hLargeN hDomainN
  let K : ℕ := phaseCochromaticMidpointIndex n
  have hKMem : (K : ℝ) ∈ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    simpa [K, C] using hGeom.index_mem
  obtain ⟨hKPosReal, hTarget⟩ := hDomainN (K : ℝ) hKMem
  have hKPos : 0 < K := by simpa [K] using hGeom.index_pos
  have hnReal : (n : ℝ) < (phaseNat n : ℝ) * (K : ℝ) := by
    rw [fourSizeTarget, mem_Ioo] at hTarget
    have hnDiv : (n : ℝ) / (K : ℝ) < (phaseNat n : ℝ) := by
      linarith [hTarget.1]
    exact (div_lt_iff₀ hKPosReal).mp hnDiv
  have hn : n ≤ phaseNat n * K := by
    have hnNat : n < phaseNat n * K := by exact_mod_cast hnReal
    exact hnNat.le
  refine ⟨hPhase, hKPos, hn, hTarget, ?_⟩
  intro i
  have hOpt := (hControlN (K : ℝ) hKMem).2 i
  have hScaled : (14 : ℝ) ≤ (K : ℝ) * c := by
    have := mul_le_mul_of_nonneg_right hLargeN hc.le
    calc
      (14 : ℝ) = (14 / c) * c := by field_simp [hc.ne']
      _ ≤ (K : ℝ) * c := this
  have hKNonneg : (0 : ℝ) ≤ K := by positivity
  exact hScaled.trans (mul_le_mul_of_nonneg_left hOpt hKNonneg)

private theorem eventually_signedFourFiniteFirstMomentErrorBound_le_phaseNat_sq :
    ∀ᶠ n : ℕ in atTop,
      signedFourFiniteFirstMomentErrorBound n ≤ (phaseNat n : ℝ) ^ 2 := by
  have hRatio : ∀ᶠ n : ℕ in atTop,
      factorialLogErrorBound n / logOrder n < 2 :=
    factorialLogErrorBound_div_logOrder_tendsto_one.eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards
    [hRatio, tendsto_logOrder_atTop.eventually_ge_atTop 30,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hRatioN hLog hPhase
  have hLogPos : 0 < logOrder n := lt_of_lt_of_le (by norm_num) hLog
  have hFac : factorialLogErrorBound n < 2 * logOrder n := by
    exact (div_lt_iff₀ hLogPos).mp hRatioN
  have hPhaseSq : (logOrder n) ^ 2 ≤ (phaseNat n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hLogPos.le hPhase.1 2
  unfold signedFourFiniteFirstMomentErrorBound
  nlinarith [sq_nonneg (logOrder n - 30)]

private theorem phase_midpoint_partialSignedFirstMoment_log_tendsto_atTop :
    Tendsto
      (fun n : ℕ ↦
        Real.log
          (partialSignedFirstMoment n
            (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n))))
      atTop atTop := by
  let C : ℝ := phaseRootCommonCorridorCoefficient + 1
  let c : ℝ := q ^ 2 / 16 * Real.log (200 / 153 : ℝ)
  let d : ℝ := q / 8 * c
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [phaseRootCommonCorridorCoefficient_pos]
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
      log_200_div_153_pos
  have hd : 0 < d := mul_pos (div_pos q_pos (by norm_num)) hc
  have hLowerTendsto :
      Tendsto (fun n : ℕ ↦ d / 2 * baseScale n) atTop atTop :=
    tendsto_baseScale_atTop.const_mul_atTop (div_pos hd (by norm_num))
  have hBaseLarge : ∀ᶠ n : ℕ in atTop, 2 / d ≤ baseScale n :=
    tendsto_baseScale_atTop.eventually_ge_atTop (2 / d)
  have hDomain := eventually_phaseRootLogLogCorridor_fourSize_domain C hC
  have hDeriv :=
    eventually_signedFourSizeObjectiveDerivative_logLogCorridor_lower C hC
  apply tendsto_atTop_mono' atTop ?_ hLowerTendsto
  filter_upwards
    [eventually_phaseCochromaticMidpointIndex_geometry,
      eventually_phaseSignedFourSizeRootSelected_spec_unique,
      eventually_phaseCochromaticMidpointIndex_rounding_admissible,
      eventually_abs_midpointPartialSignedFirstMomentLogError_le
        phaseNat phaseCochromaticMidpointIndex
          eventually_phaseCochromaticMidpointIndex_rounding_admissible,
      eventually_signedFourFiniteFirstMomentErrorBound_le_phaseNat_sq,
      eventually_five_lt_phaseNat, hBaseLarge, hDomain, hDeriv] with
      n hGeom hRoot hAdmissible hError hErrorSq hPhase hBaseLargeN
        hDomainN hDerivN
  let r : ℝ := phaseSignedFourSizeRootSelected n
  let K : ℝ := phaseCochromaticMidpointIndex n
  let F : ℝ → ℝ := signedFourSizeObjective n (phaseNat n)
  have hRMem : r ∈ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    have hOwn := hRoot.1.1
    have hWidthNonneg : 0 ≤ logLogOrder n * phaseRootGapRadius n :=
      hGeom.width_pos.le
    have hCoeff : phaseSignedFourSizeRootCorridorCoefficient ≤ C := by
      dsimp [C, phaseRootCommonCorridorCoefficient]
      linarith [unrestrictedPhaseRootCorridorCoefficient_pos]
    rw [mem_Ioo] at hOwn
    rw [mem_Icc]
    dsimp [r]
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_right hCoeff hWidthNonneg]
  have hKMem : K ∈ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    simpa [K, C] using hGeom.index_mem
  have hRK : r ≤ K := by simpa [r, K] using hGeom.signed_le_index
  have hInterval : Icc r K ⊆ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    intro x hx
    exact ⟨hRMem.1.trans hx.1, hx.2.trans hKMem.2⟩
  have hHasDeriv : ∀ x ∈ Icc r K,
      HasDerivAt F
        (signedFourSizeObjectiveDerivative n (phaseNat n) x) x := by
    intro x hx
    obtain ⟨hxPos, hTarget⟩ := hDomainN x (hInterval hx)
    exact hasDerivAt_phaseSignedFourSizeObjective n hxPos hTarget
  have hCont : ContinuousOn F (Icc r K) := by
    intro x hx
    exact (hHasDeriv x hx).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ F (Ioo r K) := by
    intro x hx
    exact (hHasDeriv x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hLower : ∀ x ∈ Ioo r K,
      q / 8 * (phaseNat n : ℝ) ^ 2 ≤ deriv F x := by
    intro x hx
    rw [(hHasDeriv x (Ioo_subset_Icc_self hx)).deriv]
    exact hDerivN x (hInterval (Ioo_subset_Icc_self hx))
  have hIncrement := derivative_lower_bound_mul_sub_le_sub
    hRK hCont hDiff hLower
  have hRootZero : F r = 0 := by
    simpa [F, r, IsPhaseSignedFourSizeRoot, isSignedFourSizeRoot_iff] using
      hRoot.1.2.2.2
  have hSlopeNonneg : 0 ≤ q / 8 * (phaseNat n : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg q_pos.le (by norm_num)) (sq_nonneg _)
  have hGap : c * baseScale n ≤ K - r := by
    simpa [c, K, r] using hGeom.gap_lower
  have hRaw : d * (phaseNat n : ℝ) ^ 2 * baseScale n ≤ F K := by
    have hScaledGap := mul_le_mul_of_nonneg_left hGap hSlopeNonneg
    rw [hRootZero] at hIncrement
    dsimp [d]
    nlinarith
  have hBaseProduct : 2 ≤ d * baseScale n := by
    calc
      (2 : ℝ) = d * (2 / d) := by field_simp [hd.ne']
      _ ≤ d * baseScale n :=
        mul_le_mul_of_nonneg_left hBaseLargeN hd.le
  have hPhaseSqOne : (1 : ℝ) ≤ (phaseNat n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ phaseNat n := by exact_mod_cast (show 1 ≤ phaseNat n by omega)
    nlinarith
  have hLogLower :
      F K - signedFourFiniteFirstMomentErrorBound n ≤
        Real.log
          (partialSignedFirstMoment n
            (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n))) := by
    rw [abs_le] at hError
    dsimp [midpointPartialSignedFirstMomentLogError] at hError
    dsimp [F, K]
    linarith [hError.1]
  have hMain : d / 2 * baseScale n ≤
      (phaseNat n : ℝ) ^ 2 * (d * baseScale n - 1) := by
    have hHalf : d / 2 * baseScale n ≤ d * baseScale n - 1 := by
      nlinarith
    have hNonneg : 0 ≤ d * baseScale n - 1 := by linarith
    exact hHalf.trans
      (le_mul_of_one_le_left hNonneg hPhaseSqOne)
  calc
    d / 2 * baseScale n ≤
        (phaseNat n : ℝ) ^ 2 * (d * baseScale n - 1) := hMain
    _ = d * (phaseNat n : ℝ) ^ 2 * baseScale n -
          (phaseNat n : ℝ) ^ 2 := by ring
    _ ≤ F K - signedFourFiniteFirstMomentErrorBound n :=
      sub_le_sub hRaw hErrorSq
    _ ≤ Real.log
          (partialSignedFirstMoment n
            (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n))) := hLogLower

/-- The complete signed first moment of the canonical midpoint profile tends
to infinity. -/
theorem phase_midpoint_completeSignedFirstMoment_tendsto_atTop :
    Tendsto
      (fun n =>
        completeSignedFirstMoment
          (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)))
      atTop atTop := by
  have hExp := Real.tendsto_exp_atTop.comp
    phase_midpoint_partialSignedFirstMoment_log_tendsto_atTop
  have hPartial :
      Tendsto
        (fun n : ℕ ↦
          partialSignedFirstMoment n
            (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)))
        atTop atTop := by
    apply hExp.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      simp only [Function.comp_apply]
      rw [Real.exp_log (partialSignedFirstMoment_pos _ _ _)]
  apply hPartial.congr'
  filter_upwards
    [eventually_phaseCochromaticMidpointIndex_rounding_admissible] with
      n hAdmissible
  unfold completeSignedFirstMoment residualVertexMass selectedVertexMass
  have hSize : midpointPartialDiagonalSize (phaseNat n) =
      fun i : Fin 4 => phaseNat n - fourDeficit i := by rfl
  rw [hSize, midpointMultiplicity_vertexMass n (phaseNat n)
    (phaseCochromaticMidpointIndex n) hAdmissible]

#print axioms eventually_phaseCochromaticMidpointIndex_rounding_admissible
#print axioms phase_midpoint_completeSignedFirstMoment_tendsto_atTop

end

end Erdos625
