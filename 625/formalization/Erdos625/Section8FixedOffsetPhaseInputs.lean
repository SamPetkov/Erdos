import Erdos625.Section8ConcretePhaseInputs
import Erdos625.PhaseSelectedRootSeparationSharp
import Erdos625.RootSeparationFixedOffsetRounding
import Erdos625.PhaseSignedFourSizeTargetTransport
import Erdos625.PhaseSignedFourSizeLogLogCorridorDomain
import Erdos625.PhaseRootLogLogCorridorScale
import Erdos625.Section11AsymptoticAssembly
import Mathlib.Tactic

/-!
# Fixed-offset phase inputs

The manuscript cocolouring selector is the integer `⌈r_co⌉ + 16` attached to the
selected signed four-size root `r_co`.  This module transports that selector to
the natural numbers, records its exact real cast bounds, places it (and the
whole segment joining it to `r_co`) inside one widened logarithmic-logarithmic
corridor about `phaseRootCenter`, checks the four-size target control at the
selector, and finally combines the sharp real root separation with the
fixed-offset rounding budget into a strict natural-number root-gap bridge.

Nothing here touches the first-moment, partial-diagonal, skeleton, seed,
amplification, or final assembly layers.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The manuscript cocolouring selector `⌈r_co⌉ + 16`, transported to the
natural numbers. -/
noncomputable def phaseCochromaticFixedOffsetIndex (n : ℕ) : ℕ :=
  (rootCochromaticFixedOffsetIndex
    (phaseSignedFourSizeRootSelected n)).toNat

private theorem tendsto_baseScale_atTop_fixedOffset :
    Tendsto baseScale atTop atTop := by
  exact tendsto_baseScale_atTop_unscaled

/-- The exact geometry of the fixed-offset selector: it is a positive natural
number, its real cast sits in `[r_co + 16, r_co + 17)`, and the entire segment
from the selected signed root to the selector stays inside the widened
logarithmic-logarithmic corridor with coefficient
`phaseRootCommonCorridorCoefficient + 1`. -/
structure PhaseFixedOffsetCorridorGeometry (n : ℕ) : Prop where
  index_pos : 0 < phaseCochromaticFixedOffsetIndex n
  index_lower :
    phaseSignedFourSizeRootSelected n + 16 ≤
      (phaseCochromaticFixedOffsetIndex n : ℝ)
  index_upper :
    (phaseCochromaticFixedOffsetIndex n : ℝ) <
      phaseSignedFourSizeRootSelected n + 17
  index_mem :
    (phaseCochromaticFixedOffsetIndex n : ℝ) ∈
      Icc
        (phaseRootCenter n -
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)
  segment_mem :
    ∀ x ∈ Icc (phaseSignedFourSizeRootSelected n)
        (phaseCochromaticFixedOffsetIndex n : ℝ),
      x ∈ Icc
        (phaseRootCenter n -
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)

/-- The fixed-offset selector eventually realises the full corridor geometry. -/
theorem eventually_phaseFixedOffsetCorridorGeometry :
    ∀ᶠ n : ℕ in atTop, PhaseFixedOffsetCorridorGeometry n := by
  have hLogLogLarge : ∀ᶠ n : ℕ in atTop, 8 / q ^ 3 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop (8 / q ^ 3)
  have hBaseLarge : ∀ᶠ n : ℕ in atTop, (17 : ℝ) ≤ baseScale n :=
    tendsto_baseScale_atTop_fixedOffset.eventually_ge_atTop 17
  have hScale :=
    eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower
      0 (by norm_num)
  filter_upwards
    [eventually_phaseSignedFourSizeRootSelected_spec_unique,
      hLogLogLarge, hBaseLarge, hScale] with
      n hSigned hLogLogLargeN hBaseLargeN hScaleN
  set rCo : ℝ := phaseSignedFourSizeRootSelected n with hrCo
  set width : ℝ := logLogOrder n * phaseRootGapRadius n with hwidth
  set z : ℤ := rootCochromaticFixedOffsetIndex rCo with hz
  have hRCoPos : 0 < rCo := hSigned.1.2.1
  have hScaleAtCenter : q ^ 3 / 8 * baseScale n ≤ phaseRootGapRadius n := by
    have h := hScaleN (phaseRootCenter n) (by simp)
    simpa [phaseRootGapRadius] using h
  have hQCubePos : 0 < q ^ 3 := pow_pos q_pos 3
  have hCoeffLogLog : 1 ≤ q ^ 3 / 8 * logLogOrder n := by
    rw [div_le_iff₀ hQCubePos] at hLogLogLargeN
    nlinarith
  have hLogLogPos : 0 < logLogOrder n := by
    have : 0 < 8 / q ^ 3 := div_pos (by norm_num) hQCubePos
    linarith
  have hBaseNonneg : (0 : ℝ) ≤ baseScale n := by linarith
  have hWidthLarge : (17 : ℝ) ≤ width := by
    calc
      (17 : ℝ) ≤ baseScale n := hBaseLargeN
      _ ≤ (q ^ 3 / 8 * logLogOrder n) * baseScale n := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hCoeffLogLog hBaseNonneg
      _ = logLogOrder n * (q ^ 3 / 8 * baseScale n) := by ring
      _ ≤ logLogOrder n * phaseRootGapRadius n :=
        mul_le_mul_of_nonneg_left hScaleAtCenter hLogLogPos.le
      _ = width := by rw [hwidth]
  have hWidthPos : (0 : ℝ) < width := by linarith
  have hSignedCoeffLe :
      phaseSignedFourSizeRootCorridorCoefficient ≤
        phaseRootCommonCorridorCoefficient := by
    unfold phaseRootCommonCorridorCoefficient
    linarith [unrestrictedPhaseRootCorridorCoefficient_pos]
  have hSignedCommon : rCo ∈ Icc
      (phaseRootCenter n - phaseRootCommonCorridorCoefficient * width)
      (phaseRootCenter n + phaseRootCommonCorridorCoefficient * width) := by
    have hOwn := hSigned.1.1
    rw [mem_Ioo] at hOwn
    rw [mem_Icc]
    rw [hrCo, hwidth] at *
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_right hSignedCoeffLe hWidthPos.le]
  -- the selector is a nonnegative integer, so the `Int.toNat` transport is exact
  have hZNonneg : 0 ≤ z := by
    rw [hz, rootCochromaticFixedOffsetIndex]
    have := Int.ceil_nonneg hRCoPos.le
    omega
  have hIndexCast : (phaseCochromaticFixedOffsetIndex n : ℝ) = (z : ℝ) := by
    rw [phaseCochromaticFixedOffsetIndex]
    norm_cast
    simpa [hz, hrCo] using Int.toNat_of_nonneg hZNonneg
  have hLower : rCo + 16 ≤ (z : ℝ) := by
    rw [hz, rootCochromaticFixedOffsetIndex]
    push_cast
    linarith [Int.le_ceil rCo]
  have hUpper : (z : ℝ) < rCo + 17 := by
    rw [hz, rootCochromaticFixedOffsetIndex]
    push_cast
    linarith [Int.ceil_lt_add_one rCo]
  have hIndexPos : 0 < phaseCochromaticFixedOffsetIndex n := by
    have hpos : (0 : ℝ) < (phaseCochromaticFixedOffsetIndex n : ℝ) := by
      rw [hIndexCast]
      linarith
    exact_mod_cast hpos
  have hIndexMem : (phaseCochromaticFixedOffsetIndex n : ℝ) ∈
      Icc
        (phaseRootCenter n -
          (phaseRootCommonCorridorCoefficient + 1) * width)
        (phaseRootCenter n +
          (phaseRootCommonCorridorCoefficient + 1) * width) := by
    rw [hIndexCast, mem_Icc]
    constructor
    · nlinarith [hSignedCommon.1, hSignedCommon.2]
    · nlinarith [hSignedCommon.2]
  refine
    { index_pos := hIndexPos
      index_lower := ?_
      index_upper := ?_
      index_mem := ?_
      segment_mem := ?_ }
  · rw [hIndexCast]
    linarith
  · rw [hIndexCast]
    linarith
  · simpa [hwidth, mul_assoc] using hIndexMem
  · intro x hx
    rw [mem_Icc] at hx
    have hmem := hIndexMem
    rw [mem_Icc] at hmem
    rw [mem_Icc]
    constructor
    · have : phaseRootCenter n -
          (phaseRootCommonCorridorCoefficient + 1) * width ≤ rCo := by
        nlinarith [hSignedCommon.1]
      calc
        phaseRootCenter n -
            (phaseRootCommonCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n
            = phaseRootCenter n -
              (phaseRootCommonCorridorCoefficient + 1) * width := by
          rw [hwidth]; ring
        _ ≤ rCo := this
        _ ≤ x := hx.1
    · calc
        x ≤ (phaseCochromaticFixedOffsetIndex n : ℝ) := hx.2
        _ ≤ phaseRootCenter n +
              (phaseRootCommonCorridorCoefficient + 1) * width := hmem.2
        _ = phaseRootCenter n +
              (phaseRootCommonCorridorCoefficient + 1) *
                logLogOrder n * phaseRootGapRadius n := by
          rw [hwidth]; ring

/-- The natural-number fixed-offset selector is eventually positive and its
real cast is exactly the manuscript window `[r_co + 16, r_co + 17)`. -/
theorem eventually_phaseCochromaticFixedOffsetIndex_cast_bounds :
    ∀ᶠ n : ℕ in atTop,
      0 < phaseCochromaticFixedOffsetIndex n ∧
      phaseSignedFourSizeRootSelected n + 16 ≤
        (phaseCochromaticFixedOffsetIndex n : ℝ) ∧
      (phaseCochromaticFixedOffsetIndex n : ℝ) <
        phaseSignedFourSizeRootSelected n + 17 := by
  filter_upwards [eventually_phaseFixedOffsetCorridorGeometry] with n hn
  exact ⟨hn.index_pos, hn.index_lower, hn.index_upper⟩

/-- The fixed-offset selector eventually lies in the widened common
logarithmic-logarithmic corridor about `phaseRootCenter`. -/
theorem eventually_phaseCochromaticFixedOffsetIndex_mem_logLogCorridor :
    ∀ᶠ n : ℕ in atTop,
      (phaseCochromaticFixedOffsetIndex n : ℝ) ∈
        Icc
          (phaseRootCenter n -
            (phaseRootCommonCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            (phaseRootCommonCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n) := by
  filter_upwards [eventually_phaseFixedOffsetCorridorGeometry] with n hn
  exact hn.index_mem

/-- The whole segment from the selected signed four-size root to the
fixed-offset selector eventually stays inside the same widened corridor. -/
theorem eventually_phaseFixedOffsetSegment_subset_logLogCorridor :
    ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ Icc (phaseSignedFourSizeRootSelected n)
          (phaseCochromaticFixedOffsetIndex n : ℝ),
        x ∈ Icc
          (phaseRootCenter n -
            (phaseRootCommonCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            (phaseRootCommonCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n) := by
  filter_upwards [eventually_phaseFixedOffsetCorridorGeometry] with n hn
  exact hn.segment_mem

/-- Four-size target control at the fixed-offset selector: the target is
eventually inside the open support `(2, 5)` and bounded by `4`. -/
theorem eventually_phaseCochromaticFixedOffsetIndex_target_control :
    ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n)
        (phaseCochromaticFixedOffsetIndex n : ℝ) ∈ Set.Ioo (2 : ℝ) 5 ∧
      fourSizeTarget n (phaseNat n)
        (phaseCochromaticFixedOffsetIndex n : ℝ) ≤ 4 := by
  set C : ℝ := phaseRootCommonCorridorCoefficient + 1 with hC
  have hCNonneg : 0 ≤ C := by
    rw [hC]
    linarith [phaseRootCommonCorridorCoefficient_pos]
  have hClose :=
    eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center
      C hCNonneg (1 / 20) (by norm_num)
  have hDomain :=
    eventually_phaseRootLogLogCorridor_fourSize_domain C hCNonneg
  filter_upwards
    [eventually_phaseFixedOffsetCorridorGeometry, eventually_phaseDomain,
      hClose, hDomain] with n hGeom hPhaseDomain hCloseN hDomainN
  have hMem : (phaseCochromaticFixedOffsetIndex n : ℝ) ∈
      Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    simpa only [hC] using hGeom.index_mem
  refine ⟨(hDomainN _ hMem).2, ?_⟩
  have hTargetEq := phaseRootDeficitTarget_eq hPhaseDomain
  have hqLower : (20 / 29 : ℝ) < q :=
    (by norm_num : (20 / 29 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hTwoDiv : 2 / q < (29 / 10 : ℝ) := by
    rw [div_lt_iff₀ q_pos]
    nlinarith
  have hCenter : phaseRootDeficitTarget n < (39 / 10 : ℝ) := by
    rw [hTargetEq]
    linarith [phaseDelta_nonneg n]
  have hAt := hCloseN (phaseCochromaticFixedOffsetIndex n : ℝ) hMem
  rw [abs_lt] at hAt
  linarith [hAt.2]

/-- The strict natural-number root-gap bridge for the fixed-offset selector:
the sharp real separation coefficient survives the fixed offset and all integer
rounding, at the cost of the negligible `fixedOffsetRoundingBudget`. -/
theorem exists_eventually_concrete_phase_fixedOffset_root_gap :
    ∃ c : ℝ,
      q ^ 2 / 4 * Real.log (200 / 153 : ℝ) < c ∧
      ∀ᶠ n : ℕ in atTop,
        (c - fixedOffsetRoundingBudget n) * baseScale n ≤
          (phaseChromaticLowerIndex n : ℝ) -
            (phaseCochromaticFixedOffsetIndex n : ℝ) := by
  obtain ⟨c, hcGt, hcGap⟩ := exists_phaseRootGapCoefficient_gt_uniformQuarter
  have hcPos : 0 < c := by
    have : 0 < q ^ 2 / 4 * Real.log (200 / 153 : ℝ) :=
      mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
        log_200_div_153_pos
    linarith
  refine ⟨c, hcGt, ?_⟩
  have hBudgetLt : ∀ᶠ n : ℕ in atTop, fixedOffsetRoundingBudget n < c :=
    fixedOffset_rounding_budget_spec.1.eventually (Iio_mem_nhds hcPos)
  have hBasePos : ∀ᶠ n : ℕ in atTop, 0 < baseScale n :=
    tendsto_baseScale_atTop_fixedOffset.eventually_gt_atTop 0
  filter_upwards
    [hcGap, eventually_phaseSignedFourSizeRootSelected_spec_unique,
      fixedOffset_rounding_budget_spec.2, hBudgetLt, hBasePos] with
      n hGap hSigned hRounding hBudget hBase
  set rCo : ℝ := phaseSignedFourSizeRootSelected n with hrCo
  set rPlus : ℝ := unrestrictedPhaseRootSelected n with hrPlus
  have hRCoPos : 0 < rCo := hSigned.1.2.1
  have hRounding' : Real.log (n : ℝ) + 19 ≤
      fixedOffsetRoundingBudget n * baseScale n := by
    simpa [baseScale] using hRounding
  have hBudgetMul :
      fixedOffsetRoundingBudget n * baseScale n ≤ c * baseScale n :=
    mul_le_mul_of_nonneg_right hBudget.le hBase.le
  have hGap' : c * baseScale n ≤ rPlus - rCo := hGap
  have hRPlusLarge : Real.log (n : ℝ) + 19 < rPlus := by linarith
  -- both integer selectors are eventually nonnegative
  have hChromaticNonneg :
      0 ≤ rootChromaticIndex rPlus (Real.log (n : ℝ)) := by
    unfold rootChromaticIndex
    rw [sub_nonneg]
    apply Int.le_floor.mpr
    have hCeil := Int.ceil_lt_add_one (Real.log (n : ℝ))
    exact (hCeil.trans (by linarith)).le
  have hCochromaticNonneg :
      0 ≤ rootCochromaticFixedOffsetIndex rCo := by
    unfold rootCochromaticFixedOffsetIndex
    have := Int.ceil_nonneg hRCoPos.le
    omega
  have hRounded := root_fixedOffset_rounding_gap_toNat
    rPlus rCo (Real.log (n : ℝ)) c (baseScale n)
      (fixedOffsetRoundingBudget n) hGap' hRounding
      hChromaticNonneg hCochromaticNonneg
  simpa [phaseChromaticLowerIndex, phaseCochromaticFixedOffsetIndex,
    hrPlus, hrCo, sub_mul] using hRounded

#print axioms phaseCochromaticFixedOffsetIndex
#print axioms eventually_phaseFixedOffsetCorridorGeometry
#print axioms eventually_phaseCochromaticFixedOffsetIndex_cast_bounds
#print axioms eventually_phaseCochromaticFixedOffsetIndex_mem_logLogCorridor
#print axioms eventually_phaseFixedOffsetSegment_subset_logLogCorridor
#print axioms eventually_phaseCochromaticFixedOffsetIndex_target_control
#print axioms exists_eventually_concrete_phase_fixedOffset_root_gap

end

end Erdos625
