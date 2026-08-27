import Erdos625.Section8ConcretePhaseInputs
import Erdos625.ColoringProfilePhaseCenteredEnvelope
import Erdos625.PhaseUnrestrictedLogLogCorridorDerivativeLower
import Erdos625.PhaseRootLogLogCorridorScale
import Erdos625.ProfileCorridorTools
import Mathlib.Tactic

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

private theorem eventually_phaseChromaticLowerIndex_geometry :
    ∀ᶠ n : ℕ in atTop,
      0 < phaseChromaticLowerIndex n ∧
      phaseChromaticLowerIndex n ≤ n ∧
      (phaseChromaticLowerIndex n : ℝ) ∈
        Icc
          (phaseRootCenter n -
            (unrestrictedPhaseRootCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            (unrestrictedPhaseRootCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n) ∧
      logOrder n ≤ unrestrictedPhaseRootSelected n -
        (phaseChromaticLowerIndex n : ℝ) ∧
      0 < logLogOrder n * phaseRootGapRadius n := by
  let c : ℝ := q ^ 2 / 8 * Real.log (200 / 153 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
      log_200_div_153_pos
  have hBudgetLt : ∀ᶠ n : ℕ in atTop, rootRoundingBudget n < c :=
    root_rounding_budget_spec.1.eventually (Iio_mem_nhds hc)
  have hBudgetOne : ∀ᶠ n : ℕ in atTop, rootRoundingBudget n ≤ 1 :=
    (root_rounding_budget_spec.1.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hn ↦ hn.le)
  have hLogLogLarge : ∀ᶠ n : ℕ in atTop,
      8 / q ^ 3 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop (8 / q ^ 3)
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hBasePos : ∀ᶠ n : ℕ in atTop, 0 < baseScale n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
    rw [baseScale]
    exact div_pos (Nat.cast_pos.mpr (by omega))
      (pow_pos (Real.log_pos hnReal) 3)
  have hScale :=
    eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower
      0 (by norm_num)
  filter_upwards
    [eventually_selected_phase_roots_separated,
      eventually_phaseSignedFourSizeRootSelected_spec_unique,
      eventually_unrestrictedPhaseRootSelected_spec_unique,
      eventually_phaseRootLogLogCorridor_fourSize_domain
        unrestrictedPhaseRootCorridorCoefficient
        unrestrictedPhaseRootCorridorCoefficient_pos.le,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_five_lt_phaseNat,
      root_rounding_budget_spec.2, hBudgetLt, hBudgetOne,
      hLogLogLarge, hLogPos, hBasePos, hScale] with
      n hGap hSigned hUnrestricted hRootDomain hPhase hPhaseLarge hRounding
        hBudgetLtN hBudgetOneN hLogLogLargeN hLogPosN hBasePosN hScaleN
  let rCo : ℝ := phaseSignedFourSizeRootSelected n
  let rPlus : ℝ := unrestrictedPhaseRootSelected n
  let L : ℝ := logOrder n
  let width : ℝ := logLogOrder n * phaseRootGapRadius n
  let z : ℤ := rootChromaticIndex rPlus L
  have hRCoPos : 0 < rCo := hSigned.1.2.1
  have hRootMem : rPlus ∈ Ioo
      (phaseRootCenter n -
        unrestrictedPhaseRootCorridorCoefficient * width)
      (phaseRootCenter n +
        unrestrictedPhaseRootCorridorCoefficient * width) := by
    simpa [rPlus, width, mul_assoc] using hUnrestricted.1.1
  have hRPlusDomain : 0 < rPlus ∧
      fourSizeTarget n (phaseNat n) rPlus ∈ Ioo (2 : ℝ) 5 := by
    have hRootMemClosed : rPlus ∈ Icc
        (phaseRootCenter n -
          unrestrictedPhaseRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          unrestrictedPhaseRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n) := by
      simpa [width, mul_assoc] using
        (show rPlus ∈ Icc
          (phaseRootCenter n -
            unrestrictedPhaseRootCorridorCoefficient * width)
          (phaseRootCenter n +
            unrestrictedPhaseRootCorridorCoefficient * width) from
          ⟨hRootMem.1.le, hRootMem.2.le⟩)
    simpa [rPlus, width, mul_assoc] using hRootDomain rPlus
      hRootMemClosed
  have hGap' : c * baseScale n ≤ rPlus - rCo := by
    simpa [c, rPlus, rCo] using hGap
  have hBudgetMul :
      rootRoundingBudget n * baseScale n ≤ c * baseScale n :=
    mul_le_mul_of_nonneg_right hBudgetLtN.le hBasePosN.le
  have hRounding' : L + 3 ≤ rootRoundingBudget n * baseScale n := by
    simpa [L, logOrder, baseScale] using hRounding
  have hRPlusLarge : L + 3 < rPlus := by
    linarith
  have hZrealPos : (0 : ℝ) < (z : ℝ) := by
    have hFloor := Int.lt_floor_add_one rPlus
    have hCeil := Int.ceil_lt_add_one L
    dsimp [z, rootChromaticIndex]
    push_cast
    linarith
  have hZpos : 0 < z := by exact_mod_cast hZrealPos
  have hIndexCast : (phaseChromaticLowerIndex n : ℝ) = (z : ℝ) := by
    rw [phaseChromaticLowerIndex]
    norm_cast
    simpa [z, rPlus, L, logOrder] using Int.toNat_of_nonneg hZpos.le
  have hIndexPos : 0 < phaseChromaticLowerIndex n := by
    exact_mod_cast (show (0 : ℝ) < (phaseChromaticLowerIndex n : ℝ) by
      rw [hIndexCast]
      exact hZrealPos)
  have hRPlusLtN : rPlus < (n : ℝ) := by
    have hTarget := hRPlusDomain.2
    rw [fourSizeTarget, mem_Ioo] at hTarget
    have hSix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast hPhaseLarge
    have hOneLt : (1 : ℝ) < (n : ℝ) / rPlus := by linarith
    rw [lt_div_iff₀ hRPlusDomain.1] at hOneLt
    simpa using hOneLt
  have hIndexLtNReal : (phaseChromaticLowerIndex n : ℝ) < (n : ℝ) := by
    rw [hIndexCast]
    calc
      (z : ℝ) ≤ (⌊rPlus⌋ : ℤ) := by
        dsimp [z, rootChromaticIndex]
        push_cast
        have hceil : (0 : ℤ) ≤ ⌈L⌉ := Int.ceil_nonneg hLogPosN.le
        exact_mod_cast (sub_le_self (⌊rPlus⌋ : ℤ) hceil)
      _ ≤ rPlus := Int.floor_le rPlus
      _ < (n : ℝ) := hRPlusLtN
  have hIndexLe : phaseChromaticLowerIndex n ≤ n := by
    exact_mod_cast hIndexLtNReal.le
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
  have hBudgetWidth :
      rootRoundingBudget n * baseScale n ≤ width := by
    calc
      rootRoundingBudget n * baseScale n ≤
          (q ^ 3 / 8 * logLogOrder n) * baseScale n :=
        mul_le_mul_of_nonneg_right
          (hBudgetOneN.trans hCoeffLogLog) hBasePosN.le
      _ = logLogOrder n * (q ^ 3 / 8 * baseScale n) := by ring
      _ ≤ logLogOrder n * phaseRootGapRadius n :=
        mul_le_mul_of_nonneg_left hScaleAtCenter hLogLogPos.le
      _ = width := by rfl
  have hWidthPays : L + 3 ≤ width := hRounding'.trans hBudgetWidth
  have hFloorLower : rPlus - 1 < (⌊rPlus⌋ : ℤ) := by
    linarith [Int.lt_floor_add_one rPlus]
  have hCeilUpper : (⌈L⌉ : ℤ) < L + 1 := Int.ceil_lt_add_one L
  have hZLower : rPlus - L - 2 < (z : ℝ) := by
    dsimp [z, rootChromaticIndex]
    push_cast
    linarith
  have hZUpper : (z : ℝ) ≤ rPlus := by
    dsimp [z, rootChromaticIndex]
    push_cast
    have hceil : (0 : ℝ) ≤ (⌈L⌉ : ℤ) := by
      exact_mod_cast Int.ceil_nonneg hLogPosN.le
    linarith [Int.floor_le rPlus]
  have hIndexCorridor : (phaseChromaticLowerIndex n : ℝ) ∈
      Icc
        (phaseRootCenter n -
          (unrestrictedPhaseRootCorridorCoefficient + 1) * width)
        (phaseRootCenter n +
          (unrestrictedPhaseRootCorridorCoefficient + 1) * width) := by
    rw [hIndexCast, mem_Icc]
    constructor
    · nlinarith [hRootMem.1]
    · nlinarith [hRootMem.2, hZUpper]
  have hDisplacement : L ≤ rPlus - (phaseChromaticLowerIndex n : ℝ) := by
    rw [hIndexCast]
    dsimp [z, rootChromaticIndex]
    push_cast
    linarith [Int.floor_le rPlus, Int.le_ceil L]
  have hWidthPos : 0 < width := hLogPosN.trans_le (by linarith [hWidthPays])
  exact ⟨hIndexPos, hIndexLe,
    by simpa [width, mul_assoc] using hIndexCorridor,
    by simpa [L, rPlus] using hDisplacement,
    by simpa [width] using hWidthPos⟩

theorem eventually_phaseChromaticLowerIndex_pos_and_le :
    ∀ᶠ n : ℕ in atTop,
      0 < phaseChromaticLowerIndex n ∧ phaseChromaticLowerIndex n ≤ n :=
  eventually_phaseChromaticLowerIndex_geometry.mono
    (fun _ hn ↦ ⟨hn.1, hn.2.1⟩)

private theorem eventually_profileBoxTerm_le_q_div_sixteen_logOrder_cubed :
    ∀ᶠ n : ℕ in atTop,
      (((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)) ≤
        q / 16 * (logOrder n) ^ 3 := by
  have hLogLarge : ∀ᶠ n : ℕ in atTop, 160 / q ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop (160 / q)
  have hLogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 1
  filter_upwards
    [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_ge_atTop (2 : ℕ), hLogLarge, hLogOne] with
      n hPhase hn hLarge hOne
  have hnPos : (0 : ℝ) < n := by positivity
  have hnNe : (n : ℝ) ≠ 0 := hnPos.ne'
  have hSuccLe : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hLogSucc : Real.log ((n : ℝ) + 1) ≤ 2 * logOrder n := by
    have hlog := Real.log_le_log (by positivity) hSuccLe
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnNe] at hlog
    have hqLe : q ≤ logOrder n := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    calc
      Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := hlog
      _ ≤ 2 * logOrder n := by
        simpa [q, logOrder, two_mul] using
          add_le_add_right hqLe (logOrder n)
  have hPhaseFive : (((phaseNat n + 1 : ℕ) : ℝ)) ≤ 5 * logOrder n := by
    push_cast
    linarith [hPhase.2]
  have hLogNonneg : 0 ≤ logOrder n := hOne.trans' (by norm_num)
  have hBox : (((phaseNat n + 1 : ℕ) : ℝ) *
      Real.log ((n : ℝ) + 1)) ≤ 10 * (logOrder n) ^ 2 := by
    calc
      (((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)) ≤
          (5 * logOrder n) * (2 * logOrder n) :=
        mul_le_mul hPhaseFive hLogSucc
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega)))
          (mul_nonneg (by norm_num) hLogNonneg)
      _ = 10 * (logOrder n) ^ 2 := by ring
  have hqL : 160 ≤ q * logOrder n := by
    rw [div_le_iff₀ q_pos] at hLarge
    linarith
  nlinarith [sq_nonneg (logOrder n)]

theorem eventually_profilePhaseObjective_phaseChromaticLowerIndex_le_neg_cubic :
    ∀ᶠ n : ℕ in atTop,
      profilePhaseObjective n (phaseChromaticLowerIndex n : ℝ) ≤
        -(q / 16) * (logOrder n) ^ 3 := by
  let C : ℝ := unrestrictedPhaseRootCorridorCoefficient + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [unrestrictedPhaseRootCorridorCoefficient_pos]
  have hDomain := eventually_phaseRootLogLogCorridor_fourSize_domain C hC
  have hDeriv :=
    eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hC
  filter_upwards
    [eventually_phaseChromaticLowerIndex_geometry,
      eventually_unrestrictedPhaseRootSelected_spec_unique,
      eventually_five_lt_phaseNat,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      tendsto_logOrder_atTop.eventually_gt_atTop 0,
      hDomain, hDeriv,
      eventually_profileBoxTerm_le_q_div_sixteen_logOrder_cubed] with
      n hGeom hRoot hPhaseLarge hPhase hLogPos hDomainN hDerivN hBox
  let r : ℝ := unrestrictedPhaseRootSelected n
  let L : ℝ := logOrder n
  let a : ℝ := phaseChromaticLowerIndex n
  have hRootMem : r ∈ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    have hWidthPos : 0 < logLogOrder n * phaseRootGapRadius n :=
      hGeom.2.2.2.2
    dsimp [C, r]
    constructor
    · nlinarith [hRoot.1.1.1]
    · nlinarith [hRoot.1.1.2]
  have hAMem : a ∈ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    simpa [a, C] using hGeom.2.2.1
  have hAR : a ≤ r := by
    have hDisp : L ≤ r - a := by
      simpa [L, r, a] using hGeom.2.2.2.1
    linarith [hDisp, hLogPos]
  have hInterval : Icc a r ⊆ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    intro x hx
    exact ⟨hAMem.1.trans hx.1, hx.2.trans hRootMem.2⟩
  have hb : 2 ≤ phaseNat n + 1 := by omega
  have hKey : ∀ x ∈ Icc a r,
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) -
          Real.log x) x := by
    intro x hx
    obtain ⟨hxPos, hTarget⟩ := hDomainN x (hInterval hx)
    rw [fourSizeTarget, mem_Ioo] at hTarget
    have hcast : (((phaseNat n + 1 : ℕ)) : ℝ) =
        (phaseNat n : ℝ) + 1 := by push_cast; ring
    have hTarget' : (n : ℝ) / x ∈
        Ioo (1 : ℝ) (((phaseNat n + 1 : ℕ)) : ℝ) := by
      rw [mem_Ioo, hcast]
      have hSix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast hPhaseLarge
      exact ⟨by linarith [hTarget.2], by linarith [hTarget.1]⟩
    exact hasDerivAt_profileDualOptimalValue_parts hb hxPos hTarget'
  have hCont : ContinuousOn (unrestrictedPhaseObjective n) (Icc a r) := by
    intro x hx
    exact (hKey x hx).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ (unrestrictedPhaseObjective n) (Ioo a r) := by
    intro x hx
    exact (hKey x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hLower : ∀ x ∈ Ioo a r,
      q / 8 * (phaseNat n : ℝ) ^ 2 ≤
        deriv (unrestrictedPhaseObjective n) x := by
    intro x hx
    exact hDerivN x (hInterval (Ioo_subset_Icc_self hx))
  have hRootZero : unrestrictedPhaseObjective n r = 0 := by
    simpa [r] using hRoot.1.2
  have hIncrement := derivative_lower_bound_mul_sub_le_sub
    hAR hCont hDiff hLower
  have hSlopeNonneg : 0 ≤ q / 8 * (phaseNat n : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg q_pos.le (by norm_num)) (sq_nonneg _)
  have hDisp : L ≤ r - a := by
    simpa [L, r, a] using hGeom.2.2.2.1
  have hRawAtIndex : unrestrictedPhaseObjective n a ≤
      -(q / 8 * (phaseNat n : ℝ) ^ 2) * L := by
    nlinarith [mul_le_mul_of_nonneg_left hDisp hSlopeNonneg]
  have hPhaseSq : L ^ 2 ≤ (phaseNat n : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hLogPos.le hPhase.1 2
  have hRawCubic : unrestrictedPhaseObjective n a ≤
      -(q / 8) * L ^ 3 := by
    have hScaled : q / 8 * (L ^ 2 * L) ≤
        q / 8 * ((phaseNat n : ℝ) ^ 2 * L) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hPhaseSq hLogPos.le)
        (div_nonneg q_pos.le (by norm_num))
    calc
      unrestrictedPhaseObjective n a ≤
          -(q / 8 * (phaseNat n : ℝ) ^ 2) * L := hRawAtIndex
      _ = -(q / 8 * ((phaseNat n : ℝ) ^ 2 * L)) := by ring
      _ ≤ -(q / 8 * (L ^ 2 * L)) := neg_le_neg hScaled
      _ = -(q / 8) * L ^ 3 := by ring
  rw [profilePhaseObjective_eq_profileBoxTerm_add_unrestricted]
  dsimp [a] at hRawCubic
  nlinarith

theorem randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero :
    Tendsto
      (fun n => randomGraphMeasure n
        {G : LabeledGraph n |
          chromaticNumberNat G ≤ phaseChromaticLowerIndex n})
      atTop (nhds 0) := by
  apply randomGraphMeasure_chromaticNumberAtMost_tendsto_zero_of_eventually_le_neg_cubic
    phaseChromaticLowerIndex (q / 16) (div_pos q_pos (by norm_num))
  · exact eventually_phaseChromaticLowerIndex_pos_and_le.mono
      (fun _ hn ↦ hn.1)
  · exact eventually_phaseChromaticLowerIndex_pos_and_le.mono
      (fun _ hn ↦ hn.2)
  · simpa only [neg_mul] using
      eventually_profilePhaseObjective_phaseChromaticLowerIndex_le_neg_cubic

#print axioms eventually_phaseChromaticLowerIndex_pos_and_le
#print axioms eventually_profilePhaseObjective_phaseChromaticLowerIndex_le_neg_cubic
#print axioms randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero

end

end Erdos625
