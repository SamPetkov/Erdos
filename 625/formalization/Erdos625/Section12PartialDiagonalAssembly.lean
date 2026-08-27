import Erdos625.Section12ConcreteSignedFirstMoment
import Erdos625.PartialDiagonalEmptyRangeAsymptotic
import Erdos625.PartialDiagonalFourDeficitRateBridge
import Erdos625.PartialDiagonalMidpointRhoIdentity
import Erdos625.FullCornerMidpointAggregate
import Mathlib.Tactic

namespace Erdos625

open Filter Set
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false

/-! ### Canonical midpoint corridor geometry -/

private theorem tendsto_baseScale_atTop_for_partialDiagonal :
    Tendsto baseScale atTop atTop := by
  let d : Real :=
    (Real.log 2) ^ 2 / 32 * Real.log (200 / 153 : Real)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hScaled : Tendsto (fun n : Nat ↦ d * baseScale n) atTop atTop := by
    simpa only [d, baseScale, mul_div_assoc] using
      tendsto_explicit_gap_scale_atTop
  have h := hScaled.const_mul_atTop (inv_pos.mpr hd)
  simpa only [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul] using h

private structure PhaseMidpointEnvelopeGeometry (n : Nat) : Prop where
  index_mem :
    (phaseCochromaticMidpointIndex n : Real) ∈
      Icc
        (phaseRootCenter n -
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          (phaseRootCommonCorridorCoefficient + 1) *
            logLogOrder n * phaseRootGapRadius n)

private theorem eventually_phaseMidpointEnvelopeGeometry :
    ∀ᶠ n : Nat in atTop, PhaseMidpointEnvelopeGeometry n := by
  let c : Real := q ^ 2 / 8 * Real.log (200 / 153 : Real)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
      log_200_div_153_pos
  have hLogLogLarge : ∀ᶠ n : Nat in atTop,
      8 / q ^ 3 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop (8 / q ^ 3)
  have hBaseOne : ∀ᶠ n : Nat in atTop, 1 ≤ baseScale n :=
    tendsto_baseScale_atTop_for_partialDiagonal.eventually_ge_atTop 1
  have hScale :=
    eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower
      0 (by norm_num)
  filter_upwards
    [eventually_selected_phase_roots_separated,
      eventually_phaseSignedFourSizeRootSelected_spec_unique,
      eventually_unrestrictedPhaseRootSelected_spec_unique,
      hLogLogLarge, hBaseOne, hScale] with
      n hGap hSigned hUnrestricted hLogLogLargeN hBaseOneN hScaleN
  let rCo : Real := phaseSignedFourSizeRootSelected n
  let rPlus : Real := unrestrictedPhaseRootSelected n
  let width : Real := logLogOrder n * phaseRootGapRadius n
  let midpoint : Real := (rCo + rPlus) / 2
  let z : Int := rootCochromaticIndex rCo rPlus
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
    (show (0 : Real) ≤ 1 by norm_num).trans hBaseOneN
  have hWidthOne : 1 ≤ width := by
    calc
      1 ≤ baseScale n := hBaseOneN
      _ ≤ (q ^ 3 / 8 * logLogOrder n) * baseScale n := by
        simpa only [one_mul] using
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
  have hSignedMem : rCo ∈ Icc
      (phaseRootCenter n - phaseRootCommonCorridorCoefficient * width)
      (phaseRootCenter n + phaseRootCommonCorridorCoefficient * width) := by
    have hOwn := hSigned.1.1
    rw [mem_Ioo] at hOwn
    rw [mem_Icc]
    dsimp [rCo, width]
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_right hSignedCoeffLe hWidthPos.le]
  have hUnrestrictedMem : rPlus ∈ Icc
      (phaseRootCenter n - phaseRootCommonCorridorCoefficient * width)
      (phaseRootCenter n + phaseRootCommonCorridorCoefficient * width) := by
    have hOwn := hUnrestricted.1.1
    rw [mem_Ioo] at hOwn
    rw [mem_Icc]
    dsimp [rPlus, width]
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_right hUnrestrictedCoeffLe hWidthPos.le]
  have hMidpointMem : midpoint ∈ Icc
      (phaseRootCenter n - phaseRootCommonCorridorCoefficient * width)
      (phaseRootCenter n + phaseRootCommonCorridorCoefficient * width) := by
    rw [mem_Icc]
    dsimp [midpoint]
    constructor <;> linarith [hSignedMem.1, hSignedMem.2,
      hUnrestrictedMem.1, hUnrestrictedMem.2]
  have hMidpointPos : 0 < midpoint := by
    dsimp [midpoint]
    positivity
  have hZNonneg : 0 ≤ z := by
    dsimp [z, rootCochromaticIndex]
    exact Int.ceil_nonneg hMidpointPos.le
  have hIndexCast : (phaseCochromaticMidpointIndex n : Real) = (z : Real) := by
    rw [phaseCochromaticMidpointIndex]
    norm_cast
    simpa [z, rCo, rPlus, rootCochromaticIndex] using
      Int.toNat_of_nonneg hZNonneg
  have hMidpointLeZ : midpoint ≤ (z : Real) := by
    dsimp [z, rootCochromaticIndex, midpoint]
    exact_mod_cast Int.le_ceil ((rCo + rPlus) / 2)
  have hZLt : (z : Real) < midpoint + 1 := by
    dsimp [z, rootCochromaticIndex, midpoint]
    exact Int.ceil_lt_add_one ((rCo + rPlus) / 2)
  refine { index_mem := ?_ }
  rw [hIndexCast, mem_Icc]
  dsimp [width] at hMidpointMem hWidthOne ⊢
  constructor
  · nlinarith [hMidpointMem.1, hMidpointLeZ]
  · nlinarith [hMidpointMem.2, hZLt, hWidthOne]

private theorem eventually_phaseMidpoint_fourSizeTarget_le_four :
    ∀ᶠ n : Nat in atTop,
      fourSizeTarget n (phaseNat n)
        (phaseCochromaticMidpointIndex n : Real) ≤ 4 := by
  let C : Real := phaseRootCommonCorridorCoefficient + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [phaseRootCommonCorridorCoefficient_pos]
  have hClose :=
    eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center
      C hC (1 / 20) (by norm_num)
  filter_upwards [eventually_phaseMidpointEnvelopeGeometry,
    eventually_phaseDomain, hClose] with n hGeom hDomain hCloseN
  have hTargetEq := phaseRootDeficitTarget_eq hDomain
  have hqLower : (20 / 29 : Real) < q := by
    exact (by norm_num : (20 / 29 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hTwoDiv : 2 / q < (29 / 10 : Real) := by
    rw [div_lt_iff₀ q_pos]
    nlinarith
  have hCenter : phaseRootDeficitTarget n < (39 / 10 : Real) := by
    rw [hTargetEq]
    linarith [phaseDelta_nonneg n]
  have hAt := hCloseN (phaseCochromaticMidpointIndex n : Real)
    (by simpa only [C] using hGeom.index_mem)
  rw [abs_lt] at hAt
  linarith

private noncomputable def phaseMidpointFullCornerSum (n : Nat) : Real :=
  ∑ ell ∈
      (partialSubprofileBox
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticMidpointIndex n))).filter
          (fun ell =>
            n - selectedVertexMass
                (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32),
    partialDiagonalWeight n
      (midpointPartialDiagonalSize (phaseNat n))
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n)) ell

private theorem phaseMidpointFullCornerSum_nonneg (n : Nat) :
    0 ≤ phaseMidpointFullCornerSum n := by
  unfold phaseMidpointFullCornerSum
  apply Finset.sum_nonneg
  intro ell hell
  have hbox := (Finset.mem_filter.mp hell).1
  exact (partialDiagonalWeight_pos n
    (midpointPartialDiagonalSize (phaseNat n))
    (midpointMultiplicity n (phaseNat n)
      (phaseCochromaticMidpointIndex n)) ell
    (mem_partialSubprofileBox.mp hbox)).le

theorem tendsto_phaseMidpointFullCornerSum_zero :
    Tendsto phaseMidpointFullCornerSum atTop (nhds 0) := by
  let M : Nat → Real := fun n =>
    completeSignedFirstMoment
      (midpointPartialDiagonalSize (phaseNat n))
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n))
  have hM : Tendsto M atTop atTop := by
    simpa only [M] using
      phase_midpoint_completeSignedFirstMoment_tendsto_atTop
  have hEnvelope : Tendsto (fun n => Real.exp 1 / M n) atTop (nhds 0) := by
    have hInv : Tendsto (fun n => (M n)⁻¹) atTop (nhds 0) :=
      hM.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero] using
      hInv.const_mul (Real.exp 1)
  have hUpper : ∀ᶠ n : Nat in atTop,
      phaseMidpointFullCornerSum n ≤ Real.exp 1 / M n := by
    filter_upwards
      [eventually_sum_midpointPartialDiagonalWeight_fullCorner_filter_mul_complete_le_exp
        1 (by norm_num),
       eventually_phaseCochromaticMidpointIndex_rounding_admissible] with
        n hfull hadm
    have hMpos : 0 < M n := by
      dsimp [M]
      exact completeSignedFirstMoment_pos _ _
    apply (le_div_iff₀ hMpos).2
    simpa only [phaseMidpointFullCornerSum, M] using
      hfull (phaseCochromaticMidpointIndex n) hadm
  exact squeeze_zero'
    (Filter.Eventually.of_forall phaseMidpointFullCornerSum_nonneg)
    hUpper hEnvelope

/-! ### Central-range finite analytic helpers -/

private theorem mul_log_le_mul_log_add_sixtyFour_abs_sub
    {a b : Real} (haLow : (1 : Real) / 64 ≤ a)
    (hbLow : (1 : Real) / 64 ≤ b)
    (haOne : a ≤ 1) (_hbOne : b ≤ 1) :
    a * Real.log a ≤ b * Real.log b + 64 * |a - b| := by
  have haPos : 0 < a := (by norm_num : (0 : Real) < 1 / 64).trans_le haLow
  have hbPos : 0 < b := (by norm_num : (0 : Real) < 1 / 64).trans_le hbLow
  rcases le_total a b with hab | hba
  · have hLogMono : Real.log a ≤ Real.log b := Real.log_le_log haPos hab
    have hInv : a⁻¹ ≤ 64 := by
      apply (inv_le_comm₀ haPos (by norm_num)).2
      simpa only [inv_eq_one_div] using haLow
    have hLogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr haPos)
    rw [Real.log_inv] at hLogInv
    have hNegLog : -Real.log a ≤ 63 := by linarith
    have hFirst : (a - b) * Real.log a ≤ 64 * (b - a) := by
      calc
        (a - b) * Real.log a = (b - a) * (-Real.log a) := by ring
        _ ≤ (b - a) * 63 :=
          mul_le_mul_of_nonneg_left hNegLog (sub_nonneg.mpr hab)
        _ ≤ 64 * (b - a) := by nlinarith
    have hSecond : b * (Real.log a - Real.log b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hbPos.le (sub_nonpos.mpr hLogMono)
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · have hLogA : Real.log a ≤ 0 := Real.log_nonpos haPos.le haOne
    have hFirst : (a - b) * Real.log a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hba) hLogA
    have hLog := Real.log_le_sub_one_of_pos (div_pos haPos hbPos)
    have hScaled := mul_le_mul_of_nonneg_left hLog hbPos.le
    rw [Real.log_div haPos.ne' hbPos.ne'] at hScaled
    have hSecond : b * (Real.log a - Real.log b) ≤ a - b := by
      calc
        b * (Real.log a - Real.log b) ≤ b * (a / b - 1) := hScaled
        _ = a - b := by field_simp [hbPos.ne']
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    nlinarith

private noncomputable def phaseMidpointSelectedFraction
    (n : Nat) (ell : Fin 4 → Nat) : Real :=
  ∑ i : Fin 4,
    midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i

private noncomputable def phaseMidpointResidualFraction
    (n : Nat) (ell : Fin 4 → Nat) : Real :=
  ∑ i : Fin 4,
    (midpointPartialDiagonalP n (phaseNat n)
        (phaseCochromaticMidpointIndex n) i -
      midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i)

private noncomputable def phaseMidpointResidualDeficit
    (n : Nat) (ell : Fin 4 → Nat) : Real :=
  ∑ i : Fin 4, (fourDeficit i : Real) *
    (midpointPartialDiagonalP n (phaseNat n)
        (phaseCochromaticMidpointIndex n) i -
      midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i)

private theorem phaseMidpointCentral_scale_facts
    (n : Nat)
    (hAlphaLarge : (384 : Real) ≤ (phaseNat n : Real))
    (hAlphaLog : logOrder n ≤ (phaseNat n : Real))
    (hLogLogPos : 0 < logLogOrder n)
    (hTargetUpper :
      fourSizeTarget n (phaseNat n)
        (phaseCochromaticMidpointIndex n : Real) ≤ 4)
    (hadm : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticMidpointIndex n))
    (ell : Fin 4 → Nat)
    (hell : IsPartialSubprofile
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n)) ell)
    (hNotEmpty : ¬ midpointPartialDiagonalEmptyRange n ell)
    (hNotFull : ¬ (n - selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32)) :
    (1 : Real) / 64 ≤ phaseMidpointResidualFraction n ell ∧
    phaseMidpointResidualFraction n ell ≤ 1 ∧
    (1 : Real) / 64 ≤ midpointPartialDiagonalRho n (phaseNat n) ell ∧
    midpointPartialDiagonalRho n (phaseNat n) ell ≤ 1 ∧
    |midpointPartialDiagonalRho n (phaseNat n) ell -
        phaseMidpointResidualFraction n ell| ≤
      6 * phaseMidpointSelectedFraction n ell / (phaseNat n : Real) ∧
    logLogOrder n / 64 ≤
      (phaseNat n : Real) * phaseMidpointSelectedFraction n ell := by
  let K : Nat := phaseCochromaticMidpointIndex n
  let p : Fin 4 → Real := midpointPartialDiagonalP n (phaseNat n) K
  let y : Fin 4 → Real := midpointPartialDiagonalY K ell
  let T : Real := fourSizeTarget n (phaseNat n) (K : Real)
  let R : Real := ∑ i : Fin 4, (p i - y i)
  let Y : Real := ∑ i : Fin 4, y i
  let Ir : Real := ∑ i : Fin 4, (fourDeficit i : Real) * (p i - y i)
  let rho : Real := midpointPartialDiagonalRho n (phaseNat n) ell
  let A : Real := Ir - T * R
  have hKnat : 0 < K := hadm.2.1
  have hK : 0 < (K : Real) := by exact_mod_cast hKnat
  have hAlpha : 0 < (phaseNat n : Real) := by linarith
  have hTlower : 2 < T := by simpa only [T, K] using hadm.2.2.2.1.1
  have hTupper : T ≤ 4 := by simpa only [T, K] using hTargetUpper
  have hpPos : ∀ i, 0 < p i := by
    intro i
    change 0 < midpointRoundedProportion n (phaseNat n) K i
    exact midpointRoundedProportion_pos_of_admissible n (phaseNat n) K hadm i
  have hpSum : ∑ i : Fin 4, p i = 1 := by
    change ∑ i : Fin 4, midpointRoundedProportion n (phaseNat n) K i = 1
    exact sum_midpointRoundedProportion n (phaseNat n) K hadm
  have hpMean : ∑ i : Fin 4, (fourDeficit i : Real) * p i = T := by
    calc
      _ = ∑ i : Fin 4,
          midpointRoundedProportion n (phaseNat n) K i *
            ProfileEntropyS4.support i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show p i = midpointRoundedProportion n (phaseNat n) K i by rfl,
          fourDeficit_cast_eq_support]
        ring
      _ = T := by
        simpa only [T] using
          sum_midpointRoundedProportion_mul_support n (phaseNat n) K hadm
  have hyNonneg : ∀ i, 0 ≤ y i := by
    intro i
    dsimp [y, midpointPartialDiagonalY]
    positivity
  have hyLe : ∀ i, y i ≤ p i := by
    intro i
    dsimp [y, p, midpointPartialDiagonalY, midpointPartialDiagonalP]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hell i) (Nat.cast_nonneg K)
  have hYNonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ ↦ hyNonneg i
  have hYOne : Y ≤ 1 := by
    calc
      Y ≤ ∑ i : Fin 4, p i := Finset.sum_le_sum fun i _ ↦ hyLe i
      _ = 1 := hpSum
  have hR : R = 1 - Y := by
    dsimp [R]
    rw [Finset.sum_sub_distrib, hpSum]
  have hRNonneg : 0 ≤ R := by rw [hR]; linarith
  have hROne : R ≤ 1 := by rw [hR]; linarith
  have hAeq : A = ∑ i : Fin 4, (T - (fourDeficit i : Real)) * y i := by
    dsimp [A, Ir, R]
    simp only [Fin.sum_univ_four] at hpSum hpMean ⊢
    norm_num [fourDeficit] at hpMean ⊢
    have hp3 : p 3 = 1 - p 0 - p 1 - p 2 := by linarith
    rw [hp3]
    have hTform : T = 5 - 3 * p 0 - 2 * p 1 - p 2 := by linarith
    rw [hTform]
    ring
  have hCoeff : ∀ i : Fin 4, |T - (fourDeficit i : Real)| ≤ 3 := by
    intro i
    fin_cases i <;> norm_num [fourDeficit] <;> rw [abs_le] <;>
      constructor <;> linarith
  have hAabs : |A| ≤ 3 * Y := by
    rw [hAeq]
    calc
      |∑ i : Fin 4, (T - (fourDeficit i : Real)) * y i| ≤
          ∑ i : Fin 4, |(T - (fourDeficit i : Real)) * y i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 4, 3 * y i := Finset.sum_le_sum fun i _ ↦ by
        rw [abs_mul, abs_of_nonneg (hyNonneg i)]
        exact mul_le_mul_of_nonneg_right (hCoeff i) (hyNonneg i)
      _ = 3 * Y := by rw [Finset.mul_sum]
  have hDenom : (phaseNat n : Real) / 2 ≤ (phaseNat n : Real) - T := by
    linarith
  have hDenomPos : 0 < (phaseNat n : Real) - T :=
    lt_of_lt_of_le (div_pos hAlpha (by norm_num)) hDenom
  have hRhoEq : rho = R - A / ((phaseNat n : Real) - T) := by
    have hId := midpointPartialDiagonalRho_eq_residual_add_correction
      n (phaseNat n) K hadm ell hell
    dsimp [rho]
    rw [hId]
    rw [show ∑ i : Fin 4,
        (fourDeficit i : Real) * midpointPartialDiagonalP n (phaseNat n) K i = T by
          simpa only [p] using hpMean]
    rw [show ∑ i : Fin 4,
        midpointPartialDiagonalZ n (phaseNat n) K ell i = R by rfl]
    change R +
        ((∑ i : Fin 4, (fourDeficit i : Real) * y i) - T * Y) /
            ((phaseNat n : Real) - T) =
      R - A / ((phaseNat n : Real) - T)
    rw [hAeq]
    dsimp [Y]
    have hsum :
        (∑ i : Fin 4, (T - (fourDeficit i : Real)) * y i) =
          T * (∑ i : Fin 4, y i) -
            ∑ i : Fin 4, (fourDeficit i : Real) * y i := by
      calc
        _ = ∑ i : Fin 4,
            (T * y i - (fourDeficit i : Real) * y i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum]
    ring
  have hDiff : |rho - R| ≤ 6 * Y / (phaseNat n : Real) := by
    rw [hRhoEq]
    have hDiv := div_le_div_of_nonneg_right hAabs hDenomPos.le
    have hCompare : 3 * Y / ((phaseNat n : Real) - T) ≤
        6 * Y / (phaseNat n : Real) := by
      apply (div_le_iff₀ hDenomPos).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hAlpha).2
      have hScaledDenom :=
        mul_le_mul_of_nonneg_left hDenom
          (mul_nonneg (by norm_num : (0 : Real) ≤ 6) hYNonneg)
      nlinarith
    rw [sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hDenomPos]
    exact hDiv.trans hCompare
  have hMass := midpointMultiplicity_vertexMass n (phaseNat n) K hadm
  have hSelectedLe : selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n := by
    calc
      selectedVertexMass (midpointPartialDiagonalSize (phaseNat n)) ell ≤
          ∑ i : Fin 4,
            (phaseNat n - fourDeficit i) *
              midpointMultiplicity n (phaseNat n) K i :=
        Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_left _ (hell i)
      _ = n := hMass
  have hn : 0 < n := by omega
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hRhoLower : (1 : Real) / 32 ≤ rho := by
    have hNat : n < 32 * (n - selectedVertexMass
        (midpointPartialDiagonalSize (phaseNat n)) ell) := by omega
    have hCast : (n : Real) < 32 *
        ((n - selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real) := by
      exact_mod_cast hNat
    dsimp [rho, midpointPartialDiagonalRho]
    apply (le_div_iff₀ hnR).2
    nlinarith
  have hRhoOne : rho ≤ 1 := by
    dsimp [rho, midpointPartialDiagonalRho]
    apply (div_le_iff₀ hnR).2
    norm_num
  have hRLower : (1 : Real) / 64 ≤ R := by
    have hSmall : 6 * Y / (phaseNat n : Real) ≤ (1 : Real) / 64 := by
      rw [div_le_iff₀ hAlpha]
      nlinarith
    have hRaw : rho - R ≤ (1 : Real) / 64 :=
      (le_abs_self (rho - R)).trans (hDiff.trans hSmall)
    linarith
  have hCountSelected : (K : Real) * Y = (∑ i : Fin 4, ell i : Nat) := by
    dsimp [Y, y, midpointPartialDiagonalY]
    rw [← Finset.sum_div, ← Nat.cast_sum]
    field_simp [hK.ne']
  have hSelectedCast :
      (selectedVertexMass (midpointPartialDiagonalSize (phaseNat n)) ell : Real) ≤
        (phaseNat n : Real) * (K : Real) * Y := by
    calc
      (selectedVertexMass (midpointPartialDiagonalSize (phaseNat n)) ell : Real) =
          ∑ i : Fin 4,
            ((phaseNat n - fourDeficit i : Nat) : Real) * (ell i : Real) := by
        unfold selectedVertexMass midpointPartialDiagonalSize
        push_cast
        ring
      _ ≤ ∑ i : Fin 4, (phaseNat n : Real) * (ell i : Real) :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Nat.sub_le (phaseNat n) (fourDeficit i)))
            (Nat.cast_nonneg _)
      _ = (phaseNat n : Real) * (K : Real) * Y := by
        rw [← Finset.mul_sum, ← Nat.cast_sum, ← hCountSelected]
        ring
  have hnOne : 1 < n := by
    by_contra hnOne
    have hnCases : n = 0 ∨ n = 1 := by omega
    rcases hnCases with rfl | rfl <;>
      norm_num [logLogOrder, logOrder] at hLogLogPos
  have hLpos : 0 < logOrder n := Real.log_pos (by exact_mod_cast hnOne)
  have hEtaNonneg : 0 ≤ midpointPartialDiagonalEta n := by
    unfold midpointPartialDiagonalEta
    exact div_nonneg hLogLogPos.le (mul_nonneg (by norm_num) hLpos.le)
  have hMassEq : (n : Real) = (K : Real) * ((phaseNat n : Real) - T) := by
    dsimp [T, fourSizeTarget]
    field_simp [hK.ne']
    ring
  have hMassLower : (K : Real) * (phaseNat n : Real) / 2 ≤ (n : Real) := by
    rw [hMassEq]
    nlinarith
  have hNotEmpty' : (n : Real) * midpointPartialDiagonalEta n <
      (selectedVertexMass (midpointPartialDiagonalSize (phaseNat n)) ell : Real) :=
    lt_of_not_ge hNotEmpty
  have hScaledY : midpointPartialDiagonalEta n / 2 < Y := by
    have hScaled :
        ((phaseNat n : Real) * (K : Real)) * (midpointPartialDiagonalEta n / 2) <
          ((phaseNat n : Real) * (K : Real)) * Y := by
      calc
        ((phaseNat n : Real) * (K : Real)) * (midpointPartialDiagonalEta n / 2) =
            ((K : Real) * (phaseNat n : Real) / 2) *
              midpointPartialDiagonalEta n := by ring
        _ ≤ (n : Real) * midpointPartialDiagonalEta n :=
          mul_le_mul_of_nonneg_right hMassLower hEtaNonneg
        _ < (selectedVertexMass
            (midpointPartialDiagonalSize (phaseNat n)) ell : Real) := hNotEmpty'
        _ ≤ (phaseNat n : Real) * (K : Real) * Y := hSelectedCast
    exact lt_of_mul_lt_mul_left hScaled (mul_nonneg hAlpha.le hK.le)
  have hSelectedScale : logLogOrder n / 64 ≤ (phaseNat n : Real) * Y := by
    have hEtaForm : midpointPartialDiagonalEta n / 2 =
        logLogOrder n / (64 * logOrder n) := by
      unfold midpointPartialDiagonalEta
      field_simp
      ring
    have hBase : logLogOrder n / 64 ≤
        (phaseNat n : Real) * (logLogOrder n / (64 * logOrder n)) := by
      calc
        logLogOrder n / 64 =
            (logLogOrder n / (64 * logOrder n)) * logOrder n := by
          field_simp [hLpos.ne']
        _ ≤ (logLogOrder n / (64 * logOrder n)) * (phaseNat n : Real) :=
          mul_le_mul_of_nonneg_left hAlphaLog (div_nonneg hLogLogPos.le
            (mul_nonneg (by norm_num) hLpos.le))
        _ = (phaseNat n : Real) *
            (logLogOrder n / (64 * logOrder n)) := by ring
    rw [← hEtaForm] at hBase
    exact hBase.trans (mul_le_mul_of_nonneg_left hScaledY.le hAlpha.le)
  dsimp [phaseMidpointResidualFraction, phaseMidpointSelectedFraction]
  simpa only [K, p, y, R, rho] using
    ⟨hRLower, hROne, hRhoLower.trans' (by norm_num), hRhoOne, hDiff,
      hSelectedScale⟩

private theorem partialDiagonal_coordinateEntropy_le_one
    {p y : Real} (hpPos : 0 < p) (hpOne : p ≤ 1)
    (hy : 0 ≤ y) (hyp : y ≤ p) :
    2 * p * Real.log p - 2 * (p - y) * Real.log (p - y) -
        y * Real.log y - y ≤ 1 := by
  have hz : 0 ≤ p - y := sub_nonneg.mpr hyp
  have hrel := ProfileEntropyS4.neg_mul_log_add_mul_log_le_sub hz hpPos
  have hlogp : Real.log p ≤ 0 := Real.log_nonpos hpPos.le hpOne
  have hylog : y * Real.log p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hlogp
  have hdiff : p * Real.log p - (p - y) * Real.log (p - y) ≤ y := by
    nlinarith
  have hyEntropy :=
    ProfileEntropyS4.neg_mul_log_add_mul_log_le_sub hy (by norm_num : (0 : Real) < 1)
  norm_num at hyEntropy
  linarith

private theorem partialDiagonal_sum_coordinateEntropy_le_four
    (p y : Fin 4 → Real)
    (hpPos : ∀ i, 0 < p i) (hpOne : ∀ i, p i ≤ 1)
    (hy : ∀ i, 0 ≤ y i) (hyp : ∀ i, y i ≤ p i) :
    (∑ i : Fin 4,
      (2 * p i * Real.log (p i) -
        2 * (p i - y i) * Real.log (p i - y i) -
        y i * Real.log (y i) - y i)) ≤ 4 := by
  calc
    _ ≤ ∑ _i : Fin 4, (1 : Real) := Finset.sum_le_sum fun i _ ↦
      partialDiagonal_coordinateEntropy_le_one (hpPos i) (hpOne i) (hy i) (hyp i)
    _ = 4 := by norm_num

private theorem probability_entropy_lower_neg_two_q
    (p : Fin 4 → Real) (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i : Fin 4, p i = 1) :
    -(2 * q) ≤ ∑ i : Fin 4, p i * Real.log (p i) := by
  let u : Fin 4 → Real := fun _ ↦ 1 / 4
  have huPos : ∀ i, 0 < u i := by intro i; norm_num [u]
  have huSum : ∑ i : Fin 4, u i = 1 := by norm_num [u, Fin.sum_univ_succ]
  have hrel := ProfileEntropyS4.sum_neg_mul_log_add_mul_log_le_zero
    p u hp huPos hpSum huSum
  have hlogFour : Real.log (4 : Real) = 2 * q := by
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
    simp [q]
  have hlogU : ∀ i, Real.log (u i) = -(2 * q) := by
    intro i
    dsimp [u]
    rw [Real.log_div (by norm_num : (1 : Real) ≠ 0)
      (by norm_num : (4 : Real) ≠ 0), Real.log_one, hlogFour]
    ring
  have hform :
      ∑ i : Fin 4, (-p i * Real.log (p i) + p i * Real.log (u i)) =
        -(∑ i : Fin 4, p i * Real.log (p i)) - 2 * q := by
    rw [Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    simp_rw [hlogU]
    rw [← Finset.sum_mul, hpSum]
    ring
  rw [hform] at hrel
  linarith

private theorem midpointPartialDiagonalP_facts
    (n alpha K : Nat) (hadm : MidpointRoundingAdmissible n alpha K) :
    (∀ i, 0 < midpointPartialDiagonalP n alpha K i) ∧
    (∀ i, midpointPartialDiagonalP n alpha K i ≤ 1) ∧
    (∑ i : Fin 4, midpointPartialDiagonalP n alpha K i = 1) ∧
    (∑ i : Fin 4,
      (fourDeficit i : Real) * midpointPartialDiagonalP n alpha K i =
        fourSizeTarget n alpha (K : Real)) := by
  have hEq : midpointPartialDiagonalP n alpha K =
      midpointRoundedProportion n alpha K := rfl
  have hPos : ∀ i, 0 < midpointPartialDiagonalP n alpha K i := by
    intro i
    simpa only [hEq] using
      midpointRoundedProportion_pos_of_admissible n alpha K hadm i
  have hSum : ∑ i : Fin 4, midpointPartialDiagonalP n alpha K i = 1 := by
    simpa only [hEq] using sum_midpointRoundedProportion n alpha K hadm
  have hOne : ∀ i, midpointPartialDiagonalP n alpha K i ≤ 1 := by
    intro i
    have hSingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 4)))
      (f := midpointPartialDiagonalP n alpha K)
      (fun j _ ↦ (hPos j).le) (Finset.mem_univ i)
    rwa [hSum] at hSingle
  have hMean := sum_midpointRoundedProportion_mul_support n alpha K hadm
  have hMean' : ∑ i : Fin 4,
      (fourDeficit i : Real) * midpointPartialDiagonalP n alpha K i =
        fourSizeTarget n alpha (K : Real) := by
    calc
      _ = ∑ i : Fin 4,
          midpointRoundedProportion n alpha K i *
            ProfileEntropyS4.support i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show midpointPartialDiagonalP n alpha K i =
            midpointRoundedProportion n alpha K i by rfl,
            fourDeficit_cast_eq_support]
          ring
      _ = _ := hMean
  exact ⟨hPos, hOne, hSum, hMean'⟩

private theorem midpointPartialDiagonalE_average_identity
    (n alpha K : Nat) (hadm : MidpointRoundingAdmissible n alpha K) :
    (K : Real) *
        ((∑ i : Fin 4,
            midpointPartialDiagonalP n alpha K i *
              Real.log (midpointPartialDiagonalP n alpha K i)) - 1 +
          ∑ i : Fin 4,
            midpointPartialDiagonalP n alpha K i *
              midpointPartialDiagonalE n alpha K i) =
      -((K : Real) * q +
        profileDiscreteObjective n
          (fourDeficitEmbedding alpha hadm.1
            (midpointMultiplicity n alpha K))) := by
  let k : Fin 4 → Nat := midpointMultiplicity n alpha K
  let u : Fin 4 → Nat := fun i ↦ alpha - fourDeficit i
  have hK : 0 < K := hadm.2.1
  have hKne : (K : Real) ≠ 0 := by exact_mod_cast hK.ne'
  have hCountNat : ∑ i : Fin 4, k i = K :=
    (midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm).1
  have hCount : ∑ i : Fin 4, (k i : Real) = (K : Real) := by
    exact_mod_cast hCountNat
  have hMassNat : ∑ i : Fin 4, u i * k i = n := by
    simpa only [u, k] using midpointMultiplicity_vertexMass n alpha K hadm
  have hMass : ∑ i : Fin 4, (u i : Real) * (k i : Real) = (n : Real) := by
    exact_mod_cast hMassNat
  have hLog := sum_midpointMultiplicity_mul_log_eq n alpha K hadm
  have hLog' :
      (K : Real) *
          ∑ i : Fin 4,
            midpointPartialDiagonalP n alpha K i *
              Real.log (midpointPartialDiagonalP n alpha K i) =
        (∑ i : Fin 4, (k i : Real) * Real.log (k i : Real)) -
          (K : Real) * Real.log (K : Real) := by
    dsimp [k] at hLog ⊢
    simp only [midpointPartialDiagonalP, midpointRoundedProportion] at hLog ⊢
    rw [hLog]
    ring
  have hE :
      (K : Real) *
          ∑ i : Fin 4,
            midpointPartialDiagonalP n alpha K i *
              midpointPartialDiagonalE n alpha K i =
        (K : Real) * Real.log (K : Real) +
          ∑ i : Fin 4, (k i : Real) * Real.log ((u i).factorial : Real) +
          (n : Real) - (n : Real) * logOrder n +
          q * ∑ i : Fin 4, (k i : Real) * ((u i).choose 2 : Real) -
          (K : Real) * q := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ i : Fin 4, (k i : Real) * midpointPartialDiagonalE n alpha K i := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          (K : Real) *
                (midpointPartialDiagonalP n alpha K i *
                  midpointPartialDiagonalE n alpha K i) =
              ((K : Real) * midpointPartialDiagonalP n alpha K i) *
                midpointPartialDiagonalE n alpha K i := by ring
          _ = (k i : Real) * midpointPartialDiagonalE n alpha K i := by
            rw [show (K : Real) * midpointPartialDiagonalP n alpha K i =
              (k i : Real) by
                dsimp [midpointPartialDiagonalP, k]
                field_simp [hKne]]
      _ = _ := by
        simp only [midpointPartialDiagonalE, midpointPartialDiagonalSize]
        dsimp [u, k] at hCount hMass ⊢
        simp only [Fin.sum_univ_four] at hCount hMass ⊢
        linear_combination
          Real.log (K : Real) * hCount +
          (1 - logOrder n) * hMass - q * hCount
  rw [profileDiscreteObjective_fourDeficitEmbedding_eq n alpha hadm.1 k]
  rw [mul_add, mul_sub, mul_one, hLog', hE, hCountNat]
  simp only [Fin.sum_univ_four, k, u, coloringClassLogCost, logOrder, q]
  ring

private theorem eventually_logOrder_pow_five_le_natCast :
    ∀ᶠ n : Nat in atTop, logOrder n ^ 5 ≤ (n : Real) := by
  have hb :=
    (isLittleO_log_rpow_atTop (r := (1 / 5 : Real)) (by norm_num)).bound
      (by norm_num : (0 : Real) < 1)
  have hnat := (tendsto_natCast_atTop_atTop (R := Real)).eventually hb
  filter_upwards [hnat, eventually_gt_atTop 1] with n hn hn1
  have hn1' : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn1.le
  have hnpos : (0 : Real) < (n : Real) := by linarith
  have hlog : 0 ≤ Real.log (n : Real) := Real.log_nonneg hn1'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hn
  calc
    logOrder n ^ 5 ≤ ((n : Real) ^ (1 / 5 : Real)) ^ 5 :=
      pow_le_pow_left₀ hlog hn 5
    _ = (n : Real) := by
      rw [← Real.rpow_natCast ((n : Real) ^ (1 / 5 : Real)) 5,
        ← Real.rpow_mul hnpos.le]
      norm_num

private theorem eventually_four_factorialLogErrorBound_le_phaseMidpointIndex :
    ∀ᶠ n : Nat in atTop,
      4 * factorialLogErrorBound n ≤
        (phaseCochromaticMidpointIndex n : Real) := by
  have hRatio : ∀ᶠ n : Nat in atTop,
      factorialLogErrorBound n / logOrder n < 2 :=
    factorialLogErrorBound_div_logOrder_tendsto_one.eventually
      (Iio_mem_nhds (by norm_num : (1 : Real) < 2))
  filter_upwards [hRatio, eventually_logOrder_pow_five_le_natCast,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logOrder_atTop.eventually_ge_atTop 4,
    eventually_phaseCochromaticMidpointIndex_rounding_admissible] with
      n hRatioN hPow hPhase hLog hadm
  let L : Real := logOrder n
  let K : Real := phaseCochromaticMidpointIndex n
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLog
  have hError : factorialLogErrorBound n < 2 * L := by
    exact (div_lt_iff₀ hLpos).mp (by simpa only [L] using hRatioN)
  have h32 : (32 : Real) ≤ L ^ 3 := by
    calc
      (32 : Real) ≤ 4 ^ (3 : Nat) := by norm_num
      _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) (by simpa only [L] using hLog) 3
  have hLower : 32 * L ^ 2 ≤ (n : Real) := by
    calc
      32 * L ^ 2 ≤ L ^ 3 * L ^ 2 :=
        mul_le_mul_of_nonneg_right h32 (sq_nonneg L)
      _ = L ^ 5 := by ring
      _ ≤ (n : Real) := by simpa only [L] using hPow
  have hAlpha : (phaseNat n : Real) ≤ 4 * L := by
    simpa only [L] using hPhase.2
  have hIndexNonneg : 0 ≤ K := by positivity
  have hMassCast : (n : Real) ≤ (phaseNat n : Real) * K := by
    dsimp [K]
    exact_mod_cast hadm.2.2.1
  have hMassUpper : (n : Real) ≤ 4 * L * K :=
    hMassCast.trans (mul_le_mul_of_nonneg_right hAlpha hIndexNonneg)
  have hEight : 8 * L ≤ K := by
    have hScaled : 4 * L * (8 * L) ≤ 4 * L * K := by
      calc
        4 * L * (8 * L) = 32 * L ^ 2 := by ring
        _ ≤ (n : Real) := hLower
        _ ≤ 4 * L * K := hMassUpper
    exact le_of_mul_le_mul_left hScaled
      (mul_pos (by norm_num : (0 : Real) < 4) hLpos)
  linarith

private theorem eventually_eight_logOrder_le_phaseMidpointIndex :
    ∀ᶠ n : Nat in atTop,
      8 * logOrder n ≤
        (phaseCochromaticMidpointIndex n : Real) := by
  filter_upwards [eventually_logOrder_pow_five_le_natCast,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logOrder_atTop.eventually_ge_atTop 4,
    eventually_phaseCochromaticMidpointIndex_rounding_admissible] with
      n hPow hPhase hLog hadm
  let L : Real := logOrder n
  let K : Real := phaseCochromaticMidpointIndex n
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLog
  have h32 : (32 : Real) ≤ L ^ 3 := by
    calc
      (32 : Real) ≤ 4 ^ (3 : Nat) := by norm_num
      _ ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num)
        (by simpa only [L] using hLog) 3
  have hLower : 32 * L ^ 2 ≤ (n : Real) := by
    calc
      32 * L ^ 2 ≤ L ^ 3 * L ^ 2 :=
        mul_le_mul_of_nonneg_right h32 (sq_nonneg L)
      _ = L ^ 5 := by ring
      _ ≤ (n : Real) := by simpa only [L] using hPow
  have hAlpha : (phaseNat n : Real) ≤ 4 * L := by
    simpa only [L] using hPhase.2
  have hIndexNonneg : 0 ≤ K := by positivity
  have hMassCast : (n : Real) ≤ (phaseNat n : Real) * K := by
    dsimp [K]
    exact_mod_cast hadm.2.2.1
  have hMassUpper : (n : Real) ≤ 4 * L * K :=
    hMassCast.trans (mul_le_mul_of_nonneg_right hAlpha hIndexNonneg)
  have hScaled : 4 * L * (8 * L) ≤ 4 * L * K := by
    calc
      4 * L * (8 * L) = 32 * L ^ 2 := by ring
      _ ≤ (n : Real) := hLower
      _ ≤ 4 * L * K := hMassUpper
  exact le_of_mul_le_mul_left hScaled
    (mul_pos (by norm_num : (0 : Real) < 4) hLpos)

private theorem eventually_midpointPartialDiagonalE_average_le_four :
    ∀ᶠ n : Nat in atTop,
      (∑ i : Fin 4,
        midpointPartialDiagonalP n (phaseNat n)
            (phaseCochromaticMidpointIndex n) i *
          midpointPartialDiagonalE n (phaseNat n)
            (phaseCochromaticMidpointIndex n) i) ≤ 4 := by
  have hMoment :=
    phase_midpoint_completeSignedFirstMoment_tendsto_atTop.eventually_ge_atTop 1
  filter_upwards [hMoment,
    eventually_four_factorialLogErrorBound_le_phaseMidpointIndex,
    eventually_phaseCochromaticMidpointIndex_rounding_admissible] with
      n hMomentN hError hadm
  let K : Nat := phaseCochromaticMidpointIndex n
  let p : Fin 4 → Real := midpointPartialDiagonalP n (phaseNat n) K
  let E : Fin 4 → Real := midpointPartialDiagonalE n (phaseNat n) K
  let D : Real :=
    (K : Real) * q +
      profileDiscreteObjective n
        (fourDeficitEmbedding (phaseNat n) hadm.1
          (midpointMultiplicity n (phaseNat n) K))
  have hK : 0 < (K : Real) := by exact_mod_cast hadm.2.1
  have hMass := midpointMultiplicity_vertexMass n (phaseNat n) K hadm
  have hMomentEq :
      partialSignedFirstMoment n
          (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
          (midpointMultiplicity n (phaseNat n) K) =
        completeSignedFirstMoment
          (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n) K) := by
    unfold completeSignedFirstMoment residualVertexMass
    change partialSignedFirstMoment n
        (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
        (midpointMultiplicity n (phaseNat n) K) =
      partialSignedFirstMoment
        (∑ i : Fin 4,
          (phaseNat n - fourDeficit i) *
            midpointMultiplicity n (phaseNat n) K i)
        (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
        (midpointMultiplicity n (phaseNat n) K)
    rw [hMass]
  have hLogNonneg :
      0 ≤ Real.log
        (partialSignedFirstMoment n
          (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
          (midpointMultiplicity n (phaseNat n) K)) := by
    apply Real.log_nonneg
    rw [hMomentEq]
    simpa only [K] using hMomentN
  have hStirling :=
    abs_log_partialSignedFirstMoment_fourDeficit_sub_discreteObjective_le
      n (phaseNat n) hadm.1
        (midpointMultiplicity n (phaseNat n) K) hMass
  have hCount :=
    (midpointMultiplicity_count_deficit_intDisplacement
      n (phaseNat n) K hadm).1
  have hCountCast :
      ((((∑ i : Fin 4, midpointMultiplicity n (phaseNat n) K i : Nat) : Real))) =
        (K : Real) := by exact_mod_cast hCount
  rw [hCountCast] at hStirling
  have hD : -D ≤ 4 * factorialLogErrorBound n := by
    rw [abs_le] at hStirling
    dsimp [D]
    linarith [hStirling.2, hLogNonneg]
  have hpFacts := midpointPartialDiagonalP_facts n (phaseNat n) K hadm
  have hEntropy : -(2 * q) ≤ ∑ i : Fin 4, p i * Real.log (p i) := by
    exact probability_entropy_lower_neg_two_q p
      (fun i ↦ (hpFacts.1 i).le) (by simpa only [p] using hpFacts.2.2.1)
  have hIdentity :=
    midpointPartialDiagonalE_average_identity n (phaseNat n) K hadm
  have hNormalized :
      (∑ i : Fin 4, p i * Real.log (p i)) - 1 +
          ∑ i : Fin 4, p i * E i ≤ 1 := by
    have hScaled :
        (K : Real) *
            ((∑ i : Fin 4, p i * Real.log (p i)) - 1 +
              ∑ i : Fin 4, p i * E i) ≤ (K : Real) * 1 := by
      calc
        (K : Real) *
            ((∑ i : Fin 4, p i * Real.log (p i)) - 1 +
              ∑ i : Fin 4, p i * E i) = -D := by
          simpa only [p, E, D] using hIdentity
        _ ≤ 4 * factorialLogErrorBound n := hD
        _ ≤ (K : Real) * 1 := by simpa only [K, mul_one] using hError
    exact le_of_mul_le_mul_left hScaled hK
  have hq : q < 1 := Real.log_two_lt_d9.trans (by norm_num)
  dsimp [p, E] at hNormalized ⊢
  dsimp [p] at hEntropy
  linarith

private noncomputable def partialDiagonalEAtSize
    (n K u : Nat) : Real :=
  Real.log (K : Real) + Real.log (u.factorial : Real) + (u : Real) -
    (u : Real) * logOrder n + q * (u.choose 2 : Real) - q

private theorem partialDiagonalEAtSize_sub_succ
    (n K s : Nat) :
    partialDiagonalEAtSize n K s - partialDiagonalEAtSize n K (s + 1) =
      logOrder n - Real.log ((s + 1 : Nat) : Real) - q * (s : Real) - 1 := by
  rw [partialDiagonalEAtSize, partialDiagonalEAtSize,
    Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity : ((s + 1 : Nat) : Real) ≠ 0)
      (by positivity : (s.factorial : Real) ≠ 0),
    chooseTwo_succ]
  push_cast
  ring

private theorem midpointPartialDiagonalE_eq_EAtSize
    (n alpha K : Nat) (i : Fin 4) :
    midpointPartialDiagonalE n alpha K i =
      partialDiagonalEAtSize n K (alpha - fourDeficit i) := rfl

private noncomputable def phaseAdjacentEError (d n : Nat) : Real :=
  logOrder n - Real.log ((phaseNat n - d : Nat) : Real) -
    q * ((phaseNat n - d - 1 : Nat) : Real) - 1 +
    q / 2 * (phaseNat n : Real)

private theorem tendsto_log_phaseNat_sub_div_logOrder_zero (d : Nat) :
    Tendsto
      (fun n : Nat ↦
        Real.log ((phaseNat n - d : Nat) : Real) / logOrder n)
      atTop (nhds 0) := by
  have hBig : ∀ᶠ n : Nat in atTop, d < phaseNat n := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_gt_atTop (d : Real),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hL hphase
    exact_mod_cast hL.trans_le hphase.1
  have hLogPos : ∀ᶠ n : Nat in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  refine squeeze_zero' ?_ ?_ (tendsto_log_phaseNat_add_div_logOrder_zero 0)
  · filter_upwards [hBig, hLogPos] with n hbig hL
    exact div_nonneg (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ phaseNat n - d by omega))) hL.le
  · filter_upwards [hBig, hLogPos] with n hbig hL
    have hsubPos : (0 : Real) < ((phaseNat n - d : Nat) : Real) := by
      exact_mod_cast (show 0 < phaseNat n - d by omega)
    have hle : ((phaseNat n - d : Nat) : Real) ≤
        ((phaseNat n + 0 : Nat) : Real) := by
      exact_mod_cast (show phaseNat n - d ≤ phaseNat n + 0 by omega)
    gcongr

private theorem tendsto_phaseNat_sub_mul_q_div_logOrder_two (d : Nat) :
    Tendsto
      (fun n : Nat ↦
        (((phaseNat n - d - 1 : Nat) : Real) * q) / logOrder n)
      atTop (nhds 2) := by
  have hBig : ∀ᶠ n : Nat in atTop, d + 1 < phaseNat n := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_gt_atTop ((d + 1 : Nat) : Real),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hL hphase
    exact_mod_cast hL.trans_le hphase.1
  have hConst : Tendsto
      (fun n : Nat ↦ (((d : Real) + 1) * q) * (logOrder n)⁻¹)
      atTop (nhds 0) := by
    simpa using tendsto_inv_logOrder_zero.const_mul (((d : Real) + 1) * q)
  have h := (tendsto_phaseNat_add_mul_q_div_logOrder_two 0).sub hConst
  rw [show (2 : Real) - 0 = 2 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [hBig,
    tendsto_logOrder_atTop.eventually_ne_atTop 0] with n hbig hL
  have hcast : ((phaseNat n - d - 1 : Nat) : Real) =
      (phaseNat n : Real) - d - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ phaseNat n - d),
      Nat.cast_sub (by omega : d ≤ phaseNat n), Nat.cast_one]
  simp only [Nat.add_zero, hcast, div_eq_mul_inv]
  ring

private theorem tendsto_phaseAdjacentEError_div_logOrder_zero (d : Nat) :
    Tendsto (fun n : Nat ↦ phaseAdjacentEError d n / logOrder n)
      atTop (nhds 0) := by
  have hOne : Tendsto (fun n : Nat ↦ logOrder n / logOrder n)
      atTop (nhds 1) := by
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [tendsto_logOrder_atTop.eventually_ne_atTop 0] with n hn
    rw [div_self hn]
  have hLog := tendsto_log_phaseNat_sub_div_logOrder_zero d
  have hPower := tendsto_phaseNat_sub_mul_q_div_logOrder_two d
  have hConst : Tendsto (fun n : Nat ↦ (1 : Real) / logOrder n)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_logOrder_zero
  have hPhase := (tendsto_phaseNat_add_mul_q_div_logOrder_two 0).const_mul (1 / 2 : Real)
  have h := (((hOne.sub hLog).sub hPower).sub hConst).add hPhase
  norm_num at h
  refine h.congr' ?_
  filter_upwards [tendsto_logOrder_atTop.eventually_ne_atTop 0] with n hn
  simp only [phaseAdjacentEError]
  field_simp [hn]

private noncomputable def phaseCenteredEError
    (n K : Nat) (i : Fin 4) : Real :=
  midpointPartialDiagonalE n (phaseNat n) K i -
    midpointPartialDiagonalE n (phaseNat n) K (0 : Fin 4) +
    q / 2 * (phaseNat n : Real) * ((fourDeficit i : Real) - 2)

private theorem phaseCenteredEError_eq_adjacent_sum
    (n K : Nat) (hphase : 5 < phaseNat n) (i : Fin 4) :
    phaseCenteredEError n K i =
      match i.1 with
      | 0 => 0
      | 1 => phaseAdjacentEError 2 n
      | 2 => phaseAdjacentEError 2 n + phaseAdjacentEError 3 n
      | _ => phaseAdjacentEError 2 n + phaseAdjacentEError 3 n +
        phaseAdjacentEError 4 n := by
  have h23 : phaseNat n - 3 + 1 = phaseNat n - 2 := by omega
  have h34 : phaseNat n - 4 + 1 = phaseNat n - 3 := by omega
  have h45 : phaseNat n - 5 + 1 = phaseNat n - 4 := by omega
  have h2 :
      partialDiagonalEAtSize n K (phaseNat n - 3) -
          partialDiagonalEAtSize n K (phaseNat n - 2) +
          q / 2 * (phaseNat n : Real) = phaseAdjacentEError 2 n := by
    rw [← h23, partialDiagonalEAtSize_sub_succ]
    simp only [phaseAdjacentEError]
    have hs : phaseNat n - 2 - 1 = phaseNat n - 3 := by omega
    rw [hs, h23]
  have h3 :
      partialDiagonalEAtSize n K (phaseNat n - 4) -
          partialDiagonalEAtSize n K (phaseNat n - 3) +
          q / 2 * (phaseNat n : Real) = phaseAdjacentEError 3 n := by
    rw [← h34, partialDiagonalEAtSize_sub_succ]
    simp only [phaseAdjacentEError]
    have hs : phaseNat n - 3 - 1 = phaseNat n - 4 := by omega
    rw [hs, h34]
  have h4 :
      partialDiagonalEAtSize n K (phaseNat n - 5) -
          partialDiagonalEAtSize n K (phaseNat n - 4) +
          q / 2 * (phaseNat n : Real) = phaseAdjacentEError 4 n := by
    rw [← h45, partialDiagonalEAtSize_sub_succ]
    simp only [phaseAdjacentEError]
    have hs : phaseNat n - 4 - 1 = phaseNat n - 5 := by omega
    rw [hs, h45]
  fin_cases i
  · simp [phaseCenteredEError]
  · norm_num [phaseCenteredEError, midpointPartialDiagonalE_eq_EAtSize,
      fourDeficit] at ⊢
    exact h2
  · norm_num [phaseCenteredEError, midpointPartialDiagonalE_eq_EAtSize,
      fourDeficit] at ⊢
    linarith
  · norm_num [phaseCenteredEError, midpointPartialDiagonalE_eq_EAtSize,
      fourDeficit] at ⊢
    linarith

private theorem eventually_abs_phaseCenteredEError_le
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      ∀ i : Fin 4,
        |phaseCenteredEError n (phaseCochromaticMidpointIndex n) i| ≤
          epsilon * (phaseNat n : Real) := by
  have h1 := tendsto_phaseAdjacentEError_div_logOrder_zero 2
  have h2 : Tendsto
      (fun n : Nat ↦ phaseAdjacentEError 2 n / logOrder n +
        phaseAdjacentEError 3 n / logOrder n) atTop (nhds 0) := by
    simpa using h1.add (tendsto_phaseAdjacentEError_div_logOrder_zero 3)
  have h3 : Tendsto
      (fun n : Nat ↦ phaseAdjacentEError 2 n / logOrder n +
        phaseAdjacentEError 3 n / logOrder n +
        phaseAdjacentEError 4 n / logOrder n) atTop (nhds 0) := by
    simpa using h2.add (tendsto_phaseAdjacentEError_div_logOrder_zero 4)
  have hb1 := h1.eventually (Metric.ball_mem_nhds 0 hepsilon)
  have hb2 := h2.eventually (Metric.ball_mem_nhds 0 hepsilon)
  have hb3 := h3.eventually (Metric.ball_mem_nhds 0 hepsilon)
  filter_upwards [hb1, hb2, hb3, eventually_five_lt_phaseNat,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logOrder_atTop.eventually_gt_atTop 0] with
      n hn1 hn2 hn3 hphase hscale hL
  intro i
  have hratio :
      |phaseCenteredEError n (phaseCochromaticMidpointIndex n) i /
        logOrder n| < epsilon := by
    rw [phaseCenteredEError_eq_adjacent_sum n _ hphase i]
    fin_cases i
    · change |(0 : Real) / logOrder n| < epsilon
      simpa using hepsilon
    · change |phaseAdjacentEError 2 n / logOrder n| < epsilon
      simpa only [Real.dist_eq, sub_zero] using hn1
    · change |(phaseAdjacentEError 2 n + phaseAdjacentEError 3 n) /
          logOrder n| < epsilon
      rw [add_div]
      simpa only [Real.dist_eq, sub_zero] using hn2
    · change |(phaseAdjacentEError 2 n + phaseAdjacentEError 3 n +
          phaseAdjacentEError 4 n) / logOrder n| < epsilon
      rw [add_div, add_div]
      simpa only [Real.dist_eq, sub_zero] using hn3
  have hraw :
      |phaseCenteredEError n (phaseCochromaticMidpointIndex n) i| <
        epsilon * logOrder n := by
    rw [abs_div, abs_of_pos hL, div_lt_iff₀ hL] at hratio
    simpa only [mul_comm] using hratio
  exact hraw.le.trans (mul_le_mul_of_nonneg_left hscale.1 hepsilon.le)

private theorem midpointPartialDiagonal_sum_y_mul_E_le
    (n alpha K : Nat) (ell : Fin 4 → Nat) (epsilon : Real)
    (_hepsilon : 0 ≤ epsilon)
    (hadm : MidpointRoundingAdmissible n alpha K)
    (hell : IsPartialSubprofile (midpointMultiplicity n alpha K) ell)
    (hcenter : ∀ i : Fin 4,
      |midpointPartialDiagonalE n alpha K i -
          midpointPartialDiagonalE n alpha K (0 : Fin 4) +
          q / 2 * (alpha : Real) * ((fourDeficit i : Real) - 2)| ≤
        epsilon * (alpha : Real)) :
    (∑ i : Fin 4,
        midpointPartialDiagonalY K ell i *
          midpointPartialDiagonalE n alpha K i) ≤
      (∑ i : Fin 4, midpointPartialDiagonalY K ell i) *
        (∑ i : Fin 4,
          midpointPartialDiagonalP n alpha K i *
            midpointPartialDiagonalE n alpha K i) +
      q / 2 * (alpha : Real) *
        ((∑ i : Fin 4,
            (fourDeficit i : Real) * midpointPartialDiagonalP n alpha K i) *
            (∑ i : Fin 4, midpointPartialDiagonalY K ell i) -
          ∑ i : Fin 4,
            (fourDeficit i : Real) * midpointPartialDiagonalY K ell i) +
      2 * epsilon * (alpha : Real) *
        (∑ i : Fin 4, midpointPartialDiagonalY K ell i) := by
  let p : Fin 4 → Real := midpointPartialDiagonalP n alpha K
  let y : Fin 4 → Real := midpointPartialDiagonalY K ell
  let E : Fin 4 → Real := midpointPartialDiagonalE n alpha K
  let H : Fin 4 → Real := fun i ↦
    E i - E (0 : Fin 4) +
      q / 2 * (alpha : Real) * ((fourDeficit i : Real) - 2)
  let Y : Real := ∑ i : Fin 4, y i
  have hpFacts := midpointPartialDiagonalP_facts n alpha K hadm
  have hpNonneg : ∀ i, 0 ≤ p i := fun i ↦ (hpFacts.1 i).le
  have hpSum : ∑ i : Fin 4, p i = 1 := hpFacts.2.2.1
  have hyNonneg : ∀ i, 0 ≤ y i := by
    intro i
    dsimp [y, midpointPartialDiagonalY]
    positivity
  have hyLe : ∀ i, y i ≤ p i := by
    intro i
    dsimp [y, p, midpointPartialDiagonalY, midpointPartialDiagonalP]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hell i)
      (Nat.cast_nonneg K)
  have hYNonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ ↦ hyNonneg i
  have hHupper : ∀ i, H i ≤ epsilon * (alpha : Real) := by
    intro i
    exact (le_abs_self (H i)).trans (by simpa [H, E] using hcenter i)
  have hHlower : ∀ i, -(epsilon * (alpha : Real)) ≤ H i := by
    intro i
    exact (neg_le_of_abs_le (by simpa [H, E] using hcenter i))
  have hyH : (∑ i : Fin 4, y i * H i) ≤
      epsilon * (alpha : Real) * Y := by
    calc
      _ ≤ ∑ i : Fin 4, y i * (epsilon * (alpha : Real)) :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hHupper i) (hyNonneg i)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hpHlower : -(epsilon * (alpha : Real)) ≤
      ∑ i : Fin 4, p i * H i := by
    calc
      _ = ∑ i : Fin 4, p i * (-(epsilon * (alpha : Real))) := by
        rw [← Finset.sum_mul, hpSum]
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hHlower i) (hpNonneg i)
  have hcorrection :
      (∑ i : Fin 4, y i * H i) -
          Y * (∑ i : Fin 4, p i * H i) ≤
        2 * epsilon * (alpha : Real) * Y := by
    have hmul := mul_le_mul_of_nonneg_left hpHlower hYNonneg
    nlinarith
  have hdecomp :
      (∑ i : Fin 4, y i * E i) -
          (Y * (∑ i : Fin 4, p i * E i) +
            q / 2 * (alpha : Real) *
              ((∑ i : Fin 4, (fourDeficit i : Real) * p i) * Y -
                ∑ i : Fin 4, (fourDeficit i : Real) * y i)) =
        (∑ i : Fin 4, y i * H i) -
          Y * (∑ i : Fin 4, p i * H i) := by
    dsimp [H, Y]
    simp only [Fin.sum_univ_four] at hpSum ⊢
    have hp3 : p 3 = 1 - p 0 - p 1 - p 2 := by linarith
    rw [hp3]
    ring
  dsimp [p, y, E, Y] at hdecomp ⊢
  linarith

/-! ### Pointwise central decay -/

private theorem phaseMidpointCentral_rho_rate_le
    (n : Nat)
    (hAlphaLarge : (384 : Real) ≤ (phaseNat n : Real))
    (hAlphaLog : logOrder n ≤ (phaseNat n : Real))
    (hLogLogPos : 0 < logLogOrder n)
    (hTargetUpper :
      fourSizeTarget n (phaseNat n)
        (phaseCochromaticMidpointIndex n : Real) ≤ 4)
    (hadm : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticMidpointIndex n))
    (ell : Fin 4 → Nat)
    (hell : IsPartialSubprofile
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n)) ell)
    (hNotEmpty : ¬ midpointPartialDiagonalEmptyRange n ell)
    (hNotFull : ¬ (n - selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32)) :
    (n : Real) * midpointPartialDiagonalRho n (phaseNat n) ell *
          Real.log (midpointPartialDiagonalRho n (phaseNat n) ell) +
        (phaseCochromaticMidpointIndex n : Real) *
          (q / 2 * (phaseNat n : Real) *
            (phaseMidpointResidualDeficit n ell -
              fourSizeTarget n (phaseNat n)
                  (phaseCochromaticMidpointIndex n : Real) *
                phaseMidpointResidualFraction n ell)) ≤
      -(1 / 5000 : Real) *
          (phaseCochromaticMidpointIndex n : Real) *
          (phaseNat n : Real) * phaseMidpointSelectedFraction n ell +
        384 * (phaseCochromaticMidpointIndex n : Real) *
          phaseMidpointSelectedFraction n ell +
        4 * (phaseCochromaticMidpointIndex n : Real) := by
  let K : Nat := phaseCochromaticMidpointIndex n
  let a : Real := (phaseNat n : Real)
  let p : Fin 4 → Real := midpointPartialDiagonalP n (phaseNat n) K
  let y : Fin 4 → Real := midpointPartialDiagonalY K ell
  let T : Real := fourSizeTarget n (phaseNat n) (K : Real)
  let R : Real := ∑ i : Fin 4, (p i - y i)
  let Y : Real := ∑ i : Fin 4, y i
  let Ir : Real := ∑ i : Fin 4, (fourDeficit i : Real) * (p i - y i)
  let rho : Real := midpointPartialDiagonalRho n (phaseNat n) ell
  have hKnat : 0 < K := hadm.2.1
  have hK : 0 < (K : Real) := by exact_mod_cast hKnat
  have ha : 0 < a := by dsimp [a]; linarith
  have hpFacts := midpointPartialDiagonalP_facts n (phaseNat n) K hadm
  have hpSum : ∑ i : Fin 4, p i = 1 := by simpa only [p] using hpFacts.2.2.1
  have hpMean : ∑ i : Fin 4, (fourDeficit i : Real) * p i = T := by
    simpa only [p, T] using hpFacts.2.2.2
  have hyNonneg : ∀ i, 0 ≤ y i := by
    intro i
    dsimp [y, midpointPartialDiagonalY]
    positivity
  have hyLe : ∀ i, y i ≤ p i := by
    intro i
    dsimp [y, p, midpointPartialDiagonalY, midpointPartialDiagonalP]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hell i) (Nat.cast_nonneg K)
  have hYNonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ ↦ hyNonneg i
  have hR : R = 1 - Y := by
    dsimp [R]
    rw [Finset.sum_sub_distrib, hpSum]
  have hScale := phaseMidpointCentral_scale_facts n hAlphaLarge hAlphaLog
    hLogLogPos hTargetUpper hadm ell hell hNotEmpty hNotFull
  have hRlow : (1 : Real) / 64 ≤ R := by
    simpa only [R, p, y, K, phaseMidpointResidualFraction] using hScale.1
  have hRone : R ≤ 1 := by
    simpa only [R, p, y, K, phaseMidpointResidualFraction] using hScale.2.1
  have hRnonneg : 0 ≤ R := (by norm_num : (0 : Real) ≤ 1 / 64).trans hRlow
  have hRhoLow : (1 : Real) / 64 ≤ rho := by
    simpa only [rho] using hScale.2.2.1
  have hRhoOne : rho ≤ 1 := by
    simpa only [rho] using hScale.2.2.2.1
  have hDiff : |rho - R| ≤ 6 * Y / a := by
    simpa only [rho, R, Y, p, y, K, a,
      phaseMidpointResidualFraction, phaseMidpointSelectedFraction] using
        hScale.2.2.2.2.1
  have hTupper : T ≤ 4 := by simpa only [T, K] using hTargetUpper
  have hTpos : 0 < T := by
    have := hadm.2.2.2.1.1
    simpa only [T, K] using (lt_trans (by norm_num : (0 : Real) < 2) this)
  have hRate : partialDiagonalRate T R Ir ≤ -Y / 5000 := by
    have h := partialDiagonalRate_uniform_negative_fourDeficit T p y hTupper
      hyNonneg hyLe hpSum hpMean hRlow
    change partialDiagonalRate T R Ir ≤ -(1 - R) / 5000 at h
    calc
      partialDiagonalRate T R Ir = partialDiagonalRate T (1 - Y) Ir := by rw [hR]
      _ ≤ -(1 - (1 - Y)) / 5000 := by simpa only [hR] using h
      _ = -Y / 5000 := by ring
  have hMass : (n : Real) = (K : Real) * (a - T) := by
    dsimp [a, T, fourSizeTarget]
    field_simp [hK.ne']
    ring
  have hnNonneg : (0 : Real) ≤ n := Nat.cast_nonneg n
  have hnLe : (n : Real) ≤ (K : Real) * a := by
    rw [hMass]
    nlinarith [hK.le, hTpos.le]
  have hRhoLip := mul_log_le_mul_log_add_sixtyFour_abs_sub
    hRhoLow hRlow hRhoOne hRone
  have hRhoTerm :
      (n : Real) * rho * Real.log rho ≤
        (n : Real) * (R * Real.log R) + 384 * (K : Real) * Y := by
    have hLipScaled := mul_le_mul_of_nonneg_left hRhoLip hnNonneg
    have hErrNonneg : 0 ≤ 6 * Y / a := div_nonneg
      (mul_nonneg (by norm_num) hYNonneg) ha.le
    have hErr :
        (n : Real) * 64 * |rho - R| ≤ 384 * (K : Real) * Y := by
      calc
        (n : Real) * 64 * |rho - R| ≤
            (n : Real) * 64 * (6 * Y / a) :=
          mul_le_mul_of_nonneg_left hDiff
            (mul_nonneg hnNonneg (by norm_num))
        _ ≤ ((K : Real) * a) * 64 * (6 * Y / a) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hnLe (by norm_num)) hErrNonneg
        _ = 384 * (K : Real) * Y := by field_simp [ha.ne']; ring
    linarith
  have hNegRLog : -(R * Real.log R) ≤ 1 := by
    have hrel := ProfileEntropyS4.neg_mul_log_add_mul_log_le_sub
      hRnonneg (by norm_num : (0 : Real) < 1)
    norm_num at hrel
    linarith
  have hNegRLogNonneg : 0 ≤ -(R * Real.log R) := by
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hRnonneg
      (Real.log_nonpos hRnonneg hRone))
  have hTError : -(T * (R * Real.log R)) ≤ 4 := by
    have hmul := mul_le_mul hTupper hNegRLog hNegRLogNonneg
      (by norm_num : (0 : Real) ≤ 4)
    calc
      -(T * (R * Real.log R)) = T * (-(R * Real.log R)) := by ring
      _ ≤ 4 * 1 := hmul
      _ = 4 := by ring
  have hRateScaled := mul_le_mul_of_nonneg_left hRate
    (mul_nonneg hK.le ha.le)
  have hTScaled := mul_le_mul_of_nonneg_left hTError hK.le
  have hIdentity :
      (n : Real) * (R * Real.log R) +
          (K : Real) * (q / 2 * a * (Ir - T * R)) =
        (K : Real) * a * partialDiagonalRate T R Ir -
          (K : Real) * T * (R * Real.log R) := by
    rw [hMass]
    unfold partialDiagonalRate
    ring
  change (n : Real) * rho * Real.log rho +
      (K : Real) * (q / 2 * a * (Ir - T * R)) ≤
    -(1 / 5000 : Real) * (K : Real) * a * Y +
      384 * (K : Real) * Y + 4 * (K : Real)
  calc
    (n : Real) * rho * Real.log rho +
          (K : Real) * (q / 2 * a * (Ir - T * R)) ≤
        ((n : Real) * (R * Real.log R) + 384 * (K : Real) * Y) +
          (K : Real) * (q / 2 * a * (Ir - T * R)) :=
      add_le_add hRhoTerm le_rfl
    _ = ((n : Real) * (R * Real.log R) +
          (K : Real) * (q / 2 * a * (Ir - T * R))) +
        384 * (K : Real) * Y := by ring
    _ = ((K : Real) * a * partialDiagonalRate T R Ir -
          (K : Real) * T * (R * Real.log R)) +
        384 * (K : Real) * Y := by rw [hIdentity]
    _ = ((K : Real) * a * partialDiagonalRate T R Ir +
          (K : Real) * (-(T * (R * Real.log R)))) +
        384 * (K : Real) * Y := by ring
    _ ≤ ((K : Real) * a * (-Y / 5000) + (K : Real) * 4) +
        384 * (K : Real) * Y :=
      add_le_add (add_le_add hRateScaled hTScaled) le_rfl
    _ = -(1 / 5000 : Real) * (K : Real) * a * Y +
        384 * (K : Real) * Y + 4 * (K : Real) := by ring

private theorem phaseMidpointCentral_log_weight_le
    (n : Nat) (C : Real)
    (hAlphaLarge : (384 : Real) ≤ (phaseNat n : Real))
    (hAlphaLog : logOrder n ≤ (phaseNat n : Real))
    (hLogLogPos : 0 < logLogOrder n)
    (hTargetUpper :
      fourSizeTarget n (phaseNat n)
        (phaseCochromaticMidpointIndex n : Real) ≤ 4)
    (hadm : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticMidpointIndex n))
    (hEavg :
      ∑ i : Fin 4,
          midpointPartialDiagonalP n (phaseNat n)
              (phaseCochromaticMidpointIndex n) i *
            midpointPartialDiagonalE n (phaseNat n)
              (phaseCochromaticMidpointIndex n) i ≤ 4)
    (hcenter : ∀ i : Fin 4,
      |midpointPartialDiagonalE n (phaseNat n)
            (phaseCochromaticMidpointIndex n) i -
          midpointPartialDiagonalE n (phaseNat n)
            (phaseCochromaticMidpointIndex n) (0 : Fin 4) +
          q / 2 * (phaseNat n : Real) *
            ((fourDeficit i : Real) - 2)| ≤
        (1 / 40000 : Real) * (phaseNat n : Real))
    (ell : Fin 4 → Nat)
    (hell : IsPartialSubprofile
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n)) ell)
    (hNotEmpty : ¬ midpointPartialDiagonalEmptyRange n ell)
    (hNotFull : ¬ (n - selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32))
    (hEnvelope :
      Real.log
          (partialDiagonalWeight n
            (midpointPartialDiagonalSize (phaseNat n))
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)) ell) ≤
        (n : Real) * midpointPartialDiagonalRho n (phaseNat n) ell *
            Real.log (midpointPartialDiagonalRho n (phaseNat n) ell) +
          (phaseCochromaticMidpointIndex n : Real) *
            ∑ i : Fin 4,
              (2 * midpointPartialDiagonalP n (phaseNat n)
                    (phaseCochromaticMidpointIndex n) i *
                    Real.log (midpointPartialDiagonalP n (phaseNat n)
                      (phaseCochromaticMidpointIndex n) i) -
                2 * midpointPartialDiagonalZ n (phaseNat n)
                    (phaseCochromaticMidpointIndex n) ell i *
                    Real.log (midpointPartialDiagonalZ n (phaseNat n)
                      (phaseCochromaticMidpointIndex n) ell i) -
                midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i *
                    Real.log (midpointPartialDiagonalY
                      (phaseCochromaticMidpointIndex n) ell i) -
                midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i +
                midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i *
                    midpointPartialDiagonalE n (phaseNat n)
                      (phaseCochromaticMidpointIndex n) i) +
          C * logOrder n) :
    Real.log
        (partialDiagonalWeight n
          (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)) ell) ≤
      -(3 / 20000 : Real) *
          (phaseCochromaticMidpointIndex n : Real) *
          (phaseNat n : Real) * phaseMidpointSelectedFraction n ell +
        388 * (phaseCochromaticMidpointIndex n : Real) *
          phaseMidpointSelectedFraction n ell +
        8 * (phaseCochromaticMidpointIndex n : Real) + C * logOrder n := by
  let K : Nat := phaseCochromaticMidpointIndex n
  let a : Real := (phaseNat n : Real)
  let p : Fin 4 → Real := midpointPartialDiagonalP n (phaseNat n) K
  let y : Fin 4 → Real := midpointPartialDiagonalY K ell
  let E : Fin 4 → Real := midpointPartialDiagonalE n (phaseNat n) K
  let T : Real := fourSizeTarget n (phaseNat n) (K : Real)
  let R : Real := ∑ i : Fin 4, (p i - y i)
  let Y : Real := ∑ i : Fin 4, y i
  let Ir : Real := ∑ i : Fin 4, (fourDeficit i : Real) * (p i - y i)
  let rho : Real := midpointPartialDiagonalRho n (phaseNat n) ell
  have hKnat : 0 < K := hadm.2.1
  have hK : 0 < (K : Real) := by exact_mod_cast hKnat
  have hpFacts := midpointPartialDiagonalP_facts n (phaseNat n) K hadm
  have hpPos : ∀ i, 0 < p i := by simpa only [p] using hpFacts.1
  have hpOne : ∀ i, p i ≤ 1 := by simpa only [p] using hpFacts.2.1
  have hpSum : ∑ i : Fin 4, p i = 1 := by simpa only [p] using hpFacts.2.2.1
  have hpMean : ∑ i : Fin 4, (fourDeficit i : Real) * p i = T := by
    simpa only [p, T] using hpFacts.2.2.2
  have hyNonneg : ∀ i, 0 ≤ y i := by
    intro i
    dsimp [y, midpointPartialDiagonalY]
    positivity
  have hyLe : ∀ i, y i ≤ p i := by
    intro i
    dsimp [y, p, midpointPartialDiagonalY, midpointPartialDiagonalP]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hell i) (Nat.cast_nonneg K)
  have hYNonneg : 0 ≤ Y := Finset.sum_nonneg fun i _ ↦ hyNonneg i
  have hR : R = 1 - Y := by
    dsimp [R]
    rw [Finset.sum_sub_distrib, hpSum]
  have hEntropy :
      (∑ i : Fin 4,
        (2 * p i * Real.log (p i) -
          2 * (p i - y i) * Real.log (p i - y i) -
          y i * Real.log (y i) - y i)) ≤ 4 :=
    partialDiagonal_sum_coordinateEntropy_le_four p y hpPos hpOne hyNonneg hyLe
  have hCorrection :
      T * Y - ∑ i : Fin 4, (fourDeficit i : Real) * y i = Ir - T * R := by
    have hIr : Ir = T - ∑ i : Fin 4, (fourDeficit i : Real) * y i := by
      dsimp [Ir]
      calc
        _ = (∑ i : Fin 4, (fourDeficit i : Real) * p i) -
            ∑ i : Fin 4, (fourDeficit i : Real) * y i := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hpMean]
    rw [hIr, hR]
    ring
  have hYEraw := midpointPartialDiagonal_sum_y_mul_E_le
    n (phaseNat n) K ell (1 / 40000 : Real) (by norm_num) hadm hell
    (by simpa only [E, K] using hcenter)
  have hYEraw' :
      (∑ i : Fin 4, y i * E i) ≤
        Y * (∑ i : Fin 4, p i * E i) +
          q / 2 * a *
            ((∑ i : Fin 4, (fourDeficit i : Real) * p i) * Y -
              ∑ i : Fin 4, (fourDeficit i : Real) * y i) +
          2 * (1 / 40000 : Real) * a * Y := by
    simpa only [p, y, E, Y, a] using hYEraw
  have hYE :
      (∑ i : Fin 4, y i * E i) ≤
        4 * Y + q / 2 * a * (Ir - T * R) +
          (1 / 20000 : Real) * a * Y := by
    have hScaledE := mul_le_mul_of_nonneg_left hEavg hYNonneg
    rw [hpMean, hCorrection] at hYEraw'
    linarith
  have hBase :
      (n : Real) * rho * Real.log rho +
          (K : Real) * (q / 2 * a * (Ir - T * R)) ≤
        -(1 / 5000 : Real) * (K : Real) * a * Y +
          384 * (K : Real) * Y + 4 * (K : Real) := by
    simpa only [rho, K, a, T, R, Y, Ir, p, y,
      phaseMidpointResidualFraction, phaseMidpointSelectedFraction,
      phaseMidpointResidualDeficit] using
        phaseMidpointCentral_rho_rate_le n hAlphaLarge hAlphaLog hLogLogPos
          hTargetUpper hadm ell hell hNotEmpty hNotFull
  have hSplit :
      (∑ i : Fin 4,
        (2 * p i * Real.log (p i) -
          2 * (p i - y i) * Real.log (p i - y i) -
          y i * Real.log (y i) - y i + y i * E i)) =
        (∑ i : Fin 4,
          (2 * p i * Real.log (p i) -
            2 * (p i - y i) * Real.log (p i - y i) -
            y i * Real.log (y i) - y i)) +
          ∑ i : Fin 4, y i * E i := by
    rw [← Finset.sum_add_distrib]
  change Real.log
      (partialDiagonalWeight n (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n) K) ell) ≤
    (n : Real) * rho * Real.log rho +
      (K : Real) *
        ∑ i : Fin 4,
          (2 * p i * Real.log (p i) -
            2 * (p i - y i) * Real.log (p i - y i) -
            y i * Real.log (y i) - y i + y i * E i) +
      C * logOrder n at hEnvelope
  rw [hSplit] at hEnvelope
  change Real.log
      (partialDiagonalWeight n (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n) K) ell) ≤
    -(3 / 20000 : Real) * (K : Real) * a * Y +
      388 * (K : Real) * Y + 8 * (K : Real) + C * logOrder n
  nlinarith [mul_le_mul_of_nonneg_left hEntropy hK.le,
    mul_le_mul_of_nonneg_left hYE hK.le]

private theorem phaseMidpointCentral_log_weight_strong
    (n : Nat) (C : Real)
    (hC : 0 ≤ C)
    (hAlphaHuge : (3880000 : Real) ≤ (phaseNat n : Real))
    (hAlphaLog : logOrder n ≤ (phaseNat n : Real))
    (hLogLogHuge :
      2000000 * (8 + C) ≤ logLogOrder n)
    (hEight : 8 * logOrder n ≤
      (phaseCochromaticMidpointIndex n : Real))
    (hTargetUpper :
      fourSizeTarget n (phaseNat n)
        (phaseCochromaticMidpointIndex n : Real) ≤ 4)
    (hadm : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticMidpointIndex n))
    (hEavg :
      ∑ i : Fin 4,
          midpointPartialDiagonalP n (phaseNat n)
              (phaseCochromaticMidpointIndex n) i *
            midpointPartialDiagonalE n (phaseNat n)
              (phaseCochromaticMidpointIndex n) i ≤ 4)
    (hcenter : ∀ i : Fin 4,
      |midpointPartialDiagonalE n (phaseNat n)
            (phaseCochromaticMidpointIndex n) i -
          midpointPartialDiagonalE n (phaseNat n)
            (phaseCochromaticMidpointIndex n) (0 : Fin 4) +
          q / 2 * (phaseNat n : Real) *
            ((fourDeficit i : Real) - 2)| ≤
        (1 / 40000 : Real) * (phaseNat n : Real))
    (ell : Fin 4 → Nat)
    (hell : IsPartialSubprofile
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n)) ell)
    (hNotEmpty : ¬ midpointPartialDiagonalEmptyRange n ell)
    (hNotFull : ¬ (n - selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32))
    (hEnvelope :
      Real.log
          (partialDiagonalWeight n
            (midpointPartialDiagonalSize (phaseNat n))
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)) ell) ≤
        (n : Real) * midpointPartialDiagonalRho n (phaseNat n) ell *
            Real.log (midpointPartialDiagonalRho n (phaseNat n) ell) +
          (phaseCochromaticMidpointIndex n : Real) *
            ∑ i : Fin 4,
              (2 * midpointPartialDiagonalP n (phaseNat n)
                    (phaseCochromaticMidpointIndex n) i *
                    Real.log (midpointPartialDiagonalP n (phaseNat n)
                      (phaseCochromaticMidpointIndex n) i) -
                2 * midpointPartialDiagonalZ n (phaseNat n)
                    (phaseCochromaticMidpointIndex n) ell i *
                    Real.log (midpointPartialDiagonalZ n (phaseNat n)
                      (phaseCochromaticMidpointIndex n) ell i) -
                midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i *
                    Real.log (midpointPartialDiagonalY
                      (phaseCochromaticMidpointIndex n) ell i) -
                midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i +
                midpointPartialDiagonalY (phaseCochromaticMidpointIndex n) ell i *
                    midpointPartialDiagonalE n (phaseNat n)
                      (phaseCochromaticMidpointIndex n) i) +
          C * logOrder n) :
    Real.log
        (partialDiagonalWeight n
          (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)) ell) ≤
      -(phaseCochromaticMidpointIndex n : Real) * logLogOrder n /
        10000000 := by
  let K : Real := phaseCochromaticMidpointIndex n
  let a : Real := phaseNat n
  let Y : Real := phaseMidpointSelectedFraction n ell
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast hadm.2.1
  have hY : 0 ≤ Y := by
    dsimp [Y, phaseMidpointSelectedFraction, midpointPartialDiagonalY]
    positivity
  have hLogLogPos : 0 < logLogOrder n := by
    nlinarith [hC, hLogLogHuge]
  have hWeak := phaseMidpointCentral_log_weight_le n C
    (hAlphaHuge.trans' (by norm_num)) hAlphaLog hLogLogPos hTargetUpper
    hadm hEavg hcenter ell hell hNotEmpty hNotFull hEnvelope
  have hScale := phaseMidpointCentral_scale_facts n
    (hAlphaHuge.trans' (by norm_num)) hAlphaLog hLogLogPos hTargetUpper
    hadm ell hell hNotEmpty hNotFull
  have hSelected : logLogOrder n / 64 ≤ a * Y := by
    simpa only [a, Y] using hScale.2.2.2.2.2
  have hAbsorbY : 388 * K * Y ≤ (1 / 10000 : Real) * K * a * Y := by
    have hmul := mul_le_mul_of_nonneg_left hAlphaHuge
      (mul_nonneg hK.le hY)
    dsimp [K, a, Y] at hmul ⊢
    nlinarith
  have hCL : C * logOrder n ≤ C * K / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hEight hC
    dsimp [K] at hmul ⊢
    nlinarith
  have hConstant : 8 * K + C * logOrder n ≤ (8 + C) * K := by
    have hCK : 0 ≤ C * K := mul_nonneg hC hK.le
    nlinarith
  have hLogAbsorb : (8 + C) * K ≤ K * logLogOrder n / 2000000 := by
    have hmul := mul_le_mul_of_nonneg_right hLogLogHuge hK.le
    nlinarith
  have hSelectedScaled : K * logLogOrder n / 64 ≤ K * a * Y := by
    have hmul := mul_le_mul_of_nonneg_left hSelected hK.le
    nlinarith
  dsimp [K, a, Y] at hAbsorbY hConstant hLogAbsorb hSelectedScaled
  nlinarith

/-! ### Central aggregate -/

private noncomputable def phaseMidpointCentralSum (n : Nat) : Real := by
  classical
  exact
    ∑ ell ∈
        (partialSubprofileBox
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n))).filter
          (fun ell =>
            ¬ midpointPartialDiagonalEmptyRange n ell ∧
            ¬ (n - selectedVertexMass
              (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32)),
      partialDiagonalWeight n
        (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticMidpointIndex n)) ell

private theorem phaseMidpointCentralSum_nonneg (n : Nat) :
    0 ≤ phaseMidpointCentralSum n := by
  classical
  unfold phaseMidpointCentralSum
  apply Finset.sum_nonneg
  intro ell hell
  have hbox := (Finset.mem_filter.mp hell).1
  exact (partialDiagonalWeight_pos n
    (midpointPartialDiagonalSize (phaseNat n))
    (midpointMultiplicity n (phaseNat n)
      (phaseCochromaticMidpointIndex n)) ell
    (mem_partialSubprofileBox.mp hbox)).le

private theorem tendsto_phaseMidpointCentralSum_zero :
    Tendsto phaseMidpointCentralSum atTop (nhds 0) := by
  classical
  obtain ⟨C, hC, N₀, hEnvelope⟩ :=
    partialDiagonal_log_upper_envelope_midpoint_fourDeficit
  have hAlphaHuge : ∀ᶠ n : Nat in atTop,
      (3880000 : Real) ≤ (phaseNat n : Real) := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop 3880000,
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
        n hL hphase
    exact hL.trans hphase.1
  have hLogLogHuge : ∀ᶠ n : Nat in atTop,
      2000000 * (8 + C) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop (2000000 * (8 + C))
  have hUpper : ∀ᶠ n : Nat in atTop,
      phaseMidpointCentralSum n ≤ Real.exp (-4 * logOrder n) := by
    filter_upwards
      [eventually_ge_atTop N₀,
        eventually_ge_atTop 3,
        hAlphaHuge,
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
        hLogLogHuge,
        eventually_eight_logOrder_le_phaseMidpointIndex,
        eventually_phaseMidpoint_fourSizeTarget_le_four,
        eventually_phaseCochromaticMidpointIndex_rounding_admissible,
        eventually_midpointPartialDiagonalE_average_le_four,
        eventually_abs_phaseCenteredEError_le (1 / 40000 : Real) (by norm_num),
        tendsto_logOrder_atTop.eventually_gt_atTop 0] with
      n hN₀ hn hAlpha hPhase hLogLog hEight hTarget hadm hEavg hcenter hLpos
    let K : Nat := phaseCochromaticMidpointIndex n
    let k : Fin 4 → Nat := midpointMultiplicity n (phaseNat n) K
    let box : Finset (Fin 4 → Nat) := partialSubprofileBox k
    let central : Finset (Fin 4 → Nat) := box.filter
      (fun ell =>
        ¬ midpointPartialDiagonalEmptyRange n ell ∧
        ¬ (n - selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32))
    let w : (Fin 4 → Nat) → Real := fun ell =>
      partialDiagonalWeight n
        (midpointPartialDiagonalSize (phaseNat n)) k ell
    have hPoint : ∀ ell ∈ central,
        w ell ≤ Real.exp (-(K : Real) * logLogOrder n / 10000000) := by
      intro ell hellCentral
      have hmem := Finset.mem_filter.mp hellCentral
      have hell : IsPartialSubprofile k ell :=
        mem_partialSubprofileBox.mp (by simpa only [box] using hmem.1)
      have henv := hEnvelope n (phaseNat n) K hN₀ hadm ell (by simpa only [k] using hell)
      have hlog := phaseMidpointCentral_log_weight_strong n C hC hAlpha
        hPhase.1 hLogLog hEight hTarget hadm hEavg
        (by simpa only [phaseCenteredEError, K] using hcenter)
        ell (by simpa only [k] using hell) hmem.2.1 hmem.2.2 henv
      have hwpos : 0 < w ell := by
        dsimp [w]
        exact partialDiagonalWeight_pos n
          (midpointPartialDiagonalSize (phaseNat n)) k ell hell
      rw [← Real.exp_log hwpos]
      exact Real.exp_le_exp.mpr (by simpa only [K, k, w] using hlog)
    have hSumPoint :
        phaseMidpointCentralSum n ≤
          (central.card : Real) *
            Real.exp (-(K : Real) * logLogOrder n / 10000000) := by
      have hLocal : (∑ ell ∈ central, w ell) ≤
          (central.card : Real) *
            Real.exp (-(K : Real) * logLogOrder n / 10000000) := by
        calc
          (∑ ell ∈ central, w ell) ≤
              ∑ _ell ∈ central,
                Real.exp (-(K : Real) * logLogOrder n / 10000000) := by
            exact Finset.sum_le_sum fun ell hell ↦ hPoint ell hell
          _ = (central.card : Real) *
              Real.exp (-(K : Real) * logLogOrder n / 10000000) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      simpa only [phaseMidpointCentralSum, central, box, w, k, K] using hLocal
    have hCount :=
      (midpointMultiplicity_count_deficit_intDisplacement
        n (phaseNat n) K hadm).1
    have hkLeK : ∀ i : Fin 4, k i ≤ K := by
      intro i
      have hi := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 4)))
        (f := k) (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      simpa only [k, hCount] using hi
    have hMass := midpointMultiplicity_vertexMass n (phaseNat n) K hadm
    have hKleN : K ≤ n := by
      calc
        K = ∑ i : Fin 4, k i := by simpa only [k] using hCount.symm
        _ ≤ ∑ i : Fin 4,
            (phaseNat n - fourDeficit i) * k i := by
          apply Finset.sum_le_sum
          intro i _
          have hsize : 1 ≤ phaseNat n - fourDeficit i := by
            have hi := i.isLt
            have halpha := hadm.1
            simp only [fourDeficit]
            omega
          exact Nat.le_mul_of_pos_left _ hsize
        _ = n := by simpa only [k] using hMass
    have hkLeN : ∀ i : Fin 4, k i ≤ n :=
      fun i ↦ (hkLeK i).trans hKleN
    have hCardNat : central.card ≤ (n + 1) ^ 4 := by
      calc
        central.card ≤ box.card := Finset.card_filter_le _ _
        _ = ∏ i : Fin 4, (k i + 1) := by
          simpa only [box] using card_partialSubprofileBox k
        _ ≤ ∏ _i : Fin 4, (n + 1) := by
          exact Finset.prod_le_prod' fun i _ ↦ Nat.add_le_add_right (hkLeN i) 1
        _ = (n + 1) ^ 4 := by norm_num [Fin.prod_univ_four]
    have hnR : (0 : Real) < (n : Real) := by exact_mod_cast (show 0 < n by omega)
    have hnTwo : 2 ≤ n := by omega
    have hSucc : ((n + 1 : Nat) : Real) ≤ (n : Real) ^ 2 := by
      exact_mod_cast (show n + 1 ≤ n ^ 2 by nlinarith)
    have hCardExp : (central.card : Real) ≤ Real.exp (8 * logOrder n) := by
      calc
        (central.card : Real) ≤ (((n + 1) ^ 4 : Nat) : Real) := by
          exact_mod_cast hCardNat
        _ = (((n + 1 : Nat) : Real) ^ 4) := by norm_cast
        _ ≤ (((n : Real) ^ 2) ^ 4) :=
          pow_le_pow_left₀ (by positivity) hSucc 4
        _ = (n : Real) ^ 8 := by ring
        _ = Real.exp (8 * logOrder n) := by
          rw [← Real.exp_log (pow_pos hnR 8), Real.log_pow]
          simp only [logOrder]
          ring
    have hW : (15000000 : Real) ≤ logLogOrder n := by
      nlinarith [hC, hLogLog]
    have hKnonneg : 0 ≤ (K : Real) := by positivity
    have hWnonneg : 0 ≤ logLogOrder n := by linarith
    have hProdLower :
        12 * logOrder n ≤ (K : Real) * logLogOrder n / 10000000 := by
      have hKW := mul_le_mul hEight hW
        (by norm_num : (0 : Real) ≤ 15000000) hKnonneg
      nlinarith
    calc
      phaseMidpointCentralSum n ≤
          (central.card : Real) *
            Real.exp (-(K : Real) * logLogOrder n / 10000000) := hSumPoint
      _ ≤ Real.exp (8 * logOrder n) *
            Real.exp (-(K : Real) * logLogOrder n / 10000000) :=
        mul_le_mul_of_nonneg_right hCardExp (Real.exp_pos _).le
      _ = Real.exp
          (8 * logOrder n - (K : Real) * logLogOrder n / 10000000) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-4 * logOrder n) :=
        Real.exp_le_exp.mpr (by linarith)
  have hDecay : Tendsto (fun n : Nat ↦ Real.exp (-4 * logOrder n))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_logOrder_atTop.const_mul_atTop_of_neg (by norm_num))
  exact squeeze_zero'
    (Filter.Eventually.of_forall phaseMidpointCentralSum_nonneg)
    hUpper hDecay

/-! ### Three-range assembly -/

private noncomputable def phaseMidpointEmptySum (n : Nat) : Real := by
  classical
  exact
    ∑ ell ∈
        (partialSubprofileBox
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n))).filter
          (fun ell => midpointPartialDiagonalEmptyRange n ell),
      partialDiagonalWeight n
        (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticMidpointIndex n)) ell

private theorem tendsto_phaseMidpointEmptySum_one :
    Tendsto phaseMidpointEmptySum atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hRange := eventually_sum_midpointPartialDiagonal_empty_mem_Icc
    (epsilon / 2) (half_pos hepsilon)
  have hEventually : ∀ᶠ n : Nat in atTop,
      dist (phaseMidpointEmptySum n) 1 < epsilon := by
    filter_upwards [hRange,
      eventually_phaseCochromaticMidpointIndex_rounding_admissible] with
        n hRangeN hadm
    have h := hRangeN (phaseCochromaticMidpointIndex n) hadm
    have h' : phaseMidpointEmptySum n ∈
        Set.Icc (1 : Real) (1 + epsilon / 2) := by
      simpa only [phaseMidpointEmptySum] using h
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [h'.1, h'.2]
  rw [Filter.eventually_atTop] at hEventually
  exact hEventually

private noncomputable def phaseMidpointRestrictedFullSum (n : Nat) : Real := by
  classical
  exact
    ∑ ell ∈
        (partialSubprofileBox
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n))).filter
          (fun ell =>
            ¬ midpointPartialDiagonalEmptyRange n ell ∧
            n - selectedVertexMass
              (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32),
      partialDiagonalWeight n
        (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticMidpointIndex n)) ell

private theorem phaseMidpointRestrictedFullSum_nonneg (n : Nat) :
    0 ≤ phaseMidpointRestrictedFullSum n := by
  classical
  unfold phaseMidpointRestrictedFullSum
  apply Finset.sum_nonneg
  intro ell hell
  have hbox := (Finset.mem_filter.mp hell).1
  exact (partialDiagonalWeight_pos n
    (midpointPartialDiagonalSize (phaseNat n))
    (midpointMultiplicity n (phaseNat n)
      (phaseCochromaticMidpointIndex n)) ell
    (mem_partialSubprofileBox.mp hbox)).le

private theorem phaseMidpointRestrictedFullSum_le (n : Nat) :
    phaseMidpointRestrictedFullSum n ≤ phaseMidpointFullCornerSum n := by
  classical
  unfold phaseMidpointRestrictedFullSum phaseMidpointFullCornerSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ell hell
    have hmem := Finset.mem_filter.mp hell
    exact Finset.mem_filter.mpr ⟨hmem.1, hmem.2.2⟩
  · intro ell hell _
    have hbox := (Finset.mem_filter.mp hell).1
    exact (partialDiagonalWeight_pos n
      (midpointPartialDiagonalSize (phaseNat n))
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n)) ell
      (mem_partialSubprofileBox.mp hbox)).le

private theorem tendsto_phaseMidpointRestrictedFullSum_zero :
    Tendsto phaseMidpointRestrictedFullSum atTop (nhds 0) :=
  squeeze_zero'
    (Filter.Eventually.of_forall phaseMidpointRestrictedFullSum_nonneg)
    (Filter.Eventually.of_forall phaseMidpointRestrictedFullSum_le)
    tendsto_phaseMidpointFullCornerSum_zero

private theorem phaseMidpoint_three_range_partition (n : Nat) :
    (∑ ell ∈ partialSubprofileBox
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)),
        partialDiagonalWeight n
          (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)) ell) =
      phaseMidpointEmptySum n + phaseMidpointCentralSum n +
        phaseMidpointRestrictedFullSum n := by
  classical
  let K : Nat := phaseCochromaticMidpointIndex n
  let k : Fin 4 → Nat := midpointMultiplicity n (phaseNat n) K
  let box : Finset (Fin 4 → Nat) := partialSubprofileBox k
  let empty : (Fin 4 → Nat) → Prop := fun ell =>
    midpointPartialDiagonalEmptyRange n ell
  let full : (Fin 4 → Nat) → Prop := fun ell =>
    n - selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n / 32
  let w : (Fin 4 → Nat) → Real := fun ell =>
    partialDiagonalWeight n
      (midpointPartialDiagonalSize (phaseNat n)) k ell
  have hFirst := Finset.sum_filter_add_sum_filter_not box empty w
  have hSecond := Finset.sum_filter_add_sum_filter_not
    (box.filter fun ell => ¬ empty ell) (fun ell => ¬ full ell) w
  have hRest :
      (∑ ell ∈ box.filter (fun ell => ¬ empty ell), w ell) =
        (∑ ell ∈ box.filter
            (fun ell => ¬ empty ell ∧ ¬ full ell), w ell) +
          ∑ ell ∈ box.filter
            (fun ell => ¬ empty ell ∧ full ell), w ell := by
    rw [← hSecond]
    simp only [Finset.filter_filter, not_not]
  have hLocal :
      (∑ ell ∈ box, w ell) =
        (∑ ell ∈ box.filter empty, w ell) +
          (∑ ell ∈ box.filter
              (fun ell => ¬ empty ell ∧ ¬ full ell), w ell) +
          ∑ ell ∈ box.filter
              (fun ell => ¬ empty ell ∧ full ell), w ell := by
    calc
      (∑ ell ∈ box, w ell) =
          (∑ ell ∈ box.filter empty, w ell) +
            ∑ ell ∈ box.filter (fun ell => ¬ empty ell), w ell :=
        hFirst.symm
      _ = _ := by rw [hRest]; ring
  simpa only [K, k, box, empty, full, w, phaseMidpointEmptySum,
    phaseMidpointCentralSum, phaseMidpointRestrictedFullSum] using hLocal

/-- The canonical midpoint partial-diagonal multiplier has asymptotic mass
one.  The proof is the literal disjoint decomposition into the empty range,
the central range, and the restricted full-corner range. -/
theorem tendsto_sum_midpointPartialDiagonalWeight :
    Tendsto
      (fun n =>
        ∑ ell ∈ partialSubprofileBox
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)),
          partialDiagonalWeight n
            (midpointPartialDiagonalSize (phaseNat n))
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)) ell)
      atTop (nhds 1) := by
  have hSum := tendsto_phaseMidpointEmptySum_one.add
    (tendsto_phaseMidpointCentralSum_zero.add
      tendsto_phaseMidpointRestrictedFullSum_zero)
  norm_num at hSum
  exact hSum.congr' (Filter.Eventually.of_forall fun n => by
    simpa only [add_assoc] using (phaseMidpoint_three_range_partition n).symm)

#print axioms tendsto_phaseMidpointFullCornerSum_zero
#print axioms tendsto_sum_midpointPartialDiagonalWeight

end

end Erdos625
