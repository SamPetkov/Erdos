import Erdos625.Section8FixedOffsetPhaseInputs
import Erdos625.SignedFourFirstMomentFiniteErrorAsymptotic
import Erdos625.PhaseSignedFourSizeLogLogCorridorCompactControl
import Erdos625.PhaseSignedFourSizeLogLogCorridorDerivativeLower
import Erdos625.PhaseRootLogLogCorridorScale
import Erdos625.Section11AsymptoticAssembly
import Erdos625.PartialDiagonalCentralLogEnvelope
import Erdos625.FullCornerWeights
import Mathlib.Tactic

/-!
# Concrete signed first moment at the fixed-offset selector

This module repeats the Section 12 signed first-moment estimate for the
manuscript *fixed-offset* cocolouring selector
`phaseCochromaticFixedOffsetIndex n = ⌈r_co⌉ + 16` instead of the root
midpoint.

Three public results are proved.

* `eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible`: every
  field of `MidpointRoundingAdmissible` holds eventually at the fixed-offset
  selector, including `n ≤ phaseNat n * K` and the uniform optimizer
  coordinate lower bound `14`.
* `eventually_phase_fixedOffset_partialSignedFirstMoment_log_lower`: the
  *quantitative* lower bound `(2 * q - 1) * phaseNat n ^ 2` for the logarithm
  of the partial signed first moment.  The exact lower selector displacement
  `K - r_co ≥ 16` and the corridor derivative lower bound `q / 8 * phaseNat ^ 2`
  give `signedFourSizeObjective n (phaseNat n) K ≥ 2 * q * phaseNat n ^ 2`
  from the signed-root identity `F r_co = 0`; the explicit finite error is
  eventually at most `phaseNat n ^ 2`.
* `phase_fixedOffset_completeSignedFirstMoment_tendsto_atTop`: divergence of
  the complete signed first moment, obtained by exponentiating the previous
  bound (`2 * q - 1 > 0` because `q = log 2 > 0.6931471803`) and identifying
  the partial and complete moments through `midpointMultiplicity_vertexMass`.

Nothing here touches the partial-diagonal, skeleton, seed, amplification, or
final assembly layers, and the existing midpoint development is not used.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- `2 * q - 1 > 0`, from the repository-certified lower bound for `log 2`. -/
private theorem two_q_sub_one_pos : 0 < 2 * q - 1 := by
  have hq : (0.6931471803 : ℝ) < q := Real.log_two_gt_d9
  linarith

/-- The fixed-offset selector eventually dominates `baseScale`.  Only the
four-size target control at the selector is used: `2 < phaseNat n - n / K`
forces `n < phaseNat n * K`, and `phaseNat n ≤ 4 * logOrder n`. -/
private theorem eventually_baseScale_le_phaseCochromaticFixedOffsetIndex :
    ∀ᶠ n : ℕ in atTop,
      baseScale n ≤ (phaseCochromaticFixedOffsetIndex n : ℝ) := by
  filter_upwards
    [eventually_phaseCochromaticFixedOffsetIndex_target_control,
      eventually_phaseFixedOffsetCorridorGeometry,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      tendsto_logOrder_atTop.eventually_ge_atTop 2] with
      n hTarget hGeom hPhase hLog
  have hKPos : (0 : ℝ) < (phaseCochromaticFixedOffsetIndex n : ℝ) := by
    exact_mod_cast hGeom.index_pos
  have hTargetLower :
      2 < (phaseNat n : ℝ) -
        (n : ℝ) / (phaseCochromaticFixedOffsetIndex n : ℝ) := by
    have := hTarget.1.1
    rwa [fourSizeTarget] at this
  have hDiv : (n : ℝ) / (phaseCochromaticFixedOffsetIndex n : ℝ) <
      (phaseNat n : ℝ) := by linarith
  have hnLt : (n : ℝ) <
      (phaseNat n : ℝ) * (phaseCochromaticFixedOffsetIndex n : ℝ) :=
    (div_lt_iff₀ hKPos).mp hDiv
  have hLogPos : (0 : ℝ) < logOrder n := by linarith
  have hCube : (0 : ℝ) < logOrder n ^ 3 := by positivity
  have hFour : (phaseNat n : ℝ) ≤ 4 * logOrder n := hPhase.2
  have hCubeGe : 4 * logOrder n ≤ logOrder n ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hLogPos.le (by linarith : (0 : ℝ) ≤
      logOrder n - 2)) (by linarith : (0 : ℝ) ≤ logOrder n + 2)]
  have hStep : (phaseNat n : ℝ) *
      (phaseCochromaticFixedOffsetIndex n : ℝ) ≤
      (phaseCochromaticFixedOffsetIndex n : ℝ) * logOrder n ^ 3 :=
    calc
      (phaseNat n : ℝ) * (phaseCochromaticFixedOffsetIndex n : ℝ)
          ≤ (4 * logOrder n) *
            (phaseCochromaticFixedOffsetIndex n : ℝ) :=
        mul_le_mul_of_nonneg_right hFour hKPos.le
      _ = (phaseCochromaticFixedOffsetIndex n : ℝ) * (4 * logOrder n) := by
        ring
      _ ≤ (phaseCochromaticFixedOffsetIndex n : ℝ) * logOrder n ^ 3 :=
        mul_le_mul_of_nonneg_left hCubeGe hKPos.le
  show (n : ℝ) / logOrder n ^ 3 ≤ (phaseCochromaticFixedOffsetIndex n : ℝ)
  rw [div_le_iff₀ hCube]
  linarith

private theorem tendsto_phaseCochromaticFixedOffsetIndex_real_atTop :
    Tendsto (fun n : ℕ ↦ (phaseCochromaticFixedOffsetIndex n : ℝ))
      atTop atTop := by
  have hBase : Tendsto baseScale atTop atTop := by
    exact tendsto_baseScale_atTop_unscaled
  exact tendsto_atTop_mono' atTop
    eventually_baseScale_le_phaseCochromaticFixedOffsetIndex hBase

/-- The fixed-offset selector eventually satisfies every finite four-size
rounding and optimizer condition required by the exact factorial bridge. -/
theorem eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible :
    ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (phaseCochromaticFixedOffsetIndex n) := by
  have hCNonneg : (0 : ℝ) ≤ phaseRootCommonCorridorCoefficient + 1 := by
    linarith [phaseRootCommonCorridorCoefficient_pos]
  obtain ⟨c, hc, hCompact⟩ :=
    exists_pos_eventually_phaseRootLogLogCorridor_fourSize_compact_control
      (phaseRootCommonCorridorCoefficient + 1) hCNonneg
  have hControl := hCompact 1 (by norm_num)
  have hLarge : ∀ᶠ n : ℕ in atTop,
      14 / c ≤ (phaseCochromaticFixedOffsetIndex n : ℝ) :=
    tendsto_phaseCochromaticFixedOffsetIndex_real_atTop.eventually_ge_atTop
      (14 / c)
  filter_upwards
    [eventually_phaseFixedOffsetCorridorGeometry,
      eventually_phaseCochromaticFixedOffsetIndex_target_control,
      eventually_five_lt_phaseNat, hControl, hLarge] with
      n hGeom hTarget hPhase hControlN hLargeN
  have hKPos : 0 < phaseCochromaticFixedOffsetIndex n := hGeom.index_pos
  have hKPosReal : (0 : ℝ) < (phaseCochromaticFixedOffsetIndex n : ℝ) := by
    exact_mod_cast hKPos
  have hKMem : ((phaseCochromaticFixedOffsetIndex n : ℕ) : ℝ) ∈ Icc
      (phaseRootCenter n -
        (phaseRootCommonCorridorCoefficient + 1) * logLogOrder n *
          phaseRootGapRadius n)
      (phaseRootCenter n +
        (phaseRootCommonCorridorCoefficient + 1) * logLogOrder n *
          phaseRootGapRadius n) := hGeom.index_mem
  have hnReal : (n : ℝ) <
      (phaseNat n : ℝ) * (phaseCochromaticFixedOffsetIndex n : ℝ) := by
    have hTargetLower :
        2 < (phaseNat n : ℝ) -
          (n : ℝ) / (phaseCochromaticFixedOffsetIndex n : ℝ) := by
      have := hTarget.1.1
      rwa [fourSizeTarget] at this
    have hnDiv : (n : ℝ) / (phaseCochromaticFixedOffsetIndex n : ℝ) <
        (phaseNat n : ℝ) := by linarith
    exact (div_lt_iff₀ hKPosReal).mp hnDiv
  have hn : n ≤ phaseNat n * phaseCochromaticFixedOffsetIndex n := by
    have hnNat : n < phaseNat n * phaseCochromaticFixedOffsetIndex n := by
      exact_mod_cast hnReal
    exact hnNat.le
  refine ⟨hPhase, hKPos, hn, hTarget.1, ?_⟩
  intro i
  have hOpt := (hControlN
    ((phaseCochromaticFixedOffsetIndex n : ℕ) : ℝ) hKMem).2 i
  have hScaled : (14 : ℝ) ≤
      ((phaseCochromaticFixedOffsetIndex n : ℕ) : ℝ) * c := by
    have hMul := mul_le_mul_of_nonneg_right hLargeN hc.le
    calc
      (14 : ℝ) = (14 / c) * c := by field_simp
      _ ≤ ((phaseCochromaticFixedOffsetIndex n : ℕ) : ℝ) * c := hMul
  have hKNonneg : (0 : ℝ) ≤ ((phaseCochromaticFixedOffsetIndex n : ℕ) : ℝ) := by
    positivity
  exact hScaled.trans (mul_le_mul_of_nonneg_left hOpt hKNonneg)

/-- The explicit finite first-moment error majorant is eventually dominated by
`phaseNat n ^ 2`. -/
private theorem
    eventually_signedFourFiniteFirstMomentErrorBound_le_phaseNat_sq' :
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
  have hFac : factorialLogErrorBound n < 2 * logOrder n :=
    (div_lt_iff₀ hLogPos).mp hRatioN
  have hPhaseSq : (logOrder n) ^ 2 ≤ (phaseNat n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hLogPos.le hPhase.1 2
  unfold signedFourFiniteFirstMomentErrorBound
  nlinarith [sq_nonneg (logOrder n - 30)]

/-- The quantitative signed first-moment lower bound at the fixed-offset
selector. -/
theorem eventually_phase_fixedOffset_partialSignedFirstMoment_log_lower :
    ∀ᶠ n : ℕ in atTop,
      (2 * q - 1) * (phaseNat n : ℝ) ^ 2 ≤
        Real.log
          (partialSignedFirstMoment n
            (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticFixedOffsetIndex n))) := by
  have hCNonneg : (0 : ℝ) ≤ phaseRootCommonCorridorCoefficient + 1 := by
    linarith [phaseRootCommonCorridorCoefficient_pos]
  have hDomain :=
    eventually_phaseRootLogLogCorridor_fourSize_domain
      (phaseRootCommonCorridorCoefficient + 1) hCNonneg
  have hDeriv :=
    eventually_signedFourSizeObjectiveDerivative_logLogCorridor_lower
      (phaseRootCommonCorridorCoefficient + 1) hCNonneg
  filter_upwards
    [eventually_phaseFixedOffsetCorridorGeometry,
      eventually_phaseSignedFourSizeRootSelected_spec_unique,
      eventually_abs_midpointPartialSignedFirstMomentLogError_le
        phaseNat phaseCochromaticFixedOffsetIndex
          eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible,
      eventually_signedFourFiniteFirstMomentErrorBound_le_phaseNat_sq',
      hDomain, hDeriv] with
      n hGeom hRoot hError hErrorSq hDomainN hDerivN
  set r : ℝ := phaseSignedFourSizeRootSelected n with hr
  set K : ℝ := ((phaseCochromaticFixedOffsetIndex n : ℕ) : ℝ) with hK
  set F : ℝ → ℝ := signedFourSizeObjective n (phaseNat n) with hF
  have hRK : r ≤ K := by
    have := hGeom.index_lower
    rw [← hr, ← hK] at this
    linarith
  have hDisplacement : (16 : ℝ) ≤ K - r := by
    have := hGeom.index_lower
    rw [← hr, ← hK] at this
    linarith
  have hInterval : Icc r K ⊆ Icc
      (phaseRootCenter n -
        (phaseRootCommonCorridorCoefficient + 1) * logLogOrder n *
          phaseRootGapRadius n)
      (phaseRootCenter n +
        (phaseRootCommonCorridorCoefficient + 1) * logLogOrder n *
          phaseRootGapRadius n) := by
    intro x hx
    exact hGeom.segment_mem x hx
  have hHasDeriv : ∀ x ∈ Icc r K,
      HasDerivAt F
        (signedFourSizeObjectiveDerivative n (phaseNat n) x) x := by
    intro x hx
    obtain ⟨hxPos, hTargetx⟩ := hDomainN x (hInterval hx)
    exact hasDerivAt_phaseSignedFourSizeObjective n hxPos hTargetx
  have hCont : ContinuousOn F (Icc r K) := fun x hx ↦
    (hHasDeriv x hx).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ F (Ioo r K) := fun x hx ↦
    (hHasDeriv x
      (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hLowerDeriv : ∀ x ∈ Ioo r K,
      q / 8 * (phaseNat n : ℝ) ^ 2 ≤ deriv F x := by
    intro x hx
    rw [(hHasDeriv x (Ioo_subset_Icc_self hx)).deriv]
    exact hDerivN x (hInterval (Ioo_subset_Icc_self hx))
  have hIncrement :=
    derivative_lower_bound_mul_sub_le_sub hRK hCont hDiff hLowerDeriv
  have hRootZero : F r = 0 := by
    simpa [hF, hr, IsPhaseSignedFourSizeRoot, isSignedFourSizeRoot_iff] using
      hRoot.1.2.2.2
  have hSlopeNonneg : 0 ≤ q / 8 * (phaseNat n : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg q_pos.le (by norm_num)) (sq_nonneg _)
  have hRaw : 2 * q * (phaseNat n : ℝ) ^ 2 ≤ F K := by
    rw [hRootZero] at hIncrement
    nlinarith [mul_le_mul_of_nonneg_left hDisplacement hSlopeNonneg]
  have hLogLower :
      F K - signedFourFiniteFirstMomentErrorBound n ≤
        Real.log
          (partialSignedFirstMoment n
            (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticFixedOffsetIndex n))) := by
    rw [abs_le] at hError
    dsimp [midpointPartialSignedFirstMomentLogError] at hError
    rw [hF, hK]
    linarith [hError.1]
  linarith

/-- The complete signed first moment of the fixed-offset profile tends to
infinity. -/
theorem phase_fixedOffset_completeSignedFirstMoment_tendsto_atTop :
    Tendsto
      (fun n =>
        completeSignedFirstMoment
          (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticFixedOffsetIndex n)))
      atTop atTop := by
  have hPhaseReal : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop
      (show (logOrder : ℕ → ℝ) ≤ᶠ[atTop] fun n : ℕ ↦ (phaseNat n : ℝ) by
        filter_upwards
          [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
            n hn
        exact hn.1)
      tendsto_logOrder_atTop
  have hSq : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ) ^ 2) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hPhaseReal
    filter_upwards [eventually_five_lt_phaseNat] with n hn
    have h1 : (1 : ℝ) ≤ (phaseNat n : ℝ) := by
      exact_mod_cast (show 1 ≤ phaseNat n by omega)
    nlinarith
  have hLogTendsto :
      Tendsto
        (fun n : ℕ ↦
          Real.log
            (partialSignedFirstMoment n
              (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
              (midpointMultiplicity n (phaseNat n)
                (phaseCochromaticFixedOffsetIndex n))))
        atTop atTop :=
    tendsto_atTop_mono' atTop
      eventually_phase_fixedOffset_partialSignedFirstMoment_log_lower
      (hSq.const_mul_atTop two_q_sub_one_pos)
  have hExp := Real.tendsto_exp_atTop.comp hLogTendsto
  have hPartial :
      Tendsto
        (fun n : ℕ ↦
          partialSignedFirstMoment n
            (fun i : Fin 4 ↦ phaseNat n - fourDeficit i)
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticFixedOffsetIndex n)))
        atTop atTop := by
    apply hExp.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      simp only [Function.comp_apply]
      rw [Real.exp_log (partialSignedFirstMoment_pos _ _ _)]
  apply hPartial.congr'
  filter_upwards
    [eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible] with
      n hAdmissible
  unfold completeSignedFirstMoment residualVertexMass selectedVertexMass
  have hSize : midpointPartialDiagonalSize (phaseNat n) =
      fun i : Fin 4 => phaseNat n - fourDeficit i := by rfl
  rw [hSize, midpointMultiplicity_vertexMass n (phaseNat n)
    (phaseCochromaticFixedOffsetIndex n) hAdmissible]

#print axioms eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible
#print axioms eventually_phase_fixedOffset_partialSignedFirstMoment_log_lower
#print axioms phase_fixedOffset_completeSignedFirstMoment_tendsto_atTop

end

end Erdos625
