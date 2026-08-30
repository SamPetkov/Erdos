import Erdos625.PhaseSelectedRootSeparation
import Erdos625.PhaseSignedFourSizeFiniteMarginBuffered
import Erdos625.PhaseSignedFourSizeLogLogCorridorDerivativeUpperSharp
import Mathlib.Tactic

/-!
# A separation coefficient strictly above the uniform quarter threshold

The corridor separation of the two selected phase roots is re-derived with two
sharpened inputs: the *buffered* finite signed four-size margin
`log (200 / 153) + eta` and the *sharp* corridor derivative ceiling
`(q / 2 + epsilon) * alpha ^ 2`.  Choosing `epsilon = q * eta / (4 * gamma)`
with `gamma = log (200 / 153)` makes the resulting fixed coefficient

`c = (q ^ 3 / 8) * (gamma + eta) / (q / 2 + epsilon)`

strictly larger than `q ^ 2 / 4 * gamma`.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- There is a fixed coefficient, strictly above `q ^ 2 / 4 * log (200 / 153)`,
which eventually bounds from below the separation of the two selected phase
roots measured in units of `baseScale`. -/
theorem exists_phaseRootGapCoefficient_gt_uniformQuarter :
    ∃ c : ℝ,
      q ^ 2 / 4 * Real.log (200 / 153 : ℝ) < c ∧
      ∀ᶠ n : ℕ in atTop,
        c * baseScale n ≤
          unrestrictedPhaseRootSelected n -
            phaseSignedFourSizeRootSelected n := by
  let C : ℝ := phaseRootCommonCorridorCoefficient
  have hCPos : 0 < C := by
    simpa [C] using phaseRootCommonCorridorCoefficient_pos
  have hCNonneg : 0 ≤ C := hCPos.le
  have hGammaPos : 0 < Real.log (200 / 153 : ℝ) := log_200_div_153_pos
  obtain ⟨eta, hetaPos, hBuffer⟩ :=
    exists_pos_uniform_finiteSignedFourMargin_buffer_on_logLogCorridor C hCNonneg
  set epsilon : ℝ := q * eta / (4 * Real.log (200 / 153 : ℝ)) with hepsilonDef
  have hepsilonPos : 0 < epsilon := by
    rw [hepsilonDef]
    exact div_pos (mul_pos q_pos hetaPos) (by linarith)
  have hDenomPos : 0 < q / 2 + epsilon := by linarith [q_pos]
  have hAdvPos : 0 < Real.log (200 / 153 : ℝ) + eta := by linarith
  refine ⟨q ^ 3 / 8 * (Real.log (200 / 153 : ℝ) + eta) / (q / 2 + epsilon),
    ?_, ?_⟩
  · -- the strict coefficient surplus
    rw [lt_div_iff₀ hDenomPos]
    have hProd : Real.log (200 / 153 : ℝ) * epsilon = q * eta / 4 := by
      rw [hepsilonDef]
      field_simp
    have hScaled :
        q ^ 2 / 4 * (Real.log (200 / 153 : ℝ) * epsilon) = q ^ 3 * eta / 16 := by
      rw [hProd]; ring
    nlinarith [hScaled, mul_pos (pow_pos q_pos 3) hetaPos]
  · have hLogLogPos : ∀ᶠ n : ℕ in atTop, 0 < logLogOrder n :=
      tendsto_logLogOrder_atTop.eventually_gt_atTop 0
    filter_upwards
      [eventually_phaseSignedFourSizeRootSelected_spec_unique,
        eventually_unrestrictedPhaseRootSelected_spec_unique,
        hBuffer,
        eventually_signedFourSizeObjectiveDerivative_logLogCorridor_lower
          C hCNonneg,
        eventually_signedFourSizeObjectiveDerivative_logLogCorridor_upper_sharp
          C hCNonneg epsilon hepsilonPos,
        eventually_phaseRootLogLogCorridor_fourSize_domain C hCNonneg,
        eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower
          C hCNonneg,
        eventually_phaseRoot_domain_pos_and_target_corridor,
        eventually_five_lt_phaseNat,
        hLogLogPos] with
        n hSigned hUnrestricted hMargin hDerivLower hDerivUpper hDomain
          hScale hCenter hPhaseLarge hLogLog
    let rCo : ℝ := phaseSignedFourSizeRootSelected n
    let rPlus : ℝ := unrestrictedPhaseRootSelected n
    let center : ℝ := phaseRootCenter n
    let radius : ℝ := phaseRootGapRadius n
    let width : ℝ := logLogOrder n * radius
    let lower : ℝ := center - C * width
    let upper : ℝ := center + C * width
    let F : ℝ → ℝ := phaseSignedFourSizeObjective n
    let a : ℝ := phaseNat n
    have hnPos : (0 : ℝ) < n := by
      exact_mod_cast (lt_trans Nat.zero_lt_one hCenter.1.1)
    have hCenterPos : 0 < center := by
      simp only [center, phaseRootCenter]
      exact div_pos hnPos hCenter.2.1
    have haNatPos : 0 < phaseNat n :=
      lt_trans (by omega : 0 < 5) hPhaseLarge
    have haPos : 0 < a := by
      simp only [a]
      exact_mod_cast haNatPos
    have hRadiusPos : 0 < radius := by
      simpa only [radius, phaseRootGapRadius, center, a] using
        div_pos hCenterPos (sq_pos_of_pos haPos)
    have hWidthNonneg : 0 ≤ width := by
      simp only [width]
      exact mul_nonneg hLogLog.le hRadiusPos.le
    have hSignedCoeffLe :
        phaseSignedFourSizeRootCorridorCoefficient ≤ C := by
      simp only [C, phaseRootCommonCorridorCoefficient]
      linarith [unrestrictedPhaseRootCorridorCoefficient_pos]
    have hUnrestrictedCoeffLe :
        unrestrictedPhaseRootCorridorCoefficient ≤ C := by
      simp only [C, phaseRootCommonCorridorCoefficient]
      linarith [phaseSignedFourSizeRootCorridorCoefficient_pos]
    have hSignedWidthLe :
        phaseSignedFourSizeRootCorridorCoefficient * width ≤ C * width :=
      mul_le_mul_of_nonneg_right hSignedCoeffLe hWidthNonneg
    have hUnrestrictedWidthLe :
        unrestrictedPhaseRootCorridorCoefficient * width ≤ C * width :=
      mul_le_mul_of_nonneg_right hUnrestrictedCoeffLe hWidthNonneg
    have hSignedCommon : rCo ∈ Icc lower upper := by
      have hOwn := hSigned.1.1
      rw [mem_Ioo] at hOwn
      rw [mem_Icc]
      constructor
      · dsimp [rCo, center, width] at hOwn ⊢
        nlinarith [hSignedWidthLe]
      · dsimp [rCo, center, width] at hOwn ⊢
        nlinarith [hSignedWidthLe]
    have hUnrestrictedCommon : rPlus ∈ Icc lower upper := by
      have hOwn := hUnrestricted.1.1
      rw [mem_Ioo] at hOwn
      rw [mem_Icc]
      constructor
      · dsimp [rPlus, center, width] at hOwn ⊢
        nlinarith [hUnrestrictedWidthLe]
      · dsimp [rPlus, center, width] at hOwn ⊢
        nlinarith [hUnrestrictedWidthLe]
    have hDomain' : ∀ x ∈ Icc lower upper,
        0 < x ∧ fourSizeTarget n (phaseNat n) x ∈ Ioo (2 : ℝ) 5 := by
      intro x hx
      apply hDomain x
      simpa [lower, upper, center, width, C, mul_assoc] using hx
    have hHasDeriv : ∀ x ∈ Icc lower upper,
        HasDerivAt F
          (signedFourSizeObjectiveDerivative n (phaseNat n) x) x := by
      intro x hx
      exact hasDerivAt_phaseSignedFourSizeObjective n
        (hDomain' x hx).1 (hDomain' x hx).2
    have hContinuous : ContinuousOn F (Icc lower upper) := by
      intro x hx
      exact (hHasDeriv x hx).continuousAt.continuousWithinAt
    have hStrict : StrictMonoOn F (Icc lower upper) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc lower upper) hContinuous
      intro x hx
      rw [interior_Icc] at hx
      have hxClosed : x ∈ Icc lower upper := ⟨hx.1.le, hx.2.le⟩
      have hLower := hDerivLower x (by
        simpa [lower, upper, center, width, radius, C, mul_assoc] using hxClosed)
      rw [(hHasDeriv x hxClosed).deriv]
      have haSqPos : 0 < (phaseNat n : ℝ) ^ 2 := by positivity
      nlinarith [q_pos]
    have hRootCo : F rCo = 0 := hSigned.1.2.2.2
    have hRootPlus : unrestrictedPhaseObjective n rPlus = 0 :=
      hUnrestricted.1.2
    have hRPlusPos : 0 < rPlus := (hDomain' rPlus hUnrestrictedCommon).1
    have hMarginPlus : Real.log (200 / 153 : ℝ) + eta ≤
        finiteSignedFourMargin (phaseNat n)
          (fourSizeTarget n (phaseNat n) rPlus) := by
      apply hMargin rPlus
      simpa [lower, upper, center, width, C, mul_assoc] using
        hUnrestrictedCommon
    have hObjectivePlus : F rPlus =
        rPlus * finiteSignedFourMargin (phaseNat n)
          (fourSizeTarget n (phaseNat n) rPlus) :=
      phaseSignedFourSizeObjective_eq_parts_mul_finiteMargin_of_unrestrictedRoot
        n hRPlusPos.ne' hRootPlus
    have hAdvantage :
        rPlus * (Real.log (200 / 153 : ℝ) + eta) ≤ F rPlus := by
      rw [hObjectivePlus]
      exact mul_le_mul_of_nonneg_left hMarginPlus hRPlusPos.le
    have hAdvantagePos : 0 < F rPlus :=
      (mul_pos hRPlusPos hAdvPos).trans_le hAdvantage
    have hOrder : rCo ≤ rPlus := by
      by_contra hNot
      have hLt : rPlus < rCo := lt_of_not_ge hNot
      have hMono := hStrict hUnrestrictedCommon hSignedCommon hLt
      rw [hRootCo] at hMono
      linarith
    have hContinuousRoots : ContinuousOn F (Icc rCo rPlus) :=
      hContinuous.mono fun x hx ↦
        ⟨hSignedCommon.1.trans hx.1, hx.2.trans hUnrestrictedCommon.2⟩
    have hDifferentiableRoots : DifferentiableOn ℝ F (Ioo rCo rPlus) := by
      intro x hx
      have hxCommon : x ∈ Icc lower upper :=
        ⟨hSignedCommon.1.trans hx.1.le,
          hx.2.le.trans hUnrestrictedCommon.2⟩
      exact (hHasDeriv x hxCommon).differentiableAt.differentiableWithinAt
    have hSlopePos : 0 < (q / 2 + epsilon) * a ^ 2 :=
      mul_pos hDenomPos (sq_pos_of_pos haPos)
    have hSlope : ∀ x ∈ Ioo rCo rPlus,
        deriv F x ≤ (q / 2 + epsilon) * a ^ 2 := by
      intro x hx
      have hxCommon : x ∈ Icc lower upper :=
        ⟨hSignedCommon.1.trans hx.1.le,
          hx.2.le.trans hUnrestrictedCommon.2⟩
      rw [(hHasDeriv x hxCommon).deriv]
      have hUp := hDerivUpper x (by
        simpa [lower, upper, center, width, C, mul_assoc] using hxCommon)
      simpa [a] using hUp
    have hRootGap := signed_root_separation_of_advantage_and_slope
      hOrder hContinuousRoots hDifferentiableRoots hSlopePos hSlope hRootCo
        hAdvantage
    have hScalePlus : q ^ 3 / 8 * baseScale n ≤ rPlus / a ^ 2 := by
      simpa [rPlus, a, lower, upper, center, width, C, mul_assoc] using
        hScale rPlus (by
          simpa [lower, upper, center, width, C, mul_assoc] using
            hUnrestrictedCommon)
    have hQuotNonneg :
        0 ≤ (Real.log (200 / 153 : ℝ) + eta) / (q / 2 + epsilon) :=
      div_nonneg hAdvPos.le hDenomPos.le
    calc
      q ^ 3 / 8 * (Real.log (200 / 153 : ℝ) + eta) / (q / 2 + epsilon) *
            baseScale n
          = (q ^ 3 / 8 * baseScale n) *
              ((Real.log (200 / 153 : ℝ) + eta) / (q / 2 + epsilon)) := by
        ring
      _ ≤ (rPlus / a ^ 2) *
            ((Real.log (200 / 153 : ℝ) + eta) / (q / 2 + epsilon)) :=
        mul_le_mul_of_nonneg_right hScalePlus hQuotNonneg
      _ = (rPlus * (Real.log (200 / 153 : ℝ) + eta)) /
            ((q / 2 + epsilon) * a ^ 2) := by
        field_simp
      _ ≤ rPlus - rCo := hRootGap
      _ = unrestrictedPhaseRootSelected n -
            phaseSignedFourSizeRootSelected n := by rfl

#print axioms exists_phaseRootGapCoefficient_gt_uniformQuarter

end

end Erdos625
