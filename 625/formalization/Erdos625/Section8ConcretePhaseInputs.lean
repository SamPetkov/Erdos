import Erdos625.PhaseSelectedRootSeparation
import Erdos625.RootSeparationRoundingNatAdapter
import Erdos625.RootSeparationRoundingBudget

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The ordinary chromatic lower threshold attached to the unrestricted
profile root. -/
noncomputable def phaseChromaticLowerIndex (n : ℕ) : ℕ :=
  (rootChromaticIndex (unrestrictedPhaseRootSelected n)
    (Real.log (n : ℝ))).toNat

/-- The manuscript midpoint selector between the signed four-size root and
the unrestricted profile root. -/
noncomputable def phaseCochromaticMidpointIndex (n : ℕ) : ℕ :=
  (rootCochromaticIndex (phaseSignedFourSizeRootSelected n)
    (unrestrictedPhaseRootSelected n)).toNat

/-- The selected real roots and the exact floor/ceiling choices give the
manuscript-scale natural-number gap, including the deterministic rounding
budget. -/
theorem eventually_concrete_phase_root_corridor_bounds :
    ∀ᶠ n : ℕ in atTop,
      (q ^ 2 / 16 * Real.log (200 / 153 : ℝ) -
          rootRoundingBudget n) * baseScale n ≤
        (phaseChromaticLowerIndex n : ℝ) -
          (phaseCochromaticMidpointIndex n : ℝ) := by
  let c : ℝ := q ^ 2 / 8 * Real.log (200 / 153 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (div_pos (sq_pos_of_pos q_pos) (by norm_num))
      log_200_div_153_pos
  have hBudgetLt : ∀ᶠ n : ℕ in atTop, rootRoundingBudget n < c :=
    root_rounding_budget_spec.1.eventually (Iio_mem_nhds hc)
  have hBasePos : ∀ᶠ n : ℕ in atTop, 0 < baseScale n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
    rw [baseScale]
    exact div_pos (Nat.cast_pos.mpr (by omega))
      (pow_pos (Real.log_pos hnReal) 3)
  filter_upwards
    [eventually_selected_phase_roots_separated,
      eventually_phaseSignedFourSizeRootSelected_spec_unique,
      eventually_unrestrictedPhaseRootSelected_spec_unique,
      eventually_phaseRootLogLogCorridor_fourSize_domain
        unrestrictedPhaseRootCorridorCoefficient
        unrestrictedPhaseRootCorridorCoefficient_pos.le,
      root_rounding_budget_spec.2, hBudgetLt, hBasePos] with
      n hGap hSigned hUnrestricted hUnrestrictedDomain hRounding hBudget hBase
  let rCo : ℝ := phaseSignedFourSizeRootSelected n
  let rPlus : ℝ := unrestrictedPhaseRootSelected n
  have hRCoPos : 0 < rCo := hSigned.1.2.1
  have hRPlusPos : 0 < rPlus := by
    exact (hUnrestrictedDomain rPlus
      ⟨hUnrestricted.1.1.1.le, hUnrestricted.1.1.2.le⟩).1
  have hGap' : c * baseScale n ≤ rPlus - rCo := by
    simpa [c, rPlus, rCo] using hGap
  have hBudgetMul :
      rootRoundingBudget n * baseScale n ≤ c * baseScale n :=
    mul_le_mul_of_nonneg_right hBudget.le hBase.le
  have hRounding' : Real.log (n : ℝ) + 3 ≤
      rootRoundingBudget n * baseScale n := by
    simpa [baseScale] using hRounding
  have hRPlusLarge : Real.log (n : ℝ) + 3 < rPlus := by
    linarith
  have hChromaticNonneg :
      0 ≤ rootChromaticIndex rPlus (Real.log (n : ℝ)) := by
    unfold rootChromaticIndex
    rw [sub_nonneg]
    apply Int.le_floor.mpr
    have hCeil := Int.ceil_lt_add_one (Real.log (n : ℝ))
    exact (hCeil.trans (by linarith)).le
  have hCochromaticNonneg :
      0 ≤ rootCochromaticIndex rCo rPlus := by
    unfold rootCochromaticIndex
    apply Int.ceil_nonneg
    linarith
  have hRounded := root_midpoint_rounding_gap_toNat
    rPlus rCo (Real.log (n : ℝ)) c (baseScale n)
      (rootRoundingBudget n) hGap' hRounding
      hChromaticNonneg hCochromaticNonneg
  calc
    (q ^ 2 / 16 * Real.log (200 / 153 : ℝ) -
          rootRoundingBudget n) * baseScale n =
        (c / 2 - rootRoundingBudget n) * baseScale n := by
          dsimp [c]
          ring
    _ ≤ (phaseChromaticLowerIndex n : ℝ) -
          (phaseCochromaticMidpointIndex n : ℝ) := by
      simpa [phaseChromaticLowerIndex, phaseCochromaticMidpointIndex,
        rPlus, rCo] using hRounded

#print axioms eventually_concrete_phase_root_corridor_bounds

end

end Erdos625
