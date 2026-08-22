import Erdos625.SignedFourMidpointTargetFromLogLogCenter
import Erdos625.PhaseRootObjectiveCenterBound
import Erdos625.ColoringProfileDualOptimalValue
import Mathlib.Tactic

/-!
# Unrestricted phase-root localization about the manuscript center

The existing phase-center computation proves that the unrestricted objective,
after division by the center, is `O(log log n)`.  This module converts that
residual estimate into an `O(log log n)` root displacement on the natural
`n/(log n)^3` scale, provided the unrestricted root equation and a positive
slope corridor are supplied.

The key finite statement is independent of the coloring model: for a function
whose derivative is bounded below by `D >= 0` between a center and a root,

`D * |root - center| <= |F center|`.

The asymptotic specialization keeps root existence, corridor feasibility, and
the derivative lower bound explicit.  It does not replace any of those inputs
by a first-moment or root-location hypothesis of equivalent difficulty.

No signed-root gap estimate, chromatic lower tail, partial diagonal, skeleton,
second moment, or final Erdős statement is used.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Displacement of an unrestricted root from the exact phase center,
normalized by the manuscript root-gap scale. -/
noncomputable def signedFourNormalizedRightRootCenterDisplacement
    (rPlus : ℕ → ℝ) (n : ℕ) : ℝ :=
  (rPlus n - phaseRootCenter n) /
    signedFourNaturalRootGapScale n

/-- A derivative lower bound between a center and a root controls the absolute
root displacement by the residual at the center.  The interval is written
with `min` and `max`, so no a priori sign of the center residual or ordering of
the root relative to the center is assumed. -/
theorem slope_mul_abs_root_sub_center_le_abs_center_value
    {F : ℝ → ℝ} {center root slope : ℝ}
    (hSlope : 0 ≤ slope)
    (hCont : ContinuousOn F (Icc (min center root) (max center root)))
    (hDiff : DifferentiableOn ℝ F
      (Ioo (min center root) (max center root)))
    (hDerivLower : ∀ x ∈ Ioo (min center root) (max center root),
      slope ≤ deriv F x)
    (hRoot : F root = 0) :
    slope * |root - center| ≤ |F center| := by
  rcases le_total center root with hCenterRoot | hRootCenter
  · have hCont' : ContinuousOn F (Icc center root) := by
      simpa [min_eq_left hCenterRoot, max_eq_right hCenterRoot] using hCont
    have hDiff' : DifferentiableOn ℝ F (Ioo center root) := by
      simpa [min_eq_left hCenterRoot, max_eq_right hCenterRoot] using hDiff
    have hDerivLower' : ∀ x ∈ Ioo center root, slope ≤ deriv F x := by
      intro x hx
      exact hDerivLower x (by
        simpa [min_eq_left hCenterRoot, max_eq_right hCenterRoot] using hx)
    have hIncrement := derivative_lower_bound_mul_sub_le_sub
      hCenterRoot hCont' hDiff' hDerivLower'
    rw [hRoot] at hIncrement
    have hCenterNonpos : F center ≤ 0 := by
      have hProductNonneg : 0 ≤ slope * (root - center) :=
        mul_nonneg hSlope (sub_nonneg.mpr hCenterRoot)
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hCenterRoot),
      abs_of_nonpos hCenterNonpos]
    exact hIncrement
  · have hCont' : ContinuousOn F (Icc root center) := by
      simpa [min_eq_right hRootCenter, max_eq_left hRootCenter] using hCont
    have hDiff' : DifferentiableOn ℝ F (Ioo root center) := by
      simpa [min_eq_right hRootCenter, max_eq_left hRootCenter] using hDiff
    have hDerivLower' : ∀ x ∈ Ioo root center, slope ≤ deriv F x := by
      intro x hx
      exact hDerivLower x (by
        simpa [min_eq_right hRootCenter, max_eq_left hRootCenter] using hx)
    have hIncrement := derivative_lower_bound_mul_sub_le_sub
      hRootCenter hCont' hDiff' hDerivLower'
    rw [hRoot] at hIncrement
    have hCenterNonneg : 0 ≤ F center := by
      have hProductNonneg : 0 ≤ slope * (center - root) :=
        mul_nonneg hSlope (sub_nonneg.mpr hRootCenter)
      linarith
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hRootCenter),
      abs_of_nonneg hCenterNonneg]
    exact hIncrement

/-- Finite specialization of the absolute localization inequality to the
unrestricted phase objective.  Feasibility supplies continuity and
differentiability from the exact finite dual calculus. -/
theorem slope_mul_abs_unrestrictedRoot_sub_phaseRootCenter_le
    (n : ℕ) (root slope : ℝ)
    (hSlope : 0 ≤ slope)
    (hFeasible : ∀ s ∈
      Icc (min (phaseRootCenter n) root) (max (phaseRootCenter n) root),
      0 < s ∧
        (n : ℝ) / s ∈
          Ioo (1 : ℝ) ((((phaseNat n) + 1 : ℕ) : ℝ)))
    (hDerivLower : ∀ s ∈
      Ioo (min (phaseRootCenter n) root) (max (phaseRootCenter n) root),
      slope ≤ deriv (unrestrictedPhaseObjective n) s)
    (hRoot : unrestrictedPhaseObjective n root = 0) :
    slope * |root - phaseRootCenter n| ≤
      |unrestrictedPhaseObjective n (phaseRootCenter n)| := by
  have hMinMem : min (phaseRootCenter n) root ∈
      Icc (min (phaseRootCenter n) root) (max (phaseRootCenter n) root) :=
    ⟨le_rfl, min_le_max⟩
  have hMinData := hFeasible _ hMinMem
  have hbReal :
      (1 : ℝ) < ((((phaseNat n) + 1 : ℕ) : ℝ)) :=
    lt_trans hMinData.2.1 hMinData.2.2
  have hbNat : 1 < phaseNat n + 1 := by
    exact_mod_cast hbReal
  have hb : 2 ≤ phaseNat n + 1 := by omega
  have hCont : ContinuousOn (unrestrictedPhaseObjective n)
      (Icc (min (phaseRootCenter n) root)
        (max (phaseRootCenter n) root)) := by
    intro s hs
    have hsData := hFeasible s hs
    simpa only [unrestrictedPhaseObjective] using
      ((hasDerivAt_profileDualOptimalValue_parts hb
        hsData.1 hsData.2).continuousAt.continuousWithinAt)
  have hDiff : DifferentiableOn ℝ (unrestrictedPhaseObjective n)
      (Ioo (min (phaseRootCenter n) root)
        (max (phaseRootCenter n) root)) := by
    intro s hs
    have hsClosed : s ∈
        Icc (min (phaseRootCenter n) root)
          (max (phaseRootCenter n) root) :=
      Ioo_subset_Icc_self hs
    have hsData := hFeasible s hsClosed
    simpa only [unrestrictedPhaseObjective] using
      ((hasDerivAt_profileDualOptimalValue_parts hb
        hsData.1 hsData.2).differentiableAt.differentiableWithinAt)
  exact slope_mul_abs_root_sub_center_le_abs_center_value
    hSlope hCont hDiff hDerivLower hRoot

/-- The scale ratio converting a center residual divided by the center into a
root displacement converges to `q^2/4` when the slope has its manuscript
normalization. -/
theorem tendsto_phaseRootCenter_div_slope_mul_rootGapScale
    (slope : ℕ → ℝ)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q))) :
    Tendsto
      (fun n : ℕ ↦
        phaseRootCenter n /
          (slope n * signedFourNaturalRootGapScale n))
      atTop (𝓝 (q ^ 2 / 4)) := by
  have hSlopeInv := hSlope.inv₀
    (div_ne_zero (by norm_num : (2 : ℝ) ≠ 0) q_ne_zero)
  have hRaw := tendsto_signedFourNormalizedPhaseRootCenter.mul hSlopeInv
  have hLimit : (q / 2) * (2 / q)⁻¹ = q ^ 2 / 4 := by
    field_simp [q_ne_zero] <;> ring
  rw [hLimit] at hRaw
  have hSlopePos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourNormalizedSlope slope n :=
    hSlope.eventually
      (Ioi_mem_nhds (div_pos (by norm_num) q_pos))
  refine hRaw.congr' ?_
  filter_upwards [hSlopePos, eventually_gt_atTop (1 : ℕ)] with
    n hnSlope hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hlog : logOrder n ≠ 0 := hlogPos.ne'
  have hslopePos : 0 < slope n := by
    unfold signedFourNormalizedSlope at hnSlope
    rcases (div_pos_iff.mp hnSlope) with h | h
    · exact h.1
    · exact (not_lt_of_ge (sq_nonneg (logOrder n)) h.2).elim
  unfold signedFourNormalizedPhaseRootCenter signedFourNormalizedSlope
    signedFourNaturalPartScale signedFourNaturalRootGapScale
  field_simp [hnReal, hlog, hslopePos.ne'] <;> ring

/-- The existing `O(log log n)` center residual and a positive normalized
slope corridor imply `O(log log n)` localization of any unrestricted root on
the natural `n/(log n)^3` scale. -/
theorem
    signedFourNormalizedRightRootCenterDisplacement_isBigO_logLogOrder
    (rPlus slope : ℕ → ℝ)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (min (phaseRootCenter n) (rPlus n))
          (max (phaseRootCenter n) (rPlus n)),
        0 < s ∧
          (n : ℝ) / s ∈
            Ioo (1 : ℝ) ((((phaseNat n) + 1 : ℕ) : ℝ)))
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (min (phaseRootCenter n) (rPlus n))
          (max (phaseRootCenter n) (rPlus n)),
        slope n ≤ deriv (unrestrictedPhaseObjective n) s)
    (hRoot : ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (rPlus n) = 0)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q))) :
    signedFourNormalizedRightRootCenterDisplacement rPlus =O[atTop]
      logLogOrder := by
  have hRatio :=
    tendsto_phaseRootCenter_div_slope_mul_rootGapScale slope hSlope
  let B : ℝ := q ^ 2 / 4 + 1
  have hRatioNear : ∀ᶠ n : ℕ in atTop,
      phaseRootCenter n /
          (slope n * signedFourNaturalRootGapScale n) ∈
        Ioo (q ^ 2 / 4 - 1) (q ^ 2 / 4 + 1) :=
    hRatio.eventually
      (Ioo_mem_nhds
        (sub_lt_self _ (by norm_num : (0 : ℝ) < 1))
        (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1)))
  have hRatioBound : ∀ᶠ n : ℕ in atTop,
      |phaseRootCenter n /
          (slope n * signedFourNaturalRootGapScale n)| ≤ B := by
    filter_upwards [hRatioNear] with n hn
    rw [abs_le]
    dsimp only [B]
    constructor
    · nlinarith [sq_nonneg q]
    · exact hn.2.le
  rcases (isBigO_iff.mp
    unrestrictedPhaseObjective_center_div_isBigO_logLogOrder) with
    ⟨C, hCenterBound⟩
  apply isBigO_iff.mpr
  refine ⟨C * B, ?_⟩
  have hSlopePos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourNormalizedSlope slope n :=
    hSlope.eventually
      (Ioi_mem_nhds (div_pos (by norm_num) q_pos))
  filter_upwards [hCenterBound, hRatioBound, hSlopePos,
    hFeasible, hDerivLower, hRoot, eventually_phaseRootCenter_pos,
    eventually_gt_atTop (1 : ℕ)] with
    n hnCenter hnRatio hnSlope hnFeasible hnDeriv hnRoot hnCenterPos hn
  have hnRealPos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hn
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hn)
  have hScalePos : 0 < signedFourNaturalRootGapScale n := by
    unfold signedFourNaturalRootGapScale
    positivity
  have hnSlopePos : 0 < slope n := by
    unfold signedFourNormalizedSlope at hnSlope
    rcases (div_pos_iff.mp hnSlope) with h | h
    · exact h.1
    · exact (not_lt_of_ge (sq_nonneg (logOrder n)) h.2).elim
  have hFinite :=
    slope_mul_abs_unrestrictedRoot_sub_phaseRootCenter_le
      n (rPlus n) (slope n) hnSlopePos.le
      hnFeasible hnDeriv hnRoot
  have hDistance :
      |rPlus n - phaseRootCenter n| ≤
        |unrestrictedPhaseObjective n (phaseRootCenter n)| / slope n := by
    apply (le_div_iff₀ hnSlopePos).2
    simpa only [mul_comm] using hFinite
  have hScaled :
      |rPlus n - phaseRootCenter n| /
          signedFourNaturalRootGapScale n ≤
        |unrestrictedPhaseObjective n (phaseRootCenter n)| /
          (slope n * signedFourNaturalRootGapScale n) := by
    calc
      _ ≤
          (|unrestrictedPhaseObjective n (phaseRootCenter n)| / slope n) /
            signedFourNaturalRootGapScale n :=
        (div_le_div_iff_of_pos_right hScalePos).2 hDistance
      _ = _ := by
        field_simp [hnSlopePos.ne', hScalePos.ne'] <;> ring
  have hNormDisplacement :
      ‖signedFourNormalizedRightRootCenterDisplacement rPlus n‖ =
        |rPlus n - phaseRootCenter n| /
          signedFourNaturalRootGapScale n := by
    rw [Real.norm_eq_abs]
    unfold signedFourNormalizedRightRootCenterDisplacement
    rw [abs_div, abs_of_pos hScalePos]
  have hEnvelope :
      |unrestrictedPhaseObjective n (phaseRootCenter n)| /
          (slope n * signedFourNaturalRootGapScale n) =
        ‖unrestrictedPhaseObjective n (phaseRootCenter n) /
            phaseRootCenter n‖ *
          |phaseRootCenter n /
            (slope n * signedFourNaturalRootGapScale n)| := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hnCenterPos,
      abs_div, abs_of_pos hnCenterPos,
      abs_of_pos (mul_pos hnSlopePos hScalePos)]
    field_simp [hnCenterPos.ne', hnSlopePos.ne', hScalePos.ne'] <;> ring
  rw [hNormDisplacement]
  calc
    _ ≤ |unrestrictedPhaseObjective n (phaseRootCenter n)| /
          (slope n * signedFourNaturalRootGapScale n) := hScaled
    _ = ‖unrestrictedPhaseObjective n (phaseRootCenter n) /
            phaseRootCenter n‖ *
          |phaseRootCenter n /
            (slope n * signedFourNaturalRootGapScale n)| := hEnvelope
    _ ≤ (C * ‖logLogOrder n‖) * B := by
      exact mul_le_mul hnCenter hnRatio (abs_nonneg _)
        (le_trans (norm_nonneg _) hnCenter)
    _ = (C * B) * ‖logLogOrder n‖ := by ring

#print axioms slope_mul_abs_root_sub_center_le_abs_center_value
#print axioms slope_mul_abs_unrestrictedRoot_sub_phaseRootCenter_le
#print axioms tendsto_phaseRootCenter_div_slope_mul_rootGapScale
#print axioms signedFourNormalizedRightRootCenterDisplacement_isBigO_logLogOrder

end

end Erdos625
