import Erdos625.UnrestrictedPhaseRootCenterLocalization
import Erdos625.SignedFourMidpointTargetFromLogLogCenter
import Mathlib.Tactic

/-!
# Root-midpoint localization about the manuscript center

The unrestricted-root localization theorem controls the right root relative to
`phaseRootCenter`.  The E625-10 target bridge instead consumes the natural
ceiling midpoint of the signed and unrestricted roots.  This module supplies
the deterministic transport between those two locations.

The only additional analytic input is the already isolated normalized
signed/unrestricted root-gap asymptotic.  The varying phase coefficient is
uniformly bounded by the welded entropy certificate, so the normalized gap is
`O(1)`, hence `O(log log n)`.  Exact ceiling geometry then shows that the
root midpoint is no farther from the right root than one half of the root gap.

No root existence, derivative estimate, root-gap coefficient proof, first-
moment estimate, chromatic lower tail, partial diagonal, skeleton, second
moment, or final Erdős statement is supplied here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The phase-varying normalized root-gap expansion implies uniform boundedness
of the normalized gap. -/
theorem signedFourNormalizedRootGap_isBigO_one
    (rCo rPlus : ℕ → ℝ)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    signedFourNormalizedRootGap rCo rPlus =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
  have hErrorNear : ∀ᶠ n : ℕ in atTop,
      signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n ∈ Ioo (-1 : ℝ) 1 :=
    hRootGap.eventually
      (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1))
  have hError : ∀ᶠ n : ℕ in atTop,
      |signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n| ≤ 1 := by
    filter_upwards [hErrorNear] with n hn
    exact (abs_lt.2 hn).le
  apply isBigO_iff.mpr
  refine ⟨1 + |q ^ 2 / 4| * q, ?_⟩
  filter_upwards [hError] with n hn
  rw [Real.norm_eq_abs, norm_one, mul_one]
  have hMargin :
      |q ^ 2 / 4 * signedFourPhaseMargin n| ≤ |q ^ 2 / 4| * q := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_signedFourPhaseMargin_le_q n) (abs_nonneg _)
  calc
    |signedFourNormalizedRootGap rCo rPlus n| =
        |(signedFourNormalizedRootGap rCo rPlus n -
            q ^ 2 / 4 * signedFourPhaseMargin n) +
          q ^ 2 / 4 * signedFourPhaseMargin n| := by
      congr 1
      ring
    _ ≤ |signedFourNormalizedRootGap rCo rPlus n -
            q ^ 2 / 4 * signedFourPhaseMargin n| +
          |q ^ 2 / 4 * signedFourPhaseMargin n| :=
      abs_add _ _
    _ ≤ 1 + |q ^ 2 / 4| * q := add_le_add hn hMargin

/-- The normalized root gap is therefore also `O(log log n)`. -/
theorem signedFourNormalizedRootGap_isBigO_logLogOrder
    (rCo rPlus : ℕ → ℝ)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    signedFourNormalizedRootGap rCo rPlus =O[atTop] logLogOrder :=
  (signedFourNormalizedRootGap_isBigO_one rCo rPlus hRootGap).trans
    one_isBigO_logLogOrder

/-- At a finite admissible root corridor, the normalized ceiling midpoint is
at most the normalized right-root displacement plus one half of the normalized
root gap.  There is no additional ceiling unit: a root gap of at least two
places the ceiling midpoint inside the closed root interval. -/
theorem norm_signedFourNormalizedCenterDisplacement_rootMidpoint_le
    (rCo rPlus : ℕ → ℝ) (n : ℕ)
    (hCo : 0 ≤ rCo n)
    (hGap : 2 ≤ rPlus n - rCo n)
    (hScalePos : 0 < signedFourNaturalRootGapScale n) :
    ‖signedFourNormalizedCenterDisplacement
        (signedFourRootMidpointPartCount rCo rPlus) n‖ ≤
      ‖signedFourNormalizedRightRootCenterDisplacement rPlus n‖ +
        ‖signedFourNormalizedRootGap rCo rPlus n‖ / 2 := by
  have hCast :=
    signedFourRootMidpointPartCount_cast_eq rCo rPlus n hCo hGap
  have hMid :=
    rootCochromaticIndex_cast_mem_Icc (rCo n) (rPlus n) hGap
  rw [← hCast] at hMid
  have hHalf :=
    (rootCochromaticIndex_cast_sub_root_bounds
      (rCo n) (rPlus n)).1
  rw [← hCast] at hHalf
  have hGapNonneg : 0 ≤ rPlus n - rCo n := by linarith
  have hMidToRight :
      |(signedFourRootMidpointPartCount rCo rPlus n : ℝ) - rPlus n| ≤
        |rPlus n - rCo n| / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hMid.2),
      abs_of_nonneg hGapNonneg]
    linarith
  have hNumerator :
      |(signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          phaseRootCenter n| ≤
        |rPlus n - phaseRootCenter n| +
          |rPlus n - rCo n| / 2 := by
    calc
      |(signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          phaseRootCenter n| =
          |((signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
              rPlus n) + (rPlus n - phaseRootCenter n)| := by
        congr 1
        ring
      _ ≤ |(signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
              rPlus n| + |rPlus n - phaseRootCenter n| :=
        abs_add _ _
      _ ≤ |rPlus n - rCo n| / 2 +
            |rPlus n - phaseRootCenter n| :=
        add_le_add_right hMidToRight _
      _ = |rPlus n - phaseRootCenter n| +
            |rPlus n - rCo n| / 2 := by ring
  unfold signedFourNormalizedCenterDisplacement
    signedFourNormalizedRightRootCenterDisplacement
    signedFourNormalizedRootGap
  simp only [Real.norm_eq_abs, abs_div, abs_of_pos hScalePos]
  calc
    |(signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
        phaseRootCenter n| / signedFourNaturalRootGapScale n ≤
      (|rPlus n - phaseRootCenter n| +
        |rPlus n - rCo n| / 2) /
          signedFourNaturalRootGapScale n :=
      (div_le_div_iff_of_pos_right hScalePos).2 hNumerator
    _ = |rPlus n - phaseRootCenter n| /
          signedFourNaturalRootGapScale n +
        (|rPlus n - rCo n| /
          signedFourNaturalRootGapScale n) / 2 := by
      field_simp [hScalePos.ne']
      ring

/-- Right-root localization plus the normalized root-gap expansion gives the
`O(log log n)` center localization required for the natural root midpoint. -/
theorem
    signedFourNormalizedRootMidpointCenterDisplacement_isBigO_logLogOrder
    (rCo rPlus : ℕ → ℝ)
    (hRight : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hCo : ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n)
    (hGap : ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n)
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    signedFourNormalizedCenterDisplacement
        (signedFourRootMidpointPartCount rCo rPlus) =O[atTop]
      logLogOrder := by
  have hGapBigO :=
    signedFourNormalizedRootGap_isBigO_logLogOrder
      rCo rPlus hRootGap
  rcases isBigO_iff.mp hRight with ⟨CRight, hRightBound⟩
  rcases isBigO_iff.mp hGapBigO with ⟨CGap, hGapBound⟩
  have hScalePos : ∀ᶠ n : ℕ in atTop,
      0 < signedFourNaturalRootGapScale n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hnPos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt hn
    have hlogPos : 0 < logOrder n :=
      Real.log_pos (by exact_mod_cast hn)
    unfold signedFourNaturalRootGapScale
    exact div_pos hnPos (pow_pos hlogPos 3)
  apply isBigO_iff.mpr
  refine ⟨CRight + CGap / 2, ?_⟩
  filter_upwards [hRightBound, hGapBound, hCo, hGap, hScalePos] with
    n hnRight hnGap hnCo hnRootGap hnScale
  have hFinite :=
    norm_signedFourNormalizedCenterDisplacement_rootMidpoint_le
      rCo rPlus n hnCo hnRootGap hnScale
  have hGapHalf :
      ‖signedFourNormalizedRootGap rCo rPlus n‖ / 2 ≤
        (CGap * ‖logLogOrder n‖) / 2 := by
    linarith
  calc
    ‖signedFourNormalizedCenterDisplacement
        (signedFourRootMidpointPartCount rCo rPlus) n‖ ≤
      ‖signedFourNormalizedRightRootCenterDisplacement rPlus n‖ +
        ‖signedFourNormalizedRootGap rCo rPlus n‖ / 2 := hFinite
    _ ≤ CRight * ‖logLogOrder n‖ +
          (CGap * ‖logLogOrder n‖) / 2 :=
      add_le_add hnRight hGapHalf
    _ = (CRight + CGap / 2) * ‖logLogOrder n‖ := by ring

#print axioms signedFourNormalizedRootGap_isBigO_one
#print axioms signedFourNormalizedRootGap_isBigO_logLogOrder
#print axioms norm_signedFourNormalizedCenterDisplacement_rootMidpoint_le
#print axioms signedFourNormalizedRootMidpointCenterDisplacement_isBigO_logLogOrder

end

end Erdos625