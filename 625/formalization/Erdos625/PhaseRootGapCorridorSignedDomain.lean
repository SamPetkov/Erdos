import Erdos625.PhaseRootDisplacementScale
import Erdos625.PhaseRootCenterOpenCorridor
import Erdos625.SignedFourSizeObjective
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- The full manuscript-scale corridor stays positive and its four-size
deficit target remains in one fixed compact subset of `(2,5)`. -/
theorem eventually_phaseRoot_gapCorridor_signed_domain :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (phaseRootCenter n - phaseRootGapRadius n)
          (phaseRootCenter n + phaseRootGapRadius n),
        0 < s ∧
          fourSizeTarget n (phaseNat n) s ∈ Icc (5 / 2 : ℝ) (9 / 2 : ℝ) := by
  have hqlo : (0.6931471803 : ℝ) < q := Real.log_two_gt_d9
  have hqhi : q < 0.6931471808 := Real.log_two_lt_d9
  have h2q_lb : (11 / 4 : ℝ) < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    linarith [hqhi]
  have h2q_ub : 2 / q < 13 / 4 := by
    rw [div_lt_iff₀ q_pos]
    linarith [hqlo]
  have hLog : ∀ᶠ n : ℕ in atTop, (10 : ℝ) < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 10
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    hLog, eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    eventually_gt_atTop (0 : ℕ)]
    with n hcorr hlog hphase hnpos0
  obtain ⟨hdom, hs0pos, hmem⟩ := hcorr
  set p : ℝ := (phaseNat n : ℝ) with hp
  set s0 : ℝ := phaseRootS0 n with hs0
  set c : ℝ := phaseRootCenter n with hc
  set r : ℝ := phaseRootGapRadius n with hr
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos0
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hs0ne : s0 ≠ 0 := hs0pos.ne'
  have hp10 : (10 : ℝ) < p := lt_of_lt_of_le hlog hphase.1
  have hpne : p ≠ 0 := by positivity
  have hp2 : (1 : ℝ) < p ^ 2 := by nlinarith [hp10]
  have hc_eq : c = (n : ℝ) / s0 := by
    rw [hc, hs0]
    rfl
  have hr_eq : r = c / p ^ 2 := by
    rw [hr, hc, hp]
    rfl
  have hcpos : (0 : ℝ) < c := by
    rw [hc_eq]
    positivity
  have hnc : (n : ℝ) / c = s0 := by
    rw [hc_eq]
    field_simp
  rw [Set.mem_Icc, hnc] at hmem
  obtain ⟨hp_s0_lo, hp_s0_hi⟩ := hmem
  have hs0_upper : s0 ≤ p - 11 / 4 := by
    linarith [hp_s0_lo, h2q_lb]
  have hs0_lower : p - 17 / 4 ≤ s0 := by
    linarith [hp_s0_hi, h2q_ub]
  have hr_lt_c : r < c := by
    rw [hr_eq, div_lt_iff₀ (by positivity : (0 : ℝ) < p ^ 2)]
    nlinarith [hcpos, hp2]
  have hcr_pos : (0 : ℝ) < c - r := by linarith
  have hcr_eq : c - r =
      (n : ℝ) * (p ^ 2 - 1) / (s0 * p ^ 2) := by
    rw [hr_eq, hc_eq]
    field_simp
  have hcr_eq2 : c + r =
      (n : ℝ) * (p ^ 2 + 1) / (s0 * p ^ 2) := by
    rw [hr_eq, hc_eq]
    field_simp
  have hpoly_lo :
      s0 * p ^ 2 ≤ (p - 5 / 2) * (p ^ 2 - 1) := by
    nlinarith [mul_nonneg
      (by linarith [hs0_upper] : (0 : ℝ) ≤ p - 11 / 4 - s0)
      (sq_nonneg p), sq_nonneg (p - 2), hp10]
  have hpoly_hi :
      (p - 9 / 2) * (p ^ 2 + 1) ≤ s0 * p ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith [hs0_lower] : (0 : ℝ) ≤ s0 - (p - 17 / 4))
      (sq_nonneg p), sq_nonneg (p - 2), hp10]
  have hCn : (n : ℝ) ≤ (p - 5 / 2) * (c - r) := by
    rw [hcr_eq,
      show (p - 5 / 2) *
          ((n : ℝ) * (p ^ 2 - 1) / (s0 * p ^ 2)) =
        ((p - 5 / 2) * (p ^ 2 - 1) * n) /
          (s0 * p ^ 2) by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < s0 * p ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_left hpoly_lo (le_of_lt hnpos)]
  have hCn2 : (p - 9 / 2) * (c + r) ≤ (n : ℝ) := by
    rw [hcr_eq2,
      show (p - 9 / 2) *
          ((n : ℝ) * (p ^ 2 + 1) / (s0 * p ^ 2)) =
        ((p - 9 / 2) * (p ^ 2 + 1) * n) /
          (s0 * p ^ 2) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < s0 * p ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_left hpoly_hi (le_of_lt hnpos)]
  intro s hs
  rw [Set.mem_Icc] at hs
  obtain ⟨hslo, hshi⟩ := hs
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le hcr_pos hslo
  refine ⟨hspos, ?_⟩
  have hp52 : (0 : ℝ) ≤ p - 5 / 2 := by linarith [hp10]
  have hp92 : (0 : ℝ) ≤ p - 9 / 2 := by linarith [hp10]
  have hns : (n : ℝ) ≤ (p - 5 / 2) * s :=
    le_trans hCn (mul_le_mul_of_nonneg_left hslo hp52)
  have hns2 : (p - 9 / 2) * s ≤ (n : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hshi hp92) hCn2
  have hlowerT : (n : ℝ) / s ≤ p - 5 / 2 :=
    (div_le_iff₀ hspos).mpr hns
  have hupperT : p - 9 / 2 ≤ (n : ℝ) / s :=
    (le_div_iff₀ hspos).mpr hns2
  rw [fourSizeTarget, Set.mem_Icc, ← hp]
  constructor <;> linarith

end

end Erdos625
