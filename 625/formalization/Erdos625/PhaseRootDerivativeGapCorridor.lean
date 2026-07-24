import Erdos625.PhaseRootDerivativeUnitCorridor
import Erdos625.PhaseRootDisplacementScale
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
/-- Upgrade the unrestricted-objective slope bound from a fixed unit
corridor to the full manuscript-scale corridor. -/
theorem eventually_unrestrictedPhaseObjective_deriv_gapCorridor_lower :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (phaseRootCenter n - phaseRootGapRadius n)
          (phaseRootCenter n + phaseRootGapRadius n),
        q / 8 * (phaseNat n : ℝ) ^ 2 ≤
          deriv (unrestrictedPhaseObjective n) s := by
  have hqLower : (1 / 2 : ℝ) < q :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hqUpper : q < 2 := Real.log_two_lt_d9.trans (by norm_num)
  have h2q4 : (2 / q : ℝ) < 4 := by rw [div_lt_iff₀ q_pos]; linarith
  have hAlow : (-1 : ℝ) < 2 / q - 1 := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hAB : (2 / q - 1 : ℝ) ≤ 2 + 2 / q := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  filter_upwards [eventually_forall_mem_Icc_abs_selectedTerm_le_quadratic hAlow hAB,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_phaseNat_sq_add_phaseNat_le,
    eventually_five_lt_phaseNat,
    eventually_abs_log_phaseRootCenter_le_quadratic,
    eventually_factorialLogErrorBound_phaseNat_le_quadratic] with
    n hsel hcorr hgrowth hfive hlogc hfac s hs
  obtain ⟨hn, hs0pos, hcentermem⟩ := hcorr
  rw [mem_Icc] at hs
  set a := (phaseNat n : ℝ) with ha
  set s0 := phaseRootS0 n with hs0
  set c := phaseRootCenter n with hc
  set r := phaseRootGapRadius n with hrdef
  -- Basic reference-center facts, exactly as in the unit-corridor argument.
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn.1)
  have hcne : c ≠ 0 := by
    rw [hc]; unfold phaseRootCenter; exact div_ne_zero hnpos.ne' hs0pos.ne'
  have hDivide : (n : ℝ) / c = s0 := by rw [hc, hs0]; unfold phaseRootCenter; field_simp
  have hnc : (n : ℝ) = c * s0 := by rw [div_eq_iff hcne] at hDivide; rw [hDivide, mul_comm]
  have haR : (6 : ℝ) ≤ a := by rw [ha]; exact_mod_cast (by omega : 6 ≤ phaseNat n)
  have hs0le : s0 ≤ a := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hn, ha]
    have := phaseDelta_lt_one n
    have hq1 : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; linarith
    linarith
  have hs0ge : (1 : ℝ) ≤ s0 := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hn]
    have := phaseDelta_nonneg n
    linarith [haR, h2q4]
  have hgrow : s0 + 1 ≤ c := by
    have hpn2 : s0 ^ 2 + s0 ≤ (n : ℝ) := by nlinarith [hgrowth, hs0le, hs0pos.le]
    rw [hnc] at hpn2; nlinarith [hpn2, hs0pos]
  have hcpos : 0 < c := by linarith [hgrow, hs0pos]
  have hcge2 : (2 : ℝ) ≤ c := by linarith [hgrow, hs0ge]
  have ha2 : (36 : ℝ) ≤ a ^ 2 := by nlinarith [haR]
  have hs01a2 : s0 + 1 ≤ a ^ 2 := by nlinarith [hs0le, haR]
  -- The corridor radius `r = c / a²`, and the key inequality `(s0+1)·r ≤ c`.
  have hr : r = c / a ^ 2 := by rw [hrdef, phaseRootGapRadius, ← hc, ← ha]
  have hrpos : 0 ≤ r := by rw [hr]; positivity
  have hkey : (s0 + 1) * r ≤ c := by
    have hexp : (s0 + 1) * r = (s0 + 1) * c / a ^ 2 := by rw [hr]; ring
    rw [hexp, div_le_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
    calc (s0 + 1) * c ≤ a ^ 2 * c := mul_le_mul_of_nonneg_right hs01a2 hcpos.le
      _ = c * a ^ 2 := mul_comm _ _
  have hr_small : r ≤ c / 36 := by
    rw [hr]; exact div_le_div_of_nonneg_left hcpos.le (by norm_num) ha2
  have hcr_pos : 0 < c - r := by nlinarith [hr_small, hcpos]
  have hcpr_pos : 0 < c + r := by linarith [hcpos, hrpos]
  have hs_pos : 0 < s := lt_of_lt_of_le hcr_pos hs.1
  have hcs0 : 0 ≤ c * s0 := by positivity
  -- Over the corridor the size mean `c·s₀/s` stays within `1` of `s₀`.
  have hupper : c * s0 / s ≤ s0 + 1 := by
    have h1 : c * s0 / s ≤ c * s0 / (c - r) := div_le_div_of_nonneg_left hcs0 hcr_pos hs.1
    have h2 : c * s0 / (c - r) ≤ s0 + 1 := by
      rw [div_le_iff₀ hcr_pos]
      have hexp : (s0 + 1) * (c - r) = c * s0 + (c - (s0 + 1) * r) := by ring
      linarith [hkey, hexp]
    linarith
  have hlo : s0 - 1 ≤ c * s0 / s := by
    have h1 : c * s0 / (c + r) ≤ c * s0 / s := div_le_div_of_nonneg_left hcs0 hs_pos hs.2
    have h2 : s0 - 1 ≤ c * s0 / (c + r) := by
      rw [le_div_iff₀ hcpr_pos]
      have hexp : (s0 - 1) * (c + r) = c * s0 + ((s0 + 1) * r - c - 2 * r) := by ring
      linarith [hkey, hrpos, hexp]
    linarith
  -- The exact deficit target lands in the fixed compact interval.
  have htar : profileDeficitTarget (phaseNat n) (n : ℝ) s = a - c * s0 / s := by
    rw [profileDeficitTarget, ha, hnc]
  rw [mem_Icc] at hcentermem
  rw [hDivide] at hcentermem
  have hTmem : profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
      Icc (2 / q - 1) (2 + 2 / q) := by
    rw [htar, mem_Icc]
    refine ⟨?_, ?_⟩
    · linarith [hcentermem.1, hupper]
    · linarith [hcentermem.2, hlo]
  -- Over the corridor the log of the size coordinate is quadratically negligible.
  have hs_ge1 : (1 : ℝ) ≤ s := by nlinarith [hs.1, hr_small, hcge2]
  have hs_le2c : s ≤ 2 * c := by nlinarith [hs.2, hr_small, hcpos]
  have hlog : |Real.log s| ≤ q / 8 * a ^ 2 := by
    have hlogs_nonneg : 0 ≤ Real.log s := Real.log_nonneg hs_ge1
    have hupper' : Real.log s ≤ Real.log (2 * c) := Real.log_le_log hs_pos hs_le2c
    have hmul2 : Real.log (2 * c) = Real.log 2 + Real.log c :=
      Real.log_mul (by norm_num) (by linarith)
    have hlogc2 : Real.log c ≤ q / 16 * a ^ 2 := (abs_le.mp hlogc).2
    have hq16 : q ≤ q / 16 * a ^ 2 := by
      nlinarith [mul_nonneg q_pos.le (show (0 : ℝ) ≤ a ^ 2 - 16 by linarith [ha2])]
    rw [abs_of_nonneg hlogs_nonneg]
    calc Real.log s ≤ Real.log (2 * c) := hupper'
      _ = Real.log 2 + Real.log c := hmul2
      _ = q + Real.log c := rfl
      _ ≤ q / 16 * a ^ 2 + q / 16 * a ^ 2 := by linarith [hq16, hlogc2]
      _ = q / 8 * a ^ 2 := by ring
  -- Combine the selected-term, log and factorial errors, exactly as in the
  -- unit corridor.
  obtain ⟨hTopen, hselbound⟩ :=
    hsel (profileDeficitTarget (phaseNat n) (n : ℝ) s) hTmem
  have hderiv := abs_unrestrictedPhaseObjective_deriv_sub_deficitMain_le
    (n := n) (k := s) hTopen
  rw [abs_le] at hderiv
  have hselle := (abs_le.mp hselbound)
  have hloge := (abs_le.mp hlog)
  have hanonneg : (0 : ℝ) ≤ (phaseNat n : ℝ) := Nat.cast_nonneg _
  have hqa : (0 : ℝ) ≤ q / 16 * (phaseNat n : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg q_pos.le (by norm_num)) (sq_nonneg _)
  linarith [hderiv.1, hselle.1, hloge.2, hfac, hanonneg, hqa]

end

end Erdos625

