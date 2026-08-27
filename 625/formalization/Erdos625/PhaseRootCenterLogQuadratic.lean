import Erdos625.PhaseRootCenterLogBound
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/--
The logarithm of the reference part-count center is eventually negligible
compared with the positive quadratic phase scale, in an explicit one-sided
form.
-/
theorem eventually_abs_log_phaseRootCenter_le_quadratic :
    ∀ᶠ n : ℕ in atTop,
      |Real.log (phaseRootCenter n)| ≤
        q / 16 * (phaseNat n : ℝ) ^ 2 := by
  obtain ⟨C, hCpos, hWith⟩ :=
    logOrder_sub_log_phaseRootCenter_isBigO.exists_pos
  have hLL : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ 1 * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1)
  have hThresh : ∀ᶠ n : ℕ in atTop,
      (16 * (1 + C) / q) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop _
  have hPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  filter_upwards [hWith.bound, hLL,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hThresh, hPos] with n hb hll hphase hthr hpos
  set L := logOrder n with hLdef
  set P := (phaseNat n : ℝ) with hPdef
  set M := Real.log (phaseRootCenter n) with hMdef
  have hq : (0 : ℝ) < q := q_pos
  have hLnorm : ‖L‖ = L := by rw [Real.norm_eq_abs, abs_of_pos hpos]
  have hll' : ‖logLogOrder n‖ ≤ L := by rw [← hLnorm]; linarith [hll]
  have hb' : |L - M| ≤ C * L := by
    have hbb : ‖L - M‖ ≤ C * ‖logLogOrder n‖ := hb
    rw [Real.norm_eq_abs] at hbb
    calc
      |L - M| ≤ C * ‖logLogOrder n‖ := hbb
      _ ≤ C * L := by nlinarith [hll', hCpos.le]
  have h1 : |M| ≤ (1 + C) * L := by
    rw [abs_le] at hb' ⊢
    obtain ⟨hlo, hhi⟩ := hb'
    exact ⟨by nlinarith [hpos.le], by nlinarith [hpos.le]⟩
  have h2 : L ≤ P := hphase.1
  have Pnonneg : (0 : ℝ) ≤ P := by
    rw [hPdef]
    exact Nat.cast_nonneg _
  have hkey : 16 * (1 + C) ≤ P * q := by
    have hPge : 16 * (1 + C) / q ≤ P := le_trans hthr h2
    rw [div_le_iff₀ hq] at hPge
    linarith
  have hPmul : (1 + C) * P ≤ q / 16 * P ^ 2 := by
    nlinarith [hkey, Pnonneg]
  calc
    |M| ≤ (1 + C) * L := h1
    _ ≤ (1 + C) * P := by nlinarith [h2, hCpos.le]
    _ ≤ q / 16 * P ^ 2 := hPmul

end

end Erdos625
