import Erdos625.PhaseEstimates

/-!
# Section IX: phase-controlled power bound

This module supplies the eventual natural-number inequality required by the
large-residual finite attachment estimate.

The proof was returned by Aristotle project
`0b21c723-27c0-44f3-a7d3-a52530bad0fe`, task
`15a8d5cc-f68f-4998-a111-cc9597b58011`, and independently audited before
integration.
-/

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/-- A phase-sized cap and the manuscript large-residual cutoff eventually
supply the exact natural power hypothesis used by the finite estimates. -/
theorem eventually_phaseControlled_two_pow_le_cube :
    ∀ᶠ n : ℕ in atTop,
      ∀ U m : ℕ,
        U ≤ phaseNat n →
        0 < m →
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m : ℝ) →
        (2 : ℕ) ^ U ≤ m ^ 3 := by
  have hLogPow :
      ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ 90 ≤ (n : ℝ) := by
    have hLittleO :
        (fun n : ℕ ↦ Real.log (n : ℝ) ^ 90) =o[atTop]
          (fun n : ℕ ↦ (n : ℝ)) :=
      (Real.isLittleO_pow_log_id_atTop (n := 90)).comp_tendsto
        tendsto_natCast_atTop_atTop
    have hBound := hLittleO.bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hBound] with n hn
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] using hn
  have hLogBudget :
      ∀ᶠ n : ℕ in atTop,
        4 * Real.log (n : ℝ) * Real.log 2 ≤
          3 * Real.log (n : ℝ) - 18 * Real.log (Real.log (n : ℝ)) := by
    filter_upwards [hLogPow, eventually_gt_atTop (1 : ℕ)] with n hn hnLarge
    have hLogPos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hnLarge)
    have hnPos : 0 < (n : ℝ) := by positivity
    have hAfterLog := Real.log_le_log (pow_pos hLogPos 90) hn
    rw [Real.log_pow] at hAfterLog
    have hLogTwo : 4 * Real.log 2 < (14 / 5 : ℝ) := by
      have := Real.log_two_lt_d9
      norm_num at *
      linarith
    have hTwoTerm :
        4 * Real.log 2 * Real.log (n : ℝ) ≤
          (14 / 5 : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right hLogTwo.le hLogPos.le
    norm_num at hAfterLog hTwoTerm ⊢
    linarith
  have hPower :
      ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, U ≤ phaseNat n →
        (2 : ℝ) ^ U ≤ (n : ℝ) ^ 3 / Real.log (n : ℝ) ^ 18 := by
    filter_upwards [hLogBudget,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_gt_atTop (1 : ℕ)] with n hnBudget hnPhase hnLarge
    intro U hU
    have hLogPos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hnLarge)
    have hUReal : (U : ℝ) ≤ 4 * Real.log (n : ℝ) :=
      (Nat.cast_le.mpr hU).trans hnPhase.2
    have hExponent :
        (U : ℝ) * Real.log 2 ≤
          3 * Real.log (n : ℝ) - 18 * Real.log (Real.log (n : ℝ)) :=
      (mul_le_mul_of_nonneg_right hUReal (Real.log_nonneg one_le_two)).trans hnBudget
    rw [← Real.log_le_log_iff (by positivity)
      (div_pos (by positivity) (pow_pos hLogPos 18)),
      Real.log_div (by positivity) (pow_ne_zero 18 hLogPos.ne'),
      Real.log_pow, Real.log_pow]
    norm_num
    linarith
  filter_upwards [hPower, eventually_gt_atTop (1 : ℕ)] with n hn hnLarge
  intro U m hU _hm hnm
  have hLogPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hnLarge)
  have hTwo := hn U hU
  rw [le_div_iff₀ (pow_pos hLogPos 18)] at hTwo
  rw [div_le_iff₀ (pow_pos hLogPos 6)] at hnm
  exact_mod_cast (by
    nlinarith [pow_le_pow_left₀ (by positivity) hnm 3,
      pow_pos hLogPos 18] : (2 : ℝ) ^ U ≤ m ^ 3)

end

end Erdos625
