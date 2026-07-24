import Erdos625.ColoringProfileFactorialBounds
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/--
The explicit factorial-log error is eventually at most one sixteenth of the
positive `q`-quadratic phase scale.
-/
theorem eventually_factorialLogErrorBound_phaseNat_le_quadratic :
    ∀ᶠ n : ℕ in atTop,
      factorialLogErrorBound (phaseNat n) ≤
        q / 16 * (phaseNat n : ℝ) ^ 2 := by
  have hM : ∀ᶠ m : ℕ in atTop,
      factorialLogErrorBound m ≤ q / 16 * (m : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop 100] with m hm
    have hmR : (100 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlog : Real.log ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have h := Real.log_le_sub_one_of_pos
        (x := ((m + 1 : ℕ) : ℝ)) (by positivity)
      push_cast at h ⊢
      linarith
    have hq : (0.6931471803 : ℝ) < q := Real.log_two_gt_d9
    have hEq : factorialLogErrorBound m =
        Real.log ((m + 1 : ℕ) : ℝ) + 4 := rfl
    rw [hEq]
    nlinarith [hlog, hq, hmR,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 100)
        (by linarith : (0 : ℝ) ≤ (m : ℝ)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ q - 0.6931471803)
        (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
  have hle : (logOrder : ℕ → ℝ) ≤ᶠ[atTop]
      fun n : ℕ ↦ (phaseNat n : ℝ) := by
    filter_upwards
      [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
    exact hn.1
  have hphaseReal : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hle tendsto_logOrder_atTop
  have hphase : Tendsto (fun n : ℕ ↦ phaseNat n) atTop atTop := by
    rwa [tendsto_natCast_atTop_iff] at hphaseReal
  exact hphase.eventually hM

end

end Erdos625
