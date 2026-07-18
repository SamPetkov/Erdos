import Mathlib

/-!
# A concrete negligible rounding budget on the root scale

This is independent of the profile/root analysis. It supplies the explicit
error needed to convert a real `n / (log n)^3` root gap to integer thresholds.
-/

namespace Erdos625

open Filter Asymptotics
open scoped Topology

noncomputable section

/-- A deterministic budget dominating the floor/ceiling loss at the root
scale. Its product with `n / (log n)^3` is eventually `log n + 4`. -/
def rootRoundingBudget (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) + 4) * (Real.log (n : ℝ)) ^ 3 / (n : ℝ)

/-- The explicit rounding budget is negligible at the root scale, and it
eventually pays for `ceil(log n) + 3`. The conclusion is a conjunction so
both the asymptotic and its exact finite inequality remain visible. -/
theorem root_rounding_budget_spec :
    Tendsto rootRoundingBudget atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) + 3 ≤
          rootRoundingBudget n *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
  constructor
  · unfold rootRoundingBudget
    suffices h : Tendsto (fun y : ℝ => (y + 4) * y ^ 3 / Real.exp y) atTop (nhds 0) by
      have h' := (h.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
      apply h'.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp [Real.exp_log (Nat.cast_pos.mpr hn)]
    ring_nf
    norm_num [← Real.exp_neg]
    simpa using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).mul tendsto_const_nhds |>.add
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog : Real.log (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (Nat.one_lt_cast.mpr hn))
    rw [rootRoundingBudget]
    field_simp
    norm_num

end

end Erdos625
