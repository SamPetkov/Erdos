import Erdos625.PhaseRootScalarCore
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseExpansionResidual_isBigO_logLogOrder :
    phaseExpansionResidual =O[atTop] logLogOrder := by
  refine phaseExpansionResidual_isBigO.trans ?_
  apply IsBigO.of_bound 1
  have hBound :=
    logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1)
  have hLogLogNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop (0 : ℝ))
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hBound, hLogPos, hLogLogNonneg] with n hb hN hw
  rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hw, abs_of_pos hN, one_mul]
  rw [div_le_iff₀ hN]
  have hw_le : logLogOrder n ≤ logOrder n := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hw, abs_of_pos hN] using hb
  nlinarith

end

end Erdos625
