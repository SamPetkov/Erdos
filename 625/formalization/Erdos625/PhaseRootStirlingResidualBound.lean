import Erdos625.PhaseRootScalarCore
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseStirlingResidual_isBigO_logLogOrder :
    phaseStirlingResidual =O[atTop] logLogOrder := by
  refine phaseStirlingResidual_isBigO_inv_logOrder.trans ?_
  apply IsBigO.of_bound 1
  have hLog : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hLogLog : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hLog, hLogLog] with n hn hhn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_trans zero_le_one hn)),
    abs_of_nonneg (le_trans zero_le_one hhn), one_mul]
  exact le_trans ((inv_le_one₀ (le_trans zero_le_one hn)).2 hn) hhn

end

end Erdos625
