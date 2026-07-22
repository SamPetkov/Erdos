import Erdos625.PhaseRootScalarCore
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseNat_stirlingLogRemainder_isBigO_logLogOrder :
    (fun n : ℕ ↦ stirlingLogRemainder (phaseNat n)) =O[atTop] logLogOrder := by
  apply Asymptotics.IsBigO.of_bound 1
  have hLogLog : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_two_le_phaseNat, hLogLog] with n hn hll
  have hpos : 0 < phaseNat n := by omega
  have hnonneg := stirlingLogRemainder_nonneg hpos
  have hle := stirlingLogRemainder_le hpos
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
    abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hll)]
  have hphase : (1 : ℝ) ≤ phaseNat n := by
    exact_mod_cast (show 1 ≤ phaseNat n by omega)
  have hone : 1 / (12 * (phaseNat n : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith
  linarith

end

end Erdos625
