import Erdos625.PhaseRootScalarBound
import Erdos625.PhaseRootSelectedDeficitBound

/-!
# The unrestricted phase objective at the reference center

This module combines the exact finite center decomposition with the two
independently established bounds for its scalar and selected-deficit terms.
-/

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

/-- A constant error is eventually dominated by `logLogOrder`. -/
theorem one_isBigO_logLogOrder :
    (fun _n : ℕ ↦ (1 : ℝ)) =O[atTop] logLogOrder := by
  apply IsBigO.of_bound 1
  filter_upwards
    [tendsto_logLogOrder_atTop.eventually_ge_atTop (1 : ℝ)] with n hn
  rw [norm_one, Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one hn), one_mul]
  exact hn

/-- At the manuscript reference center, the attained unrestricted-profile
objective divided by the center is at most logarithmic in the logarithmic
order.  This is the direct asymptotic consequence of the exact center
decomposition: its scalar contribution is `O(log log n)`, while its
selected-deficit contribution is uniformly bounded. -/
theorem unrestrictedPhaseObjective_center_div_isBigO_logLogOrder :
    (fun n : ℕ ↦
        unrestrictedPhaseObjective n (phaseRootCenter n) /
          phaseRootCenter n) =O[atTop] logLogOrder := by
  have hSelected : phaseRootSelectedDeficitTerm =O[atTop] logLogOrder :=
    phaseRootSelectedDeficitTerm_isBigO_one.trans one_isBigO_logLogOrder
  have hSum :
      (fun n : ℕ ↦ phaseRootScalarTerm n + phaseRootSelectedDeficitTerm n)
        =O[atTop] logLogOrder :=
    phaseRootScalarTerm_isBigO_logLogOrder.add hSelected
  refine hSum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor] with n hn
  exact (unrestrictedPhaseObjective_center_div_decomposition hn.1 hn.2.1).symm

end

end Erdos625
