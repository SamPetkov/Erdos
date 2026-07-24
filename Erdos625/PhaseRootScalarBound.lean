import Erdos625.PhaseRootAlgebraicCoreBound
import Erdos625.PhaseRootExpansionResidualBound
import Erdos625.PhaseRootScalarResidualRemainderBound
import Erdos625.PhaseRootStirlingResidualBound
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseRootScalarTerm_isBigO_logLogOrder :
    phaseRootScalarTerm =O[atTop] logLogOrder := by
  have hBound :
      (fun n : ℕ ↦
          phaseRootAlgebraicCore n + phaseExpansionResidual n -
            phaseStirlingResidual n - stirlingLogRemainder (phaseNat n))
        =O[atTop] logLogOrder :=
    ((phaseRootAlgebraicCore_isBigO.add
        phaseExpansionResidual_isBigO_logLogOrder).sub
      phaseStirlingResidual_isBigO_logLogOrder).sub
        phaseNat_stirlingLogRemainder_isBigO_logLogOrder
  refine hBound.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_two_le_phaseNat] with n hn hphase
  exact (phaseRootScalarTerm_eq_core hn.1 hn.2.1 (by omega)).symm

end

end Erdos625
