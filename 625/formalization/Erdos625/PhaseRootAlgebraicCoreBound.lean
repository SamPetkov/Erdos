import Erdos625.PhaseRootAlgebraicNoLogBound
import Erdos625.PhaseRootCenterLogBound

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseRootAlgebraicCore_eq (n : ℕ) :
    phaseRootAlgebraicCore n =
      (phaseRootAlgebraicNoLog n - logOrder n) +
        (logOrder n - Real.log (phaseRootCenter n)) := by
  unfold phaseRootAlgebraicCore phaseRootAlgebraicNoLog
  ring

theorem phaseRootAlgebraicCore_isBigO :
    (fun n : ℕ ↦ phaseRootAlgebraicCore n)
      =O[atTop] (fun n : ℕ ↦ logLogOrder n) := by
  have h := phaseRootAlgebraicNoLog_sub_logOrder_isBigO.add
    logOrder_sub_log_phaseRootCenter_isBigO
  exact h.congr_left
    (Filter.Eventually.of_forall fun n ↦
      (phaseRootAlgebraicCore_eq n).symm)

end

end Erdos625
