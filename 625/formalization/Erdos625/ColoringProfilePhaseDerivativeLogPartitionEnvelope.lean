import Erdos625.ColoringProfileDeficitPartitionBounds
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

theorem log_profileDeficitPartition_mem_Icc_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    Real.log (profileDeficitPartition alpha lambda) ∈
      Icc 0
        (Real.log
          (Real.exp M +
            Real.exp (M ^ 2 / q) *
              (1 / (1 - Real.exp (-q / 4))))) := by
  constructor
  · exact Real.log_nonneg
      (one_le_profileDeficitPartition alpha halpha lambda)
  · exact Real.log_le_log
      (profileDeficitPartition_pos alpha lambda)
      (profileDeficitPartition_le_gaussianEnvelope alpha halpha hlambda)

end

end Erdos625
