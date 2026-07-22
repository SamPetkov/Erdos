import Erdos625.ColoringProfileDeficitDual
import Erdos625.ColoringProfileFactorialBounds
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

theorem abs_profileDeficitAffineCore_sub_quadratic_le
    (alpha : ℕ) (halpha : 0 < alpha) :
    |profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : ℝ) -
        (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ))| ≤
      factorialLogErrorBound alpha := by
  have hchoose : ((alpha.choose 2 : ℕ) : ℝ) =
      (alpha : ℝ) * ((alpha : ℝ) - 1) / 2 := by
    exact Nat.cast_choose_two ℝ alpha
  have hmain := abs_log_factorial_sub_factorialEntropyMain_le alpha
  rw [factorialEntropyMain_of_pos halpha] at hmain
  unfold profileDeficitAffineA profileDeficitAffineB coloringClassLogCost
  rw [show Real.log 2 = q from rfl, hchoose]
  rw [show
      -(Real.log (alpha.factorial : ℝ) +
          ((alpha : ℝ) * ((alpha : ℝ) - 1) / 2) * q) +
          (q * (alpha : ℝ) - q / 2 + Real.log (alpha : ℝ)) * (alpha : ℝ) -
          (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ)) =
        - (Real.log (alpha.factorial : ℝ) -
          ((alpha : ℝ) * Real.log (alpha : ℝ) - (alpha : ℝ))) by ring]
  simpa only [abs_neg] using hmain

end

end Erdos625
