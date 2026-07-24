import Erdos625.FourDeficitScoreConvergence
import Erdos625.ColoringProfileDeficitScoreBounds
import Mathlib.Tactic

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- Each exact finite four-deficit residual score is bounded above by its limiting Gaussian score. -/
theorem fourDeficitScore_le_fourGaussianScore
    (alpha : ℕ) (hAlpha : 5 < alpha) (i : Fin 4) :
    fourDeficitScore alpha i ≤ fourGaussianScore i := by
  have hDeficit : fourDeficit i ≤ 5 := by
    simp [fourDeficit]
    omega
  have hDeficitAlpha : fourDeficit i ≤ alpha := by omega
  have hAlphaPos : 0 < alpha := by omega
  have hlog := log_descFactorial_le_mul_log alpha (fourDeficit i)
    hDeficitAlpha hAlphaPos
  rw [fourDeficitScore, fourGaussianScore, ← fourDeficit_cast_eq_support]
  linarith

end

end Erdos625
