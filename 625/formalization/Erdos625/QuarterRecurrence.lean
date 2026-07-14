import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The quarter-neighbourhood recurrence

This file isolates the elementary recurrence in manuscript display (10.3a).
It is deterministic: no random-graph or colouring assertion is made here.
-/

namespace Erdos625

/-- If every step retains at least one quarter of the preceding value after
the additive loss of one, then the value after `t` steps is bounded below by
`4⁻ᵗ s₀ - 1/3`.  This is the exact real-valued recurrence used in (10.3a). -/
theorem quarterRecurrence_lowerBound (s : ℕ → ℝ)
    (hstep : ∀ t : ℕ, (s t - 1) / 4 ≤ s (t + 1)) :
    ∀ t : ℕ, (4 : ℝ)⁻¹ ^ t * s 0 - 1 / 3 ≤ s t := by
  intro t
  induction t with
  | zero => norm_num
  | succ t ih =>
      calc
        (4 : ℝ)⁻¹ ^ (t + 1) * s 0 - 1 / 3 =
            (((4 : ℝ)⁻¹ ^ t * s 0 - 1 / 3) - 1) / 4 := by
              ring
        _ ≤ (s t - 1) / 4 := by linarith
        _ ≤ s (t + 1) := hstep t

#print axioms quarterRecurrence_lowerBound

end Erdos625
