import Mathlib

/-!
# Eventual logarithmic growth bounds for Section IX

This isolates the two growth inequalities required by the accepted finite
large-residual envelope after setting `L = log n`.
-/

open Filter
open scoped Topology

set_option autoImplicit false

/-- Eventually `log n` is positive, `(log n)^2 ≤ n`, and
`(log n)^28 ≤ n^3`. -/
theorem eventually_log_growth_bounds :
    ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) ∧
      Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ∧
      Real.log (n : ℝ) ^ 28 ≤ (n : ℝ) ^ 3 := by
  sorry
