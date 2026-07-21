import Mathlib

/-!
# ENNReal two-power transport

This is the exact finite bridge needed after a real logarithmic exponent
comparison in the small-residual Section IX branch.
-/

open scoped ENNReal

set_option autoImplicit false

/-- A real upper bound on `log 2 * N` bounds the corresponding finite
`ENNReal` power by `ofReal (exp x)`. -/
theorem ennreal_two_pow_nat_le_of_log_bound
    (N : ℕ) (x : ℝ)
    (h : Real.log 2 * (N : ℝ) ≤ x) :
    ((2 : ℝ≥0∞) ^ N) ≤ ENNReal.ofReal (Real.exp x) := by
  sorry
