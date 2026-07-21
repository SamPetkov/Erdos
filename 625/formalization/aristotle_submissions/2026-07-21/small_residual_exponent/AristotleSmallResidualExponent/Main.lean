import Mathlib

/-!
# Small-residual exponent arithmetic

This is an isolated algebraic leaf for the small-residual branch of Section IX.
It deliberately states only the exponent comparison.  Transport to an `ENNReal`
power is a separate target.
-/

open Real

set_option autoImplicit false

/-- If `U = O(L)` and the residual mass is at most `n / L^6`, then the
small-residual exponent is at most the required `O(n / L^5)` quantity. -/
theorem smallResidualExponent_bound
    (n L U m C : ℝ)
    (hn : 0 ≤ n)
    (hL : 0 < L)
    (hU0 : 0 ≤ U)
    (hm0 : 0 ≤ m)
    (hC : 0 ≤ C)
    (hU : U ≤ C * L)
    (hm : m ≤ n / L ^ 6) :
    Real.log 2 * (U * m / 2) ≤
      (C * Real.log 2 / 2) * (n / L ^ 5) := by
  sorry
