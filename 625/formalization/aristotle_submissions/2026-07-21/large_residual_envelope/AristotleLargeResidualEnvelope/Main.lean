import Mathlib

/-!
# Large-residual envelope arithmetic

This is the isolated real-arithmetic comparison needed to turn the strict
large-residual finite envelope into an `O(L^8)` exponent.  The later application
sets `L = log n` and proves the two displayed growth hypotheses separately.
-/

set_option autoImplicit false

/-- The three terms in the strict large-residual envelope are bounded by one
explicit multiple of `L^8` under the manuscript-scale algebraic hypotheses. -/
theorem largeResidualEnvelope_bound
    (n L U m A H kappaLambda kappaQ C_U : ℝ)
    (hn : 0 < n)
    (hL : 0 < L)
    (hU0 : 0 ≤ U)
    (hm0 : 0 < m)
    (hA0 : 0 ≤ A)
    (hH0 : 0 ≤ H)
    (hkappaLambda0 : 0 ≤ kappaLambda)
    (hkappaQ0 : 0 ≤ kappaQ)
    (hCU0 : 0 ≤ C_U)
    (hm : n / L ^ 6 ≤ m)
    (hU : U ≤ C_U * L)
    (hA : A ≤ n)
    (hH : H * U ≤ 2 * n)
    (hL2 : L ^ 2 ≤ n)
    (hL28 : L ^ 28 ≤ n ^ 3) :
    kappaLambda * U ^ 4 / m +
          2 * A * (kappaQ * U ^ 3 / m) ^ 4 +
          6 * H * (kappaQ * U ^ 3 / m) ≤
      (kappaLambda * C_U ^ 4 +
          2 * kappaQ ^ 4 * C_U ^ 12 +
          12 * kappaQ * C_U ^ 2) * L ^ 8 := by
  sorry
