import Mathlib

/-!
# Section IX: residual-regime asymptotic arithmetic

This module contains three exact finite arithmetic bridges used when the
large- and small-residual estimates are specialized to the manuscript scale.
The proofs were returned by isolated Aristotle projects and are accepted here
only subject to the repository's Lean 4.31 warning-fatal, source, and axiom
gates.

No probabilistic estimate, skeleton bound, seed estimate, or final theorem is
claimed in this file.
-/

namespace Erdos625

open scoped ENNReal

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
  rw [le_div_iff₀ (by positivity)] at hm
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hU hm0,
    mul_le_mul_of_nonneg_left hm hC, pow_pos hL 5, pow_pos hL 6]

/-- A real upper bound on `log 2 * N` bounds the corresponding finite
`ENNReal` power by `ofReal (exp x)`. -/
theorem ennreal_two_pow_nat_le_of_log_bound
    (N : ℕ) (x : ℝ)
    (h : Real.log 2 * (N : ℝ) ≤ x) :
    ((2 : ℝ≥0∞) ^ N) ≤ ENNReal.ofReal (Real.exp x) := by
  rw [← ENNReal.toReal_le_toReal] <;> norm_num
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos] <;> norm_num
  linarith

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
  have hn_le_mL6 : n ≤ m * L ^ 6 := by
    rwa [div_le_iff₀ (by positivity)] at hm
  have h1m_le_L6n : 1 / m ≤ L ^ 6 / n := by
    rw [div_le_div_iff₀] <;> first | positivity | linarith
  have h_term3 :
      6 * H * (kappaQ * U ^ 3 / m) ≤
        12 * kappaQ * C_U ^ 2 * L ^ 8 := by
    have h_term3_bound :
        H * U ^ 3 / m ≤ 2 * n * (C_U * L) ^ 2 * (L ^ 6 / n) := by
      convert mul_le_mul
        (mul_le_mul hH (pow_le_pow_left₀ (by positivity) hU 2)
          (by positivity) (by positivity))
        h1m_le_L6n (by positivity) (by positivity) using 1 <;> ring
    convert mul_le_mul_of_nonneg_left h_term3_bound
      (show 0 ≤ 6 * kappaQ by positivity) using 1 <;> ring_nf
    norm_num [hn.ne']
  have h_term1 :
      kappaLambda * U ^ 4 / m ≤ kappaLambda * C_U ^ 4 * L ^ 8 := by
    have h_term1' :
        kappaLambda * U ^ 4 / m ≤
          kappaLambda * C_U ^ 4 * L ^ 4 * (L ^ 6 / n) := by
      have h_term1'' :
          kappaLambda * U ^ 4 / m ≤
            kappaLambda * (C_U * L) ^ 4 * (1 / m) := by
        rw [mul_one_div]
        gcongr
      exact h_term1''.trans (by
        convert mul_le_mul_of_nonneg_left h1m_le_L6n
          (show 0 ≤ kappaLambda * (C_U * L) ^ 4 by positivity) using 1
        ring)
    refine le_trans h_term1' ?_
    rw [mul_div, div_le_iff₀] <;>
      nlinarith [show 0 ≤ kappaLambda * C_U ^ 4 * L ^ 4 by positivity,
        show 0 ≤ kappaLambda * C_U ^ 4 * L ^ 8 by positivity]
  have h_term2 :
      2 * A * (kappaQ * U ^ 3 / m) ^ 4 ≤
        2 * kappaQ ^ 4 * C_U ^ 12 * L ^ 36 / n ^ 3 := by
    have h_term2' :
        2 * A * (kappaQ * U ^ 3 / m) ^ 4 ≤
          2 * n * (kappaQ * (C_U * L) ^ 3 / (n / L ^ 6)) ^ 4 := by
      gcongr
    convert h_term2' using 1
    · ring_nf
      norm_num [hn.ne', hL.ne']
      ring_nf
      field_simp [hn.ne']
    · ring
  have h_L36_div_n3_le_L8 : L ^ 36 / n ^ 3 ≤ L ^ 8 := by
    rw [div_le_iff₀] <;>
      first | positivity | nlinarith [pow_pos hL 8, pow_pos hL 28]
  ring_nf at *
  nlinarith [show 0 ≤ kappaQ ^ 4 * C_U ^ 12 by positivity]

#print axioms smallResidualExponent_bound
#print axioms ennreal_two_pow_nat_le_of_log_bound
#print axioms largeResidualEnvelope_bound

end Erdos625
