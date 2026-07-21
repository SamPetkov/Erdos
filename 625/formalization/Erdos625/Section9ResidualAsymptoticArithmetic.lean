import Mathlib

/-!
# Section IX: residual-regime asymptotic arithmetic

This module contains two exact finite arithmetic bridges used when the
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

#print axioms smallResidualExponent_bound
#print axioms ennreal_two_pow_nat_le_of_log_bound

end Erdos625
