import Mathlib

/-!
# Small-residual power-to-exponential scale adapter

The two context lemmas are already accepted in the Erdős 625 Lean 4.31
formalization.  The sole target combines them with the natural half-exponent
rounding needed by the literal small-residual attachment bound.
-/

open scoped ENNReal

set_option autoImplicit false

theorem smallResidualExponent_bound_context
    (n L U m C : ℝ)
    (hn : 0 ≤ n)
    (hL : 0 < L)
    (hU0 : 0 ≤ U)
    (_hm0 : 0 ≤ m)
    (_hC : 0 ≤ C)
    (hU : U ≤ C * L)
    (hm : m ≤ n / L ^ 6) :
    Real.log 2 * (U * m / 2) ≤
      (C * Real.log 2 / 2) * (n / L ^ 5) := by
  rw [le_div_iff₀ (by positivity)] at hm
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hU _hm0,
    mul_le_mul_of_nonneg_left hm _hC, pow_pos hL 5, pow_pos hL 6]

theorem ennreal_two_pow_nat_le_of_log_bound_context
    (N : ℕ) (x : ℝ)
    (h : Real.log 2 * (N : ℝ) ≤ x) :
    ((2 : ℝ≥0∞) ^ N) ≤ ENNReal.ofReal (Real.exp x) := by
  rw [← ENNReal.toReal_le_toReal] <;> norm_num
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos] <;> norm_num
  linarith

/-- The literal natural exponent `U*m/2` from the small-residual branch is
bounded by the manuscript-scale exponential whenever `U = O(L)` and
`m ≤ n/L^6`. -/
theorem smallResidual_two_pow_le_exp_scale
    (n L C : ℝ) (U m : ℕ)
    (hn : 0 ≤ n)
    (hL : 0 < L)
    (hC : 0 ≤ C)
    (hU : (U : ℝ) ≤ C * L)
    (hm : (m : ℝ) ≤ n / L ^ 6) :
    ((2 : ℝ≥0∞) ^ (U * m / 2)) ≤
      ENNReal.ofReal
        (Real.exp ((C * Real.log 2 / 2) * (n / L ^ 5))) := by
  sorry
