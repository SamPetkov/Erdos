import Mathlib

/-!
# Section IX: residual-regime asymptotic arithmetic

This module contains three exact finite arithmetic bridges used when the
large- and small-residual estimates are specialized to the manuscript scale.
The first two proofs were returned by isolated Aristotle projects.  The third
was revised after a second Aristotle consultation exposed a Lean 4.31
portability failure in an orientation-sensitive `convert` step.

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
    rwa [div_le_iff₀ (pow_pos hL 6)] at hm
  have h1m_le_L6n : 1 / m ≤ L ^ 6 / n := by
    rw [div_le_div_iff₀ hm0 hn]
    simpa [mul_comm] using hn_le_mL6

  have hU4 : U ^ 4 ≤ (C_U * L) ^ 4 :=
    pow_le_pow_left₀ hU0 hU 4
  have hL6_div_n_le_L4 : L ^ 6 / n ≤ L ^ 4 := by
    rw [div_le_iff₀ hn]
    calc
      L ^ 6 = L ^ 4 * L ^ 2 := by ring
      _ ≤ L ^ 4 * n :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h_term1_base : U ^ 4 / m ≤ C_U ^ 4 * L ^ 8 := by
    calc
      U ^ 4 / m = U ^ 4 * (1 / m) := by ring
      _ ≤ (C_U * L) ^ 4 * (L ^ 6 / n) :=
        mul_le_mul hU4 h1m_le_L6n (by positivity) (by positivity)
      _ ≤ (C_U * L) ^ 4 * L ^ 4 :=
        mul_le_mul_of_nonneg_left hL6_div_n_le_L4 (by positivity)
      _ = C_U ^ 4 * L ^ 8 := by ring
  have h_term1 : kappaLambda * U ^ 4 / m ≤
      kappaLambda * C_U ^ 4 * L ^ 8 := by
    calc
      kappaLambda * U ^ 4 / m = kappaLambda * (U ^ 4 / m) := by ring
      _ ≤ kappaLambda * (C_U ^ 4 * L ^ 8) :=
        mul_le_mul_of_nonneg_left h_term1_base hkappaLambda0
      _ = kappaLambda * C_U ^ 4 * L ^ 8 := by ring

  have hU3 : U ^ 3 ≤ (C_U * L) ^ 3 :=
    pow_le_pow_left₀ hU0 hU 3
  have hkU3 : kappaQ * U ^ 3 ≤ kappaQ * (C_U * L) ^ 3 :=
    mul_le_mul_of_nonneg_left hU3 hkappaQ0
  have h_ratio : kappaQ * U ^ 3 / m ≤
      kappaQ * (C_U * L) ^ 3 * (L ^ 6 / n) := by
    calc
      kappaQ * U ^ 3 / m = (kappaQ * U ^ 3) * (1 / m) := by ring
      _ ≤ (kappaQ * (C_U * L) ^ 3) * (L ^ 6 / n) :=
        mul_le_mul hkU3 h1m_le_L6n (by positivity) (by positivity)
  have h_ratio4 : (kappaQ * U ^ 3 / m) ^ 4 ≤
      (kappaQ * (C_U * L) ^ 3 * (L ^ 6 / n)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h_ratio 4
  have h2A : 2 * A ≤ 2 * n := by linarith
  have h_term2_raw : 2 * A * (kappaQ * U ^ 3 / m) ^ 4 ≤
      2 * kappaQ ^ 4 * C_U ^ 12 * L ^ 36 / n ^ 3 := by
    calc
      2 * A * (kappaQ * U ^ 3 / m) ^ 4 ≤
          2 * n * (kappaQ * (C_U * L) ^ 3 * (L ^ 6 / n)) ^ 4 :=
        mul_le_mul h2A h_ratio4 (by positivity) (by positivity)
      _ = 2 * kappaQ ^ 4 * C_U ^ 12 * L ^ 36 / n ^ 3 := by
        field_simp [hn.ne'] <;> ring
  have hL36_div_n3_le_L8 : L ^ 36 / n ^ 3 ≤ L ^ 8 := by
    rw [div_le_iff₀ (pow_pos hn 3)]
    calc
      L ^ 36 = L ^ 8 * L ^ 28 := by ring
      _ ≤ L ^ 8 * n ^ 3 :=
        mul_le_mul_of_nonneg_left hL28 (by positivity)
  have h_term2 : 2 * A * (kappaQ * U ^ 3 / m) ^ 4 ≤
      2 * kappaQ ^ 4 * C_U ^ 12 * L ^ 8 := by
    calc
      2 * A * (kappaQ * U ^ 3 / m) ^ 4 ≤
          2 * kappaQ ^ 4 * C_U ^ 12 * L ^ 36 / n ^ 3 := h_term2_raw
      _ = 2 * kappaQ ^ 4 * C_U ^ 12 * (L ^ 36 / n ^ 3) := by ring
      _ ≤ 2 * kappaQ ^ 4 * C_U ^ 12 * L ^ 8 :=
        mul_le_mul_of_nonneg_left hL36_div_n3_le_L8 (by positivity)

  have hU2 : U ^ 2 ≤ (C_U * L) ^ 2 :=
    pow_le_pow_left₀ hU0 hU 2
  have hHU3 : H * U ^ 3 ≤ 2 * n * (C_U * L) ^ 2 := by
    calc
      H * U ^ 3 = (H * U) * U ^ 2 := by ring
      _ ≤ (2 * n) * (C_U * L) ^ 2 :=
        mul_le_mul hH hU2 (by positivity) (by positivity)
  have h_term3_base : H * U ^ 3 / m ≤ 2 * C_U ^ 2 * L ^ 8 := by
    calc
      H * U ^ 3 / m = (H * U ^ 3) * (1 / m) := by ring
      _ ≤ (2 * n * (C_U * L) ^ 2) * (L ^ 6 / n) :=
        mul_le_mul hHU3 h1m_le_L6n (by positivity) (by positivity)
      _ = 2 * C_U ^ 2 * L ^ 8 := by
        field_simp [hn.ne'] <;> ring
  have h_term3 : 6 * H * (kappaQ * U ^ 3 / m) ≤
      12 * kappaQ * C_U ^ 2 * L ^ 8 := by
    calc
      6 * H * (kappaQ * U ^ 3 / m) =
          (6 * kappaQ) * (H * U ^ 3 / m) := by ring
      _ ≤ (6 * kappaQ) * (2 * C_U ^ 2 * L ^ 8) :=
        mul_le_mul_of_nonneg_left h_term3_base (by positivity)
      _ = 12 * kappaQ * C_U ^ 2 * L ^ 8 := by ring

  calc
    kappaLambda * U ^ 4 / m +
          2 * A * (kappaQ * U ^ 3 / m) ^ 4 +
          6 * H * (kappaQ * U ^ 3 / m) ≤
        kappaLambda * C_U ^ 4 * L ^ 8 +
          2 * kappaQ ^ 4 * C_U ^ 12 * L ^ 8 +
          12 * kappaQ * C_U ^ 2 * L ^ 8 :=
      add_le_add (add_le_add h_term1 h_term2) h_term3
    _ = (kappaLambda * C_U ^ 4 +
          2 * kappaQ ^ 4 * C_U ^ 12 +
          12 * kappaQ * C_U ^ 2) * L ^ 8 := by ring

#print axioms smallResidualExponent_bound
#print axioms ennreal_two_pow_nat_le_of_log_bound
#print axioms largeResidualEnvelope_bound

end Erdos625
