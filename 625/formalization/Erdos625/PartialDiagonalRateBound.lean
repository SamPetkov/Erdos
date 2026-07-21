import Erdos625.Phase
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The Section VII central partial-diagonal rate from equation (7.21). -/
noncomputable def partialDiagonalRate (T R Ir : ℝ) : ℝ :=
  R * Real.log R + q / 2 * (Ir - T * R)

/-- Robust scalar core of the Section VII numerical rate bound.  The two
hypotheses `hLeft` and `hRight` are exactly the two structural estimates in
(7.22), and are both retained rather than replacing the rate by an assumed
surrogate.  The only target restriction is the actual-midpoint-compatible
upper bound `T ≤ 4`; a later bridge must establish that application-specific
fact.  The endpoint `R = 1` is deliberately included, where both sides are
zero.

For `0 ≤ R ≤ 1`, take the `(1 - R), R` weighted combination of `hLeft` and
`hRight`.  It gives the universal bound
`Ir - T * R ≤ 3 * R * (1 - R)`, without a lower restriction on `T`.
For `R ≤ 7 / 10`, combine it with
`log R ≤ 2 * (R - 1) / (R + 1)`.  For `7 / 10 ≤ R`, instead use `hRight`,
`T ≤ 4`, and `log R ≤ R - 1`.  These are the two valid scalar routes to the
displayed bound. -/
theorem partialDiagonalRate_uniform_negative
    (T R Ir : ℝ)
    (hTupper : T ≤ 4)
    (hRlower : (1 : ℝ) / 64 ≤ R)
    (hRupper : R ≤ 1)
    (hLeft : Ir - T * R ≤ (5 - T) * R)
    (hRight : Ir - T * R ≤ (T - 2) * (1 - R)) :
    partialDiagonalRate T R Ir ≤ -(1 - R) / 5000 := by
  have hRpos : 0 < R := by linarith
  have hRnonneg : 0 ≤ R := hRpos.le
  have hOneR : 0 ≤ 1 - R := by linarith
  have hqnonneg : 0 ≤ q := by
    rw [q]
    exact Real.log_nonneg (by norm_num)
  have hd : Ir - T * R ≤ 3 * R * (1 - R) := by
    have hL := mul_le_mul_of_nonneg_left hLeft hOneR
    have hRt := mul_le_mul_of_nonneg_left hRight hRnonneg
    nlinarith
  have hq7 : q ≤ (7 : ℝ) / 10 := by
    rw [q]
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10) 7
    have hexp : (2 : ℝ) < Real.exp (7 / 10) := by
      norm_num [Finset.sum_range_succ] at hs ⊢
      linarith
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
    exact (Real.exp_lt_exp.mp hexp).le
  by_cases hRsmall : R ≤ (7 : ℝ) / 10
  · have hlog : Real.log R ≤ 2 * (R - 1) / (R + 1) := by
      have hx : 0 ≤ (1 - R) / R := div_nonneg hOneR hRnonneg
      have h := Real.le_log_one_add_of_nonneg hx
      have hone : 1 + (1 - R) / R = R⁻¹ := by
        field_simp
        ring
      have htwo : 2 * ((1 - R) / R) / ((1 - R) / R + 2) =
          2 * (1 - R) / (1 + R) := by
        (field_simp; ring)
      rw [hone, Real.log_inv, htwo] at h
      have := neg_le_neg h
      convert this using 1 <;> ring
    have hlogmul := mul_le_mul_of_nonneg_left hlog hRnonneg
    have hdq : q / 2 * (Ir - T * R) ≤ q / 2 * (3 * R * (1 - R)) :=
      mul_le_mul_of_nonneg_left hd (div_nonneg hqnonneg (by norm_num))
    have hqmul := mul_le_mul_of_nonneg_left hq7
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 * R) hOneR)
    have hden : 0 < R + 1 := by linarith
    have hcoef :
        -2 * R / (R + 1) + 21 * R / 20 + 1 / 5000 ≤ 0 := by
      have hc : 21 * R / 20 + 1 / 5000 ≤ 2 * R / (R + 1) := by
        apply (le_div_iff₀ hden).2
        nlinarith
      calc
        _ = (21 * R / 20 + 1 / 5000) - 2 * R / (R + 1) := by ring
        _ ≤ 0 := sub_nonpos.mpr hc
    have hcoefmul := mul_nonpos_of_nonneg_of_nonpos hOneR hcoef
    unfold partialDiagonalRate
    calc
      R * Real.log R + q / 2 * (Ir - T * R)
          ≤ R * (2 * (R - 1) / (R + 1)) + q / 2 * (3 * R * (1 - R)) :=
            add_le_add hlogmul hdq
      _ ≤ R * (2 * (R - 1) / (R + 1)) + (7 / 10) / 2 * (3 * R * (1 - R)) := by
            nlinarith
      _ ≤ -(1 - R) / 5000 := by
            field_simp at hcoefmul ⊢
            nlinarith
  · have hRlarge : (7 : ℝ) / 10 ≤ R := by linarith
    have hlog := Real.log_le_sub_one_of_pos hRpos
    have hdright : Ir - T * R ≤ 2 * (1 - R) := by
      have := mul_le_mul_of_nonneg_right hTupper hOneR
      nlinarith [hRight]
    have hlogmul := mul_le_mul_of_nonneg_left hlog hRnonneg
    have hdq : q / 2 * (Ir - T * R) ≤ q / 2 * (2 * (1 - R)) :=
      mul_le_mul_of_nonneg_left hdright (div_nonneg hqnonneg (by norm_num))
    have hqsharp : q ≤ (6932 : ℝ) / 10000 := by
      rw [q]
      have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6932 / 10000) 9
      have hexp : (2 : ℝ) < Real.exp (6932 / 10000) := by
        norm_num [Finset.sum_range_succ] at hs ⊢
        linarith
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
      exact (Real.exp_lt_exp.mp hexp).le
    have hqmul := mul_le_mul_of_nonneg_right hqsharp hOneR
    unfold partialDiagonalRate
    nlinarith

end

end Erdos625
