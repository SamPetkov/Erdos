import Erdos625.FiveSizePhaseGainCertificate
import Mathlib

/-!
# Lemma C.1 (`lem:five-size-rate`): uniform rate for five deficit sizes

For `1/64 ≤ R ≤ 1`, `T ≤ 39/10`, `J ≤ 4 R (1 - R)`, and `J ≤ (T - 2) (1 - R)`,
we have
`R log R + (log 2 / 2) J ≤ -(1 - R) / 10000`.
This is the exact scalar rate inequality behind the intermediate common-class
bound (Lemma 6.1(i) and (iv)) in the HP-route manuscript.
-/

namespace Erdos625HP

open Erdos625.FiveSizePhaseGainCertificate

noncomputable section

set_option autoImplicit false

/-- Rational lower bound `-log (12/25) = log (25/12) ≥ 111176 / 151959` via the
`artanh` series at `u = 13 / 37`. -/
theorem neg_log_12_div_25_ge :
    (111176 / 151959 : ℝ) ≤ -Real.log (12 / 25) := by
  have hlog : Real.log (25 / 12 : ℝ) = -Real.log (12 / 25) := by
    rw [show (25 / 12 : ℝ) = ((12 / 25 : ℝ))⁻¹ by norm_num, Real.log_inv]
  rw [← hlog]
  have h := log_ge_of_artanh (m := 25 / 12) (c := 1) (u := 13 / 37)
    (lc := 0) (L := 111176 / 151959) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 2
    (by norm_num [Finset.sum_range_succ])
  linarith

/-- Secant upper bound from concavity of `log` on `[R, 1]`, evaluated at
`a ∈ [R, 1]`: for `0 < R ≤ a < 1`, `log R ≤ (1 - R) log a / (1 - a)`. -/
theorem log_le_secant_of_le {R a : ℝ} (hRpos : 0 < R) (hRa : R ≤ a)
    (ha1 : a < 1) :
    Real.log R ≤ (1 - R) * Real.log a / (1 - a) := by
  rcases eq_or_lt_of_le hRa with rfl | hlt
  · have h1a : (1 : ℝ) - R ≠ 0 := by linarith
    rw [mul_div_cancel_left₀ _ h1a]
  · have h1R : 0 < 1 - R := by linarith
    have h1a : 0 < 1 - a := by linarith
    let w1 : ℝ := (1 - a) / (1 - R)
    let w2 : ℝ := (a - R) / (1 - R)
    have hw1 : 0 ≤ w1 := div_nonneg h1a.le h1R.le
    have hw2 : 0 ≤ w2 := div_nonneg (by linarith) h1R.le
    have hwsum : w1 + w2 = 1 := by
      dsimp [w1, w2]
      field_simp
      ring
    have hcomb : w1 * R + w2 * 1 = a := by
      dsimp [w1, w2]
      field_simp
      ring
    have hconc := strictConcaveOn_log_Ioi.concaveOn.2
      (show R ∈ Set.Ioi (0 : ℝ) from hRpos)
      (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) hw1 hw2 hwsum
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hconc
    rw [hcomb] at hconc
    dsimp [w1] at hconc
    rw [div_mul_eq_mul_div, div_le_iff₀ h1R] at hconc
    rw [le_div_iff₀ h1a]
    linarith

/-- Chord upper bound from convexity of `x ↦ x log x` on `[a, 1]`: for
`0 < a ≤ R ≤ 1`, `R log R ≤ (1 - R) a log a / (1 - a)`. -/
theorem mul_log_le_chord_of_ge {R a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (haR : a ≤ R) (hR1 : R ≤ 1) :
    R * Real.log R ≤ (1 - R) * a * Real.log a / (1 - a) := by
  have h1a : 0 < 1 - a := by linarith
  let w1 : ℝ := (1 - R) / (1 - a)
  let w2 : ℝ := (R - a) / (1 - a)
  have hw1 : 0 ≤ w1 := div_nonneg (by linarith) h1a.le
  have hw2 : 0 ≤ w2 := div_nonneg (by linarith) h1a.le
  have hwsum : w1 + w2 = 1 := by
    dsimp [w1, w2]
    field_simp
    ring
  have hcomb : w1 * a + w2 * 1 = R := by
    dsimp [w1, w2]
    field_simp
    ring
  have hconv := (Real.convexOn_mul_log).2
    (show a ∈ Set.Ici (0 : ℝ) from ha0.le)
    (show (1 : ℝ) ∈ Set.Ici (0 : ℝ) by norm_num) hw1 hw2 hwsum
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hconv
  rw [hcomb] at hconv
  calc
    R * Real.log R ≤ w1 * (a * Real.log a) := hconv
    _ = (1 - R) * a * Real.log a / (1 - a) := by
      dsimp [w1]
      ring

/-- **Manuscript Lemma C.1 (`lem:five-size-rate`).** -/
theorem fiveSizeRate_le_neg_div_10000
    (T R J : ℝ)
    (hR_low : (1 : ℝ) / 64 ≤ R)
    (hR_high : R ≤ 1)
    (hT : T ≤ 39 / 10)
    (hJ_quad : J ≤ 4 * R * (1 - R))
    (hJ_lin : J ≤ (T - 2) * (1 - R)) :
    R * Real.log R + Real.log 2 / 2 * J ≤ -(1 - R) / 10000 := by
  have hRpos : 0 < R := by linarith
  have h1R : 0 ≤ 1 - R := by linarith
  have hqpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq7 : Real.log 2 ≤ 7 / 10 := le_trans Real.log_two_lt_d9.le (by norm_num)
  have hL0 : Real.log (12 / 25 : ℝ) ≤ -(111176 / 151959 : ℝ) := by
    linarith [neg_log_12_div_25_ge]
  rcases le_or_gt R (12 / 25) with hRle | hRgt
  · have hsec := log_le_secant_of_le hRpos hRle (by norm_num)
    have hsec0 : Real.log R ≤ (1 - R) * Real.log (12 / 25) / (13 / 25) := by
      simpa [show (1 : ℝ) - 12 / 25 = 13 / 25 by norm_num] using hsec
    have hsec' : Real.log R ≤ -(1 - R) * (111176 / 151959) / (13 / 25) := by
      have hnum : (1 - R) * Real.log (12 / 25) ≤ (1 - R) * (-(111176 / 151959)) :=
        mul_le_mul_of_nonneg_left hL0 h1R
      have hdiv : (1 - R) * Real.log (12 / 25) / (13 / 25) ≤
          (1 - R) * (-(111176 / 151959)) / (13 / 25) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
      linarith
    have hRlog : R * Real.log R ≤ -R * (1 - R) * (111176 / 151959) / (13 / 25) := by
      have hm := mul_le_mul_of_nonneg_left hsec' hRpos.le
      linarith
    have hJterm : Real.log 2 / 2 * J ≤ (7 / 5) * R * (1 - R) := by
      have h1 : Real.log 2 / 2 * J ≤ Real.log 2 / 2 * (4 * R * (1 - R)) :=
        mul_le_mul_of_nonneg_left hJ_quad (by positivity)
      have h2 : Real.log 2 / 2 * (4 * R * (1 - R)) ≤ (7 / 10) / 2 * (4 * R * (1 - R)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hcomb :
        -R * (1 - R) * (111176 / 151959) / (13 / 25) + (7 / 5) * R * (1 - R) =
          -(5287 / 759795) * R * (1 - R) := by ring
    have hRfloor : (1 / 64 : ℝ) * (1 - R) ≤ R * (1 - R) :=
      mul_le_mul_of_nonneg_right hR_low h1R
    linarith
  · have hchord := mul_log_le_chord_of_ge (by norm_num : (0 : ℝ) < 12 / 25)
      (by norm_num) hRgt.le hR_high
    have hchord0 : R * Real.log R ≤ (1 - R) * (12 / 25) * Real.log (12 / 25) / (13 / 25) := by
      simpa [show (1 : ℝ) - 12 / 25 = 13 / 25 by norm_num] using hchord
    have hRlog : R * Real.log R ≤ -(1 - R) * (12 / 25) * (111176 / 151959) / (13 / 25) := by
      have hnum : (1 - R) * (12 / 25) * Real.log (12 / 25) ≤
          (1 - R) * (12 / 25) * (-(111176 / 151959)) :=
        mul_le_mul_of_nonneg_left hL0 (by positivity)
      have hdiv : (1 - R) * (12 / 25) * Real.log (12 / 25) / (13 / 25) ≤
          (1 - R) * (12 / 25) * (-(111176 / 151959)) / (13 / 25) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
      linarith
    have hJ19 : J ≤ (19 / 10) * (1 - R) := by
      have hT' : (T - 2) * (1 - R) ≤ (39 / 10 - 2) * (1 - R) :=
        mul_le_mul_of_nonneg_right (by linarith) h1R
      linarith
    have hJterm : Real.log 2 / 2 * J ≤ (133 / 200) * (1 - R) := by
      have h1 : Real.log 2 / 2 * J ≤ Real.log 2 / 2 * ((19 / 10) * (1 - R)) :=
        mul_le_mul_of_nonneg_left hJ19 (by positivity)
      have h2 : Real.log 2 / 2 * ((19 / 10) * (1 - R)) ≤
          (7 / 10) / 2 * ((19 / 10) * (1 - R)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    linarith

end

end Erdos625HP
