import Erdos625.FiveSizePhaseGainCertificate

/-!
# Two-sided phase-gain coefficients (`0.063 < c_5` and `C_5 < 0.104`)

In the two-sided Heckel–Panagiotou manuscript, for phase `δ ∈ [0, 1]`:
* the lower coefficient is `lowerPhaseCoeff δ = (log 2)² / 4 · A₅(δ)`;
* the upper coefficient is `upperPhaseCoeff δ = (log 2)² / 4 · (2 log 2 - A₅(δ))`.

Using `Erdos625.FiveSizePhaseGainCertificate.log_169_div_100_lt_phaseGain5`
(`A₅(δ) > log (169/100)` on `[0, 1]`), this module proves:
* `lowerPhaseCoeff δ + upperPhaseCoeff δ = (log 2)³ / 2`;
* `2 log 2 - A₅(δ) < log (400 / 169)` on `[0, 1]`;
* `0.063 < lowerPhaseCoeff δ` and `upperPhaseCoeff δ < 0.104` uniformly on `[0, 1]`.
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap Erdos625.FiveSizePhaseGainCertificate

noncomputable section

set_option autoImplicit false

/-- Phase-dependent lower-bound coefficient `(log 2)² / 4 · A₅(δ)`. -/
def lowerPhaseCoeff (delta : ℝ) : ℝ :=
  (Real.log 2) ^ 2 / 4 * phaseGain5 delta

/-- Phase-dependent upper-bound coefficient `(log 2)² / 4 · (2 log 2 - A₅(δ))`. -/
def upperPhaseCoeff (delta : ℝ) : ℝ :=
  (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain5 delta)

/-- The lower and upper phase coefficients sum to `(log 2)³ / 2` at every phase. -/
theorem lowerPhaseCoeff_add_upperPhaseCoeff (delta : ℝ) :
    lowerPhaseCoeff delta + upperPhaseCoeff delta = (Real.log 2) ^ 3 / 2 := by
  unfold lowerPhaseCoeff upperPhaseCoeff
  ring

/-- Rational lower bound `5247 / 10000 < log (169 / 100)` via the `artanh`
series at `u = 69 / 269` (`N = 4` terms). -/
theorem log_169_div_100_gt : (5247 / 10000 : ℝ) < Real.log (169 / 100) := by
  have h := log_ge_of_artanh (m := 169 / 100) (c := 1) (u := 69 / 269)
    (lc := 0) (L := 52472 / 100000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 4
    (by norm_num [Finset.sum_range_succ])
  linarith

/-- On `[0, 1]`, `2 log 2 - A₅(δ) < log (400 / 169)`. -/
theorem two_mul_log_two_sub_phaseGain5_lt (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    2 * Real.log 2 - phaseGain5 delta < Real.log (400 / 169) := by
  have hA := log_169_div_100_lt_phaseGain5 delta hdelta
  have hlog : 2 * Real.log 2 - Real.log (169 / 100) = Real.log (400 / 169) := by
    have h4 : 2 * Real.log 2 = Real.log 4 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h4, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- Uniform numerical lower bound `0.063 < (log 2)² / 4 · A₅(δ)` on `[0, 1]`. -/
theorem lowerPhaseCoeff_gt_0063 (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    (63 / 1000 : ℝ) < lowerPhaseCoeff delta := by
  have hA : (5247 / 10000 : ℝ) < phaseGain5 delta :=
    lt_trans log_169_div_100_gt (log_169_div_100_lt_phaseGain5 delta hdelta)
  have hqlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hqsq : (0.6931471803 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by nlinarith
  unfold lowerPhaseCoeff
  nlinarith

/-- Uniform numerical upper bound `(log 2)² / 4 · (2 log 2 - A₅(δ)) < 0.104`
on `[0, 1]`. -/
theorem upperPhaseCoeff_lt_0104 (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    upperPhaseCoeff delta < (104 / 1000 : ℝ) := by
  have hA : (5247 / 10000 : ℝ) < phaseGain5 delta :=
    lt_trans log_169_div_100_gt (log_169_div_100_lt_phaseGain5 delta hdelta)
  have hqhi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hqpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hqsq : (Real.log 2) ^ 2 < (0.6931471808 : ℝ) ^ 2 := by nlinarith
  have hspan : 2 * Real.log 2 - phaseGain5 delta <
      2 * 0.6931471808 - 5247 / 10000 := by linarith
  unfold upperPhaseCoeff
  by_cases hnonneg : 0 ≤ 2 * Real.log 2 - phaseGain5 delta
  · have hmul :
        (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain5 delta) ≤
          (0.6931471808 : ℝ) ^ 2 / 4 * (2 * 0.6931471808 - 5247 / 10000) :=
      mul_le_mul (by linarith) hspan.le hnonneg (by norm_num)
    linarith
  · have hneg_span : 2 * Real.log 2 - phaseGain5 delta < 0 := not_le.mp hnonneg
    have hneg : (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain5 delta) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg_span
    linarith

end

end Erdos625HP
