import Erdos625.FiveSizePhaseGainCertificate
import Erdos625.SPlusEntropySupremumDualInterior
import Erdos625.UniformFiniteFourEntropyCertificate

/-!
# Sharp four-size phase-gain certificate (`> 1/16`) and regularity of `A₄`, `A₅`

This module proves three groups of unconditional results on top of
`Erdos625.FiveSizePhaseGainCertificate` and `Erdos625.SPlusEntropySupremumDualInterior`:

1. **Two-cell rational certificate for `A₄`:**
   * `log_4207_div_2500_lt_phaseGain4`: for every `δ ∈ [0, 1]`,
     `Real.log (4207 / 2500) < A₄(δ)` (`log (4207/2500) ≈ 0.520459`; numerically
     `min_δ A₄ = A₄(1) ≈ 0.520701`).
   * `one_sixteenth_lt_lowerPhaseCoeff4`: for every `δ ∈ [0, 1]`,
     `1 / 16 < (log 2)² / 4 · A₄(δ)` (`0.0625 < 0.062514...`).
2. **Concavity, Lipschitz continuity, and nonconstancy of `A₅` and `A₄`:**
   * `abs_dualValue_sub_le_of_mem_Icc` and `continuousOn_dualValue_Icc`: for every
     support `S` with `S₄ ⊆ S ⊆ S₊`, `𝓕_S` is concave on `(2, 5)` and explicitly
     Lipschitz (hence continuous) on `[9/4, 17/4]`.
   * `continuousOn_phaseGain5`, `continuousOn_phaseGain4`, and
     `phaseGain5_one_lt_phaseGain5_zero`: `A₅` is continuous, positive, and
     strictly nonconstant (`A₅(1) < log(9/5) < A₅(0)`) on `[0, 1]`, certifying
     the analytic properties stated at the start of the Phase Refinement theorem.
3. **Bridge to `Erdos625.fourEntropyLoss`:**
   * `fourEntropyLoss_le_dualValue_diff`: for every `T ∈ (2, 5)`,
     `fourEntropyLoss T ≤ 𝓕_{S₊}(T) - 𝓕_{S₄}(T)`.
-/

namespace Erdos625HP

open Erdos625 FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Two-cell rational certificate for `A₄(δ)` and the `1/16` constant -/

/-- `Z_{S₄}(yTilt y) = y²/2 + y³/8 + y⁴/64 + y⁵/1024`. -/
def fourPartY (y : ℝ) : ℝ :=
  y ^ 2 / 2 + y ^ 3 / 8 + y ^ 4 / 64 + y ^ 5 / 1024

/-- `∑_{i ∈ S₄} i · w_i(yTilt y)`. -/
def fourFirstY (y : ℝ) : ℝ :=
  2 * (y ^ 2 / 2) + 3 * (y ^ 3 / 8) + 4 * (y ^ 4 / 64) + 5 * (y ^ 5 / 1024)

/-- The four-size mean `M₄` at the tilt `yTilt y`. -/
def fourMeanY (y : ℝ) : ℝ :=
  fourFirstY y / fourPartY y

theorem fourPartY_pos {y : ℝ} (hy : 0 < y) : 0 < fourPartY y := by
  unfold fourPartY
  positivity

theorem sum_F4_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F4, gaussWeight (yTilt y) i = fourPartY y := by
  obtain ⟨-, -, -, h2, h3, h4, h5, -, -⟩ := weights_yTilt y hy
  unfold fourPartY
  rw [sum_F4, h2, h3, h4, h5]

theorem four_mean_condition_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F4, ((i : ℝ) - fourMeanY y) * gaussWeight (yTilt y) i = 0 := by
  obtain ⟨-, -, -, h2, h3, h4, h5, -, -⟩ := weights_yTilt y hy
  have hP := fourPartY_pos hy
  have hmul : fourMeanY y * fourPartY y = fourFirstY y := by
    unfold fourMeanY
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hP.ne', mul_one]
  unfold fourPartY fourFirstY at hmul
  rw [sum_F4, h2, h3, h4, h5]
  push_cast
  linear_combination -hmul

theorem four_dual_lower (y : ℝ) (hy : 0 < y) (lambda : ℝ) :
    Real.log (fourPartY y) - yTilt y * fourMeanY y ≤
      Real.log (partitionFn S4 lambda) - lambda * fourMeanY y := by
  have htan := tangent_finset F4 (fourMeanY y) (yTilt y) lambda
  rw [four_mean_condition_yTilt y hy, mul_zero, add_zero, sum_F4_yTilt y hy] at htan
  have hP := fourPartY_pos hy
  have hZ4 := sum_gaussWeight_pos F4 F4_nonempty lambda
  rw [partitionFn_S4, log_sub_mul_eq hP, log_sub_mul_eq hZ4]
  exact Real.log_le_log (mul_pos hP (Real.exp_pos _)) htan

theorem four_dual_interp {ya yb T : ℝ} (hya : 0 < ya) (hyb : 0 < yb)
    (hTa : fourMeanY ya ≤ T) (hTb : T ≤ fourMeanY yb)
    (hab : fourMeanY ya < fourMeanY yb) :
    (fourMeanY yb - T) * (Real.log (fourPartY ya) - yTilt ya * fourMeanY ya) +
        (T - fourMeanY ya) * (Real.log (fourPartY yb) - yTilt yb * fourMeanY yb) ≤
      dualValue S4 T * (fourMeanY yb - fourMeanY ya) := by
  have hD : 0 < fourMeanY yb - fourMeanY ya := by linarith
  have hα : 0 ≤ fourMeanY yb - T := by linarith
  have hβ : 0 ≤ T - fourMeanY ya := by linarith
  have key :
      ((fourMeanY yb - T) * (Real.log (fourPartY ya) - yTilt ya * fourMeanY ya) +
          (T - fourMeanY ya) * (Real.log (fourPartY yb) - yTilt yb * fourMeanY yb)) /
        (fourMeanY yb - fourMeanY ya) ≤ dualValue S4 T := by
    refine le_ciInf fun l ↦ ?_
    show _ ≤ Real.log (partitionFn S4 l) - l * T
    rw [div_le_iff₀ hD]
    have e1 := mul_le_mul_of_nonneg_left (four_dual_lower ya hya l) hα
    have e2 := mul_le_mul_of_nonneg_left (four_dual_lower yb hyb l) hβ
    linarith
  exact (div_le_iff₀ hD).mp key

theorem fourPhaseGain_cell_T {ya yb z K T : ℝ} (hya : 0 < ya) (hyb : 0 < yb) (hz : 0 < z)
    (hz16 : z ≤ 16) (hK : 0 < K) (hab : fourMeanY ya < fourMeanY yb)
    (hVa : 0 < Real.log (2 * fourPartY ya / (K * plusBoundY z)) +
      fourMeanY ya * Real.log (z / ya))
    (hVb : 0 < Real.log (2 * fourPartY yb / (K * plusBoundY z)) +
      fourMeanY yb * Real.log (z / yb))
    (hT25 : T ∈ Set.Ioo (2 : ℝ) 5) (hTa : fourMeanY ya ≤ T) (hTb : T ≤ fourMeanY yb) :
    Real.log K < Real.log 2 - dualValue Splus T + dualValue S4 T := by
  have hmean4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  have hU := plusBoundY_pos hz
  have hPa := fourPartY_pos hya
  have hPb := fourPartY_pos hyb
  have hplus : dualValue Splus T ≤ Real.log (plusBoundY z) - yTilt z * T := by
    have h1 := dualValue_le_at S4_subset_Splus hmean4 (yTilt z)
    rw [partitionFn_Splus] at h1
    have h2 := Zplus_le (yTilt z) (yTilt_le_nine_q_half hz hz16)
    rw [lowPart_yTilt z hz, fourPartition_yTilt z hz, highPart_yTilt z hz] at h2
    have h3 : Real.log (extendedGaussianPartition q (yTilt z)) ≤ Real.log (plusBoundY z) :=
      Real.log_le_log (extendedGaussianPartition_pos q_pos) h2
    linarith
  have h4 := four_dual_interp hya hyb hTa hTb hab
  have eρa : Real.log (2 * fourPartY ya / (K * plusBoundY z)) =
      Real.log 2 + Real.log (fourPartY ya) - Real.log K - Real.log (plusBoundY z) := by
    rw [Real.log_div (mul_pos two_pos hPa).ne' (mul_pos hK hU).ne',
      Real.log_mul two_ne_zero hPa.ne', Real.log_mul hK.ne' hU.ne']
    ring
  have eρb : Real.log (2 * fourPartY yb / (K * plusBoundY z)) =
      Real.log 2 + Real.log (fourPartY yb) - Real.log K - Real.log (plusBoundY z) := by
    rw [Real.log_div (mul_pos two_pos hPb).ne' (mul_pos hK hU).ne',
      Real.log_mul two_ne_zero hPb.ne', Real.log_mul hK.ne' hU.ne']
    ring
  have era : Real.log (z / ya) = yTilt z - yTilt ya := by
    unfold yTilt
    rw [Real.log_div hz.ne' hya.ne']
    ring
  have erb : Real.log (z / yb) = yTilt z - yTilt yb := by
    unfold yTilt
    rw [Real.log_div hz.ne' hyb.ne']
    ring
  rw [eρa, era] at hVa
  rw [eρb, erb] at hVb
  have hD : 0 < fourMeanY yb - fourMeanY ya := by linarith
  have hα : 0 ≤ fourMeanY yb - T := by linarith
  have hβ : 0 ≤ T - fourMeanY ya := by linarith
  have hpos : 0 < (fourMeanY yb - T) *
        (Real.log 2 + Real.log (fourPartY ya) - Real.log K - Real.log (plusBoundY z) +
          fourMeanY ya * (yTilt z - yTilt ya)) +
      (T - fourMeanY ya) *
        (Real.log 2 + Real.log (fourPartY yb) - Real.log K - Real.log (plusBoundY z) +
          fourMeanY yb * (yTilt z - yTilt yb)) := by
    rcases eq_or_lt_of_le hα with h0 | h0
    · rw [← h0, zero_mul, zero_add]
      exact mul_pos (by linarith) hVb
    · exact add_pos_of_pos_of_nonneg (mul_pos h0 hVa) (mul_nonneg hβ hVb.le)
  have e := mul_le_mul_of_nonneg_left hplus hD.le
  have key : (fourMeanY yb - fourMeanY ya) * Real.log K <
      (fourMeanY yb - fourMeanY ya) * (Real.log 2 - dualValue Splus T + dualValue S4 T) := by
    linarith
  exact lt_of_mul_lt_mul_left key hD.le

private theorem endpoint4_1a :
    0 < Real.log (2 * fourPartY (487 / 125) / (4207 / 2500 * plusBoundY (261 / 50))) +
      fourMeanY (487 / 125) * Real.log (261 / 50 / (487 / 125)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fourPartY (487 / 125) / (4207 / 2500 * plusBoundY (261 / 50)))
    (u := 1323541 / 5000000) (L := 2711646351 / 5000000000) (by norm_num) log_quarter_ge
    (by norm_num) (by norm_num) (by unfold fourPartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 261 / 50 / (487 / 125)) (u := 1452391 / 10000000)
    (L := 91420917 / 312500000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (t := 2885071 / 1000000) (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (by norm_num)

private theorem endpoint4_1b :
    0 < Real.log (2 * fourPartY (67 / 10) / (4207 / 2500 * plusBoundY (261 / 50))) +
      fourMeanY (67 / 10) * Real.log (261 / 50 / (67 / 10)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fourPartY (67 / 10) / (4207 / 2500 * plusBoundY (261 / 50)))
    (u := 45493 / 625000) (L := 729177603 / 5000000000) (by norm_num) log_two_ge
    (by norm_num) (by norm_num) (by unfold fourPartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 261 / 50 / (67 / 10)) (u := 218203 / 1000000)
    (L := 887073969 / 2000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (t := 52159 / 15625) (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (by norm_num)

private theorem endpoint4_2a :
    0 < Real.log (2 * fourPartY (67 / 10) / (4207 / 2500 * plusBoundY (183 / 20))) +
      fourMeanY (67 / 10) * Real.log (183 / 20 / (67 / 10)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fourPartY (67 / 10) / (4207 / 2500 * plusBoundY (183 / 20)))
    (u := 233989 / 1250000) (L := 3788495563 / 10000000000) (by norm_num) log_quarter_ge
    (by norm_num) (by norm_num) (by unfold fourPartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 183 / 20 / (67 / 10)) (u := 1545741 / 10000000)
    (L := 3116462863 / 10000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (t := 133527 / 40000) (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (by norm_num)

private theorem endpoint4_2b :
    0 < Real.log (2 * fourPartY (308 / 25) / (4207 / 2500 * plusBoundY (183 / 20))) +
      fourMeanY (308 / 25) * Real.log (183 / 20 / (308 / 25)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fourPartY (308 / 25) / (4207 / 2500 * plusBoundY (183 / 20)))
    (u := 2455133 / 10000000) (L := 2506326803 / 5000000000) (by norm_num) log_two_ge
    (by norm_num) (by norm_num) (by unfold fourPartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 183 / 20 / (308 / 25)) (u := 1952971 / 10000000)
    (L := 989192279 / 2500000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (t := 3885557 / 1000000) (by unfold fourMeanY fourFirstY fourPartY; norm_num)
    (by norm_num)

private theorem fourMean_breakpoints :
    fourMeanY (487 / 125) < 288537 / 100000 ∧
      fourMeanY (487 / 125) < fourMeanY (67 / 10) ∧
      fourMeanY (67 / 10) < fourMeanY (308 / 25) ∧
      (38854 / 10000 : ℝ) < fourMeanY (308 / 25) := by
  unfold fourMeanY fourFirstY fourPartY
  norm_num

/-- **Sharp uniform bound `A₄(δ) > log (4207 / 2500)` on `[0, 1]`.** -/
theorem log_4207_div_2500_lt_phaseGain4 (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (4207 / 2500) < phaseGain4 delta := by
  obtain ⟨hT25, -⟩ := phaseTarget_bounds delta hdelta
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  obtain ⟨c0, c01, c12, c2⟩ := fourMean_breakpoints
  obtain ⟨h0, h1⟩ := hdelta
  have hlo : fourMeanY (487 / 125) ≤ phaseTarget delta := by
    unfold phaseTarget
    linarith
  have hhi : phaseTarget delta ≤ fourMeanY (308 / 25) := by
    unfold phaseTarget
    linarith
  unfold phaseGain4
  rcases le_total (phaseTarget delta) (fourMeanY (67 / 10)) with h | h
  · exact fourPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c01 endpoint4_1a endpoint4_1b hT25 hlo h
  · exact fourPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c12 endpoint4_2a endpoint4_2b hT25 h hhi

/-- Rational lower bound `0.5204590443 ≤ log (4207 / 2500)`. -/
theorem log_4207_div_2500_ge :
    (5204590443 / 10000000000 : ℝ) ≤ Real.log (4207 / 2500) := by
  have h := log_ge_of_artanh (m := 4207 / 2500) (c := 1)
    (u := 1272551 / 5000000) (lc := 0) (L := 5204590443 / 10000000000)
    (by norm_num) log_one_ge (by norm_num) (by norm_num) (by norm_num) 7
    (by norm_num [Finset.sum_range_succ])
  linarith

/-- The four-size phase coefficient `(log 2)² / 4 · A₄(δ)` exceeds `6251 / 100000 > 1 / 16`
uniformly on `[0, 1]`. -/
theorem coeff4_gt_6251_div_100000 (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    (6251 / 100000 : ℝ) < (Real.log 2) ^ 2 / 4 * phaseGain4 delta := by
  have hA := lt_of_le_of_lt log_4207_div_2500_ge (log_4207_div_2500_lt_phaseGain4 delta hdelta)
  have hqlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hqsq : (0.6931471803 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by nlinarith
  nlinarith

/-- **Explicit `1 / 16` bound:** `(log 2)² / 4 · A₄(δ) > 1 / 16 = 0.0625` on `[0, 1]`. -/
theorem one_sixteenth_lt_lowerPhaseCoeff4 (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    (1 / 16 : ℝ) < (Real.log 2) ^ 2 / 4 * phaseGain4 delta :=
  lt_trans (by norm_num) (coeff4_gt_6251_div_100000 delta hdelta)

/-! ## 2. Concavity, Lipschitz continuity, and nonconstancy of `A₅` and `A₄` -/

/-- Concavity of `𝓕_S` on `(2, 5)` for every support `S` containing `S₄`. -/
theorem dualValue_concave_on_Ioo {S : Set ℤ} (hS : S4 ⊆ S)
    {T₁ T₂ a b : ℝ} (hT₁ : T₁ ∈ Set.Ioo (2 : ℝ) 5) (hT₂ : T₂ ∈ Set.Ioo (2 : ℝ) 5)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * dualValue S T₁ + b * dualValue S T₂ ≤ dualValue S (a * T₁ + b * T₂) := by
  have hm₁ := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT₁)
  have hm₂ := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT₂)
  refine le_ciInf fun l ↦ ?_
  show _ ≤ Real.log (partitionFn S l) - l * (a * T₁ + b * T₂)
  have e₁ := mul_le_mul_of_nonneg_left (dualValue_le_at hS hm₁ l) ha
  have e₂ := mul_le_mul_of_nonneg_left (dualValue_le_at hS hm₂ l) hb
  calc a * dualValue S T₁ + b * dualValue S T₂
      ≤ a * (Real.log (partitionFn S l) - l * T₁) +
          b * (Real.log (partitionFn S l) - l * T₂) := add_le_add e₁ e₂
    _ = (a + b) * Real.log (partitionFn S l) - l * (a * T₁ + b * T₂) := by ring
    _ = Real.log (partitionFn S l) - l * (a * T₁ + b * T₂) := by rw [hab, one_mul]

/-- Explicit constant bounding `|𝓕_S|` variation on `[17/8, 35/8]`. -/
def dualLipschitzSpan : ℝ :=
  Real.log (partitionFn Splus 0) -
    min (Real.log (fourPartY (1 / 4)) - yTilt (1 / 4) * fourMeanY (1 / 4))
        (Real.log (fourPartY 32) - yTilt 32 * fourMeanY 32)

private theorem dualValue_bounds_on_wideIcc {S : Set ℤ} (hS4 : S4 ⊆ S) (hSp : S ⊆ Splus)
    {T : ℝ} (hT : T ∈ Set.Icc (17 / 8 : ℝ) (35 / 8)) :
    min (Real.log (fourPartY (1 / 4)) - yTilt (1 / 4) * fourMeanY (1 / 4))
        (Real.log (fourPartY 32) - yTilt 32 * fourMeanY 32) ≤ dualValue S T ∧
      dualValue S T ≤ Real.log (partitionFn Splus 0) := by
  have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hT.1], by linarith [hT.2]⟩
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  constructor
  · have hbr : fourMeanY (1 / 4) ≤ 17 / 8 ∧ (35 / 8 : ℝ) ≤ fourMeanY 32 ∧
        fourMeanY (1 / 4) < fourMeanY 32 := by
      unfold fourMeanY fourFirstY fourPartY
      norm_num
    have h4 := four_dual_interp (ya := 1 / 4) (yb := 32) (by norm_num) (by norm_num)
      (hbr.1.trans hT.1) (hT.2.trans hbr.2.1) hbr.2.2
    set L := min (Real.log (fourPartY (1 / 4)) - yTilt (1 / 4) * fourMeanY (1 / 4))
        (Real.log (fourPartY 32) - yTilt 32 * fourMeanY 32)
    have hLa : L ≤ Real.log (fourPartY (1 / 4)) - yTilt (1 / 4) * fourMeanY (1 / 4) :=
      min_le_left _ _
    have hLb : L ≤ Real.log (fourPartY 32) - yTilt 32 * fourMeanY 32 :=
      min_le_right _ _
    have hD : 0 < fourMeanY 32 - fourMeanY (1 / 4) := by linarith [hbr.2.2]
    have hα : 0 ≤ fourMeanY 32 - T := by linarith [hT.2, hbr.2.1]
    have hβ : 0 ≤ T - fourMeanY (1 / 4) := by linarith [hT.1, hbr.1]
    have hLmul : L * (fourMeanY 32 - fourMeanY (1 / 4)) ≤
        dualValue S4 T * (fourMeanY 32 - fourMeanY (1 / 4)) := by
      have e1 := mul_le_mul_of_nonneg_left hLa hα
      have e2 := mul_le_mul_of_nonneg_left hLb hβ
      linarith
    have hL4 : L ≤ dualValue S4 T := le_of_mul_le_mul_right hLmul hD
    exact hL4.trans (dualValue_mono subset_rfl hS4 hm)
  · have h0 := dualValue_le_at hS4 hm 0
    have hpos : 0 < partitionFn S 0 := by
      refine lt_of_lt_of_le (sum_gaussWeight_pos F4 F4_nonempty 0) ?_
      rw [← partitionFn_S4]
      exact partitionFn_mono hS4 0
    have hmono := Real.log_le_log hpos (partitionFn_mono hSp 0)
    linarith

theorem dualLipschitzSpan_nonneg : 0 ≤ dualLipschitzSpan := by
  have h := dualValue_bounds_on_wideIcc subset_rfl S4_subset_Splus
    (T := 3) (by norm_num)
  unfold dualLipschitzSpan
  linarith [h.1, h.2]

/-- **Explicit Lipschitz bound on `[9/4, 17/4]`:** for every support `S` with
`S₄ ⊆ S ⊆ S₊`, `|𝓕_S(x) - 𝓕_S(y)| ≤ 8 · dualLipschitzSpan · |x - y|`. -/
theorem abs_dualValue_sub_le_of_mem_Icc {S : Set ℤ} (hS4 : S4 ⊆ S) (hSp : S ⊆ Splus)
    {x y : ℝ} (hx : x ∈ Set.Icc (9 / 4 : ℝ) (17 / 4))
    (hy : y ∈ Set.Icc (9 / 4 : ℝ) (17 / 4)) :
    |dualValue S x - dualValue S y| ≤ 8 * dualLipschitzSpan * |x - y| := by
  have step : ∀ {u v : ℝ}, u ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) →
      v ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) → u ≤ v →
      dualValue S v - dualValue S u ≤ 8 * dualLipschitzSpan * (v - u) ∧
      dualValue S u - dualValue S v ≤ 8 * dualLipschitzSpan * (v - u) := by
    intro u v hu hv huv
    have hu25 : u ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv25 : v ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hul : u - 1 / 8 ∈ Set.Icc (17 / 8 : ℝ) (35 / 8) :=
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hvr : v + 1 / 8 ∈ Set.Icc (17 / 8 : ℝ) (35 / 8) :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hul25 : u - 1 / 8 ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hul.1], by linarith [hul.2]⟩
    have hvr25 : v + 1 / 8 ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hvr.1], by linarith [hvr.2]⟩
    have hbu := dualValue_bounds_on_wideIcc hS4 hSp (T := u)
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hbv := dualValue_bounds_on_wideIcc hS4 hSp (T := v)
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hbul := dualValue_bounds_on_wideIcc hS4 hSp hul
    have hbvr := dualValue_bounds_on_wideIcc hS4 hSp hvr
    set D : ℝ := 1 / 8 + (v - u)
    have hDpos : 0 < D := by dsimp [D]; linarith
    have ha : 0 ≤ (1 / 8 : ℝ) / D := div_nonneg (by norm_num) hDpos.le
    have hb : 0 ≤ (v - u) / D := div_nonneg (by linarith) hDpos.le
    have hab : (1 / 8 : ℝ) / D + (v - u) / D = 1 := by
      rw [← add_div, div_self hDpos.ne']
    constructor
    · have hcomb : (1 / 8 : ℝ) / D * v + (v - u) / D * (u - 1 / 8) = u := by
        apply mul_right_cancel₀ hDpos.ne'
        have h1 : (1 / 8 : ℝ) / D * D = 1 / 8 := div_mul_cancel₀ _ hDpos.ne'
        have h2 : (v - u) / D * D = v - u := div_mul_cancel₀ _ hDpos.ne'
        calc ((1 / 8 : ℝ) / D * v + (v - u) / D * (u - 1 / 8)) * D
            = ((1 / 8 : ℝ) / D * D) * v + ((v - u) / D * D) * (u - 1 / 8) := by ring
          _ = (1 / 8) * v + (v - u) * (u - 1 / 8) := by rw [h1, h2]
          _ = u * D := by dsimp [D]; ring
      have hc := dualValue_concave_on_Ioo hS4 hv25 hul25 ha hb hab
      rw [hcomb] at hc
      have hdiv : ((1 / 8 : ℝ) * dualValue S v + (v - u) * dualValue S (u - 1 / 8)) / D ≤
          dualValue S u := by
        rwa [add_div, mul_div_right_comm, mul_div_right_comm]
      have hmul := (div_le_iff₀ hDpos).mp hdiv
      dsimp [D] at hmul
      have hspan' : dualValue S u - dualValue S (u - 1 / 8) ≤ dualLipschitzSpan := by
        unfold dualLipschitzSpan; linarith [hbu.2, hbul.1]
      have hprod' : (v - u) * (dualValue S u - dualValue S (u - 1 / 8)) ≤
          (v - u) * dualLipschitzSpan :=
        mul_le_mul_of_nonneg_left hspan' (by linarith)
      linarith
    · have hcomb : (1 / 8 : ℝ) / D * u + (v - u) / D * (v + 1 / 8) = v := by
        apply mul_right_cancel₀ hDpos.ne'
        have h1 : (1 / 8 : ℝ) / D * D = 1 / 8 := div_mul_cancel₀ _ hDpos.ne'
        have h2 : (v - u) / D * D = v - u := div_mul_cancel₀ _ hDpos.ne'
        calc ((1 / 8 : ℝ) / D * u + (v - u) / D * (v + 1 / 8)) * D
            = ((1 / 8 : ℝ) / D * D) * u + ((v - u) / D * D) * (v + 1 / 8) := by ring
          _ = (1 / 8) * u + (v - u) * (v + 1 / 8) := by rw [h1, h2]
          _ = v * D := by dsimp [D]; ring
      have hc := dualValue_concave_on_Ioo hS4 hu25 hvr25 ha hb hab
      rw [hcomb] at hc
      have hdiv : ((1 / 8 : ℝ) * dualValue S u + (v - u) * dualValue S (v + 1 / 8)) / D ≤
          dualValue S v := by
        rwa [add_div, mul_div_right_comm, mul_div_right_comm]
      have hmul := (div_le_iff₀ hDpos).mp hdiv
      dsimp [D] at hmul
      have hspan' : dualValue S v - dualValue S (v + 1 / 8) ≤ dualLipschitzSpan := by
        unfold dualLipschitzSpan; linarith [hbv.2, hbvr.1]
      have hprod' : (v - u) * (dualValue S v - dualValue S (v + 1 / 8)) ≤
          (v - u) * dualLipschitzSpan :=
        mul_le_mul_of_nonneg_left hspan' (by linarith)
      linarith
  rcases le_total x y with hxy | hyx
  · obtain ⟨h1, h2⟩ := step hx hy hxy
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy), abs_le]
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨h1, h2⟩ := step hy hx hyx
    have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hyx)
    rw [habs, abs_le]
    exact ⟨by linarith, by linarith⟩

theorem continuousOn_dualValue_Icc {S : Set ℤ} (hS4 : S4 ⊆ S) (hSp : S ⊆ Splus) :
    ContinuousOn (dualValue S) (Set.Icc (9 / 4 : ℝ) (17 / 4)) := by
  rw [Metric.continuousOn_iff]
  intro x hx eps heps
  let K : ℝ := 8 * dualLipschitzSpan + 1
  have hKpos : 0 < K := by
    dsimp [K]
    linarith [dualLipschitzSpan_nonneg]
  refine ⟨eps / K, div_pos heps hKpos, fun y hy hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hlip := abs_dualValue_sub_le_of_mem_Icc hS4 hSp hy hx
  have h1 : 8 * dualLipschitzSpan * |y - x| ≤ K * |y - x| := by
    dsimp [K]
    nlinarith [abs_nonneg (y - x)]
  have h2 : K * |y - x| < K * (eps / K) := mul_lt_mul_of_pos_left hdist hKpos
  rw [mul_div_cancel₀ _ hKpos.ne'] at h2
  linarith

private theorem phaseTarget_mapsTo_Icc :
    Set.MapsTo phaseTarget (Set.Icc (0 : ℝ) 1) (Set.Icc (9 / 4 : ℝ) (17 / 4)) := by
  intro delta hdelta
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  unfold phaseTarget
  exact ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩

/-- **Continuity of `A₅` on `[0, 1]`.** -/
theorem continuousOn_phaseGain5 : ContinuousOn phaseGain5 (Set.Icc (0 : ℝ) 1) := by
  have hT : ContinuousOn phaseTarget (Set.Icc (0 : ℝ) 1) := by
    unfold phaseTarget
    exact continuousOn_const.sub continuousOn_id
  have hSp := (continuousOn_dualValue_Icc S4_subset_Splus subset_rfl).comp hT phaseTarget_mapsTo_Icc
  have hS5 := (continuousOn_dualValue_Icc S4_subset_S5 S5_subset_Splus).comp hT phaseTarget_mapsTo_Icc
  exact (continuousOn_const.sub hSp).add hS5

/-- **Continuity of `A₄` on `[0, 1]`.** -/
theorem continuousOn_phaseGain4 : ContinuousOn phaseGain4 (Set.Icc (0 : ℝ) 1) := by
  have hT : ContinuousOn phaseTarget (Set.Icc (0 : ℝ) 1) := by
    unfold phaseTarget
    exact continuousOn_const.sub continuousOn_id
  have hSp := (continuousOn_dualValue_Icc S4_subset_Splus subset_rfl).comp hT phaseTarget_mapsTo_Icc
  have hS4 := (continuousOn_dualValue_Icc subset_rfl S4_subset_Splus).comp hT phaseTarget_mapsTo_Icc
  exact (continuousOn_const.sub hSp).add hS4

/-! ### Nonconstancy of `A₅`: `A₅(1) < log(9/5) < A₅(0)` -/

/-- The eight-point finite subset `{-1, 0, 1, 2, 3, 4, 5, 6}` of `S₊`. -/
private def F8 : Finset ℤ := {-1, 0, 1, 2, 3, 4, 5, 6}

private theorem sum_F8 (f : ℤ → ℝ) :
    ∑ i ∈ F8, f i = f (-1) + f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  have h : F8 = insert (-1) (insert 0 (insert 1 (insert 2 (insert 3 (insert 4 (insert 5 {6})))))) := rfl
  rw [h,
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_singleton]
  ring

private def eightPartY (y : ℝ) : ℝ :=
  1 / (2 * y) + 1 + y + y ^ 2 / 2 + y ^ 3 / 8 + y ^ 4 / 64 + y ^ 5 / 1024 + y ^ 6 / 32768

private def eightFirstY (y : ℝ) : ℝ :=
  -(1 / (2 * y)) + y + 2 * (y ^ 2 / 2) + 3 * (y ^ 3 / 8) + 4 * (y ^ 4 / 64) +
    5 * (y ^ 5 / 1024) + 6 * (y ^ 6 / 32768)

private def eightMeanY (y : ℝ) : ℝ :=
  eightFirstY y / eightPartY y

private theorem eightPartY_pos {y : ℝ} (hy : 0 < y) : 0 < eightPartY y := by
  unfold eightPartY
  positivity

private theorem sum_F8_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F8, gaussWeight (yTilt y) i = eightPartY y := by
  obtain ⟨hm1, h0, h1, h2, h3, h4, h5, h6, -⟩ := weights_yTilt y hy
  unfold eightPartY
  rw [sum_F8, hm1, h0, h1, h2, h3, h4, h5, h6]

private theorem eight_mean_condition_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F8, ((i : ℝ) - eightMeanY y) * gaussWeight (yTilt y) i = 0 := by
  obtain ⟨hm1, h0, h1, h2, h3, h4, h5, h6, -⟩ := weights_yTilt y hy
  have hP := eightPartY_pos hy
  have hmul : eightMeanY y * eightPartY y = eightFirstY y := by
    unfold eightMeanY
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hP.ne', mul_one]
  unfold eightPartY eightFirstY at hmul
  rw [sum_F8, hm1, h0, h1, h2, h3, h4, h5, h6]
  push_cast
  linear_combination -hmul

private theorem F8_subset_Splus : (F8 : Set ℤ) ⊆ Splus := by
  intro i hi
  simp only [F8, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  show (-1 : ℤ) ≤ i
  omega

private theorem splus_dual_lower_eight (y : ℝ) (hy : 0 < y) (lambda : ℝ) :
    Real.log (eightPartY y) - yTilt y * eightMeanY y ≤
      Real.log (partitionFn Splus lambda) - lambda * eightMeanY y := by
  have htan := tangent_finset F8 (eightMeanY y) (yTilt y) lambda
  rw [eight_mean_condition_yTilt y hy, mul_zero, add_zero, sum_F8_yTilt y hy] at htan
  have hP := eightPartY_pos hy
  have hF8ne : F8.Nonempty := ⟨0, by simp [F8]⟩
  have hZ8 := sum_gaussWeight_pos F8 hF8ne lambda
  have h1 : Real.log (eightPartY y) - yTilt y * eightMeanY y ≤
      Real.log (∑ i ∈ F8, gaussWeight lambda i) - lambda * eightMeanY y := by
    rw [log_sub_mul_eq hP, log_sub_mul_eq hZ8]
    exact Real.log_le_log (mul_pos hP (Real.exp_pos _)) htan
  have h2 : ∑ i ∈ F8, gaussWeight lambda i ≤ partitionFn Splus lambda := by
    rw [← partitionFn_coe_finset F8 lambda]
    exact partitionFn_mono F8_subset_Splus lambda
  linarith [Real.log_le_log hZ8 h2]

theorem log_9_div_5_lt_phaseGain5_zero : Real.log (9 / 5) < phaseGain5 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨hT25, -⟩ := phaseTarget_bounds 0 h0
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  have hbr : fiveMeanY 10 < 1 + 288537 / 100000 ∧
      fiveMeanY 10 < fiveMeanY (513 / 50) ∧
      (38854 / 10000 : ℝ) < fiveMeanY (513 / 50) := by
    unfold fiveMeanY fiveFirstY fivePartY
    norm_num
  have hVa : 0 < Real.log (2 * fivePartY 10 / (9 / 5 * plusBoundY (19 / 2))) +
      fiveMeanY 10 * Real.log (19 / 2 / 10) := by
    have hρ := log_ge_of_artanh
      (m := 2 * fivePartY 10 / (9 / 5 * plusBoundY (19 / 2)))
      (u := 328437 / 2500000) (L := 66069 / 250000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by unfold fivePartY plusBoundY; norm_num) 3
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := 19 / 2 / 10) (u := 387931 / 1250000)
      (L := 80221 / 125000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by norm_num) 3 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
      (t := 38557 / 10000) (by unfold fiveMeanY fiveFirstY fivePartY; norm_num) (by norm_num)
  have hVb : 0 < Real.log (2 * fivePartY (513 / 50) / (9 / 5 * plusBoundY (19 / 2))) +
      fiveMeanY (513 / 50) * Real.log (19 / 2 / (513 / 50)) := by
    have hρ := log_ge_of_artanh
      (m := 2 * fivePartY (513 / 50) / (9 / 5 * plusBoundY (19 / 2)))
      (u := 359673 / 2000000) (L := 2909 / 8000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by unfold fivePartY plusBoundY; norm_num) 3
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := 19 / 2 / (513 / 50)) (u := 746753 / 2500000)
      (L := 15403 / 25000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by norm_num) 3 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
      (t := 38857 / 10000) (by unfold fiveMeanY fiveFirstY fivePartY; norm_num) (by norm_num)
  unfold phaseGain5
  refine phaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hbr.2.1 hVa hVb hT25 ?_ ?_
  · unfold phaseTarget; linarith [hbr.1]
  · unfold phaseTarget; linarith [hbr.2.2]

theorem phaseGain5_one_lt_log_9_div_5 : phaseGain5 1 < Real.log (9 / 5) := by
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨hT25, -⟩ := phaseTarget_bounds 1 h1
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  set T₁ : ℝ := phaseTarget 1
  have hT₁lo : 288537 / 100000 < T₁ := by unfold T₁ phaseTarget; linarith
  have hT₁hi : T₁ < 28854 / 10000 := by unfold T₁ phaseTarget; linarith
  have hbr : eightMeanY (26 / 5) < 288537 / 100000 ∧
      eightMeanY (26 / 5) < eightMeanY (27 / 5) ∧
      (28854 / 10000 : ℝ) < eightMeanY (27 / 5) := by
    unfold eightMeanY eightFirstY eightPartY
    norm_num
  have h5up : dualValue S5 T₁ ≤ Real.log (fivePartY (19 / 5)) - yTilt (19 / 5) * T₁ := by
    have h := dualValue_le_at S4_subset_S5 hm4 (yTilt (19 / 5))
    rwa [partitionFn_S5, sum_F5_yTilt (19 / 5) (by norm_num)] at h
  have hplus_interp :
      (eightMeanY (27 / 5) - T₁) *
          (Real.log (eightPartY (26 / 5)) - yTilt (26 / 5) * eightMeanY (26 / 5)) +
        (T₁ - eightMeanY (26 / 5)) *
          (Real.log (eightPartY (27 / 5)) - yTilt (27 / 5) * eightMeanY (27 / 5)) ≤
        dualValue Splus T₁ * (eightMeanY (27 / 5) - eightMeanY (26 / 5)) := by
    have hD : 0 < eightMeanY (27 / 5) - eightMeanY (26 / 5) := by linarith [hbr.2.1]
    have hα : 0 ≤ eightMeanY (27 / 5) - T₁ := by linarith [hbr.2.2]
    have hβ : 0 ≤ T₁ - eightMeanY (26 / 5) := by linarith [hbr.1]
    refine (div_le_iff₀ hD).mp (le_ciInf fun l ↦ ?_)
    show _ ≤ Real.log (partitionFn Splus l) - l * T₁
    rw [div_le_iff₀ hD]
    have e1 := mul_le_mul_of_nonneg_left (splus_dual_lower_eight (26 / 5) (by norm_num) l) hα
    have e2 := mul_le_mul_of_nonneg_left (splus_dual_lower_eight (27 / 5) (by norm_num) l) hβ
    linarith
  have hVa : 0 < Real.log (9 * eightPartY (26 / 5) / (10 * fivePartY (19 / 5))) +
      eightMeanY (26 / 5) * Real.log (19 / 5 / (26 / 5)) := by
    have hρ := log_ge_of_artanh
      (m := 9 * eightPartY (26 / 5) / (10 * fivePartY (19 / 5)))
      (u := 847 / 6250) (L := 272717 / 1000000) (by norm_num) log_two_ge
      (by norm_num) (by norm_num) (by unfold eightPartY fivePartY; norm_num) 3
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := 19 / 5 / (26 / 5)) (u := 3 / 16)
      (L := 379487 / 1000000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by norm_num) 3 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr (by unfold eightMeanY eightFirstY eightPartY; norm_num)
      (t := 23 / 8) (by unfold eightMeanY eightFirstY eightPartY; norm_num) (by norm_num)
  have hVb : 0 < Real.log (9 * eightPartY (27 / 5) / (10 * fivePartY (19 / 5))) +
      eightMeanY (27 / 5) * Real.log (19 / 5 / (27 / 5)) := by
    have hρ := log_ge_of_artanh
      (m := 9 * eightPartY (27 / 5) / (10 * fivePartY (19 / 5)))
      (u := 472059 / 2500000) (L := 382231 / 1000000) (by norm_num) log_two_ge
      (by norm_num) (by norm_num) (by unfold eightPartY fivePartY; norm_num) 3
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := 19 / 5 / (27 / 5)) (u := 1692307 / 10000000)
      (L := 341747 / 1000000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by norm_num) 3 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr (by unfold eightMeanY eightFirstY eightPartY; norm_num)
      (t := 3661 / 1250) (by unfold eightMeanY eightFirstY eightPartY; norm_num) (by norm_num)
  have hP5 := fivePartY_pos (y := 19 / 5) (by norm_num)
  have hP8a := eightPartY_pos (y := 26 / 5) (by norm_num)
  have hP8b := eightPartY_pos (y := 27 / 5) (by norm_num)
  have hlog95 : Real.log (9 / 5 : ℝ) = Real.log 9 - Real.log 10 + Real.log 2 := by
    have : (9 / 5 : ℝ) = 9 / 10 * 2 := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num)]
  have eρa : Real.log (9 * eightPartY (26 / 5) / (10 * fivePartY (19 / 5))) =
      Real.log 9 + Real.log (eightPartY (26 / 5)) - Real.log 10 - Real.log (fivePartY (19 / 5)) := by
    rw [Real.log_div (mul_pos (by norm_num) hP8a).ne' (mul_pos (by norm_num) hP5).ne',
      Real.log_mul (by norm_num) hP8a.ne', Real.log_mul (by norm_num) hP5.ne']
    ring
  have eρb : Real.log (9 * eightPartY (27 / 5) / (10 * fivePartY (19 / 5))) =
      Real.log 9 + Real.log (eightPartY (27 / 5)) - Real.log 10 - Real.log (fivePartY (19 / 5)) := by
    rw [Real.log_div (mul_pos (by norm_num) hP8b).ne' (mul_pos (by norm_num) hP5).ne',
      Real.log_mul (by norm_num) hP8b.ne', Real.log_mul (by norm_num) hP5.ne']
    ring
  have era : Real.log (19 / 5 / (26 / 5)) = yTilt (19 / 5) - yTilt (26 / 5) := by
    unfold yTilt; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have erb : Real.log (19 / 5 / (27 / 5)) = yTilt (19 / 5) - yTilt (27 / 5) := by
    unfold yTilt; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  rw [eρa, era] at hVa
  rw [eρb, erb] at hVb
  have hD : 0 < eightMeanY (27 / 5) - eightMeanY (26 / 5) := by linarith [hbr.2.1]
  have hα : 0 < eightMeanY (27 / 5) - T₁ := by linarith [hbr.2.2]
  have hβ : 0 < T₁ - eightMeanY (26 / 5) := by linarith [hbr.1]
  have hpos := add_pos (mul_pos hα hVa) (mul_pos hβ hVb)
  have e5 := mul_le_mul_of_nonneg_left h5up hD.le
  unfold phaseGain5
  change Real.log 2 - dualValue Splus T₁ + dualValue S5 T₁ < Real.log (9 / 5)
  have key : (eightMeanY (27 / 5) - eightMeanY (26 / 5)) *
      (Real.log 2 - dualValue Splus T₁ + dualValue S5 T₁) <
      (eightMeanY (27 / 5) - eightMeanY (26 / 5)) * Real.log (9 / 5) := by
    rw [hlog95]
    linarith
  exact lt_of_mul_lt_mul_left key hD.le

/-- **Strict nonconstancy of `A₅`:** `A₅(1) < A₅(0)`. -/
theorem phaseGain5_one_lt_phaseGain5_zero : phaseGain5 1 < phaseGain5 0 :=
  lt_trans phaseGain5_one_lt_log_9_div_5 log_9_div_5_lt_phaseGain5_zero

/-! ## 3. Bridge between `Erdos625.fourEntropyLoss` and `dualValue` -/

theorem extendedGaussianEntropyValue_le_dualValue_Splus
    {T : ℝ} (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    extendedGaussianEntropyValue T ≤ dualValue Splus T := by
  refine le_ciInf fun l ↦ ?_
  have h := extendedGaussianEntropyValue_le_dual_interior (tilt := l) hT
  unfold extendedGaussianDualTestValue at h
  rwa [partitionFn_Splus]

theorem fourOptimizedValue_eq_dualValue_S4
    {T : ℝ} (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    ProfileEntropyS4.optimizedValue fourGaussianScore T = dualValue S4 T := by
  set l4 := ProfileEntropyS4.tilt fourGaussianScore T
  have hMean : ProfileEntropyS4.mean fourGaussianScore l4 = T :=
    ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT
  rw [dualValue_S4_eq (mean_condition hMean), sum_F4, ← partition_four_eq]
  rfl

/-- For every interior deficit target `T ∈ (2, 5)`, the primal four-size entropy
loss `fourEntropyLoss T` is at most the dual gap `𝓕_{S₊}(T) - 𝓕_{S₄}(T)`. -/
theorem fourEntropyLoss_le_dualValue_diff
    {T : ℝ} (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    fourEntropyLoss T ≤ dualValue Splus T - dualValue S4 T := by
  unfold fourEntropyLoss
  linarith [extendedGaussianEntropyValue_le_dualValue_Splus hT,
    fourOptimizedValue_eq_dualValue_S4 hT]

end

end Erdos625HP
