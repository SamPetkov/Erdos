import Erdos625.FiveSizePhaseGainSharp

/-!
# A two-cell certificate: `A₅(δ) > log (169/100)` on `[0,1]`

This module proves a uniform lower bound for the five-size phase gain that is
close to its true minimum (`min_δ A₅ ≈ 0.525995 = log 1.69214`, numerical
evidence only).  `Erdos625.lean` imports it, so it is part of the one-file
proof `Erdos625SelfContained.lean`; the released theorem `Erdos625.erdos625`
does not use it and is unchanged.  The definitions are those of
`Erdos625.FiveSizeEntropyGap`.

## Main result

* `log_169_div_100_lt_phaseGain5` — for every `0 ≤ δ ≤ 1`,
  `A₅(δ) = log 2 - 𝓕_{S₊}(T_δ) + 𝓕_{S₅}(T_δ) > log (169/100) ≈ 0.52473`.

The proof uses neither the four-size partition ratio nor the five-versus-four
step of `FiveSizeEntropyGap`.

## Proof

Write `q = log 2`, `yTilt y = q/2 + log y`, and for `y > 0`
`P₅(y) = Z_{S₅}(yTilt y)`, `M₅(y)` = the five-size mean at `yTilt y`
(both rational for rational `y`).

1. Tangent bound: `𝓕_{S₅}(M₅(y)) ≥ log P₅(y) - yTilt y · M₅(y)`.
2. Concavity: `𝓕_{S₅}` is an infimum of affine functions of `T`, so on
   `[M₅(y_a), M₅(y_b)]` it lies above the chord through the two values of 1.
3. For one tilt `yTilt z` per cell, `𝓕_{S₊}(T) ≤ log U(z) - yTilt z · T`, where
   `U(z) ≥ Z_{S₊}(yTilt z)` is the explicit tail bound of
   `FiveSizePhaseGainSharp.Zplus_le`.
4. The resulting lower bound for `A₅` is affine in `T` on the cell, so it
   suffices that at both endpoints
   `log (2 P₅(y_e) / (K U(z))) + M₅(y_e) · log (z / y_e) > 0`, `K = 169/100`.
5. These four endpoint inequalities are certified with rational lower bounds
   for logarithms (partial sums of `log ((1+u)/(1-u)) = 2 ∑ u^{2j+1}/(2j+1)`
   and `0.6931471803 < log 2 < 0.6931471808`).

Cells: `y ∈ [1907/500, 703/100]` with `z = 527/100`, and
`y ∈ [703/100, 513/50]` with `z = 213/25`.  The means satisfy
`M₅(1907/500) < 2/q` and `M₅(513/50) > 1 + 2/q`, so the two cells cover every
`T_δ`, `0 ≤ δ ≤ 1`.
-/

namespace Erdos625

namespace FiveSizePhaseGainCertificate

open scoped BigOperators Topology
open FiveSizeEntropyGap FiveSizePhaseGainSharp

set_option autoImplicit false

noncomputable section

/-! ## Five-size quantities at the tilt `yTilt y` -/

/-- `Z_{S₅}(yTilt y) = y²/2 + y³/8 + y⁴/64 + y⁵/1024 + y⁶/32768`. -/
def fivePartY (y : ℝ) : ℝ :=
  y ^ 2 / 2 + y ^ 3 / 8 + y ^ 4 / 64 + y ^ 5 / 1024 + y ^ 6 / 32768

/-- `∑_{i ∈ S₅} i · w_i(yTilt y)`. -/
def fiveFirstY (y : ℝ) : ℝ :=
  2 * (y ^ 2 / 2) + 3 * (y ^ 3 / 8) + 4 * (y ^ 4 / 64) + 5 * (y ^ 5 / 1024) +
    6 * (y ^ 6 / 32768)

/-- The five-size mean `M₅` at the tilt `yTilt y`. -/
def fiveMeanY (y : ℝ) : ℝ :=
  fiveFirstY y / fivePartY y

/-- The explicit upper bound `U(z) ≥ Z_{S₊}(yTilt z)` (valid for `z ≤ 16`). -/
def plusBoundY (z : ℝ) : ℝ :=
  (1 / (2 * z) + 1 + z) + (z ^ 2 / 2 + z ^ 3 / 8 + z ^ 4 / 64 + z ^ 5 / 1024) +
    (z ^ 6 / 32768 + 8 / 7 * (z ^ 7 / 2097152))

theorem fivePartY_pos {y : ℝ} (hy : 0 < y) : 0 < fivePartY y := by
  unfold fivePartY
  positivity

theorem plusBoundY_pos {z : ℝ} (hz : 0 < z) : 0 < plusBoundY z := by
  unfold plusBoundY
  positivity

theorem sum_F5_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F5, gaussWeight (yTilt y) i = fivePartY y := by
  obtain ⟨-, -, -, h2, h3, h4, h5, h6, -⟩ := weights_yTilt y hy
  unfold fivePartY
  rw [sum_F5, h2, h3, h4, h5, h6]

/-- At the tilt `yTilt y` the five-size mean is `fiveMeanY y`. -/
theorem five_mean_condition_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F5, ((i : ℝ) - fiveMeanY y) * gaussWeight (yTilt y) i = 0 := by
  obtain ⟨-, -, -, h2, h3, h4, h5, h6, -⟩ := weights_yTilt y hy
  have hP := fivePartY_pos hy
  have hmul : fiveMeanY y * fivePartY y = fiveFirstY y := by
    unfold fiveMeanY
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hP.ne', mul_one]
  unfold fivePartY fiveFirstY at hmul
  rw [sum_F5, h2, h3, h4, h5, h6]
  push_cast
  linear_combination -hmul

/-- Tangent bound: `𝓕_{S₅}`'s objective at any tilt dominates its value at
`yTilt y` for the target `M₅(y)`. -/
theorem five_dual_lower (y : ℝ) (hy : 0 < y) (lambda : ℝ) :
    Real.log (fivePartY y) - yTilt y * fiveMeanY y ≤
      Real.log (partitionFn S5 lambda) - lambda * fiveMeanY y := by
  have htan := tangent_finset F5 (fiveMeanY y) (yTilt y) lambda
  rw [five_mean_condition_yTilt y hy, mul_zero, add_zero, sum_F5_yTilt y hy] at htan
  have hP := fivePartY_pos hy
  have hZ5 := sum_gaussWeight_pos F5 F5_nonempty lambda
  rw [partitionFn_S5, log_sub_mul_eq hP, log_sub_mul_eq hZ5]
  exact Real.log_le_log (mul_pos hP (Real.exp_pos _)) htan

/-- Concavity of `𝓕_{S₅}` between two tangent points: the chord bound. -/
theorem five_dual_interp {ya yb T : ℝ} (hya : 0 < ya) (hyb : 0 < yb)
    (hTa : fiveMeanY ya ≤ T) (hTb : T ≤ fiveMeanY yb)
    (hab : fiveMeanY ya < fiveMeanY yb) :
    (fiveMeanY yb - T) * (Real.log (fivePartY ya) - yTilt ya * fiveMeanY ya) +
        (T - fiveMeanY ya) * (Real.log (fivePartY yb) - yTilt yb * fiveMeanY yb) ≤
      dualValue S5 T * (fiveMeanY yb - fiveMeanY ya) := by
  have hD : 0 < fiveMeanY yb - fiveMeanY ya := by linarith
  have hα : 0 ≤ fiveMeanY yb - T := by linarith
  have hβ : 0 ≤ T - fiveMeanY ya := by linarith
  have key :
      ((fiveMeanY yb - T) * (Real.log (fivePartY ya) - yTilt ya * fiveMeanY ya) +
          (T - fiveMeanY ya) * (Real.log (fivePartY yb) - yTilt yb * fiveMeanY yb)) /
        (fiveMeanY yb - fiveMeanY ya) ≤ dualValue S5 T := by
    refine le_ciInf fun l => ?_
    show _ ≤ Real.log (partitionFn S5 l) - l * T
    rw [div_le_iff₀ hD]
    have e1 := mul_le_mul_of_nonneg_left (five_dual_lower ya hya l) hα
    have e2 := mul_le_mul_of_nonneg_left (five_dual_lower yb hyb l) hβ
    linarith
  exact (div_le_iff₀ hD).mp key

/-! ## One cell -/

/-- **Cell lemma.**  If both endpoint inequalities hold, then
`log K < log 2 - 𝓕_{S₊}(T) + 𝓕_{S₅}(T)` for every `T` between the two
five-size means. -/
theorem phaseGain_cell_T {ya yb z K T : ℝ} (hya : 0 < ya) (hyb : 0 < yb) (hz : 0 < z)
    (hz16 : z ≤ 16) (hK : 0 < K) (hab : fiveMeanY ya < fiveMeanY yb)
    (hVa : 0 < Real.log (2 * fivePartY ya / (K * plusBoundY z)) +
      fiveMeanY ya * Real.log (z / ya))
    (hVb : 0 < Real.log (2 * fivePartY yb / (K * plusBoundY z)) +
      fiveMeanY yb * Real.log (z / yb))
    (hT25 : T ∈ Set.Ioo (2 : ℝ) 5) (hTa : fiveMeanY ya ≤ T) (hTb : T ≤ fiveMeanY yb) :
    Real.log K < Real.log 2 - dualValue Splus T + dualValue S5 T := by
  have hmean4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  have hU := plusBoundY_pos hz
  have hPa := fivePartY_pos hya
  have hPb := fivePartY_pos hyb
  -- the unrestricted support, at the single tilt `yTilt z`
  have hplus : dualValue Splus T ≤ Real.log (plusBoundY z) - yTilt z * T := by
    have h1 := dualValue_le_at S4_subset_Splus hmean4 (yTilt z)
    rw [partitionFn_Splus] at h1
    have h2 := Zplus_le (yTilt z) (yTilt_le_nine_q_half hz hz16)
    rw [lowPart_yTilt z hz, fourPartition_yTilt z hz, highPart_yTilt z hz] at h2
    have h3 : Real.log (extendedGaussianPartition q (yTilt z)) ≤ Real.log (plusBoundY z) :=
      Real.log_le_log (extendedGaussianPartition_pos q_pos) h2
    linarith
  -- the five-size support, by the chord bound
  have h5 := five_dual_interp hya hyb hTa hTb hab
  -- unfold the endpoint inequalities
  have eρa : Real.log (2 * fivePartY ya / (K * plusBoundY z)) =
      Real.log 2 + Real.log (fivePartY ya) - Real.log K - Real.log (plusBoundY z) := by
    rw [Real.log_div (mul_pos two_pos hPa).ne' (mul_pos hK hU).ne',
      Real.log_mul two_ne_zero hPa.ne', Real.log_mul hK.ne' hU.ne']
    ring
  have eρb : Real.log (2 * fivePartY yb / (K * plusBoundY z)) =
      Real.log 2 + Real.log (fivePartY yb) - Real.log K - Real.log (plusBoundY z) := by
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
  have hD : 0 < fiveMeanY yb - fiveMeanY ya := by linarith
  have hα : 0 ≤ fiveMeanY yb - T := by linarith
  have hβ : 0 ≤ T - fiveMeanY ya := by linarith
  have hpos : 0 < (fiveMeanY yb - T) *
        (Real.log 2 + Real.log (fivePartY ya) - Real.log K - Real.log (plusBoundY z) +
          fiveMeanY ya * (yTilt z - yTilt ya)) +
      (T - fiveMeanY ya) *
        (Real.log 2 + Real.log (fivePartY yb) - Real.log K - Real.log (plusBoundY z) +
          fiveMeanY yb * (yTilt z - yTilt yb)) := by
    rcases eq_or_lt_of_le hα with h0 | h0
    · rw [← h0, zero_mul, zero_add]
      exact mul_pos (by linarith) hVb
    · exact add_pos_of_pos_of_nonneg (mul_pos h0 hVa) (mul_nonneg hβ hVb.le)
  have e := mul_le_mul_of_nonneg_left hplus hD.le
  have key : (fiveMeanY yb - fiveMeanY ya) * Real.log K <
      (fiveMeanY yb - fiveMeanY ya) * (Real.log 2 - dualValue Splus T + dualValue S5 T) := by
    linarith
  exact lt_of_mul_lt_mul_left key hD.le

/-! ## Rational lower bounds for logarithms -/

/-- Partial sums of `log ((1+u)/(1-u)) = ∑ 2 u^{2j+1}/(2j+1)` are lower bounds
for `0 ≤ u < 1`. -/
theorem artanh_partial_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, 2 * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
      Real.log ((1 + u) / (1 - u)) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one
    (show |u| < 1 by rw [abs_of_nonneg hu0]; exact hu1)
  rw [Real.log_div (show (0 : ℝ) < 1 + u by linarith).ne'
    (show (0 : ℝ) < 1 - u by linarith).ne']
  refine sum_le_hasSum (Finset.range N) (fun j _ => ?_) h
  have h1 : (0 : ℝ) ≤ 1 / (2 * (j : ℝ) + 1) := by positivity
  exact mul_nonneg (mul_nonneg (by norm_num) h1) (pow_nonneg hu0 _)

/-- `log m ≥ lc + L` whenever `m ≥ c (1+u)/(1-u)`, `log c ≥ lc`, and `L` is
below a partial sum of the series of `log ((1+u)/(1-u))`. -/
theorem log_ge_of_artanh {m c u lc L : ℝ} (hc : 0 < c) (hlc : lc ≤ Real.log c)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hm : c * ((1 + u) / (1 - u)) ≤ m) (N : ℕ)
    (hL : L ≤ ∑ j ∈ Finset.range N, 2 * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)) :
    lc + L ≤ Real.log m := by
  have hX : 0 < (1 + u) / (1 - u) := div_pos (by linarith) (by linarith)
  have hlog := Real.log_le_log (mul_pos hc hX) hm
  rw [Real.log_mul hc.ne' hX.ne'] at hlog
  have := artanh_partial_le hu0 hu1 N
  linarith

theorem log_two_ge : (0.6931471803 : ℝ) ≤ Real.log 2 :=
  Real.log_two_gt_d9.le

theorem log_one_ge : (0 : ℝ) ≤ Real.log 1 := by
  simp

theorem log_half_ge : -(0.6931471808 : ℝ) ≤ Real.log (1 / 2) := by
  rw [one_div, Real.log_inv]
  linarith [Real.log_two_lt_d9]

theorem log_quarter_ge : -(2 * 0.6931471808 : ℝ) ≤ Real.log (1 / 4) := by
  rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

/-- Combine lower bounds `lρ ≤ log ρ`, `lr ≤ log r` and a bound on `T`. -/
theorem endpoint_of_bounds {ρ r T lρ lr t : ℝ} (hρ : lρ ≤ Real.log ρ)
    (hr : lr ≤ Real.log r) (hT : 0 ≤ T) (ht : t * lr ≤ T * lr)
    (hpos : 0 < lρ + t * lr) :
    0 < Real.log ρ + T * Real.log r := by
  have := mul_le_mul_of_nonneg_left hr hT
  linarith

/-! ## The four endpoint certificates -/

theorem endpoint_1a :
    0 < Real.log (2 * fivePartY (1907 / 500) / (169 / 100 * plusBoundY (527 / 100))) +
      fiveMeanY (1907 / 500) * Real.log (527 / 100 / (1907 / 500)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fivePartY (1907 / 500) / (169 / 100 * plusBoundY (527 / 100)))
    (u := 2233739 / 10000000) (L := 71001373 / 156250000) (by norm_num) log_quarter_ge
    (by norm_num) (by norm_num) (by unfold fivePartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 527 / 100 / (1907 / 500)) (u := 364 / 2271)
    (L := 3233518553 / 10000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (t := 577073 / 200000) (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (by norm_num)

theorem endpoint_1b :
    0 < Real.log (2 * fivePartY (703 / 100) / (169 / 100 * plusBoundY (527 / 100))) +
      fiveMeanY (703 / 100) * Real.log (527 / 100 / (703 / 100)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fivePartY (703 / 100) / (169 / 100 * plusBoundY (527 / 100)))
    (u := 189183 / 1250000) (L := 610072451 / 2000000000) (by norm_num) log_two_ge
    (by norm_num) (by norm_num) (by unfold fivePartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 527 / 100 / (703 / 100)) (u := 351 / 1757)
    (L := 4049908371 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (t := 345789 / 100000) (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (by norm_num)

theorem endpoint_2a :
    0 < Real.log (2 * fivePartY (703 / 100) / (169 / 100 * plusBoundY (213 / 25))) +
      fiveMeanY (703 / 100) * Real.log (213 / 25 / (703 / 100)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fivePartY (703 / 100) / (169 / 100 * plusBoundY (213 / 25)))
    (u := 660957 / 10000000) (L := 1323844051 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by unfold fivePartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 213 / 25 / (703 / 100)) (u := 149 / 1555)
    (L := 38445927 / 200000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (t := 3457889 / 1000000) (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (by norm_num)

theorem endpoint_2b :
    0 < Real.log (2 * fivePartY (513 / 50) / (169 / 100 * plusBoundY (213 / 25))) +
      fiveMeanY (513 / 50) * Real.log (213 / 25 / (513 / 50)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * fivePartY (513 / 50) / (169 / 100 * plusBoundY (213 / 25)))
    (u := 332433 / 5000000) (L := 1331696559 / 10000000000) (by norm_num) log_two_ge
    (by norm_num) (by norm_num) (by unfold fivePartY plusBoundY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := 213 / 25 / (513 / 50)) (u := 113 / 455)
    (L := 2536553397 / 5000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (t := 3885603 / 1000000) (by unfold fiveMeanY fiveFirstY fivePartY; norm_num)
    (by norm_num)

/-! ## Covering the phase interval -/

theorem two_div_log_two_bounds :
    (288537 / 100000 : ℝ) < 2 / Real.log 2 ∧ 1 + 2 / Real.log 2 < 38854 / 10000 := by
  have hq0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hqlo := Real.log_two_gt_d9
  have hqhi := Real.log_two_lt_d9
  constructor
  · rw [lt_div_iff₀ hq0]
    linarith
  · have h : 2 / Real.log 2 < 28854 / 10000 := by
      rw [div_lt_iff₀ hq0]
      linarith
    linarith

theorem fiveMean_breakpoints :
    fiveMeanY (1907 / 500) < 288537 / 100000 ∧
      fiveMeanY (1907 / 500) < fiveMeanY (703 / 100) ∧
      fiveMeanY (703 / 100) < fiveMeanY (513 / 50) ∧
      (38854 / 10000 : ℝ) < fiveMeanY (513 / 50) := by
  unfold fiveMeanY fiveFirstY fivePartY
  norm_num

/-! ## Main theorem -/

/-- **Uniform bound `A₅(δ) > log (169/100)`.**  For every `0 ≤ δ ≤ 1`,
`log (169/100) < A₅(δ) = log 2 - 𝓕_{S₊}(T_δ) + 𝓕_{S₅}(T_δ)`
(`log (169/100) ≈ 0.52473`; numerically `min_δ A₅ ≈ 0.52599`). -/
theorem log_169_div_100_lt_phaseGain5 (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (169 / 100) < phaseGain5 delta := by
  obtain ⟨hT25, -⟩ := phaseTarget_bounds delta hdelta
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  obtain ⟨c0, c01, c12, c2⟩ := fiveMean_breakpoints
  obtain ⟨h0, h1⟩ := hdelta
  have hlo : fiveMeanY (1907 / 500) ≤ phaseTarget delta := by
    unfold phaseTarget
    linarith
  have hhi : phaseTarget delta ≤ fiveMeanY (513 / 50) := by
    unfold phaseTarget
    linarith
  unfold phaseGain5
  rcases le_total (phaseTarget delta) (fiveMeanY (703 / 100)) with h | h
  · exact phaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c01 endpoint_1a endpoint_1b hT25 hlo h
  · exact phaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c12 endpoint_2a endpoint_2b hT25 h hhi

/-- The new constant improves both `γ₅ = log (8750/6681)` and the constant
`log (2605/1651)` of `FiveSizePhaseGainSharp`. -/
theorem log_2605_div_1651_lt_log_169_div_100 :
    gamma5 < Real.log (169 / 100) ∧ Real.log (2605 / 1651) < Real.log (169 / 100) := by
  unfold gamma5
  exact ⟨Real.log_lt_log (by norm_num) (by norm_num),
    Real.log_lt_log (by norm_num) (by norm_num)⟩

end

end FiveSizePhaseGainCertificate

end Erdos625

#print axioms Erdos625.FiveSizePhaseGainCertificate.log_169_div_100_lt_phaseGain5
#print axioms Erdos625.FiveSizePhaseGainCertificate.log_2605_div_1651_lt_log_169_div_100
