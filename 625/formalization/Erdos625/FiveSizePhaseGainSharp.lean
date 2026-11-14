import Erdos625.FiveSizeEntropyGap

/-!
# A sharper uniform lower bound for the five-size phase gain

This module sharpens the uniform constant of `Erdos625.FiveSizeEntropyGap`
without editing it.  `Erdos625.lean` imports it, so it is part of the one-file
proof `Erdos625SelfContained.lean`; the released theorem `Erdos625.erdos625`
does not use it and is unchanged.

The definitions are those of `Erdos625.FiveSizeEntropyGap` (the manuscript's
literal `gaussWeight`, `partitionFn`, `dualValue`, `phaseTarget`, `phaseGain5`,
...).  The only change is a sharper four-size partition-ratio certificate.

## Main results

* `sharp_four_size_partition_ratio_for_delta` — at the four-size tilt
  `λ₄ = λ_{S₄}(T_δ)`, `Z_{S₊}(λ₄) / Z_{S₄}(λ₄) < 127/100` for `0 ≤ δ ≤ 1`
  (the repository's `uniform_four_size_partition_ratio_for_delta` has `153/100`).
* `sharp_four_size_entropy_certificate` — `0 ≤ D₄(δ) < log (127/100)` and
  `A₄(δ) > log (200/127)`.
* `log_2605_div_1651_lt_phaseGain5` — `A₅(δ) > log (2605/1651)` on `[0,1]`,
  where `log (2605/1651) = log (200/127) + log (521/520) ≈ 0.45605`
  (the module `FiveSizeEntropyGap` proves `log (8750/6681) ≈ 0.26979`).

## Proof of the ratio certificate

Write `q = log 2` and parametrize tilts by `y = e^{λ - q/2}`
(`yTilt y = q/2 + log y`).  Then `w_i(yTilt y) = y^i / 2^{i(i-1)/2}` is
rational for rational `y`.

1. Tilt corridor: the four-size mean at `y = 389/100` is below `2885/1000 < 2/q`
   and at `y = 308/25` it is above `38854/10000 > 1 + 2/q`; strict monotonicity
   of the mean gives `yTilt (389/100) < λ₄ < yTilt (308/25)`.
2. Tail: for `λ ≤ 9q/2`, `w_{d+1} ≤ w_d / 8` for `d ≥ 7`, so
   `Z_{S₊} ≤ (w_{-1} + w_0 + w_1) + Z_{S₄} + (w_6 + (8/7) w_7)`.
3. Cell bound: for `a ≤ λ ≤ b`, each `w_i(λ)/Z_{S₄}(λ)` with `i ≤ 1` is at most
   its value at `a`, and each with `i ≥ 6` is at most its value at `b`.
4. Four rational cells with breakpoints `y = 389/100, 4, 5, 10, 308/25`; on each
   the cell bound is below `27/100` (checked by `norm_num`).
-/

namespace Erdos625

namespace FiveSizePhaseGainSharp

open scoped BigOperators Topology
open FiveSizeEntropyGap

set_option autoImplicit false

noncomputable section

/-! ## The tilt parametrization `y = e^{λ - q/2}` -/

/-- The tilt `λ = log 2 / 2 + log y`, i.e. `e^{λ - q/2} = y`. -/
def yTilt (y : ℝ) : ℝ :=
  Real.log 2 / 2 + Real.log y

theorem gaussWeight_yTilt (y : ℝ) (hy : 0 < y) (i : ℤ) (n k : ℕ)
    (hi : (i : ℝ) = n) (hk : (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2) :
    gaussWeight (yTilt y) i = y ^ n / 2 ^ k := by
  rw [gaussWeight_eq_exp (yTilt y) i ((n : ℝ) * Real.log y - (k : ℝ) * Real.log 2)
      (by unfold yTilt; rw [hi]; linear_combination (Real.log 2) * hk),
    Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hy,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem gaussWeight_yTilt_neg_one (y : ℝ) (hy : 0 < y) :
    gaussWeight (yTilt y) (-1) = 1 / (2 * y) := by
  rw [gaussWeight_eq_exp (yTilt y) (-1) (-Real.log (2 * y))
      (by unfold yTilt; rw [Real.log_mul two_ne_zero hy.ne']; push_cast; ring),
    Real.exp_neg, Real.exp_log (mul_pos two_pos hy), one_div]

/-- The weights `w_{-1}, …, w_7` at the tilt `yTilt y`. -/
theorem weights_yTilt (y : ℝ) (hy : 0 < y) :
    gaussWeight (yTilt y) (-1) = 1 / (2 * y) ∧
      gaussWeight (yTilt y) 0 = 1 ∧
      gaussWeight (yTilt y) 1 = y ∧
      gaussWeight (yTilt y) 2 = y ^ 2 / 2 ∧
      gaussWeight (yTilt y) 3 = y ^ 3 / 8 ∧
      gaussWeight (yTilt y) 4 = y ^ 4 / 64 ∧
      gaussWeight (yTilt y) 5 = y ^ 5 / 1024 ∧
      gaussWeight (yTilt y) 6 = y ^ 6 / 32768 ∧
      gaussWeight (yTilt y) 7 = y ^ 7 / 2097152 := by
  refine ⟨gaussWeight_yTilt_neg_one y hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gaussWeight_yTilt y hy 0 0 0 (by norm_num) (by norm_num)]
    norm_num
  · rw [gaussWeight_yTilt y hy 1 1 0 (by norm_num) (by norm_num)]
    norm_num
  · rw [gaussWeight_yTilt y hy 2 2 1 (by norm_num) (by norm_num)]
    norm_num
  · rw [gaussWeight_yTilt y hy 3 3 3 (by norm_num) (by norm_num)]
    norm_num
  · rw [gaussWeight_yTilt y hy 4 4 6 (by norm_num) (by norm_num)]
    norm_num
  · rw [gaussWeight_yTilt y hy 5 5 10 (by norm_num) (by norm_num)]
    norm_num
  · rw [gaussWeight_yTilt y hy 6 6 15 (by norm_num) (by norm_num)]
    norm_num
  · rw [gaussWeight_yTilt y hy 7 7 21 (by norm_num) (by norm_num)]
    norm_num

theorem yTilt_le_yTilt {y y' : ℝ} (hy : 0 < y) (h : y ≤ y') : yTilt y ≤ yTilt y' := by
  unfold yTilt
  linarith [Real.log_le_log hy h]

theorem yTilt_le_nine_q_half {y : ℝ} (hy : 0 < y) (h : y ≤ 16) : yTilt y ≤ 9 * q / 2 := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hl := Real.log_le_log hy h
  unfold yTilt q
  linarith

/-! ## The pieces of the partition functions -/

/-- `Z_{S₄}(λ) = ∑_{i ∈ {2,3,4,5}} w_i(λ)`. -/
def fourPartition (lambda : ℝ) : ℝ :=
  ∑ i ∈ F4, gaussWeight lambda i

/-- The weights of `S₊` below `S₄`: `w_{-1} + w_0 + w_1`. -/
def lowPart (lambda : ℝ) : ℝ :=
  gaussWeight lambda (-1) + gaussWeight lambda 0 + gaussWeight lambda 1

/-- The bound `w_6 + (8/7) w_7` for the weights of `S₊` above `S₄`. -/
def highPart (lambda : ℝ) : ℝ :=
  gaussWeight lambda 6 + 8 / 7 * gaussWeight lambda 7

theorem fourPartition_pos (lambda : ℝ) : 0 < fourPartition lambda :=
  sum_gaussWeight_pos F4 F4_nonempty lambda

theorem fourPartition_yTilt (y : ℝ) (hy : 0 < y) :
    fourPartition (yTilt y) = y ^ 2 / 2 + y ^ 3 / 8 + y ^ 4 / 64 + y ^ 5 / 1024 := by
  obtain ⟨-, -, -, h2, h3, h4, h5, -, -⟩ := weights_yTilt y hy
  unfold fourPartition
  rw [sum_F4, h2, h3, h4, h5]

theorem lowPart_yTilt (y : ℝ) (hy : 0 < y) :
    lowPart (yTilt y) = 1 / (2 * y) + 1 + y := by
  obtain ⟨hm1, h0, h1, -, -, -, -, -, -⟩ := weights_yTilt y hy
  unfold lowPart
  rw [hm1, h0, h1]

theorem highPart_yTilt (y : ℝ) (hy : 0 < y) :
    highPart (yTilt y) = y ^ 6 / 32768 + 8 / 7 * (y ^ 7 / 2097152) := by
  obtain ⟨-, -, -, -, -, -, -, h6, h7⟩ := weights_yTilt y hy
  unfold highPart
  rw [h6, h7]

theorem mean_yTilt (y : ℝ) (hy : 0 < y) :
    ProfileEntropyS4.mean fourGaussianScore (yTilt y) =
      (2 * (y ^ 2 / 2) + 3 * (y ^ 3 / 8) + 4 * (y ^ 4 / 64) + 5 * (y ^ 5 / 1024)) /
        (y ^ 2 / 2 + y ^ 3 / 8 + y ^ 4 / 64 + y ^ 5 / 1024) := by
  obtain ⟨-, -, -, h2, h3, h4, h5, -, -⟩ := weights_yTilt y hy
  unfold ProfileEntropyS4.mean
  rw [firstNumerator_four_eq, partition_four_eq, h2, h3, h4, h5]

/-! ## A sharper tilt corridor -/

theorem two_div_q_bounds : (2885 / 1000 : ℝ) < 2 / q ∧ 1 + 2 / q < 38854 / 10000 := by
  have hq0 : 0 < q := q_pos
  have hqlo : (0.6931471803 : ℝ) < q := Real.log_two_gt_d9
  have hqhi : q < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  constructor
  · rw [lt_div_iff₀ hq0]
    linarith
  · have h : 2 / q < 28854 / 10000 := by
      rw [div_lt_iff₀ hq0]
      linarith
    linarith

theorem mean_lower_endpoint :
    ProfileEntropyS4.mean fourGaussianScore (yTilt (389 / 100)) < 2885 / 1000 := by
  rw [mean_yTilt (389 / 100) (by norm_num)]
  norm_num

theorem mean_upper_endpoint :
    (38854 / 10000 : ℝ) < ProfileEntropyS4.mean fourGaussianScore (yTilt (308 / 25)) := by
  rw [mean_yTilt (308 / 25) (by norm_num)]
  norm_num

/-- **Sharper tilt corridor.**  For `0 ≤ δ ≤ 1`, every four-size tilt with
mean `T_δ` satisfies `log 2/2 + log (389/100) < λ < log 2/2 + log (308/25)`. -/
theorem sharp_tilt_corridor {delta lambda : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hMean : ProfileEntropyS4.mean fourGaussianScore lambda = 1 + 2 / q - delta) :
    yTilt (389 / 100) < lambda ∧ lambda < yTilt (308 / 25) := by
  obtain ⟨hlo, hhi⟩ := two_div_q_bounds
  have hm := ProfileEntropyS4.strictMono_mean fourGaussianScore
  have e1 := mean_lower_endpoint
  have e2 := mean_upper_endpoint
  constructor
  · by_contra h
    have h' := hm.monotone (not_lt.mp h)
    rw [hMean] at h'
    linarith
  · by_contra h
    have h' := hm.monotone (not_lt.mp h)
    rw [hMean] at h'
    linarith

/-! ## Tail of the unrestricted partition function -/

theorem atom_eq (lambda : ℝ) :
    extendedGaussianExceptionalAtom q lambda = gaussWeight lambda (-1) := by
  unfold extendedGaussianExceptionalAtom gaussWeight q
  congr 1
  push_cast
  ring

theorem natTerm_eq (lambda : ℝ) (d : ℕ) :
    extendedGaussianNaturalTerm q lambda d = gaussWeight lambda (d : ℤ) := by
  unfold gaussWeight extendedGaussianNaturalTerm q
  simp

theorem exp_neg_three_q : Real.exp (-(3 * q)) = 1 / 8 := by
  rw [Real.exp_neg, show (3 : ℝ) * q = ((3 : ℕ) : ℝ) * Real.log 2 by unfold q; norm_num,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem natTerm_succ_le (lambda : ℝ) (hl : lambda ≤ 9 * q / 2) (d : ℕ) (hd : 7 ≤ d) :
    extendedGaussianNaturalTerm q lambda (d + 1) ≤
      1 / 8 * extendedGaussianNaturalTerm q lambda d := by
  have hq : 0 < q := q_pos
  have hstep : extendedGaussianNaturalTerm q lambda (d + 1) =
      Real.exp (lambda - q / 2 * (2 * d + 1)) * extendedGaussianNaturalTerm q lambda d := by
    unfold extendedGaussianNaturalTerm
    rw [← Real.exp_add]
    push_cast
    congr 1
    ring
  have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hle : lambda - q / 2 * (2 * d + 1) ≤ -(3 * q) := by
    nlinarith [mul_le_mul_of_nonneg_left hd' hq.le]
  have h8 : Real.exp (lambda - q / 2 * (2 * d + 1)) ≤ 1 / 8 := by
    rw [← exp_neg_three_q]
    exact Real.exp_le_exp.mpr hle
  rw [hstep]
  exact mul_le_mul_of_nonneg_right h8 (Real.exp_nonneg _)

theorem tsum_natTerm_le (lambda : ℝ) (hl : lambda ≤ 9 * q / 2) :
    ∑' d : ℕ, extendedGaussianNaturalTerm q lambda d ≤
      (∑ d ∈ Finset.range 7, extendedGaussianNaturalTerm q lambda d) +
        8 / 7 * extendedGaussianNaturalTerm q lambda 7 := by
  have hs : Summable (extendedGaussianNaturalTerm q lambda) :=
    summable_extendedGaussianNaturalTerm q_pos
  have hgeom : ∀ n : ℕ, extendedGaussianNaturalTerm q lambda (n + 7) ≤
      (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 7 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [(by omega : n + 1 + 7 = n + 7 + 1)]
      calc extendedGaussianNaturalTerm q lambda (n + 7 + 1)
          ≤ 1 / 8 * extendedGaussianNaturalTerm q lambda (n + 7) :=
            natTerm_succ_le lambda hl (n + 7) (by omega)
        _ ≤ 1 / 8 * ((1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 7) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 8 : ℝ) ^ (n + 1) * extendedGaussianNaturalTerm q lambda 7 := by
            ring
  have hgs : Summable (fun n : ℕ => (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 7) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have htail : ∑' n : ℕ, extendedGaussianNaturalTerm q lambda (n + 7) ≤
      8 / 7 * extendedGaussianNaturalTerm q lambda 7 := by
    calc ∑' n : ℕ, extendedGaussianNaturalTerm q lambda (n + 7)
        ≤ ∑' n : ℕ, (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 7 :=
          Summable.tsum_le_tsum hgeom ((summable_nat_add_iff 7).mpr hs) hgs
      _ = 8 / 7 * extendedGaussianNaturalTerm q lambda 7 := by
          rw [tsum_mul_right,
            tsum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num)]
          norm_num
  rw [← hs.sum_add_tsum_nat_add 7]
  linarith

/-- For `λ ≤ 9q/2`: `Z_{S₊}(λ) ≤ (w_{-1}+w_0+w_1) + Z_{S₄} + (w_6 + (8/7) w_7)`. -/
theorem Zplus_le (lambda : ℝ) (hl : lambda ≤ 9 * q / 2) :
    extendedGaussianPartition q lambda ≤
      lowPart lambda + fourPartition lambda + highPart lambda := by
  have h := tsum_natTerm_le lambda hl
  have hfin : (∑ d ∈ Finset.range 7, extendedGaussianNaturalTerm q lambda d) +
      8 / 7 * extendedGaussianNaturalTerm q lambda 7 =
      gaussWeight lambda 0 + gaussWeight lambda 1 + fourPartition lambda +
        highPart lambda := by
    unfold fourPartition highPart
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, natTerm_eq, sum_F4]
    push_cast
    ring
  unfold extendedGaussianPartition
  rw [atom_eq]
  unfold lowPart
  linarith

/-! ## Monotone ratio bounds on a cell -/

theorem cross_le {a lambda : ℝ} (h : a ≤ lambda) {i j : ℤ} (hij : i ≤ j) :
    gaussWeight lambda i * gaussWeight a j ≤ gaussWeight a i * gaussWeight lambda j := by
  rw [gaussWeight_shift lambda a i, gaussWeight_shift lambda a j]
  have hexp : Real.exp ((lambda - a) * (i : ℝ)) ≤ Real.exp ((lambda - a) * (j : ℝ)) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (sub_nonneg.mpr h))
  have hpos := mul_pos (gaussWeight_pos a i) (gaussWeight_pos a j)
  calc gaussWeight a i * Real.exp ((lambda - a) * (i : ℝ)) * gaussWeight a j
      = (gaussWeight a i * gaussWeight a j) * Real.exp ((lambda - a) * (i : ℝ)) := by ring
    _ ≤ (gaussWeight a i * gaussWeight a j) * Real.exp ((lambda - a) * (j : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp hpos.le
    _ = gaussWeight a i * (gaussWeight a j * Real.exp ((lambda - a) * (j : ℝ))) := by ring

theorem mem_F4_bounds {j : ℤ} (hj : j ∈ F4) : 2 ≤ j ∧ j ≤ 5 := by
  simp only [F4, Finset.mem_insert, Finset.mem_singleton] at hj
  omega

/-- For `i ≤ 2` and `a ≤ λ`: `w_i(λ)/Z_{S₄}(λ) ≤ w_i(a)/Z_{S₄}(a)`. -/
theorem one_low_mono {a lambda : ℝ} (h : a ≤ lambda) {i : ℤ} (hi : i ≤ 2) :
    gaussWeight lambda i * fourPartition a ≤ gaussWeight a i * fourPartition lambda := by
  unfold fourPartition
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => cross_le h ?_
  have := (mem_F4_bounds hj).1
  omega

/-- For `i ≥ 5` and `λ ≤ b`: `w_i(λ)/Z_{S₄}(λ) ≤ w_i(b)/Z_{S₄}(b)`. -/
theorem one_high_mono {lambda b : ℝ} (h : lambda ≤ b) {i : ℤ} (hi : 5 ≤ i) :
    gaussWeight lambda i * fourPartition b ≤ gaussWeight b i * fourPartition lambda := by
  unfold fourPartition
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hji : j ≤ i := by
    have := (mem_F4_bounds hj).2
    omega
  linarith [cross_le h hji]

theorem low_mono {a lambda : ℝ} (h : a ≤ lambda) :
    lowPart lambda * fourPartition a ≤ lowPart a * fourPartition lambda := by
  have h1 := one_low_mono h (i := -1) (by norm_num)
  have h2 := one_low_mono h (i := 0) (by norm_num)
  have h3 := one_low_mono h (i := 1) (by norm_num)
  calc lowPart lambda * fourPartition a
      = gaussWeight lambda (-1) * fourPartition a + gaussWeight lambda 0 * fourPartition a +
          gaussWeight lambda 1 * fourPartition a := by unfold lowPart; ring
    _ ≤ gaussWeight a (-1) * fourPartition lambda + gaussWeight a 0 * fourPartition lambda +
          gaussWeight a 1 * fourPartition lambda := add_le_add (add_le_add h1 h2) h3
    _ = lowPart a * fourPartition lambda := by unfold lowPart; ring

theorem high_mono {lambda b : ℝ} (h : lambda ≤ b) :
    highPart lambda * fourPartition b ≤ highPart b * fourPartition lambda := by
  have h6 := one_high_mono h (i := 6) (by norm_num)
  have h7 := one_high_mono h (i := 7) (by norm_num)
  calc highPart lambda * fourPartition b
      = gaussWeight lambda 6 * fourPartition b +
          8 / 7 * (gaussWeight lambda 7 * fourPartition b) := by unfold highPart; ring
    _ ≤ gaussWeight b 6 * fourPartition lambda +
          8 / 7 * (gaussWeight b 7 * fourPartition lambda) :=
        add_le_add h6 (mul_le_mul_of_nonneg_left h7 (by norm_num))
    _ = highPart b * fourPartition lambda := by unfold highPart; ring

/-- **Cell bound.**  If `a ≤ λ ≤ b ≤ 9q/2` then
`Z_{S₊}(λ) < (1 + r) Z_{S₄}(λ)` whenever
`(w_{-1}+w_0+w_1)(a)/Z_{S₄}(a) + (w_6 + (8/7)w_7)(b)/Z_{S₄}(b) < r`. -/
theorem ratio_cell {a b lambda : ℝ} (ha : a ≤ lambda) (hb : lambda ≤ b)
    (hb9 : b ≤ 9 * q / 2) {r : ℝ}
    (hcell : lowPart a / fourPartition a + highPart b / fourPartition b < r) :
    extendedGaussianPartition q lambda < (1 + r) * fourPartition lambda := by
  have hZa := fourPartition_pos a
  have hZb := fourPartition_pos b
  have hZ := fourPartition_pos lambda
  have h1 : lowPart lambda ≤ lowPart a / fourPartition a * fourPartition lambda := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hZa]
    exact low_mono ha
  have h2 : highPart lambda ≤ highPart b / fourPartition b * fourPartition lambda := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hZb]
    exact high_mono hb
  calc extendedGaussianPartition q lambda
      ≤ lowPart lambda + fourPartition lambda + highPart lambda :=
        Zplus_le lambda (hb.trans hb9)
    _ ≤ lowPart a / fourPartition a * fourPartition lambda + fourPartition lambda +
          highPart b / fourPartition b * fourPartition lambda := by linarith
    _ = (1 + (lowPart a / fourPartition a + highPart b / fourPartition b)) *
          fourPartition lambda := by ring
    _ < (1 + r) * fourPartition lambda :=
        mul_lt_mul_of_pos_right (by linarith) hZ

/-! ## The four rational cells -/

theorem cell_1 :
    lowPart (yTilt (389 / 100)) / fourPartition (yTilt (389 / 100)) +
      highPart (yTilt 4) / fourPartition (yTilt 4) < 27 / 100 := by
  rw [lowPart_yTilt (389 / 100) (by norm_num), fourPartition_yTilt (389 / 100) (by norm_num),
    highPart_yTilt 4 (by norm_num), fourPartition_yTilt 4 (by norm_num)]
  norm_num

theorem cell_2 :
    lowPart (yTilt 4) / fourPartition (yTilt 4) +
      highPart (yTilt 5) / fourPartition (yTilt 5) < 27 / 100 := by
  rw [lowPart_yTilt 4 (by norm_num), fourPartition_yTilt 4 (by norm_num),
    highPart_yTilt 5 (by norm_num), fourPartition_yTilt 5 (by norm_num)]
  norm_num

theorem cell_3 :
    lowPart (yTilt 5) / fourPartition (yTilt 5) +
      highPart (yTilt 10) / fourPartition (yTilt 10) < 27 / 100 := by
  rw [lowPart_yTilt 5 (by norm_num), fourPartition_yTilt 5 (by norm_num),
    highPart_yTilt 10 (by norm_num), fourPartition_yTilt 10 (by norm_num)]
  norm_num

theorem cell_4 :
    lowPart (yTilt 10) / fourPartition (yTilt 10) +
      highPart (yTilt (308 / 25)) / fourPartition (yTilt (308 / 25)) < 27 / 100 := by
  rw [lowPart_yTilt 10 (by norm_num), fourPartition_yTilt 10 (by norm_num),
    highPart_yTilt (308 / 25) (by norm_num), fourPartition_yTilt (308 / 25) (by norm_num)]
  norm_num

/-! ## The sharper partition-ratio certificate -/

/-- **Sharper uniform partition-ratio certificate.**  For `0 ≤ δ ≤ 1` and every
tilt `λ` whose four-size mean is `T_δ = 1 + 2/q - δ`,
`Z_{S₊}(λ) / Z_{S₄}(λ) < 127/100`.  Same hypotheses as the repository's
`uniform_four_size_partition_ratio_for_delta` (which has `153/100`). -/
theorem sharp_four_size_partition_ratio_for_delta
    (delta lambda : ℝ)
    (hDeltaLower : 0 ≤ delta)
    (hDeltaUpper : delta ≤ 1)
    (hMean : ProfileEntropyS4.mean fourGaussianScore lambda = 1 + 2 / q - delta) :
    extendedGaussianPartition q lambda /
        ProfileEntropyS4.partition fourGaussianScore lambda <
      (127 / 100 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := sharp_tilt_corridor hDeltaLower hDeltaUpper hMean
  have hZ : ProfileEntropyS4.partition fourGaussianScore lambda = fourPartition lambda := by
    rw [partition_four_eq]
    unfold fourPartition
    rw [sum_F4]
  rw [hZ, div_lt_iff₀ (fourPartition_pos lambda)]
  have h9 : ∀ y : ℝ, 0 < y → y ≤ 16 → yTilt y ≤ 9 * q / 2 :=
    fun y hy h => yTilt_le_nine_q_half hy h
  have key : extendedGaussianPartition q lambda < (1 + 27 / 100) * fourPartition lambda := by
    rcases le_or_gt lambda (yTilt 4) with h1 | h1
    · exact ratio_cell hlo.le h1 (h9 4 (by norm_num) (by norm_num)) cell_1
    rcases le_or_gt lambda (yTilt 5) with h2 | h2
    · exact ratio_cell h1.le h2 (h9 5 (by norm_num) (by norm_num)) cell_2
    rcases le_or_gt lambda (yTilt 10) with h3 | h3
    · exact ratio_cell h2.le h3 (h9 10 (by norm_num) (by norm_num)) cell_3
    · exact ratio_cell h3.le hhi.le (h9 (308 / 25) (by norm_num) (by norm_num)) cell_4
  linarith

/-! ## Consequences for `A₄` and `A₅` -/

/-- The comparison inequalities at the phase target with the sharper ratio,
with the four-size dual value `v = 𝓕_{S₄}(T_δ)`. -/
theorem sharp_core_at_delta (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    ∃ v : ℝ,
      dualValue S4 (phaseTarget delta) = v ∧
      Real.log (521 / 520) + v ≤ dualValue S5 (phaseTarget delta) ∧
      dualValue Splus (phaseTarget delta) < Real.log (127 / 100) + v ∧
      v ≤ dualValue Splus (phaseTarget delta) := by
  obtain ⟨hT25, hT⟩ := phaseTarget_bounds delta hdelta
  obtain ⟨l4, hmeanT⟩ : ∃ l4 : ℝ,
      ProfileEntropyS4.mean fourGaussianScore l4 = phaseTarget delta :=
    ⟨_, ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25⟩
  have hmean := mean_condition hmeanT
  refine ⟨Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * phaseTarget delta,
    dualValue_S4_eq hmean, le_dualValue_S5 hT hmean, ?_,
    le_dualValue_of_superset S4_subset_Splus hmean⟩
  have hratio := sharp_four_size_partition_ratio_for_delta delta l4
    hdelta.1 hdelta.2 hmeanT
  have hle := dualValue_le_at S4_subset_Splus hmean l4
  rw [partitionFn_Splus] at hle
  have hZ4 : ProfileEntropyS4.partition fourGaussianScore l4 =
      ∑ i ∈ F4, gaussWeight l4 i := by
    rw [partition_four_eq, sum_F4]
  rw [hZ4] at hratio
  have hZ4pos := sum_gaussWeight_pos F4 F4_nonempty l4
  have hZpos := extendedGaussianPartition_pos (a := q) (lambda := l4) q_pos
  have hlog : Real.log (extendedGaussianPartition q l4) -
      Real.log (∑ i ∈ F4, gaussWeight l4 i) < Real.log (127 / 100) := by
    rw [← Real.log_div hZpos.ne' hZ4pos.ne']
    exact Real.log_lt_log (div_pos hZpos hZ4pos) hratio
  linarith

theorem log_200_div_127_eq :
    Real.log (200 / 127) = Real.log 2 - Real.log (127 / 100) := by
  rw [show (200 / 127 : ℝ) = 2 / (127 / 100) by norm_num]
  exact Real.log_div (by norm_num) (by norm_num)

theorem log_2605_div_1651_eq :
    Real.log (2605 / 1651) = Real.log (200 / 127) + Real.log (521 / 520) := by
  rw [show (2605 / 1651 : ℝ) = 200 / 127 * (521 / 520) by norm_num]
  exact Real.log_mul (by norm_num) (by norm_num)

/-- The sharper four-size certificate: for `0 ≤ δ ≤ 1`,
`0 ≤ D₄(δ) < log (127/100)` and `A₄(δ) > log (200/127)`. -/
theorem sharp_four_size_entropy_certificate (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    (0 ≤ entropyLoss4 delta ∧ entropyLoss4 delta < Real.log (127 / 100)) ∧
      Real.log (200 / 127) < phaseGain4 delta := by
  obtain ⟨v, h4, -, hplus, hv⟩ := sharp_core_at_delta delta hdelta
  have L1 := log_200_div_127_eq
  unfold entropyLoss4 phaseGain4
  rw [h4]
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- **Sharper uniform bound for the five-size phase gain.**  For every
`0 ≤ δ ≤ 1`, `A₅(δ) > log (2605/1651) = log (200/127) + log (521/520)`
(`≈ 0.45605`). -/
theorem log_2605_div_1651_lt_phaseGain5 (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (2605 / 1651) < phaseGain5 delta := by
  obtain ⟨v, -, h5, hplus, -⟩ := sharp_core_at_delta delta hdelta
  have L1 := log_200_div_127_eq
  have L2 := log_2605_div_1651_eq
  unfold phaseGain5
  linarith

/-- The new constant improves the manuscript's `γ₅ = log (8750/6681)`. -/
theorem gamma5_lt_log_2605_div_1651 : gamma5 < Real.log (2605 / 1651) := by
  unfold gamma5
  exact Real.log_lt_log (by norm_num) (by norm_num)

end

end FiveSizePhaseGainSharp

end Erdos625

#print axioms Erdos625.FiveSizePhaseGainSharp.sharp_tilt_corridor
#print axioms Erdos625.FiveSizePhaseGainSharp.sharp_four_size_partition_ratio_for_delta
#print axioms Erdos625.FiveSizePhaseGainSharp.sharp_four_size_entropy_certificate
#print axioms Erdos625.FiveSizePhaseGainSharp.log_2605_div_1651_lt_phaseGain5
#print axioms Erdos625.FiveSizePhaseGainSharp.gamma5_lt_log_2605_div_1651
