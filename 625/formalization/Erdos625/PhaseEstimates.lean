import Erdos625.PhaseExpansion
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Quantitative estimates for the independence-number phase

This file supplies elementary analytic infrastructure for the phase expansion.
Every estimate is finite and has explicit hypotheses.  In particular, none of
the manuscript's endpoint-uniform asymptotic expansions is assumed here.
-/

namespace Erdos625

open Filter Asymptotics Finset

/-! ## A real logarithm remainder bound -/

/-- A quadratic Taylor bound for `-log (1-x)` on the interval used in the
falling-factorial expansion.  The statement is symmetric in its hypothesis,
although applications below only use `0 ≤ x`. -/
theorem abs_neg_log_one_sub_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by
  have hxLower : -(1 / 2 : ℝ) ≤ x := (abs_le.mp hx).1
  have hxUpper : x ≤ (1 / 2 : ℝ) := (abs_le.mp hx).2
  have hOneSub : 0 < 1 - x := by linarith
  have hNonneg : 0 ≤ -Real.log (1 - x) - x := by
    have h := Real.log_le_sub_one_of_pos hOneSub
    linarith
  rw [abs_of_nonneg hNonneg]
  have hLogLower := Real.one_sub_inv_le_log_of_pos hOneSub
  have hInv : (1 - x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hOneSub (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hUpper : -Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := by
    have hIdentity : (1 - x)⁻¹ - 1 - x = x ^ 2 / (1 - x) := by
      field_simp
      ring
    calc
      -Real.log (1 - x) - x ≤ (1 - x)⁻¹ - 1 - x := by linarith
      _ = x ^ 2 / (1 - x) := hIdentity
  calc
    -Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := hUpper
    _ = x ^ 2 * (1 - x)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ x ^ 2 * 2 := mul_le_mul_of_nonneg_left hInv (sq_nonneg x)
    _ = 2 * x ^ 2 := by ring

/-! ## Linear-scale control of the integer phase -/

/-- The centered scale `S = log n - log log n + C` is asymptotic to
`log n`. -/
theorem phaseS_isEquivalent_logOrder :
    phaseS ~[atTop] logOrder := by
  have hConst :
      (fun _n : ℕ ↦ phaseC) =o[atTop] (fun n : ℕ ↦ logOrder n) := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop phaseC).comp_tendsto tendsto_logOrder_atTop
  have hError :
      (fun n : ℕ ↦ -logLogOrder n + phaseC) =o[atTop]
        (fun n : ℕ ↦ logOrder n) :=
    logLogOrder_isLittleO_logOrder.neg_left.add hConst
  have hEquivalent := hError.add_isEquivalent
    (IsEquivalent.refl : (fun n : ℕ ↦ logOrder n) ~[atTop]
      (fun n : ℕ ↦ logOrder n))
  have hEq :
      (fun n : ℕ ↦ -logLogOrder n + phaseC) +
          (fun n : ℕ ↦ logOrder n) = phaseS := by
    funext n
    simp only [Pi.add_apply, phaseS]
    ring
  rw [← hEq]
  exact hEquivalent

/-- The bounded floor offset is negligible compared with `log n`. -/
theorem phaseB_isLittleO_logOrder :
    phaseB =o[atTop] logOrder := by
  have hBounded :
      phaseB =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_pos (phaseB_pos n), norm_one, one_mul]
    exact phaseB_le_one n
  have hOne :
      (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] logOrder := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_logOrder_atTop
  exact hBounded.trans_isLittleO hOne

/-- The natural phase is asymptotic to `(2 / log 2) log n`.  The floor is
handled through the bounded offset `phaseB`, rather than by an unproved
rounding heuristic. -/
theorem phaseNat_isEquivalent_scaled_logOrder :
    (fun n : ℕ ↦ (phaseNat n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ (2 / q) * logOrder n) := by
  have hScaleNe : (2 / q : ℝ) ≠ 0 := div_ne_zero (by norm_num) q_ne_zero
  have hScaled :
      (fun n : ℕ ↦ (2 / q) * phaseS n) ~[atTop]
        (fun n : ℕ ↦ (2 / q) * logOrder n) :=
    (IsEquivalent.refl : (fun _n : ℕ ↦ (2 / q : ℝ)) ~[atTop]
      (fun _n : ℕ ↦ (2 / q : ℝ))).mul phaseS_isEquivalent_logOrder
  have hOffset :
      phaseB =o[atTop] (fun n : ℕ ↦ (2 / q) * logOrder n) :=
    phaseB_isLittleO_logOrder.const_mul_right hScaleNe
  have hSum := hScaled.add_isLittleO hOffset
  apply hSum.congr'
  · filter_upwards [eventually_phaseDomain] with n hn
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
    ring
  · exact EventuallyEq.rfl

/-- In particular, `phaseNat` has the same asymptotic order as `log n`. -/
theorem phaseNat_isTheta_logOrder :
    (fun n : ℕ ↦ (phaseNat n : ℝ)) =Θ[atTop] logOrder := by
  have hTheta := phaseNat_isEquivalent_scaled_logOrder.isTheta
  exact hTheta.of_const_mul_right (div_ne_zero (by norm_num) q_ne_zero)

/-- A fixed-constant version of the preceding `Θ` statement.  The constants
`1` and `4` are deliberately coarse, but convenient in later range checks. -/
theorem eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder :
    ∀ᶠ n : ℕ in atTop,
      logOrder n ≤ (phaseNat n : ℝ) ∧
        (phaseNat n : ℝ) ≤ 4 * logOrder n := by
  have hDenom : ∀ᶠ n : ℕ in atTop, (2 / q) * logOrder n ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hlog : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    exact mul_ne_zero (div_ne_zero (by norm_num) q_ne_zero) hlog.ne'
  have hRatioOne : Tendsto
      ((fun n : ℕ ↦ (phaseNat n : ℝ)) /
        (fun n : ℕ ↦ (2 / q) * logOrder n)) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hDenom).mp phaseNat_isEquivalent_scaled_logOrder
  have hRatio : Tendsto
      (fun n : ℕ ↦ (phaseNat n : ℝ) / logOrder n) atTop (nhds (2 / q)) := by
    have hScaled := hRatioOne.const_mul (2 / q)
    convert hScaled using 1
    · funext n
      by_cases hlog : logOrder n = 0
      · simp [hlog]
      · change (phaseNat n : ℝ) / logOrder n =
            (2 / q) * ((phaseNat n : ℝ) / ((2 / q) * logOrder n))
        field_simp [q_ne_zero]
    · simp
  have hqLower : (1 / 2 : ℝ) < q := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hqUpper : q < 2 := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hLimitLower : (1 : ℝ) < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    linarith
  have hLimitUpper : 2 / q < (4 : ℝ) := by
    rw [div_lt_iff₀ q_pos]
    linarith
  have hEventuallyRatio :
      ∀ᶠ n : ℕ in atTop,
        (phaseNat n : ℝ) / logOrder n ∈ Set.Icc (1 : ℝ) 4 :=
    hRatio.eventually (Icc_mem_nhds hLimitLower hLimitUpper)
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact Real.log_pos (by exact_mod_cast hn)
  filter_upwards [hEventuallyRatio, hLogPos] with n hnRatio hnLog
  constructor
  · simpa only [one_mul] using (le_div_iff₀ hnLog).mp hnRatio.1
  · exact (div_le_iff₀ hnLog).mp hnRatio.2

/-- Since the phase is eventually at least `log n` and `log n → ∞`, its
natural-number phase eventually exceeds the fixed threshold five. -/
theorem eventually_five_lt_phaseNat :
    ∀ᶠ n : ℕ in atTop, 5 < phaseNat n := by
  have hLog : ∀ᶠ n : ℕ in atTop, (5 : ℝ) < logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_gt_atTop 5)
  filter_upwards
    [hLog, eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder]
      with n hnLog hnPhase
  exact_mod_cast (hnLog.trans_le hnPhase.1)

/-- The phase is eventually small enough that two phase-sized vertex blocks
fit inside an `n`-vertex graph. -/
theorem eventually_two_mul_phaseNat_le :
    ∀ᶠ n : ℕ in atTop, 2 * phaseNat n ≤ n := by
  have hLittleO :
      (fun n : ℕ ↦ (phaseNat n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) :=
    phaseNat_isTheta_logOrder.1.trans_isLittleO logOrder_isLittleO_natCast
  have hBound := hLittleO.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hBound] with n hn
  have hnNorm : ‖(n : ℝ)‖ = (n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  have hPhaseNorm : ‖(phaseNat n : ℝ)‖ = (phaseNat n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (phaseNat n))]
  rw [hnNorm, hPhaseNorm] at hn
  exact_mod_cast (show (2 : ℝ) * phaseNat n ≤ n by linarith)

/-! ## Exact logarithmic identities -/

/-- The logarithm of a descending factorial is the sum of the logarithms of
its positive factors. -/
theorem log_descFactorial_eq_sum {n s : ℕ} (hsn : s ≤ n) :
    Real.log (n.descFactorial s : ℝ) =
      ∑ i ∈ Finset.range s, Real.log ((n - i : ℕ) : ℝ) := by
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  rw [Real.log_prod]
  intro i hi
  have hiLt : i < s := Finset.mem_range.mp hi
  have hiN : i < n := lt_of_lt_of_le hiLt hsn
  exact_mod_cast Nat.sub_pos_of_lt hiN |>.ne'

/-- Exact normalization of the descending-factorial logarithm by `n^s`.
The hypotheses ensure every logarithm is taken at a positive real number. -/
theorem log_descFactorial_eq_main_add_sum {n s : ℕ} (hn : 0 < n) (hsn : s ≤ n) :
    Real.log (n.descFactorial s : ℝ) =
      (s : ℝ) * Real.log (n : ℝ) +
        ∑ i ∈ Finset.range s, Real.log (1 - (i : ℝ) / n) := by
  rw [log_descFactorial_eq_sum hsn]
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    ∑ i ∈ Finset.range s, Real.log ((n - i : ℕ) : ℝ) =
        ∑ i ∈ Finset.range s,
          (Real.log (n : ℝ) + Real.log (1 - (i : ℝ) / n)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiLt : i < s := Finset.mem_range.mp hi
      have hiN : i < n := lt_of_lt_of_le hiLt hsn
      have hiLe : i ≤ n := Nat.le_of_lt hiN
      have hCastSub : ((n - i : ℕ) : ℝ) = (n : ℝ) - i := by
        simpa using (Nat.cast_sub hiLe : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ))
      have hFactor : (n : ℝ) - i = (n : ℝ) * (1 - (i : ℝ) / n) := by
        field_simp
      have hSecond : 1 - (i : ℝ) / n ≠ 0 := by
        have hiReal : (i : ℝ) < n := by exact_mod_cast hiN
        have hRatio : (i : ℝ) / n < 1 := (div_lt_one hnReal).mpr hiReal
        linarith
      rw [hCastSub, hFactor, Real.log_mul hnReal.ne' hSecond]
    _ = (s : ℝ) * Real.log (n : ℝ) +
          ∑ i ∈ Finset.range s, Real.log (1 - (i : ℝ) / n) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The exact factorial decomposition of a binomial coefficient, after
taking logarithms. -/
theorem log_choose_eq_log_descFactorial_sub {n s : ℕ} (hsn : s ≤ n) :
    Real.log (n.choose s : ℝ) =
      Real.log (n.descFactorial s : ℝ) - Real.log (s.factorial : ℝ) := by
  have hChoose : (n.choose s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hsn).ne'
  have hFact : (s.factorial : ℝ) ≠ 0 := by positivity
  have hCast := congrArg (fun m : ℕ ↦ (m : ℝ))
    (Nat.descFactorial_eq_factorial_mul_choose n s)
  norm_num only [Nat.cast_mul] at hCast
  rw [hCast, Real.log_mul hFact hChoose]
  ring

/-- Exact logarithm of the first moment `mu`. -/
theorem log_mu_eq {n s : ℕ} (hsn : s ≤ n) :
    Real.log (mu n s) =
      Real.log (n.choose s : ℝ) - (s.choose 2 : ℝ) * q := by
  have hChoose : (n.choose s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hsn).ne'
  have hPow : (2 : ℝ) ^ (s.choose 2) ≠ 0 := by positivity
  rw [mu, Real.log_mul hChoose (inv_ne_zero hPow), Real.log_inv, Real.log_pow]
  simp only [q]
  ring

/-! ## A quantitative falling-factorial error -/

/-- If `2s ≤ n`, replacing each factor `n-i` in the descending factorial by
`n` and retaining the linear logarithmic correction has an explicit cubic
error.  The intentionally coarse bound avoids importing a closed formula for
the sum of squares and is uniform in both finite parameters. -/
theorem log_descFactorial_linear_error_le {n s : ℕ}
    (hn : 0 < n) (hTwo : 2 * s ≤ n) :
    |Real.log (n.descFactorial s : ℝ) -
        (s : ℝ) * Real.log (n : ℝ) +
        (s.choose 2 : ℝ) / n| ≤
      2 * (s : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  have hsn : s ≤ n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hHalf : (s : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hnReal]
    have hTwoReal : (2 : ℝ) * s ≤ n := by exact_mod_cast hTwo
    linarith
  have hSumId :
      (∑ i ∈ Finset.range s, (i : ℝ)) = (s.choose 2 : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.sum_range_id s).trans (Nat.choose_two_right s).symm
  have hSumRatio :
      (∑ i ∈ Finset.range s, (i : ℝ) / n) = (s.choose 2 : ℝ) / n := by
    rw [← Finset.sum_div, hSumId]
  have hErrorEq :
      Real.log (n.descFactorial s : ℝ) -
          (s : ℝ) * Real.log (n : ℝ) +
          (s.choose 2 : ℝ) / n =
        ∑ i ∈ Finset.range s,
          (Real.log (1 - (i : ℝ) / n) + (i : ℝ) / n) := by
    rw [log_descFactorial_eq_main_add_sum hn hsn]
    rw [Finset.sum_add_distrib, hSumRatio]
    ring
  rw [hErrorEq]
  calc
    |∑ i ∈ Finset.range s,
        (Real.log (1 - (i : ℝ) / n) + (i : ℝ) / n)| ≤
        ∑ i ∈ Finset.range s,
          |Real.log (1 - (i : ℝ) / n) + (i : ℝ) / n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range s, 2 * ((i : ℝ) / n) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hiLt : i < s := Finset.mem_range.mp hi
      have hiLe : (i : ℝ) / n ≤ (s : ℝ) / n := by
        gcongr
      have hiNonneg : 0 ≤ (i : ℝ) / n := div_nonneg (Nat.cast_nonneg i) hnReal.le
      have hiAbs : |(i : ℝ) / n| ≤ 1 / 2 := by
        rw [abs_of_nonneg hiNonneg]
        exact hiLe.trans hHalf
      have hTaylor := abs_neg_log_one_sub_sub_le hiAbs
      calc
        |Real.log (1 - (i : ℝ) / n) + (i : ℝ) / n| =
            |-(Real.log (1 - (i : ℝ) / n) + (i : ℝ) / n)| :=
          (abs_neg _).symm
        _ = |-Real.log (1 - (i : ℝ) / n) - (i : ℝ) / n| := by ring
        _ ≤ 2 * ((i : ℝ) / n) ^ 2 := hTaylor
    _ ≤ ∑ _i ∈ Finset.range s, 2 * ((s : ℝ) / n) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hiLt : i < s := Finset.mem_range.mp hi
      have hiLe : (i : ℝ) / n ≤ (s : ℝ) / n := by
        gcongr
      have hiNonneg : 0 ≤ (i : ℝ) / n := div_nonneg (Nat.cast_nonneg i) hnReal.le
      have hsNonneg : 0 ≤ (s : ℝ) / n := div_nonneg (Nat.cast_nonneg s) hnReal.le
      gcongr
    _ = 2 * (s : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-! ## Robbins' logarithmic Stirling remainder -/

/-- The standard logarithmic Stirling remainder. -/
noncomputable def stirlingLogRemainder (s : ℕ) : ℝ :=
  Real.log (s.factorial : ℝ) -
    ((s : ℝ) * Real.log (s : ℝ) - s +
      Real.log (s : ℝ) / 2 + Real.log (2 * Real.pi) / 2)

/-- A finite telescoping form of Robbins' sharp step estimate. -/
theorem log_stirlingSeq_sub_log_stirlingSeq_add_le (s k : ℕ) (hs : 0 < s) :
    Real.log (Stirling.stirlingSeq s) -
        Real.log (Stirling.stirlingSeq (s + k)) ≤
      1 / (12 * (s : ℝ)) - 1 / (12 * (s + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hStep := Stirling.log_stirlingSeq_sdiff_le (s + k)
      have hStep' :
          Real.log (Stirling.stirlingSeq (s + k)) -
              Real.log (Stirling.stirlingSeq (s + k + 1)) ≤
            1 / (12 * ((s + k : ℕ) : ℝ) * ((s + k + 1 : ℕ) : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hStep
      rw [Nat.add_succ]
      calc
        Real.log (Stirling.stirlingSeq s) -
            Real.log (Stirling.stirlingSeq (s + k + 1)) =
          (Real.log (Stirling.stirlingSeq s) -
              Real.log (Stirling.stirlingSeq (s + k))) +
            (Real.log (Stirling.stirlingSeq (s + k)) -
              Real.log (Stirling.stirlingSeq (s + k + 1))) := by ring
        _ ≤ (1 / (12 * (s : ℝ)) - 1 / (12 * (s + k : ℕ) : ℝ)) +
            1 / (12 * ((s + k : ℕ) : ℝ) * ((s + k + 1 : ℕ) : ℝ)) :=
          add_le_add ih hStep'
        _ = 1 / (12 * (s : ℝ)) -
            1 / (12 * (s + k + 1 : ℕ) : ℝ) := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          field_simp
          ring

/-- Robbins' upper bound, first in the normalization naturally supplied by
mathlib's Stirling sequence. -/
theorem log_stirlingSeq_sub_log_sqrt_pi_le {s : ℕ} (hs : 0 < s) :
    Real.log (Stirling.stirlingSeq s) - Real.log (Real.sqrt Real.pi) ≤
      1 / (12 * (s : ℝ)) := by
  have hSeq : Tendsto
      (fun k : ℕ ↦ Real.log (Stirling.stirlingSeq (s + k))) atTop
        (nhds (Real.log (Real.sqrt Real.pi))) := by
    have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (tendsto_add_atTop_nat s)).log (by positivity : Real.sqrt Real.pi ≠ 0)
    simpa only [Function.comp_apply, Function.comp_def, Nat.add_comm] using h
  have hLeft : Tendsto
      (fun k : ℕ ↦ Real.log (Stirling.stirlingSeq s) -
        Real.log (Stirling.stirlingSeq (s + k))) atTop
      (nhds (Real.log (Stirling.stirlingSeq s) - Real.log (Real.sqrt Real.pi))) :=
    tendsto_const_nhds.sub hSeq
  have hTail : Tendsto
      (fun k : ℕ ↦ 1 / (12 * (s + k : ℕ) : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)).comp
      (tendsto_add_atTop_nat s)
    convert h using 1
    · funext k
      simp only [Function.comp_apply]
      rw [Nat.add_comm]
      field_simp
  have hRight : Tendsto
      (fun k : ℕ ↦ 1 / (12 * (s : ℝ)) - 1 / (12 * (s + k : ℕ) : ℝ)) atTop
      (nhds (1 / (12 * (s : ℝ)))) := by
    simpa using tendsto_const_nhds.sub hTail
  exact le_of_tendsto_of_tendsto' hLeft hRight
    (fun k ↦ log_stirlingSeq_sub_log_stirlingSeq_add_le s k hs)

/-- The Stirling-sequence remainder is nonnegative. -/
theorem log_sqrt_pi_le_log_stirlingSeq {s : ℕ} (hs : 0 < s) :
    Real.log (Real.sqrt Real.pi) ≤ Real.log (Stirling.stirlingSeq s) := by
  exact Real.log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq hs.ne')

/-- Exact identification of the usual log-factorial remainder with the
Stirling-sequence normalization. -/
theorem stirlingLogRemainder_eq {s : ℕ} (hs : 0 < s) :
    stirlingLogRemainder s =
      Real.log (Stirling.stirlingSeq s) - Real.log (Real.sqrt Real.pi) := by
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  rw [Stirling.log_stirlingSeq_formula]
  simp only [stirlingLogRemainder]
  rw [Real.log_div (by positivity : (s : ℝ) ≠ 0) (Real.exp_ne_zero 1),
    Real.log_exp, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : (s : ℝ) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by positivity : Real.pi ≠ 0),
    Real.log_sqrt (by positivity : (0 : ℝ) ≤ Real.pi)]
  ring

/-- Robbins' two-sided, fully explicit log-factorial remainder bound. -/
theorem stirlingLogRemainder_mem_Icc {s : ℕ} (hs : 0 < s) :
    stirlingLogRemainder s ∈ Set.Icc (0 : ℝ) (1 / (12 * (s : ℝ))) := by
  rw [stirlingLogRemainder_eq hs]
  exact ⟨sub_nonneg.mpr (log_sqrt_pi_le_log_stirlingSeq hs),
    log_stirlingSeq_sub_log_sqrt_pi_le hs⟩

theorem stirlingLogRemainder_nonneg {s : ℕ} (hs : 0 < s) :
    0 ≤ stirlingLogRemainder s :=
  (stirlingLogRemainder_mem_Icc hs).1

theorem stirlingLogRemainder_le {s : ℕ} (hs : 0 < s) :
    stirlingLogRemainder s ≤ 1 / (12 * (s : ℝ)) :=
  (stirlingLogRemainder_mem_Icc hs).2

end Erdos625
