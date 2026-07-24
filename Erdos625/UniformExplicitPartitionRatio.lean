import Erdos625.FourGaussianTiltCorridor
import Erdos625.ExtendedGaussianProfile
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform explicit four-size partition-ratio certificate

This file ports the audited numerical core of manuscript Lemma 5.1 into the
repository's existing analytic infrastructure.  It reuses `q`,
`fourGaussianScore`, `ProfileEntropyS4.partition`, the extended-Gaussian
partition, and the already checked variable-target tilt corridor.  In
particular, it introduces no duplicate exponential-family definitions and
does not repeat the corridor proof.

The conclusion closes only the strict numerical partition-ratio input
`extended/four < 153/100`, uniformly over the full target interval.  It does
not by itself prove the remaining asymptotic, optimization, or probabilistic
claims of Lemma 5.1.
-/

namespace Erdos625

open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

private lemma extendedGaussian_ratio_high_corridor (lambda : Real)
    (hl : 5 * q / 2 ≤ lambda) (hu : lambda ≤ 9 * q / 2) :
    extendedGaussianPartition q lambda /
        ProfileEntropyS4.partition fourGaussianScore lambda <
      (153 / 100 : Real) := by
  suffices h_suff :
      (extendedGaussianExceptionalAtom q lambda +
          (∑ d ∈ Finset.range 6, extendedGaussianNaturalTerm q lambda d) +
          (4 / 3) * extendedGaussianNaturalTerm q lambda 6) /
        ProfileEntropyS4.partition fourGaussianScore lambda < 153 / 100 by
    have h_tail :
        ∑' d : ℕ, extendedGaussianNaturalTerm q lambda d ≤
          (∑ d ∈ Finset.range 6, extendedGaussianNaturalTerm q lambda d) +
            (4 / 3) * extendedGaussianNaturalTerm q lambda 6 := by
      have h_tail : ∀ d ≥ 6,
          extendedGaussianNaturalTerm q lambda (d + 1) ≤
            (1 / 4) * extendedGaussianNaturalTerm q lambda d := by
        intros d hd
        have h_exp :
            Real.exp (lambda - q / 2 * (2 * d + 1)) ≤ 1 / 4 := by
          rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_div] <;>
            norm_num
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
          nlinarith [show (d : ℝ) ≥ 6 by norm_cast,
            show q = Real.log 2 by rfl, Real.log_pos one_lt_two]
        calc
          extendedGaussianNaturalTerm q lambda (d + 1) =
              Real.exp (lambda - q / 2 * (2 * d + 1)) *
                extendedGaussianNaturalTerm q lambda d := by
            unfold extendedGaussianNaturalTerm
            rw [← Real.exp_add]
            push_cast
            ring
          _ ≤ (1 / 4) * extendedGaussianNaturalTerm q lambda d :=
            mul_le_mul_of_nonneg_right h_exp
              (Real.exp_nonneg (lambda * d - q / 2 * d ^ 2))
      have h_tail_sum :
          ∑' d : ℕ, extendedGaussianNaturalTerm q lambda (d + 6) ≤
            (4 / 3) * extendedGaussianNaturalTerm q lambda 6 := by
        have h_tail_sum : ∀ n : ℕ,
            extendedGaussianNaturalTerm q lambda (n + 6) ≤
              (1 / 4) ^ n * extendedGaussianNaturalTerm q lambda 6 := by
          intro n
          induction n <;> simp_all +decide [pow_succ', mul_assoc]
          exact le_trans (h_tail _ (by linarith))
            (mul_le_mul_of_nonneg_left ‹_› (by norm_num))
        refine le_trans (Summable.tsum_le_tsum h_tail_sum ?_ ?_) ?_
        · exact Summable.of_nonneg_of_le (fun n ↦ Real.exp_nonneg _)
            h_tail_sum
            (Summable.mul_right _ <|
              summable_geometric_of_lt_one (by norm_num) (by norm_num))
        · exact Summable.mul_right _
            (summable_geometric_of_lt_one (by norm_num) (by norm_num))
        · rw [tsum_mul_right, tsum_geometric_of_lt_one] <;> norm_num
      have h_summable : Summable (extendedGaussianNaturalTerm q lambda) := by
        refine summable_of_ratio_norm_eventually_le (r := (1 / 4 : ℝ)) (by norm_num) ?_
        filter_upwards [Filter.eventually_ge_atTop (6 : ℕ)] with n hn
        show ‖extendedGaussianNaturalTerm q lambda (n + 1)‖ ≤
          (1 / 4 : ℝ) * ‖extendedGaussianNaturalTerm q lambda n‖
        unfold extendedGaussianNaturalTerm
        rw [Real.norm_of_nonneg (Real.exp_nonneg _),
          Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact h_tail n hn
      convert add_le_add_left h_tail_sum
          (∑ d ∈ Finset.range 6, extendedGaussianNaturalTerm q lambda d) using 1
      · rw [← h_summable.sum_add_tsum_nat_add]
        exact add_comm _ _
      · ring
    exact lt_of_le_of_lt
      (by
        unfold extendedGaussianPartition
        exact div_le_div_of_nonneg_right (by linarith)
          (ProfileEntropyS4.partition_pos fourGaussianScore lambda).le)
      h_suff
  unfold extendedGaussianExceptionalAtom extendedGaussianNaturalTerm
    ProfileEntropyS4.partition ProfileEntropyS4.unnormalized
    fourGaussianScore ProfileEntropyS4.support
  norm_num [Finset.sum_range_succ, Fin.sum_univ_four]
  rw [div_lt_iff₀ (by positivity)]
  unfold q at *
  ring_nf at *
  norm_num [Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_mul,
    Real.exp_log] at *
  rw [show (2 : ℝ) ^ (9 / 2 : ℝ) =
          2 ^ (4 : ℝ) * 2 ^ (1 / 2 : ℝ) by
        rw [← Real.rpow_add] <;> norm_num,
      show (2 : ℝ) ^ (25 / 2 : ℝ) =
          2 ^ (12 : ℝ) * 2 ^ (1 / 2 : ℝ) by
        rw [← Real.rpow_add] <;> norm_num]
  norm_num [← Real.sqrt_eq_rpow]
  ring_nf
  norm_num
  have h_exp_bounds :
      2 ^ (5 / 2 : ℝ) ≤ Real.exp lambda ∧
        Real.exp lambda ≤ 2 ^ (9 / 2 : ℝ) := by
    norm_num [Real.rpow_def_of_pos]
    exact ⟨hl, hu⟩
  rw [show (2 : ℝ) ^ (5 / 2 : ℝ) =
          2 ^ (2 : ℝ) * 2 ^ (1 / 2 : ℝ) by
        rw [← Real.rpow_add] <;> norm_num,
      show (2 : ℝ) ^ (9 / 2 : ℝ) =
          2 ^ (4 : ℝ) * 2 ^ (1 / 2 : ℝ) by
        rw [← Real.rpow_add] <;> norm_num] at h_exp_bounds
  norm_num [← Real.sqrt_eq_rpow] at *
  field_simp
  nlinarith [pow_pos (Real.exp_pos lambda) 3,
    pow_pos (Real.exp_pos lambda) 4, pow_pos (Real.exp_pos lambda) 5,
    pow_pos (Real.exp_pos lambda) 6,
    mul_le_mul_of_nonneg_left h_exp_bounds.1 (Real.sqrt_nonneg 2),
    mul_le_mul_of_nonneg_left h_exp_bounds.2 (Real.sqrt_nonneg 2),
    Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]

private lemma extendedGaussian_ratio_low_corridor (lambda : Real)
    (hl : 2 * q ≤ lambda) (hu : lambda ≤ 5 * q / 2) :
    extendedGaussianPartition q lambda /
        ProfileEntropyS4.partition fourGaussianScore lambda <
      (153 / 100 : Real) := by
  set x := Real.exp lambda
  have hx_bounds : 4 ≤ x ∧ x ≤ 4 * Real.sqrt 2 := by
    constructor
    · rw [show (4 : ℝ) = Real.exp (2 * Real.log 2) by
          rw [mul_comm, Real.exp_mul, Real.exp_log] <;> norm_num]
      exact Real.exp_le_exp.mpr (by linarith! [show q = Real.log 2 from rfl])
    · rw [← Real.log_le_log_iff (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_exp,
        Real.log_sqrt] <;> norm_num
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      linarith! [Real.log_pos one_lt_two]
  have h_partition_bounds :
      extendedGaussianPartition q lambda ≤
          x⁻¹ + (∑ d ∈ Finset.range 6,
            x ^ d * (2 : ℝ) ^ (-d ^ 2 / 2 : ℝ)) +
          x ^ 6 * (2 : ℝ) ^ (-6 ^ 2 / 2 : ℝ) /
            (1 - x / (2 ^ 6 : ℝ)) ∧
        ProfileEntropyS4.partition fourGaussianScore lambda =
          ∑ i ∈ Finset.range 4,
            x ^ (i + 2) * (2 : ℝ) ^ (-(i + 2) ^ 2 / 2 : ℝ) := by
    constructor
    · have h_partition_bounds :
          extendedGaussianPartition q lambda ≤
            x⁻¹ + (∑ d ∈ Finset.range 6,
              x ^ d * (2 : ℝ) ^ (-d ^ 2 / 2 : ℝ)) +
            (∑' d : ℕ,
              x ^ (d + 6) * (2 : ℝ) ^ (-(d + 6) ^ 2 / 2 : ℝ)) := by
        have h_partition_bounds :
            extendedGaussianPartition q lambda ≤
              x⁻¹ + (∑' d : ℕ,
                x ^ d * (2 : ℝ) ^ (-d ^ 2 / 2 : ℝ)) := by
          refine add_le_add ?_ ?_
          · rw [← Real.exp_neg]
            exact Real.exp_le_exp.mpr
              (by linarith [show 0 ≤ q by exact Real.log_nonneg one_le_two])
          · unfold extendedGaussianNaturalTerm
            norm_num [Real.rpow_def_of_pos, Real.exp_pos]
            ring_nf
            norm_num +zetaDelta at *
            norm_num [← Real.exp_nat_mul, ← Real.exp_add, mul_assoc,
              mul_comm, mul_left_comm, q]
        convert h_partition_bounds using 1
        rw [eq_comm, ← Summable.sum_add_tsum_nat_add 6]
        · norm_num [add_assoc]
        · have h_summable : Summable
              (fun d : ℕ ↦ x ^ d * (2 : ℝ) ^ (-d ^ 2 / 2 : ℝ)) := by
            have h_exp_decay : ∀ d : ℕ,
                x ^ d * (2 : ℝ) ^ (-d ^ 2 / 2 : ℝ) ≤
                  (x / 2 ^ (d / 2 : ℝ)) ^ d := by
              intro d
              rw [div_pow]
              ring_nf
              norm_num
              rw [← Real.rpow_natCast _ d, ← Real.rpow_natCast _ d,
                ← Real.rpow_mul (by positivity)]
              ring_nf
              norm_num
              rw [Real.rpow_neg (by positivity)]
            obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ d ≥ N,
                x / 2 ^ (d / 2 : ℝ) < 1 / 2 := by
              have h_exp_decay : Filter.Tendsto
                  (fun d : ℕ ↦ x / 2 ^ (d / 2 : ℝ)) Filter.atTop (nhds 0) := by
                norm_num [Real.rpow_def_of_pos]
                exact tendsto_const_nhds.div_atTop
                  (Real.tendsto_exp_atTop.comp <|
                    Filter.Tendsto.const_mul_atTop (by positivity) <|
                      tendsto_natCast_atTop_atTop.atTop_div_const
                        (by positivity))
              simpa using h_exp_decay.eventually (gt_mem_nhds <| by norm_num)
            rw [← summable_nat_add_iff N]
            exact Summable.of_nonneg_of_le (fun n ↦ by positivity)
              (fun n ↦ h_exp_decay _)
              (Summable.of_nonneg_of_le (fun n ↦ by positivity)
                (fun n ↦ pow_le_pow_left₀ (by positivity)
                  (le_of_lt (hN _ (by linarith))) _)
                (summable_geometric_two.comp_injective
                  (add_left_injective N)))
          convert h_summable using 1
      have h_term_bound : ∀ d : ℕ,
          x ^ (d + 6) * (2 : ℝ) ^ (-(d + 6) ^ 2 / 2 : ℝ) ≤
            x ^ 6 * (2 : ℝ) ^ (-6 ^ 2 / 2 : ℝ) *
              (x / (2 ^ 6 : ℝ)) ^ d := by
        intro d
        ring_nf
        norm_num [Real.rpow_add, Real.rpow_neg]
        ring_nf
        norm_num
        norm_num [Real.rpow_sub, Real.rpow_mul]
        ring_nf
        norm_num
        norm_num [pow_mul', ← Real.sqrt_eq_rpow]
        exact mul_le_of_le_one_right
          (mul_nonneg
            (mul_nonneg (pow_nonneg (by linarith) _)
              (pow_nonneg (by linarith) _))
            (by positivity))
          (inv_le_one_of_one_le₀
            (Real.le_sqrt_of_sq_le
              (mod_cast Nat.one_le_pow _ _ (by norm_num))))
      refine le_trans h_partition_bounds ?_
      gcongr
      refine le_trans (Summable.tsum_le_tsum h_term_bound ?_ ?_) ?_
      · exact Summable.of_nonneg_of_le (fun d ↦ by positivity)
          (fun d ↦ h_term_bound d)
          (Summable.mul_left _ <|
            summable_geometric_of_lt_one (by positivity) <|
              by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two])
      · exact Summable.mul_left _ <|
          summable_geometric_of_lt_one (by positivity) <|
            by
              rw [div_lt_iff₀ <| by positivity]
              nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]
      · rw [tsum_mul_left,
          tsum_geometric_of_lt_one (by positivity)
            (by norm_num; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])]
        ring_nf
        norm_num
    · unfold ProfileEntropyS4.partition ProfileEntropyS4.unnormalized
        fourGaussianScore ProfileEntropyS4.support
      rw [Finset.sum_range]
      norm_num [Real.rpow_def_of_pos, Real.exp_pos]
      ring
      norm_num +zetaDelta at *
      norm_num [← Real.exp_nat_mul, ← Real.exp_add, q]
      congr
      ext
      ring
  rw [div_lt_iff₀] <;> norm_num [Finset.sum_range_succ] at *
  · refine lt_of_le_of_lt h_partition_bounds.1 ?_
    rw [h_partition_bounds.2, add_div', div_lt_iff₀] <;>
      norm_num [Real.rpow_neg] at *
    · rw [show (9 / 2 : ℝ) = 4 + 1 / 2 by norm_num,
        show (25 / 2 : ℝ) = 12 + 1 / 2 by norm_num,
        Real.rpow_add, Real.rpow_add] <;> norm_num
      ring_nf
      norm_num at *
      rw [← Real.sqrt_eq_rpow] at *
      rw [show (Real.sqrt 2) ⁻¹ = Real.sqrt 2 / 2 by
        rw [inv_eq_one_div, Real.sqrt_div_self']] at *
      nlinarith [pow_pos (by linarith : 0 < x) 3,
        pow_pos (by linarith : 0 < x) 4,
        pow_pos (by linarith : 0 < x) 5,
        pow_pos (by linarith : 0 < x) 6,
        mul_inv_cancel₀ (by linarith : x ≠ 0),
        mul_le_mul_of_nonneg_left hx_bounds.2 (sq_nonneg (x - 4)),
        mul_le_mul_of_nonneg_left hx_bounds.2 (sq_nonneg (x ^ 2 - 16)),
        Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]
    · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · exact h_partition_bounds.2.symm ▸ by
      have := hx_bounds.1
      positivity

/-- **Uniform partition-ratio certificate (Lemma 5.1 numerical core).**

Every target in the full manuscript interval, and every tilt representing
that target under the repository's exact four-size mean, has total extended
Gaussian partition ratio strictly below `153/100`.  This is the numerical
ratio input only, not the complete statement of Lemma 5.1.
-/
theorem uniform_four_size_partition_ratio
    (target lambda : Real)
    (hTargetLower : 2 / q ≤ target)
    (hTargetUpper : target ≤ 1 + 2 / q)
    (hMean : ProfileEntropyS4.mean fourGaussianScore lambda = target) :
    extendedGaussianPartition q lambda /
        ProfileEntropyS4.partition fourGaussianScore lambda <
      (153 / 100 : Real) := by
  have hCorridor := uniform_four_size_tilt_corridor target lambda
    hTargetLower hTargetUpper hMean
  by_cases hsplit : lambda ≤ 5 * q / 2
  · exact extendedGaussian_ratio_low_corridor lambda hCorridor.1.le hsplit
  · exact extendedGaussian_ratio_high_corridor lambda
      (le_of_not_ge hsplit) hCorridor.2.le

/-- The original `delta` parameterization of the uniform ratio theorem. -/
theorem uniform_four_size_partition_ratio_for_delta
    (delta lambda : Real)
    (hDeltaLower : 0 ≤ delta)
    (hDeltaUpper : delta ≤ 1)
    (hMean : ProfileEntropyS4.mean fourGaussianScore lambda =
      1 + 2 / q - delta) :
    extendedGaussianPartition q lambda /
        ProfileEntropyS4.partition fourGaussianScore lambda <
      (153 / 100 : Real) := by
  apply uniform_four_size_partition_ratio (1 + 2 / q - delta) lambda
  · linarith
  · linarith
  · exact hMean

#print axioms uniform_four_size_partition_ratio
#print axioms uniform_four_size_partition_ratio_for_delta

end

end Erdos625
