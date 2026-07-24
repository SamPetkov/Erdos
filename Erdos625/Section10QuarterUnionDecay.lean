import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Section 10: quarter-density union-bound decay

This module proves the deterministic full-sequence asymptotic used after the
fixed-set lower-quarter binomial tail in Lemma 10.1.  It does not assert the
probabilistic tail or the simultaneous graph event.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The cutoff `u₀ = ceil(n^(1/4))` from Lemma 10.1. -/
noncomputable def quarterDensityCutoff (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊

/-- For every fixed positive lower-tail constant `c`, the union-bound cost
`choose(n,u₀) * exp(-c*u₀²)` tends to zero along the full natural sequence. -/
theorem quarterDensity_unionBound_tendsto_zero
    (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (Nat.choose n (quarterDensityCutoff n) : ℝ) *
          Real.exp (-c * (quarterDensityCutoff n : ℝ) ^ 2))
      atTop (nhds 0) := by
  set u₀ := fun n : ℕ => ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊
  have hu₀_inf : Filter.Tendsto u₀ Filter.atTop Filter.atTop := by
    exact tendsto_nat_ceil_atTop.comp
      ((tendsto_rpow_atTop (by norm_num)).comp
        tendsto_natCast_atTop_atTop)
  have h_log_div_u₀_zero :
      Filter.Tendsto (fun n : ℕ => Real.log n / u₀ n)
        Filter.atTop (nhds 0) := by
    have h_log_div_n_root :
        Filter.Tendsto
          (fun n : ℕ => Real.log n / (n : ℝ) ^ (1 / 4 : ℝ))
          Filter.atTop (nhds 0) := by
      suffices h_log :
          Filter.Tendsto (fun y : ℝ => y / Real.exp (y / 4))
            Filter.atTop (nhds 0) by
        have h := h_log.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        refine h.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        rw [Function.comp_apply, Function.comp_apply,
          Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
        ring_nf
      suffices h_z :
          Filter.Tendsto (fun z : ℝ => 4 * z / Real.exp z)
            Filter.atTop (nhds 0) by
        convert h_z.comp
          (Filter.tendsto_id.atTop_mul_const
            (by norm_num : 0 < (4 : ℝ)⁻¹)) using 2
        all_goals norm_num
        all_goals ring_nf
      simpa only [pow_one, Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_zero] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 4
    refine' squeeze_zero_norm' _ h_log_div_n_root
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    exact Nat.le_ceil _
  have h_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.exp (u₀ n * Real.log n - c * u₀ n ^ 2))
        Filter.atTop (nhds 0) := by
    have h_tendsto_zero :
        Filter.Tendsto
          (fun n : ℕ => u₀ n * (Real.log n - c * u₀ n))
          Filter.atTop Filter.atBot := by
      have h_tendsto_zero :
          Filter.Tendsto
            (fun n : ℕ => Real.log n - c * u₀ n)
            Filter.atTop Filter.atBot := by
        have h_tendsto_zero :
            Filter.Tendsto
              (fun n : ℕ => (Real.log n / u₀ n - c) * u₀ n)
              Filter.atTop Filter.atBot := by
          apply Filter.Tendsto.neg_mul_atTop
          exacts
            [show (-c : ℝ) < 0 by linarith,
              by simpa using h_log_div_u₀_zero.sub_const c,
              tendsto_natCast_atTop_atTop.comp hu₀_inf]
        refine h_tendsto_zero.congr' ?_
        filter_upwards [hu₀_inf.eventually_ne_atTop 0] with n hn
        rw [sub_mul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]
      exact Filter.Tendsto.atTop_mul_atBot₀
        (tendsto_natCast_atTop_atTop.comp hu₀_inf) h_tendsto_zero
    exact Real.tendsto_exp_atBot.comp <|
      h_tendsto_zero.congr fun n => by ring
  refine' squeeze_zero_norm' _ h_tendsto_zero
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have h_bound :
      (Nat.choose n (u₀ n) : ℝ) ≤
        Real.exp (u₀ n * Real.log n) := by
    have h_bound : (Nat.choose n (u₀ n) : ℝ) ≤ n ^ (u₀ n) := by
      exact_mod_cast Nat.le_trans (Nat.choose_le_pow _ _) (by norm_num)
    exact h_bound.trans_eq
      (by rw [Real.exp_nat_mul, Real.exp_log (by positivity)])
  rw [Real.norm_of_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))]
  calc
    (Nat.choose n (u₀ n) : ℝ) * Real.exp (-c * (u₀ n : ℝ) ^ 2) ≤
        Real.exp ((u₀ n : ℝ) * Real.log (n : ℝ)) *
          Real.exp (-c * (u₀ n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right h_bound (Real.exp_nonneg _)
    _ = Real.exp
        ((u₀ n : ℝ) * Real.log (n : ℝ) - c * (u₀ n : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

#print axioms quarterDensity_unionBound_tendsto_zero

end

end Erdos625
