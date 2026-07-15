import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Analytic attachment bridges for Section IX

This module contains two asymptotic consequences of the explicit finite
estimates in Section IX.  The first converts the large-residual profile bounds
into eventual smallness of the traversal parameter.  The second combines the
large- and small-residual attachment estimates into one deterministic error
sequence tending to zero.  Neither theorem proves the upstream finite
probability, cycle, or row/column estimates supplied in its hypotheses.
-/

namespace Erdos625

open Filter
open scoped Topology

/-- The large-residual inequalities force `C U^3 / m₀` below the fixed
geometric-series threshold `1/3`, uniformly over all admissible `U` and `m₀`.
-/
theorem eventually_tau_lt_one_third
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (U m₀ : ℕ),
        0 < m₀ →
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m₀ : ℝ) →
        (U : ℝ) ≤ 4 * (Real.log (n : ℝ) / Real.log 2) →
        C * (U : ℝ) ^ 3 / (m₀ : ℝ) < (1 : ℝ) / 3 := by
  have h_bound : ∀ᶠ n : ℕ in atTop,
      ∀ (U m₀ : ℕ),
        0 < m₀ →
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m₀ : ℝ) →
        (U : ℝ) ≤ 4 * (Real.log (n : ℝ) / Real.log 2) →
        C * (U : ℝ) ^ 3 / (m₀ : ℝ) ≤
          (64 * C / Real.log 2 ^ 3) *
            (Real.log (n : ℝ) ^ 9 / (n : ℝ)) := by
    refine Filter.eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
    intro U m₀ hm₀ hmass hU
    have hUcube :
        (U : ℝ) ^ 3 ≤
          (4 * (Real.log (n : ℝ) / Real.log 2)) ^ 3 := by
      gcongr
    have hinv :
        (1 : ℝ) / (m₀ : ℝ) ≤
          Real.log (n : ℝ) ^ 6 / (n : ℝ) := by
      simpa using inv_anti₀
        (by
          exact div_pos (by positivity)
            (pow_pos (Real.log_pos (by norm_cast)) _))
        hmass
    have hraw :
        C * (U : ℝ) ^ 3 / (m₀ : ℝ) ≤
          C * (4 * (Real.log (n : ℝ) / Real.log 2)) ^ 3 *
            Real.log (n : ℝ) ^ 6 / (n : ℝ) := by
      calc
        C * (U : ℝ) ^ 3 / (m₀ : ℝ) =
            C * ((U : ℝ) ^ 3 * ((1 : ℝ) / (m₀ : ℝ))) := by ring
        _ ≤ C *
            ((4 * (Real.log (n : ℝ) / Real.log 2)) ^ 3 *
              (Real.log (n : ℝ) ^ 6 / (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hUcube hinv (by positivity) (by positivity)) hC
        _ = C * (4 * (Real.log (n : ℝ) / Real.log 2)) ^ 3 *
              Real.log (n : ℝ) ^ 6 / (n : ℝ) := by ring
    have hsimplify :
        C * (4 * (Real.log (n : ℝ) / Real.log 2)) ^ 3 *
            Real.log (n : ℝ) ^ 6 / (n : ℝ) ≤
          (64 * C / Real.log 2 ^ 3) *
            (Real.log (n : ℝ) ^ 9 / (n : ℝ)) := by
      ring_nf
      norm_num
    exact hraw.trans hsimplify
  have h_limit :
      Tendsto
        (fun n : ℕ => Real.log (n : ℝ) ^ 9 / (n : ℝ))
        atTop (nhds 0) := by
    suffices h_log :
        Tendsto (fun y : ℝ => y ^ 9 / Real.exp y) atTop (nhds 0) by
      have hcomp := h_log.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact hcomp.congr' (by
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        simp +decide [Real.exp_log (Nat.cast_pos.mpr hn)])
    simpa only [Real.exp_neg, div_eq_mul_inv] using
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9
  have hscaled := h_limit.const_mul (64 * C / Real.log 2 ^ 3)
  filter_upwards
    [hscaled.eventually
      (gt_mem_nhds <| show
        64 * C / Real.log 2 ^ 3 * 0 < (1 : ℝ) / 3 by norm_num),
      h_bound] with n hn hmajorant
  exact fun U m₀ hm₀ hmass hU =>
    lt_of_le_of_lt (hmajorant U m₀ hm₀ hmass hU) hn

/-- The bounds `exp(C log(n)^8)` and `exp(C n/log(n)^5)` are uniformly
`exp(o(n/log(n)^4))`, even when the applicable residual regime varies with
the finite index. -/
theorem exists_uniform_twoRegime_error
    (S : ℕ → Type*)
    (attachment : ∀ n, S n → ℝ)
    (m₀ : ∀ n, S n → ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hlarge : ∀ᶠ n : ℕ in atTop,
      ∀ s : S n,
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m₀ n s : ℝ) →
        attachment n s ≤ Real.exp (C * Real.log (n : ℝ) ^ 8))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      ∀ s : S n,
        (m₀ n s : ℝ) < (n : ℝ) / Real.log (n : ℝ) ^ 6 →
        attachment n s ≤
          Real.exp (C * (n : ℝ) / Real.log (n : ℝ) ^ 5)) :
    ∃ εAtt : ℕ → ℝ,
      Tendsto εAtt atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop,
          0 ≤ εAtt n ∧
            ∀ s : S n,
              attachment n s ≤
                Real.exp
                  (εAtt n * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  refine ⟨fun n =>
    C * (Real.log (n : ℝ) ^ 12 / (n : ℝ) +
      1 / Real.log (n : ℝ)), ?_, ?_⟩ <;>
    norm_num at *
  · have h_log_div_n :
        Tendsto
          (fun n : ℕ => Real.log (n : ℝ) ^ 12 / (n : ℝ))
          atTop (nhds 0) := by
      suffices h_log :
          Tendsto (fun y : ℝ => y ^ 12 / Real.exp y) atTop (nhds 0) by
        have hcomp := h_log.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        exact hcomp.congr' (by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn
          simp +decide [Real.exp_log (Nat.cast_pos.mpr hn)])
      simpa only [Real.exp_neg, div_eq_mul_inv] using
        Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12
    simpa using tendsto_const_nhds.mul
      (h_log_div_n.add
        (tendsto_inv_atTop_zero.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)))
  · obtain ⟨a₁, ha₁⟩ := hlarge
    obtain ⟨a₂, ha₂⟩ := hsmall
    use Nat.max (Nat.max a₁ a₂) 3
    intro b hb
    refine ⟨?_, ?_⟩
    · exact mul_nonneg hC
        (add_nonneg
          (div_nonneg
            (pow_nonneg (Real.log_natCast_nonneg _) _)
            (Nat.cast_nonneg _))
          (inv_nonneg.mpr (Real.log_natCast_nonneg _)))
    · intro s
      by_cases hmass :
          (m₀ b s : ℝ) <
            (b : ℝ) / Real.log (b : ℝ) ^ 6 <;>
        simp_all +decide [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      · refine (ha₂ b hb.2.1 s hmass).trans (Real.exp_le_exp.mpr ?_)
        gcongr
        ring_nf
        exact le_add_of_nonneg_left (by positivity)
      · refine (ha₁ b hb.1 s hmass).trans (Real.exp_le_exp.mpr ?_)
        by_cases hbzero : b = 0 <;>
          simp_all +decide [mul_add, add_mul, mul_assoc]
        exact le_add_of_le_of_nonneg
          (mul_le_mul_of_nonneg_left
            (by
              rw [← div_eq_mul_inv]
              rw [le_div_iff₀
                (by
                  exact pow_pos
                    (Real.log_pos
                      (Nat.one_lt_cast.mpr (by linarith))) _) ]
              nlinarith)
            hC)
          (by positivity)

#print axioms eventually_tau_lt_one_third
#print axioms exists_uniform_twoRegime_error

end Erdos625
