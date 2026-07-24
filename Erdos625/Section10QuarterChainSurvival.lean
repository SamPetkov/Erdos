import Erdos625.Section10QuarterUnionDecay
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Section X: shifted-potential survival leaf

This module records the deterministic asymptotic inequality needed by the
finite quarter-dense clique-chain theorem when its initial set has the chosen
cube-root scale.  It is deliberately only an arithmetic survival leaf: it
contains no random-graph, density-event, clique-to-independent-set, greedy,
or probability conclusion.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The deterministic starting size used for the complement-neighbour chain. -/
def quarterChainStart (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊

/-- The requested integer number of quarter-neighbourhood steps. -/
def quarterChainSteps (n : ℕ) : ℕ :=
  ⌊Real.log (n : ℝ) / (13 * Real.log 4)⌋₊

/-- The eventual rounding-safe shifted-potential survival inequality for the
chosen cutoff, chain start, and number of steps. -/
theorem quarterChain_shifted_survival_eventually :
    ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ, j < quarterChainSteps n →
        (quarterDensityCutoff n : ℝ) ≤
          (4 : ℝ)⁻¹ ^ j * ((quarterChainStart n : ℝ) + 1 / 3) - 1 / 3 := by
  suffices h_bound : ∀ᶠ (n : ℕ) in atTop, ∀ j < quarterChainSteps n,
      (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤
        (1 / 4 : ℝ) ^ j * ((n : ℝ) ^ (1 / 3 : ℝ) + 1 / 3) - 1 / 3 by
    refine' h_bound.mono fun n hn j hj => le_trans _ (le_trans (hn j hj) _) <;>
      norm_num [quarterDensityCutoff, quarterChainStart]
    · exact le_of_lt <| Nat.ceil_lt_add_one <| by positivity
    · exact Nat.le_ceil _
  suffices h_bound : ∀ᶠ (n : ℕ) in atTop, ∀ j < quarterChainSteps n,
      (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤
        (1 / 4 : ℝ) ^ (Real.log n / (13 * Real.log 4)) *
          ((n : ℝ) ^ (1 / 3 : ℝ) + 1 / 3) - 1 / 3 by
    refine h_bound.mono fun n hn j hj => le_trans (hn j hj) ?_
    gcongr
    exact le_trans
      (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (show Real.log n / (13 * Real.log 4) ≥ ↑j from
          (Nat.cast_le.mpr hj.le).trans (Nat.floor_le (by positivity))))
      (by norm_num)
  suffices h_exp : ∀ᶠ (n : ℕ) in atTop,
      (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤
        (n : ℝ) ^ (-1 / 13 : ℝ) * ((n : ℝ) ^ (1 / 3 : ℝ) + 1 / 3) - 1 / 3 by
    filter_upwards [h_exp, Filter.eventually_gt_atTop 0] with n hn hn' j hj
    refine le_trans hn ?_
    norm_num [Real.rpow_def_of_pos]
    ring_nf
    norm_num [hn'.ne']
    norm_num [Real.rpow_def_of_pos, hn']
    ring_nf
    norm_num [Real.log_div]
    ring_nf
    norm_num
  suffices h_simp : ∀ᶠ (n : ℕ) in atTop,
      (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤
        (n : ℝ) ^ (10 / 39 : ℝ) + (1 / 3) * (n : ℝ) ^ (-1 / 13 : ℝ) - 1 / 3 by
    filter_upwards [h_simp, Filter.eventually_gt_atTop 0] with n hn hn' using
      hn.trans_eq (by
        rw [mul_add, ← Real.rpow_add (by positivity)]
        norm_num
        ring)
  have h_exp : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ (10 / 39 : ℝ) - (n : ℝ) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop := by
    suffices h_factor : Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) *
          ((n : ℝ) ^ (10 / 39 - 1 / 4 : ℝ) - 1))
        Filter.atTop Filter.atTop by
      refine h_factor.congr' (by
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        rw [mul_sub, ← Real.rpow_add (by positivity)]
        ring)
    exact Filter.Tendsto.atTop_mul_atTop₀
      ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
      (Filter.tendsto_atTop_add_const_right _ _
        ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop))
  filter_upwards [h_exp.eventually_gt_atTop 2, Filter.eventually_gt_atTop 0]
    with n hn hn' using by
      linarith [(show (n : ℝ) ^ (-1 / 13 : ℝ) ≥ 0 by positivity)]

#print axioms quarterChain_shifted_survival_eventually

end

end Erdos625
