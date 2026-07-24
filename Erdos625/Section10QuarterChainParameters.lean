import Erdos625.Section10QuarterChainSurvival

/-!
# Section X: quarter-chain parameter facts

This module records the elementary eventual comparisons among the concrete
cutoff, starting size, and step count used by the quarter-neighbourhood chain.
It contains no graph-theoretic or probabilistic assertion.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- Eventually, the quarter-density cutoff is no larger than the chosen
cube-root starting size. -/
theorem quarterDensityCutoff_le_quarterChainStart_eventually :
    ∀ᶠ n : ℕ in atTop, quarterDensityCutoff n ≤ quarterChainStart n := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [quarterDensityCutoff, quarterChainStart]
  exact Nat.ceil_mono
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))

/-- Eventually, the quarter-density cutoff is positive. -/
theorem one_le_quarterDensityCutoff_eventually :
    ∀ᶠ n : ℕ in atTop, 1 ≤ quarterDensityCutoff n := by
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [quarterDensityCutoff, Nat.one_le_ceil_iff]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

/-- The concrete number of quarter-neighbourhood steps diverges. -/
theorem quarterChainSteps_tendsto_atTop :
    Tendsto quarterChainSteps atTop atTop := by
  unfold quarterChainSteps
  exact tendsto_nat_floor_atTop.comp
    (Tendsto.atTop_div_const (by positivity)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/-- Eventually, at least one quarter-neighbourhood step is requested. -/
theorem one_le_quarterChainSteps_eventually :
    ∀ᶠ n : ℕ in atTop, 1 ≤ quarterChainSteps n :=
  quarterChainSteps_tendsto_atTop.eventually_ge_atTop 1

/-- The floor in the concrete step count still leaves an eventual
`1 / (14 * log 4)` logarithmic lower bound. -/
theorem quarterChainSteps_real_lower_bound_eventually :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / (14 * Real.log 4) ≤ (quarterChainSteps n : ℝ) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : 0 < (1 / (182 * Real.log 4) : ℝ) := by
    positivity
  have hmargin :
      Tendsto
        (fun n : ℕ => Real.log (n : ℝ) * (1 / (182 * Real.log 4)) - 1)
        atTop atTop := by
    simpa only [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (hlog.atTop_mul_const hc)
  filter_upwards [hmargin.eventually_ge_atTop 0] with n hn
  have hlogFour : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hidentity :
      Real.log (n : ℝ) / (13 * Real.log 4) - 1 -
          Real.log (n : ℝ) / (14 * Real.log 4) =
        Real.log (n : ℝ) * (1 / (182 * Real.log 4)) - 1 := by
    field_simp [hlogFour]
    ring
  have hgap :
      Real.log (n : ℝ) / (14 * Real.log 4) ≤
        Real.log (n : ℝ) / (13 * Real.log 4) - 1 := by
    have hnonneg :
        0 ≤ Real.log (n : ℝ) / (13 * Real.log 4) - 1 -
          Real.log (n : ℝ) / (14 * Real.log 4) := by
      rw [hidentity]
      exact hn
    linarith
  calc
    Real.log (n : ℝ) / (14 * Real.log 4) ≤
        Real.log (n : ℝ) / (13 * Real.log 4) - 1 := hgap
    _ ≤ (⌊Real.log (n : ℝ) / (13 * Real.log 4)⌋₊ : ℝ) :=
      (Nat.sub_one_lt_floor _).le
    _ = (quarterChainSteps n : ℝ) := by
      rfl

#print axioms quarterDensityCutoff_le_quarterChainStart_eventually
#print axioms one_le_quarterDensityCutoff_eventually
#print axioms quarterChainSteps_tendsto_atTop
#print axioms one_le_quarterChainSteps_eventually
#print axioms quarterChainSteps_real_lower_bound_eventually

end

end Erdos625
