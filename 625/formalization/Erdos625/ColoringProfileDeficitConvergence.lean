import Erdos625.ColoringProfileDeficitScoreBounds

/-!
# Fixed-deficit convergence of the factorial correction

This module proves that the exact descending-factorial correction in the
deficit-coordinate score vanishes when the deficit is fixed and the ambient
class size tends to infinity.  Values below the finite threshold needed for
the product rewrite are discarded by eventual equality at `Filter.atTop`.
-/

open Filter
open scoped Topology

namespace Erdos625

/-- For every fixed deficit, the logarithmic descending-factorial correction
vanishes as the ambient class size grows. -/
theorem tendsto_log_descFactorial_sub_mul_log (d : ℕ) :
    Tendsto
      (fun a : ℕ ↦
        Real.log (a.descFactorial d : ℝ) -
          (d : ℝ) * Real.log (a : ℝ))
      atTop (𝓝 0) := by
  have h_log_prod :
      ∀ a ≥ d,
        Real.log (Nat.descFactorial a d) =
          ∑ i ∈ Finset.range d, Real.log (a - i) := by
    intro a ha
    rw [← Real.log_prod] <;>
      norm_cast <;>
      simp +decide [Nat.descFactorial_eq_prod_range]
    · exact congr_arg Real.log <|
        Finset.prod_congr rfl fun x hx => by
          rw [Nat.cast_sub (by linarith [Finset.mem_range.mp hx])]
    · grind
  have h_log_diff :
      ∀ a ≥ d + 1,
        ∑ i ∈ Finset.range d, (Real.log (a - i) - Real.log a) =
          ∑ i ∈ Finset.range d, Real.log (1 - i / (a : ℝ)) := by
    intro a ha
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [one_sub_div (by
      norm_cast
      linarith [Finset.mem_range.mp hi])]
    rw [Real.log_div] <;>
      norm_num <;>
      linarith [Finset.mem_range.mp hi,
        show (a : ℝ) ≥ i + 1 by
          norm_cast
          linarith [Finset.mem_range.mp hi]]
  have h_log_zero :
      Tendsto
        (fun a : ℕ => ∑ i ∈ Finset.range d, Real.log (1 - i / (a : ℝ)))
        atTop (nhds 0) := by
    exact le_trans
      (tendsto_finsetSum _ fun i _ =>
        Tendsto.log
          (tendsto_const_nhds.sub <|
            tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
          (by norm_num))
      (by norm_num)
  exact h_log_zero.congr' (by
    filter_upwards [eventually_ge_atTop (d + 1)] with a ha
    rw [← h_log_diff a ha, Finset.sum_sub_distrib,
      h_log_prod a (by linarith)]
    simp +decide)

end Erdos625
