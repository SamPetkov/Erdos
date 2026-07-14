import Mathlib

/-!
# Series convergence tools

This module records two small analytic interfaces used when passing from
finite deficit profiles to their limiting natural-index series.

* `tendsto_tsum_of_norm_le_summable` is a real-valued Tannery/dominated-
  convergence wrapper with a single summable majorant.
* `tsum_eq_sum_range_of_eq_zero` rewrites a natural-index `tsum` whose terms
  vanish at and beyond a cutoff as the corresponding finite range sum.

Neither theorem establishes a profile-specific majorant, pointwise limit, or
optimizer bound; those remain separate proof obligations.
-/

namespace Erdos625

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Dominated convergence for real series indexed by the natural numbers. -/
theorem tendsto_tsum_of_norm_le_summable
    {f : ℕ → ℕ → ℝ} {F g : ℕ → ℝ}
    (hg : Summable g)
    (hdom : ∀ n d, ‖f n d‖ ≤ g d)
    (hpoint : ∀ d, Tendsto (fun n ↦ f n d) atTop (nhds (F d))) :
    Tendsto (fun n ↦ ∑' d : ℕ, f n d) atTop
      (nhds (∑' d : ℕ, F d)) := by
  exact tendsto_tsum_of_dominated_convergence hg hpoint
    (Filter.Eventually.of_forall fun n d ↦ hdom n d)

/-- A natural-index real series supported below `N` is exactly its finite
range sum, without any separate summability assumption. -/
theorem tsum_eq_sum_range_of_eq_zero
    (f : ℕ → ℝ) (N : ℕ) (hzero : ∀ d, N ≤ d → f d = 0) :
    (∑' d : ℕ, f d) = ∑ d ∈ Finset.range N, f d := by
  rw [tsum_eq_sum]
  aesop

end

end Erdos625
