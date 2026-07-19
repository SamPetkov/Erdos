import Erdos625.Section8NearSkeletonExpansion

/-!
# Section VIII: uniform near-skeleton product bound

The exact product formula sums all distinguishable near-deficit choices.
This module gives its first quantitative consequence: if every one-cell
deficit tail is at most `eps` and there are at most `K` cells, then the full
choice sum is at most `(1 + eps) ^ K`.

This is the finite product step used between the per-cell estimate in (8.25)
and the later asymptotic substitution.  It neither identifies distinguishable
choices with physical unlabelled skeletons nor proves that asymptotic bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- A uniform finite bound for the exact distinguishable near-skeleton
expansion.  The assumptions are the literal per-cell weighted-sum bound and
the literal cardinality bound; no probabilistic or asymptotic premise is
introduced. -/
theorem sum_nearSkeletonChoiceWeight_le_one_add_pow
    {Cell Deficit : Type*} [Fintype Cell] [Fintype Deficit]
    [DecidableEq Deficit] (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal) (eps : ENNReal) (K : Nat)
    (hcell : ∀ c, (∑ e ∈ allowed c, weight c e) ≤ eps)
    (hcard : Fintype.card Cell ≤ K) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤ (1 + eps) ^ K := by
  rw [sum_nearSkeletonChoiceWeight_eq_product]
  calc
    (∏ c, (1 + ∑ e ∈ allowed c, weight c e)) ≤ ∏ _ : Cell, (1 + eps) := by
      apply Finset.prod_le_prod
      · intro c _
        exact bot_le
      · intro c _
        exact add_le_add_right (hcell c) 1
    _ = (1 + eps) ^ Fintype.card Cell := by simp
    _ ≤ (1 + eps) ^ K := pow_le_pow_right₀ (by simp) hcard

#print axioms sum_nearSkeletonChoiceWeight_le_one_add_pow

end

end Erdos625
