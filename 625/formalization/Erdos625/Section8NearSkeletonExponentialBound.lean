import Erdos625.Section8NearSkeletonUniformProductBound
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Section VIII: exponential form of the near-skeleton product bound

This is the finite conversion from the already proved `(1 + ε)^K` bound to
its exponential form.  It does not assert a concrete `ε` asymptotic or any
physical/unlabelled skeleton estimate.
-/

namespace Erdos625

/-- If every one-cell deficit tail is at most `ENNReal.ofReal eps` and there
are at most `K` cells, then the exact distinguishable near-skeleton expansion
is at most `exp (K * eps)`. -/
theorem sum_nearSkeletonChoiceWeight_le_exp_of_card
    {Cell Deficit : Type*} [Fintype Cell] [Fintype Deficit]
    [DecidableEq Deficit] (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal) (eps : ℝ) (K : ℕ)
    (heps : 0 ≤ eps)
    (hcell : ∀ c, (∑ e ∈ allowed c, weight c e) ≤ ENNReal.ofReal eps)
    (hcard : Fintype.card Cell ≤ K) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤
      ENNReal.ofReal (Real.exp ((K : ℝ) * eps)) := by
  refine le_trans
    (sum_nearSkeletonChoiceWeight_le_one_add_pow _ _ _ _ hcell hcard) ?_
  have h_exp_bound : (1 + eps) ^ K ≤ Real.exp (K * eps) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [Real.add_one_le_exp eps]) _
  calc
    (1 + ENNReal.ofReal eps) ^ K =
        (ENNReal.ofReal (1 + eps)) ^ K := by
      rw [ENNReal.ofReal_add zero_le_one heps, ENNReal.ofReal_one]
    _ = ENNReal.ofReal ((1 + eps) ^ K) := by
      rw [ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp ((K : ℝ) * eps)) :=
      ENNReal.ofReal_le_ofReal h_exp_bound

end Erdos625

#print axioms Erdos625.sum_nearSkeletonChoiceWeight_le_exp_of_card
