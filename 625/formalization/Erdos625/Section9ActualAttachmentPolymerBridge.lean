import Erdos625.Section9FixedFFubiniBridge

/-!
# Section IX: polymer bound for the actual attachment numerator

The exact finite Fubini identity identifies the literal actual-family
numerator with the capped fixed-`F` sum.  This module composes that identity
with the previously proved even-family and polymer bounds.

Both conclusions concern the **event-restricted expectation** in manuscript
(9.1): the cap/no-return indicator remains inside the uniform residual
matching expectation.  No division by its event probability belongs in the
(9.1)--(9.2) route.  The cycle-space cardinality, full-table reward/support
split, tagged incidence integration, and final Lemma 9.1 estimate remain
separate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The event-restricted attachment numerator is bounded by the common local-threshold
product times the unrestricted finite even-family weight sum.

This is the fixed-residual-fibre form, before tagged incidence integration. -/
theorem residualActualAttachmentNumerator_le_lambdaProduct_mul_evenWeightSum
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    residualActualAttachmentNumerator M R row col htotal ≤
      (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
        (∑ F ∈ bipartiteEvenEdgeSets A B,
          edgeWeightOutsideENN (residualQ M R row col) M F) := by
  rw [residualActualAttachmentNumerator_eq_residualCappedEvenFixedFSum]
  exact residualCappedEvenFixedFSum_le_lambdaProduct_mul_evenWeightSum
    M R row col htotal hm

/-- The event-restricted attachment numerator is bounded by the common local-threshold
product times the simple-cycle polymer product.

It does not yet identify the even-family cardinality with the manuscript
cycle-space factor or integrate the demand-dependent residual estimate over
the global tagged law. -/
theorem residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    residualActualAttachmentNumerator M R row col htotal ≤
      (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
        (∏ C ∈ simpleBipartiteCycles A B,
          (1 + edgeWeightOutsideENN (residualQ M R row col) M C)) := by
  rw [residualActualAttachmentNumerator_eq_residualCappedEvenFixedFSum]
  exact residualCappedEvenFixedFSum_le_lambdaProduct_mul_polymerProduct
    M R row col htotal hm

#print axioms residualActualAttachmentNumerator_le_lambdaProduct_mul_evenWeightSum
#print axioms residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct

end

end Erdos625
