import Erdos625.Section9FixedFFubiniBridge

/-!
# Section IX: polymer bound for the actual attachment numerator

The exact finite Fubini identity identifies the literal actual-family
numerator with the capped fixed-`F` sum.  This module composes that identity
with the previously proved even-family and polymer bounds.

Both conclusions concern an **unnormalised numerator**: the uniform matching
mass of the cap/no-return event remains present.  No division by the event
probability is performed.  Consequently these theorems are not conditional
expectation bounds, tagged-law integrations, or the final attachment estimate
of Lemma 9.1.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The actual attachment numerator is bounded by the common local-threshold
product times the unrestricted finite even-family weight sum.

This is an unnormalised numerator bound, not a conditional expectation. -/
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

/-- The actual attachment numerator is bounded by the common local-threshold
product times the simple-cycle polymer product.

This is still an unnormalised numerator bound.  It neither conditions on the
cap/no-return event nor integrates a demand-dependent residual estimate over
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
