import Erdos625.Section9FixedFFactorization

/-!
# Section IX: finite even-family aggregation of the fixed-`F` bound

This module sums the capped fixed-`F` expectations over the finite family of
all even bipartite edge sets.  The fixed-family factorization separates a
common product of local threshold increments; the finite even-subgraph
polymer theorem then bounds the remaining edge-weight sum by the product over
simple bipartite cycles.

The quantity defined here is deliberately named a fixed-`F` sum.  This module
does **not** identify it with the manuscript's actual attachment expectation,
the tagged residual law, or any conditional expectation.  Such an
identification requires a separate multiplicity/law bridge and is not used
below.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The finite sum of capped fixed-`F` expectations over every even
bipartite edge set.  No claim that this is an attachment expectation is part
of the definition. -/
def residualCappedEvenFixedFSum
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) : ℝ≥0∞ :=
  ∑ F ∈ bipartiteEvenEdgeSets A B,
    residualFixedFExpectation M F R row col htotal

/-- Summing the fixed-`F` factorization extracts its common local-`lambda`
product from the finite even-family sum. -/
theorem residualCappedEvenFixedFSum_le_lambdaProduct_mul_evenWeightSum
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    residualCappedEvenFixedFSum M R row col htotal ≤
      (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
        (∑ F ∈ bipartiteEvenEdgeSets A B,
          edgeWeightOutsideENN (residualQ M R row col) M F) := by
  unfold residualCappedEvenFixedFSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro F hF
  exact residualFixedFExpectation_le_lambdaProduct_mul_edgeWeight
    M F R row col htotal hm

/-- The finite even-family fixed-`F` sum is bounded by the common local
threshold product times the simple-cycle polymer product.

This is a finite deterministic aggregation theorem.  In particular, it does
not assert that `residualCappedEvenFixedFSum` equals the actual attachment
expectation. -/
theorem residualCappedEvenFixedFSum_le_lambdaProduct_mul_polymerProduct
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    residualCappedEvenFixedFSum M R row col htotal ≤
      (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
        (∏ C ∈ simpleBipartiteCycles A B,
          (1 + edgeWeightOutsideENN (residualQ M R row col) M C)) := by
  calc
    residualCappedEvenFixedFSum M R row col htotal ≤
        (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
          (∑ F ∈ bipartiteEvenEdgeSets A B,
            edgeWeightOutsideENN (residualQ M R row col) M F) :=
      residualCappedEvenFixedFSum_le_lambdaProduct_mul_evenWeightSum
        M R row col htotal hm
    _ ≤
        (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
          (∏ C ∈ simpleBipartiteCycles A B,
            (1 + edgeWeightOutsideENN (residualQ M R row col) M C)) :=
      mul_le_mul_right
        (weighted_evenSubgraph_ennreal_polymer_product
          (residualQ M R row col) M)
        _

#print axioms residualCappedEvenFixedFSum_le_lambdaProduct_mul_evenWeightSum
#print axioms residualCappedEvenFixedFSum_le_lambdaProduct_mul_polymerProduct

end

end Erdos625
