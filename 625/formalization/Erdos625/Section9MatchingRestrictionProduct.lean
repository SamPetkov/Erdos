import Erdos625.Section9FixedFEvenAggregation
import Erdos625.EvenMatchingRestriction
import Mathlib.Tactic

/-!
# Section IX: direct product bound from matching restriction

For an exposed bipartite matching `M`, an even edge set is uniquely determined
by its restriction outside `M`.  This gives a direct subset-product bound for
the weighted even-family sum and avoids the cycle/polymer decomposition at the
finite algebraic level.

The final theorem composes this injection with the already checked fixed-`F`
aggregation.  It does not identify the fixed-`F` sum with the actual tagged
attachment expectation, prove the residual-`q` analytic envelope, or establish
Lemma 9.1.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- On the finite family of even bipartite edge sets, deleting a matching is
injective.  Equivalently, an even completion of a prescribed outside-matching
edge set is unique when it exists. -/
theorem sdiff_matching_injective_on_bipartiteEvenEdgeSets
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    ∀ F ∈ bipartiteEvenEdgeSets A B,
      ∀ G ∈ bipartiteEvenEdgeSets A B,
        F \ M = G \ M → F = G := by
  intro F hF G hG hdiff
  apply bipartiteEdgeMatrix_injective
  apply evenMatrix_eq_of_eq_on_residual
    (bipartiteEdgeMatrix F) (bipartiteEdgeMatrix G)
    (fun a b => (a, b) ∈ M) (fun a b => (a, b) ∉ M)
  · apply (bipartiteEdgeMatrix_even_iff F).2
    apply (bipartiteEvenEdgeSet_iff_isBipartiteEven F).2
    simpa [bipartiteEvenEdgeSets] using hF
  · apply (bipartiteEdgeMatrix_even_iff G).2
    apply (bipartiteEvenEdgeSet_iff_isBipartiteEven G).2
    simpa [bipartiteEvenEdgeSets] using hG
  · exact hM.1
  · intro a b _hab
    by_cases hmem : (a, b) ∈ M
    · exact Or.inl hmem
    · exact Or.inr hmem
  · intro a b _hab
    by_cases hmem : (a, b) ∈ M
    · exact Or.inl hmem
    · exact Or.inr hmem
  · intro a b hab
    have hmem : ((a, b) ∈ F) ↔ ((a, b) ∈ G) := by
      have h := congrArg (fun S : Finset (A × B) => (a, b) ∈ S) hdiff
      simpa [hab] using h
    by_cases hFmem : (a, b) ∈ F
    · have hGmem : (a, b) ∈ G := hmem.mp hFmem
      simp [bipartiteEdgeMatrix, hFmem, hGmem]
    · have hGmem : (a, b) ∉ G := by
        intro hG
        exact hFmem (hmem.mpr hG)
      simp [bipartiteEdgeMatrix, hFmem, hGmem]

/-- The weighted even-family sum is bounded directly by the full subset product
on the cells outside the matching.  No cycle decomposition is used. -/
theorem weighted_evenSubgraph_ennreal_matching_product
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B))
    (hM : IsBipartiteMatching M) :
    (∑ F ∈ bipartiteEvenEdgeSets A B,
      edgeWeightOutsideENN q M F) ≤
      ∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
        (1 + q e.1 e.2) := by
  classical
  unfold edgeWeightOutsideENN
  calc
    (∑ F ∈ bipartiteEvenEdgeSets A B,
        ∏ e ∈ F \ M, q e.1 e.2) =
        ∑ S ∈ Finset.image (fun F : Finset (A × B) => F \ M)
            (bipartiteEvenEdgeSets A B),
          ∏ e ∈ S, q e.1 e.2 := by
      symm
      rw [Finset.sum_image]
      exact sdiff_matching_injective_on_bipartiteEvenEdgeSets M hM
    _ ≤ ∑ S ∈ Finset.powerset
          ((Finset.univ : Finset (A × B)) \ M),
          ∏ e ∈ S, q e.1 e.2 := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.image_subset_iff.mpr fun F _hF =>
        Finset.mem_powerset.mpr (by
          intro e he
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ e, (Finset.mem_sdiff.mp he).2⟩)
    _ = ∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
          (1 + q e.1 e.2) := by
      simp +decide [Finset.prod_add, add_comm]

/-- Direct matching-restriction replacement for the polymer-product endpoint
in the finite capped fixed-`F` aggregation. -/
theorem residualCappedEvenFixedFSum_le_lambdaProduct_mul_matchingProduct
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row)
    (hM : IsBipartiteMatching M) :
    residualCappedEvenFixedFSum M R row col htotal ≤
      (∏ a : A, ∏ b : B,
        (1 + residualLambda M R row col a b)) *
      (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
        (1 + residualQ M R row col e.1 e.2)) := by
  calc
    residualCappedEvenFixedFSum M R row col htotal ≤
        (∏ a : A, ∏ b : B,
          (1 + residualLambda M R row col a b)) *
        (∑ F ∈ bipartiteEvenEdgeSets A B,
          edgeWeightOutsideENN (residualQ M R row col) M F) :=
      residualCappedEvenFixedFSum_le_lambdaProduct_mul_evenWeightSum
        M R row col htotal hm
    _ ≤
        (∏ a : A, ∏ b : B,
          (1 + residualLambda M R row col a b)) *
        (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
          (1 + residualQ M R row col e.1 e.2)) :=
      mul_le_mul_right
        (weighted_evenSubgraph_ennreal_matching_product
          (residualQ M R row col) M hM)
        _

#print axioms sdiff_matching_injective_on_bipartiteEvenEdgeSets
#print axioms weighted_evenSubgraph_ennreal_matching_product
#print axioms residualCappedEvenFixedFSum_le_lambdaProduct_mul_matchingProduct

end

end Erdos625
