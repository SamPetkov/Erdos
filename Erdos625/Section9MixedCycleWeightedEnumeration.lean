import Erdos625.Section9MarkedCycleEnumeration
import Erdos625.Section9MatchingTraversalBridge

/-!
# Section IX: abstract weighted enumeration of mixed cycles

This module closes the finite, assumption-faithful cycle-to-walk bridge.  The
physical encoder and its aggregate marked enumeration are composed with the
endpoint positive-walk row bound and the matching partial-permutation
geometric estimate.  The marked matching edge costs exactly `2 * |M|` once.

The result is still an abstract finite kernel theorem: its hypotheses are
literal row and column bounds for a supplied cell kernel `q`.  It does not
identify `q` with the conditioned residual table, establish those bounds from
the manuscript profile, or prove an attachment probability estimate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Weighted enumeration of all simple bipartite cycles meeting a matching.

The positive residual-path kernel has row mass at most
`b = tau * (1 - tau)⁻¹`.  Cutting each physical cycle at its matching edges,
injecting the resulting marked code into the full relaxed enumeration, and
using the matching partial permutation gives one factor `2 * |M|` and no
additional matching-cardinality loss. -/
theorem mixedSimpleCycle_weighted_walk_enumeration
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞) (M : Finset (A × B))
    (hM : IsBipartiteMatching M)
    (tau : ℝ≥0∞) (htau : tau < (1 / 3 : ℝ≥0∞))
    (hRow : ∀ a, ∑ b, q a b ≤ tau)
    (hColumn : ∀ b, ∑ a, q a b ≤ tau) :
    let b : ℝ≥0∞ := tau * (1 - tau)⁻¹
    b < 1 ∧
      (∑ C : MixedSimpleCycle A B M,
          edgeWeightOutsideENN q M C.1) ≤
        (((2 * M.card : ℕ) : ℝ≥0∞) * (b * (1 - b)⁻¹)) := by
  dsimp only
  let L := Fintype.card (A ⊕ B)
  let K := bipartiteCellKernel q
  let S := finitePositiveWalkKernel K L
  have hKRow : ∀ v, ∑ w, K v w ≤ tau := by
    dsimp only [K]
    exact bipartiteCellKernel_rowSum_le q tau hRow hColumn
  have hSRow :
      ∀ v, ∑ w, S v w ≤ tau * (1 - tau)⁻¹ := by
    exact
      (finitePositiveWalkKernel_rowSum_le_geometric
        K tau hKRow L).2
  have hGeometric :=
    finite_relaxed_matchingTraversal_enumeration
      M hM tau htau S hSRow L
  dsimp only at hGeometric
  refine ⟨hGeometric.1, ?_⟩
  calc
    (∑ C : MixedSimpleCycle A B M,
        edgeWeightOutsideENN q M C.1) ≤
        ∑ z ∈ orientedMatchingStarts M,
          ∑ r ∈ Finset.range L,
            finiteKernelWalkMass
              (finiteKernelComp S (matchingTraversalKernel M))
              (r + 1) (orientedMatchingStartState z) := by
      simpa only [L, K, S] using
        sum_mixedSimpleCycle_weight_le_nested_walkMass q M hM
    _ ≤ (((2 * M.card : ℕ) : ℝ≥0∞) *
          ((tau * (1 - tau)⁻¹) *
            (1 - tau * (1 - tau)⁻¹)⁻¹)) :=
      hGeometric.2

#print axioms mixedSimpleCycle_weighted_walk_enumeration

end

end Erdos625
