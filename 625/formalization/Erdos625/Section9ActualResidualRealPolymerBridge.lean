import Erdos625.Section9ActualResidualWeightedEmbedding
import Erdos625.Section9CyclePolymerBound

/-!
# Section IX: actual-residual real polymer bridge

For nonnegative real cell weights, the literal actual residual even-edge
family is a weighted subfamily of all finite bipartite even edge sets.  This
module composes that finite inclusion with the established real-valued polymer
bound.  It is deliberately separate from the `ENNReal` inclusion: it does not
identify a residual probability law, specialize `residualQ`, supply an
`ENNReal` polymer theorem, or provide a cycle-to-walk or attachment estimate.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

local instance fintypeActualResidualEvenEdgeFamilyReal
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A -> B -> Nat) (M : Finset (A × B)) :
    Fintype (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) := by
  letI : Finite (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- For nonnegative real cell weights, the actual residual even-edge family
is a weighted subfamily of all finite bipartite even edge sets. -/
theorem sum_actualResidualEvenEdgeFamily_real_weight_le_all_even
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A -> B -> Nat) (M : Finset (A × B))
    (q : A -> B -> Real)
    (hq : ∀ a b, 0 ≤ q a b) :
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      edgeWeightOutside q M F.1) ≤
      ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutside q M F := by
  classical
  have hvalInj : Function.Injective
      (fun F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M) => F.1) :=
    Subtype.val_injective
  have hsubset :
      Finset.image
          (fun F : ActualResidualEvenEdgeFamily cellCount
            (fun a b => (a, b) ∈ M) => F.1)
          Finset.univ ⊆
        bipartiteEvenEdgeSets A B := by
    intro F hF
    rcases Finset.mem_image.mp hF with ⟨G, _, rfl⟩
    simp only [bipartiteEvenEdgeSets, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (bipartiteEvenEdgeSet_iff_isBipartiteEven G.1).mp G.2.1
  calc
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M), edgeWeightOutside q M F.1) =
        ∑ F ∈ Finset.image
            (fun G : ActualResidualEvenEdgeFamily cellCount
              (fun a b => (a, b) ∈ M) => G.1)
            Finset.univ, edgeWeightOutside q M F := by
      symm
      rw [Finset.sum_image]
      exact fun _ _ _ _ hxy => hvalInj hxy
    _ ≤ ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutside q M F := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro F hF hnotmem
      exact Finset.prod_nonneg fun e he => hq e.1 e.2

/-- The finite real actual-residual weighted sum is bounded by the established
polymer product whenever the distinguished high-cell set is a matching. -/
theorem sum_actualResidualEvenEdgeFamily_real_weight_le_polymer_product
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A -> B -> Nat) (M : Finset (A × B))
    (q : A -> B -> Real)
    (hM : IsBipartiteMatching M)
    (hq : ∀ a b, 0 ≤ q a b) :
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      edgeWeightOutside q M F.1) ≤
      ∏ C ∈ simpleBipartiteCycles A B,
        (1 + edgeWeightOutside q M C) := by
  calc
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M), edgeWeightOutside q M F.1) ≤
        ∑ F ∈ bipartiteEvenEdgeSets A B, edgeWeightOutside q M F :=
      sum_actualResidualEvenEdgeFamily_real_weight_le_all_even
        cellCount M q hq
    _ ≤ ∏ C ∈ simpleBipartiteCycles A B,
        (1 + edgeWeightOutside q M C) :=
      (weighted_evenSubgraph_polymer_bound q M hM hq).1

/-- The same finite real bridge continues to the exponential endpoint of the
established polymer theorem.  This remains a finite algebraic statement. -/
theorem sum_actualResidualEvenEdgeFamily_real_weight_le_polymer_exp
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A -> B -> Nat) (M : Finset (A × B))
    (q : A -> B -> Real)
    (hM : IsBipartiteMatching M)
    (hq : ∀ a b, 0 ≤ q a b) :
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      edgeWeightOutside q M F.1) ≤
      Real.exp (∑ C ∈ simpleBipartiteCycles A B,
        edgeWeightOutside q M C) := by
  exact le_trans
    (sum_actualResidualEvenEdgeFamily_real_weight_le_polymer_product
      cellCount M q hM hq)
    (weighted_evenSubgraph_polymer_bound q M hM hq).2

#print axioms sum_actualResidualEvenEdgeFamily_real_weight_le_all_even
#print axioms sum_actualResidualEvenEdgeFamily_real_weight_le_polymer_product
#print axioms sum_actualResidualEvenEdgeFamily_real_weight_le_polymer_exp

end

end Erdos625
