import Erdos625.Section6SignedOverlapLocalFactor
import Mathlib.Tactic

/-!
# Section VI: row/column signs as support-graph signs

This module identifies a pair consisting of one Boolean sign on every row
part and one Boolean sign on every column part with a Boolean sign on the
vertices of the bipartite support graph.  Under this identification, the
cellwise compatibility condition at cells of multiplicity at least two is
exactly constancy across every support-graph edge.
-/

namespace Erdos625

noncomputable section

/-- A Boolean sign on every row part and on every column part. -/
abbrev PairBoolSignAssignments (A B : Type*) :=
  (A → Bool) × (B → Bool)

/-- Splitting a sign function on a disjoint union into its row and column
restrictions is an equivalence. -/
def pairBoolSignAssignmentsEquivSum (A B : Type*) :
    PairBoolSignAssignments A B ≃ (A ⊕ B → Bool) where
  toFun sigma := Sum.elim sigma.1 sigma.2
  invFun tau := (fun a ↦ tau (Sum.inl a), fun b ↦ tau (Sum.inr b))
  left_inv sigma := by
    rcases sigma with ⟨sigmaA, sigmaB⟩
    rfl
  right_inv tau := by
    funext x
    cases x <;> rfl

/-- Row and column signs agree at every overlap cell containing at least two
vertices.  Cells of multiplicity zero or one impose no condition. -/
def CompatiblePairSignAssignments
    {A B : Type*} (r : A → B → ℕ) :=
  {sigma : PairBoolSignAssignments A B //
    ∀ a b, 2 ≤ r a b → sigma.1 a = sigma.2 b}

/-- The multiplicity-at-least-two support graph used by the pair-sign
compatibility relation. -/
def pairSignSupportGraph {A B : Type*} (r : A → B → ℕ) :
    SimpleGraph (A ⊕ B) :=
  bipartiteGraph fun a b ↦ 2 ≤ r a b

/-- The pair-sign support graph is definitionally the canonical signed-overlap
support graph used by the local-factor theorem. -/
theorem pairSignSupportGraph_eq_signedOverlapSupportGraph
    {A B : Type*} (r : A → B → ℕ) :
    pairSignSupportGraph r = signedOverlapSupportGraph r := rfl

/-- For a fixed pair of row/column sign functions, agreement on every
multiplicity-at-least-two cell is equivalent to constancy across every edge of
the support graph. -/
theorem pairSign_cellCompatible_iff_graphEdgeConstant
    {A B : Type*} (r : A → B → ℕ)
    (sigma : PairBoolSignAssignments A B) :
    (∀ a b, 2 ≤ r a b → sigma.1 a = sigma.2 b) ↔
      ∀ u v, (pairSignSupportGraph r).Adj u v →
        pairBoolSignAssignmentsEquivSum A B sigma u =
          pairBoolSignAssignmentsEquivSum A B sigma v := by
  constructor
  · intro h u v huv
    cases u with
    | inl a =>
        cases v with
        | inl a' =>
            simp [pairSignSupportGraph, bipartiteGraph,
              SimpleGraph.fromRel_adj] at huv
        | inr b =>
            exact h a b (by
              simpa [pairSignSupportGraph, bipartiteGraph,
                SimpleGraph.fromRel_adj] using huv)
    | inr b =>
        cases v with
        | inl a =>
            exact (h a b (by
              simpa [pairSignSupportGraph, bipartiteGraph,
                SimpleGraph.fromRel_adj] using huv)).symm
        | inr b' =>
            simp [pairSignSupportGraph, bipartiteGraph,
              SimpleGraph.fromRel_adj] at huv
  · intro h a b hab
    exact h (Sum.inl a) (Sum.inr b) (by
      simpa [pairSignSupportGraph, bipartiteGraph,
        SimpleGraph.fromRel_adj] using hab)

/-- Pair-sign consistency at all supported cells is exactly edge constancy on
the bipartite support graph. -/
def compatiblePairSignAssignmentsEquivOverlap
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    CompatiblePairSignAssignments r ≃
      CompatibleOverlapSignAssignments r where
  toFun sigma := ⟨pairBoolSignAssignmentsEquivSum A B sigma.1, by
    have hpair :=
      (pairSign_cellCompatible_iff_graphEdgeConstant r sigma.1).mp sigma.2
    intro u v huv
    exact hpair u v (by
      simpa only [pairSignSupportGraph_eq_signedOverlapSupportGraph] using huv)⟩
  invFun tau :=
    ⟨(pairBoolSignAssignmentsEquivSum A B).symm tau.1,
      (pairSign_cellCompatible_iff_graphEdgeConstant r
        ((pairBoolSignAssignmentsEquivSum A B).symm tau.1)).mpr (by
          intro u v huv
          have htau := tau.2 u v (by
            simpa only [pairSignSupportGraph_eq_signedOverlapSupportGraph]
              using huv)
          simpa only [Equiv.apply_symm_apply] using htau)⟩
  left_inv sigma := by
    apply Subtype.ext
    exact (pairBoolSignAssignmentsEquivSum A B).symm_apply_apply sigma.1
  right_inv tau := by
    apply Subtype.ext
    exact (pairBoolSignAssignmentsEquivSum A B).apply_symm_apply tau.1

/-- Consequently, the two presentations of compatible signs have exactly the
same finite cardinality. -/
theorem natCard_compatiblePairSignAssignments_eq_overlap
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    Nat.card (CompatiblePairSignAssignments r) =
      Nat.card (CompatibleOverlapSignAssignments r) := by
  exact Nat.card_congr (compatiblePairSignAssignmentsEquivOverlap r)

/-- The pair-sign presentation therefore has one free Boolean choice per
connected component of the support graph, including isolated vertices. -/
theorem natCard_compatiblePairSignAssignments_eq_two_pow_components
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    Nat.card (CompatiblePairSignAssignments r) =
      2 ^ Nat.card (signedOverlapSupportGraph r).ConnectedComponent := by
  classical
  let e : CompatiblePairSignAssignments r ≃
      CompatibleBoolSignAssignments (pairSignSupportGraph r) := {
    toFun := fun sigma ↦
      ⟨pairBoolSignAssignmentsEquivSum A B sigma.1,
        (pairSign_cellCompatible_iff_graphEdgeConstant r sigma.1).mp sigma.2⟩
    invFun := fun tau ↦
      ⟨(pairBoolSignAssignmentsEquivSum A B).symm tau.1,
        (pairSign_cellCompatible_iff_graphEdgeConstant r
          ((pairBoolSignAssignmentsEquivSum A B).symm tau.1)).mpr (by
            simpa only [Equiv.apply_symm_apply] using tau.2)⟩
    left_inv := by
      intro sigma
      apply Subtype.ext
      exact (pairBoolSignAssignmentsEquivSum A B).symm_apply_apply sigma.1
    right_inv := by
      intro tau
      apply Subtype.ext
      exact (pairBoolSignAssignmentsEquivSum A B).apply_symm_apply tau.1 }
  calc
    Nat.card (CompatiblePairSignAssignments r) =
        Nat.card (CompatibleBoolSignAssignments (pairSignSupportGraph r)) :=
      Nat.card_congr e
    _ = 2 ^ Nat.card (pairSignSupportGraph r).ConnectedComponent := by
      simpa only [Nat.card_eq_fintype_card] using
        natCard_compatibleBoolSignAssignments_eq_two_pow_components
          (pairSignSupportGraph r)
    _ = 2 ^ Nat.card (signedOverlapSupportGraph r).ConnectedComponent := by
      rw [pairSignSupportGraph_eq_signedOverlapSupportGraph]

#print axioms pairBoolSignAssignmentsEquivSum
#print axioms pairSignSupportGraph_eq_signedOverlapSupportGraph
#print axioms pairSign_cellCompatible_iff_graphEdgeConstant
#print axioms compatiblePairSignAssignmentsEquivOverlap
#print axioms natCard_compatiblePairSignAssignments_eq_overlap
#print axioms natCard_compatiblePairSignAssignments_eq_two_pow_components

end

end Erdos625
