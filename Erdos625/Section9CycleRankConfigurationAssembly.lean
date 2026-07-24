import Erdos625.Section9ActualResidualFamily
import Erdos625.Section9CycleRankResidual

/-!
# Section IX cycle-rank assembly for the configuration residual support

This module instantiates the generic cycle-rank residual theorem with the
literal configuration-model relation of cells containing at least two matched
stub pairs.  It records both the exact finite support-cardinality bound and
the ensuing half-stub-mass bound from manuscript (9.20).

The final theorem also places the already verified actual even-edge-family
encoding over the same literal residual relation.  No cycle decomposition,
attachment probability, or asymptotic estimate is asserted here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The generic relation finset for the literal configuration residual
relation is exactly the previously defined configuration support finset. -/
theorem relationFinset_configurationResidualSupportRelation
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) :
    relationFinset (configurationResidualSupportRelation matching) =
      configurationResidualSupportFinset matching := by
  classical
  ext p
  simp [relationFinset, configurationResidualSupportRelation,
    configurationResidualSupportFinset]

/-- Exact finite form of (9.20): adjoining the literal configuration residual
support to a bipartite matching has cycle rank at most the number of actual
residual support cells. -/
theorem cycleRank_matching_union_configurationResidualSupport_le_card
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (M : A → B → Prop)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hColumnMatching : ∀ b a₁ a₂, M a₁ b → M a₂ b → a₁ = a₂) :
    cycleRank
        (bipartiteGraph fun a b ↦
          M a b ∨ configurationResidualSupportRelation matching a b) ≤
      (configurationResidualSupportFinset matching).card := by
  rw [← relationFinset_configurationResidualSupportRelation matching]
  exact cycleRank_matching_union_le_card_residual M
    (configurationResidualSupportRelation matching)
    hRowMatching hColumnMatching

/-- Literal half-stub-mass form of (9.20). -/
theorem cycleRank_matching_union_configurationResidualSupport_le_half_stubMass
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (M : A → B → Prop)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hColumnMatching : ∀ b a₁ a₂, M a₁ b → M a₂ b → a₁ = a₂) :
    cycleRank
        (bipartiteGraph fun a b ↦
          M a b ∨ configurationResidualSupportRelation matching a b) ≤
      (∑ a, row a) / 2 := by
  exact
    (cycleRank_matching_union_configurationResidualSupport_le_card
      matching M hRowMatching hColumnMatching).trans
      (card_configurationResidualSupportFinset_le_half_stubMass matching)

/-- Manuscript-notation form of (9.20), with `m₀` explicitly identified as
the total residual row-stub mass. -/
theorem cycleRank_matching_union_configurationResidualSupport_le_half_m₀
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (M : A → B → Prop)
    (m₀ : ℕ) (hm₀ : ∑ a, row a = m₀)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hColumnMatching : ∀ b a₁ a₂, M a₁ b → M a₂ b → a₁ = a₂) :
    cycleRank
        (bipartiteGraph fun a b ↦
          M a b ∨ configurationResidualSupportRelation matching a b) ≤
      m₀ / 2 := by
  simpa only [hm₀] using
    cycleRank_matching_union_configurationResidualSupport_le_half_stubMass
      matching M hRowMatching hColumnMatching

/-- The same cycle-rank estimate with the ambient mass written as the
cardinality of the row-stub type. -/
theorem cycleRank_matching_union_configurationResidualSupport_le_half_rowStubCard
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (M : A → B → Prop)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hColumnMatching : ∀ b a₁ a₂, M a₁ b → M a₂ b → a₁ = a₂) :
    cycleRank
        (bipartiteGraph fun a b ↦
          M a b ∨ configurationResidualSupportRelation matching a b) ≤
      Fintype.card (RowStub row) / 2 := by
  exact
    (cycleRank_matching_union_configurationResidualSupport_le_card
      matching M hRowMatching hColumnMatching).trans
      (card_configurationResidualSupportFinset_le_half_rowStubCard matching)

/-- The concrete actual residual even-edge family over the configuration
cell table is bounded by `2` to half the total row-stub mass. -/
theorem card_configurationActualResidualEvenEdgeFamily_le_two_pow_half_stubMass
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (M : A → B → Prop)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂) :
    Nat.card
        (ActualResidualEvenEdgeFamily
          (configurationCellCount matching) M) ≤
      2 ^ ((∑ a, row a) / 2) := by
  have hFamily :=
    card_actualResidualEvenEdgeFamily_le_pow_support
      (configurationCellCount matching) M hRowMatching
  have hResidualCard :
      Nat.card
          (ResidualCell
            (fun a b ↦ 2 ≤ configurationCellCount matching a b)) ≤
        (∑ a, row a) / 2 := by
    change
      Nat.card
          (ResidualCell
            (configurationResidualSupportRelation matching)) ≤
        (∑ a, row a) / 2
    rw [natCard_configurationResidualCell_eq_supportFinset_card matching]
    exact card_configurationResidualSupportFinset_le_half_stubMass matching
  exact hFamily.trans
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hResidualCard)

#print axioms relationFinset_configurationResidualSupportRelation
#print axioms cycleRank_matching_union_configurationResidualSupport_le_card
#print axioms cycleRank_matching_union_configurationResidualSupport_le_half_stubMass
#print axioms cycleRank_matching_union_configurationResidualSupport_le_half_m₀
#print axioms cycleRank_matching_union_configurationResidualSupport_le_half_rowStubCard
#print axioms card_configurationActualResidualEvenEdgeFamily_le_two_pow_half_stubMass

end

end Erdos625
