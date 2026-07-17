import Erdos625.Section9ActualResidualCycleSpaceEquiv
import Erdos625.Section9FixedFFubiniBridge
import Mathlib.Tactic

/-!
# Section IX: literal actual-family cycle-rank factor

For one realised configuration matching, this module transports the literal
finite family in `actualResidualEvenEdgeSets` to the already-proved actual
residual even-edge family.  It then rewrites the exact event-restricted
attachment numerator by the resulting binary cycle-space factor.

The cap/no-return indicator, uniform configuration-matching mass, and local
reward product are retained verbatim.  This is a finite exact rewrite only:
it proves neither a tagged-law identity, an attachment estimate, a seed or
`Lambda` bound, nor the final theorem.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The literal finite family retained by one realised matching is equivalent
to the existing actual residual even-edge family for its realised cell table.
-/
noncomputable def actualResidualEvenEdgeSetsEquivActualResidualEvenEdgeFamily
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (M : Finset (A × B)) (matching : ConfigurationMatching row col) :
    {F : Finset (A × B) // F ∈ actualResidualEvenEdgeSets M matching} ≃
      ActualResidualEvenEdgeFamily
        (configurationCellCount matching) (fun a b => (a, b) ∈ M) := by
  exact Equiv.subtypeEquivRight (fun F =>
    mem_actualResidualEvenEdgeSets_iff_actualResidualEvenEdgeFamilyPredicate
      M matching F)

/-- The literal finite family retained by one realised matching has exactly
the binary cycle-space cardinality of its exposed-plus-residual support graph.
-/
theorem card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (M : Finset (A × B)) (matching : ConfigurationMatching row col) :
    (actualResidualEvenEdgeSets M matching).card =
      2 ^ cycleRank
        (bipartiteGraph fun a b =>
          (a, b) ∈ M ∨ 2 ≤ configurationCellCount matching a b) := by
  classical
  have hcard :
      Nat.card {F : Finset (A × B) // F ∈ actualResidualEvenEdgeSets M matching} =
        Nat.card
          (ActualResidualEvenEdgeFamily
            (configurationCellCount matching) (fun a b => (a, b) ∈ M)) :=
    Nat.card_congr
      (actualResidualEvenEdgeSetsEquivActualResidualEvenEdgeFamily M matching)
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, hcard]
  exact natCard_actualResidualEvenEdgeFamily_eq_two_pow_cycleRank
    (configurationCellCount matching) (fun a b => (a, b) ∈ M)

/-- Direct `ENNReal` cast of the literal cycle-space cardinality identity. -/
theorem coe_card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (M : Finset (A × B)) (matching : ConfigurationMatching row col) :
    ((actualResidualEvenEdgeSets M matching).card : ℝ≥0∞) =
      (2 : ℝ≥0∞) ^ cycleRank
        (bipartiteGraph fun a b =>
          (a, b) ∈ M ∨ 2 ≤ configurationCellCount matching a b) := by
  norm_cast
  exact card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank M matching

/-- Exact rewrite of the Section IX event-restricted attachment numerator by
the literal actual-family cycle-rank factor. -/
theorem residualActualAttachmentNumerator_eq_cycleRankExpectation
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ)
    (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    residualActualAttachmentNumerator M R row col htotal =
      ∑ matching : ConfigurationMatching row col,
        uniformConfigurationMatching row col htotal matching *
          (if matching ∈ ResidualCapNoReturnEvent M R row col
            then 1 else 0) *
          (∏ a : A, ∏ b : B,
            (residualReward
              (configurationCellCount matching a b) : ℝ≥0∞)) *
          (2 : ℝ≥0∞) ^
            cycleRank
              (bipartiteGraph fun a b =>
                (a, b) ∈ M ∨
                  2 ≤ configurationCellCount matching a b) := by
  classical
  unfold residualActualAttachmentNumerator
  apply Finset.sum_congr rfl
  intro matching _
  rw [coe_card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank]

#print axioms actualResidualEvenEdgeSetsEquivActualResidualEvenEdgeFamily
#print axioms card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank
#print axioms coe_card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank
#print axioms residualActualAttachmentNumerator_eq_cycleRankExpectation

end

end Erdos625
