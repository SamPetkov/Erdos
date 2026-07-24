import Erdos625.Section9FixedFEvenAggregation
import Erdos625.Section9ActualResidualWeightedEmbedding

/-!
# Section IX: exact finite fixed-family Fubini bridge

This module identifies the literal sum of the capped fixed-`F` expectations
with an event-restricted numerator under the uniform configuration-matching law.
For a realised matching, the finite family retained in the numerator consists
exactly of the even edge sets whose every edge is either already in the
high-skeleton matching `M` or lies in a cell of residual multiplicity at least
two.

The result is a finite sum-commutation and zero-one multiplicity identity.  It
retains the cap/no-return indicator inside the residual expectation exactly as
in manuscript (9.1).  Division by that event probability is not part of the
(9.1)--(9.2) assembly.  The separate cycle-space cardinality, full-table
reward/support split, and tagged incidence identities are not asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The literal finite family of actual residual even edge sets for one
configuration matching. -/
def actualResidualEvenEdgeSets
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (M : Finset (A × B)) (matching : ConfigurationMatching row col) :
    Finset (Finset (A × B)) :=
  (bipartiteEvenEdgeSets A B).filter fun F ↦
    ∀ e ∈ F, e ∈ M ∨ 2 ≤ configurationCellCount matching e.1 e.2

/-- Membership in the literal finite family is exactly the predicate defining
`ActualResidualEvenEdgeFamily` for the realised cell-count table. -/
theorem mem_actualResidualEvenEdgeSets_iff_actualResidualEvenEdgeFamilyPredicate
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (M : Finset (A × B)) (matching : ConfigurationMatching row col)
    (F : Finset (A × B)) :
    F ∈ actualResidualEvenEdgeSets M matching ↔
      BipartiteEvenEdgeSet F ∧
        ∀ e ∈ F, (e.1, e.2) ∈ M ∨
          2 ≤ configurationCellCount matching e.1 e.2 := by
  classical
  simp only [actualResidualEvenEdgeSets, Finset.mem_filter,
    bipartiteEvenEdgeSets, Finset.mem_univ, true_and]
  rw [bipartiteEvenEdgeSet_iff_isBipartiteEven]

/-- For one realised matching, summing the fixed-`F` threshold indicators over
all even edge sets gives exactly the cardinality of the actual finite family.
-/
theorem sum_fixedF_thresholdIndicator_eq_card_actualResidualEvenEdgeSets
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (M : Finset (A × B)) (matching : ConfigurationMatching row col) :
    (∑ F ∈ bipartiteEvenEdgeSets A B,
      ∏ e ∈ F,
        if e ∈ M then (1 : ℝ≥0∞)
        else if 2 ≤ configurationCellCount matching e.1 e.2 then 1 else 0) =
      ((actualResidualEvenEdgeSets M matching).card : ℝ≥0∞) := by
  classical
  calc
    (∑ F ∈ bipartiteEvenEdgeSets A B,
      ∏ e ∈ F,
        if e ∈ M then (1 : ℝ≥0∞)
        else if 2 ≤ configurationCellCount matching e.1 e.2 then 1 else 0) =
        ∑ F ∈ bipartiteEvenEdgeSets A B,
          if (∀ e ∈ F, e ∈ M ∨
              2 ≤ configurationCellCount matching e.1 e.2)
          then (1 : ℝ≥0∞) else 0 := by
      apply Finset.sum_congr rfl
      intro F hF
      clear hF
      induction F using Finset.induction_on with
      | empty => simp
      | @insert e F he ih =>
          by_cases heM : e ∈ M
          · simp [he, heM, ih]
          · by_cases heCount :
                2 ≤ configurationCellCount matching e.1 e.2
            · simp [he, heM, heCount, ih]
            · simp [he, heM, heCount]
    _ = ((actualResidualEvenEdgeSets M matching).card : ℝ≥0∞) := by
      rw [Finset.sum_boole]
      rfl

/-- The event-restricted actual attachment numerator.  The cap/no-return
indicator and hence its probability mass remain inside the expectation. -/
def residualActualAttachmentNumerator
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) : ℝ≥0∞ := by
  classical
  exact
    ∑ matching : ConfigurationMatching row col,
      uniformConfigurationMatching row col htotal matching *
        (if matching ∈ ResidualCapNoReturnEvent M R row col then 1 else 0) *
        (∏ a : A, ∏ b : B,
          (residualReward (configurationCellCount matching a b) : ℝ≥0∞)) *
        ((actualResidualEvenEdgeSets M matching).card : ℝ≥0∞)

/-- Exact finite Fubini/multiplicity identity for the event-restricted
expectation in manuscript (9.1). -/
theorem residualActualAttachmentNumerator_eq_residualCappedEvenFixedFSum
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    residualActualAttachmentNumerator M R row col htotal =
      residualCappedEvenFixedFSum M R row col htotal := by
  classical
  unfold residualActualAttachmentNumerator residualCappedEvenFixedFSum
  simp only [residualFixedFExpectation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro matching hmatching
  by_cases hevent : matching ∈ ResidualCapNoReturnEvent M R row col
  · simp only [residualFixedFWeight, hevent, if_pos]
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    rw [sum_fixedF_thresholdIndicator_eq_card_actualResidualEvenEdgeSets]
    ring
  · simp [residualFixedFWeight, hevent]

#print axioms mem_actualResidualEvenEdgeSets_iff_actualResidualEvenEdgeFamilyPredicate
#print axioms sum_fixedF_thresholdIndicator_eq_card_actualResidualEvenEdgeSets
#print axioms residualActualAttachmentNumerator_eq_residualCappedEvenFixedFSum

end

end Erdos625
