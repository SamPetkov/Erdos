import Erdos625.ConfigurationModelCellMarginals
import Erdos625.ResidualSupportMass

/-!
# Residual support cells of a configuration matching

This module instantiates the deterministic selected-cell mass bound for the
actual cell-count table of a configuration matching.  A residual support cell
is one containing at least two matched stub pairs.  The number of such cells
is at most half the total number of row stubs.

No even-subgraph encoding, cycle-space identity, probability law, or
asymptotic estimate is asserted here.
-/

namespace Erdos625

open scoped BigOperators

/-- The relation of configuration-model cells containing at least two matched
stub pairs. -/
def configurationResidualSupportRelation
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) : A → B → Prop :=
  fun a b ↦ 2 ≤ configurationCellCount matching a b

/-- The finite set of cells in the residual support relation. -/
def configurationResidualSupportFinset
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) : Finset (A × B) :=
  Finset.univ.filter fun p ↦
    2 ≤ configurationCellCount matching p.1 p.2

@[simp] theorem mem_configurationResidualSupportFinset
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (p : A × B) :
    p ∈ configurationResidualSupportFinset matching ↔
      2 ≤ configurationCellCount matching p.1 p.2 := by
  simp [configurationResidualSupportFinset]

/-- The total mass of the configuration cell table is the total number of row
stubs. -/
theorem sum_configurationCellCount_all
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) :
    (∑ p : A × B, configurationCellCount matching p.1 p.2) =
      ∑ a, row a := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact sum_configurationCellCount_row matching a

/-- Cells containing at least two matched pairs occupy at most half of the
total row-stub mass. -/
theorem card_configurationResidualSupportFinset_le_half_stubMass
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) :
    (configurationResidualSupportFinset matching).card ≤
      (∑ a, row a) / 2 := by
  apply card_selectedCells_le_half_total
    (configurationResidualSupportFinset matching)
    (fun p : A × B ↦ configurationCellCount matching p.1 p.2)
    (∑ a, row a)
  · intro p hp
    exact (mem_configurationResidualSupportFinset matching p).mp hp
  · exact sum_configurationCellCount_all matching

/-- The same bound with the ambient mass written literally as the cardinality
of the row-stub type. -/
theorem card_configurationResidualSupportFinset_le_half_rowStubCard
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) :
    (configurationResidualSupportFinset matching).card ≤
      Fintype.card (RowStub row) / 2 := by
  rw [card_rowStub]
  exact card_configurationResidualSupportFinset_le_half_stubMass matching

end Erdos625
