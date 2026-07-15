import Erdos625.ResidualDegreeMatching
import Erdos625.ConfigurationModelProbability

/-!
# Section 8: total residual degree balance

Removing a feasible labelled prescribed-demand witness preserves equality of
the total row and column residual degrees.  This is a finite deterministic
bridge used by the canonical-residual construction.
-/

namespace Erdos625

open scoped BigOperators

/-- Removing one feasible prescribed-demand witness preserves equality of the
total row and column residual degrees. -/
theorem sum_residualRowDegree_eq_sum_residualColumnDegree
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (htotal : (∑ a, row a) = ∑ b, col b)
    (witness : PrescribedDemandWitness demand row col) :
    (∑ a, residualRowDegree witness a) =
      ∑ b, residualColumnDegree witness b := by
  calc
    (∑ a, residualRowDegree witness a) =
        Fintype.card (RowStub (residualRowDegree witness)) :=
      (card_rowStub (residualRowDegree witness)).symm
    _ = Fintype.card (RemainingRowStub witness) :=
      (Fintype.card_congr (remainingRowStubEquivResidual witness)).symm
    _ = Fintype.card (RemainingColumnStub witness) :=
      card_remainingStubs_eq witness htotal
    _ = Fintype.card (ColumnStub (residualColumnDegree witness)) :=
      Fintype.card_congr (remainingColumnStubEquivResidual witness)
    _ = ∑ b, residualColumnDegree witness b :=
      card_columnStub (residualColumnDegree witness)

#print axioms sum_residualRowDegree_eq_sum_residualColumnDegree

/-- Exposing a prescribed-demand witness removes exactly its total demand
from the total row residual degree. -/
theorem sum_residualRowDegree_eq_rowTotal_sub_totalDemand
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    (∑ a, residualRowDegree witness a) =
      (∑ a, row a) - totalDemand demand := by
  calc
    (∑ a, residualRowDegree witness a) =
        Fintype.card (RowStub (residualRowDegree witness)) :=
      (card_rowStub (residualRowDegree witness)).symm
    _ = Fintype.card (RemainingRowStub witness) :=
      (Fintype.card_congr (remainingRowStubEquivResidual witness)).symm
    _ = (∑ a, row a) - totalDemand demand := by
      simpa only [totalDemand] using card_remainingRowStub witness

#print axioms sum_residualRowDegree_eq_rowTotal_sub_totalDemand

/-- Exposing a prescribed-demand witness removes exactly its total demand
from the total column residual degree. -/
theorem sum_residualColumnDegree_eq_colTotal_sub_totalDemand
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    (∑ b, residualColumnDegree witness b) =
      (∑ b, col b) - totalDemand demand := by
  calc
    (∑ b, residualColumnDegree witness b) =
        Fintype.card (ColumnStub (residualColumnDegree witness)) :=
      (card_columnStub (residualColumnDegree witness)).symm
    _ = Fintype.card (RemainingColumnStub witness) :=
      (Fintype.card_congr (remainingColumnStubEquivResidual witness)).symm
    _ = (∑ b, col b) - totalDemand demand := by
      simpa only [totalDemand] using card_remainingColumnStub witness

#print axioms sum_residualColumnDegree_eq_colTotal_sub_totalDemand

/-- Every feasible prescribed-demand witness leaves residual degrees bounded
by their ambient row and column degrees, and preserves equality of the two
residual totals. -/
theorem residualDegreeProfile_of_witness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (htotal : (∑ a, row a) = ∑ b, col b)
    (witness : PrescribedDemandWitness demand row col) :
    (∀ a, residualRowDegree witness a ≤ row a) ∧
      (∀ b, residualColumnDegree witness b ≤ col b) ∧
      ((∑ a, residualRowDegree witness a) =
        ∑ b, residualColumnDegree witness b) := by
  refine ⟨?_, ?_,
    sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness⟩
  · intro a
    change row a - (∑ b, demand a b) ≤ row a
    exact Nat.sub_le _ _
  · intro b
    change col b - (∑ a, demand a b) ≤ col b
    exact Nat.sub_le _ _

#print axioms residualDegreeProfile_of_witness

end Erdos625
