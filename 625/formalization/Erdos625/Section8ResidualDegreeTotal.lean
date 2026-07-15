import Erdos625.ResidualDegreeMatching

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

end Erdos625
