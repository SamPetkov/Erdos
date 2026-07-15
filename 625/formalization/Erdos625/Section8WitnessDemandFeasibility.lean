import Erdos625.ConfigurationModelProbability

/-!
# Section 8: prescribed-demand feasibility

A labelled prescribed-demand witness chooses pairwise disjoint row stubs in
every row class.  Consequently its total demand cannot exceed the ambient
row-stub mass.  This is the finite feasibility condition needed before
factorial cancellation in the canonical-event count.
-/

namespace Erdos625

open scoped BigOperators

/-- Existence of a labelled prescribed-demand witness forces total demand not
to exceed the ambient row-stub mass. -/
theorem totalDemand_le_rowTotal_of_witness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    totalDemand demand ≤ ∑ a, row a := by
  refine Finset.sum_le_sum fun a _ ↦ ?_
  have hcard := card_iUnion_stubAllocation (witness.1 a)
  calc
    ∑ b, demand a b =
        (Finset.univ.biUnion (witness.1 a).1).card := hcard.symm
    _ ≤ (Finset.univ : Finset (Fin (row a))).card := Finset.card_le_univ _
    _ = row a := by simp

#print axioms totalDemand_le_rowTotal_of_witness

end Erdos625
