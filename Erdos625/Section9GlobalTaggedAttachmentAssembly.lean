import Erdos625.Section9TaggedFiberCancellation
import Mathlib.Tactic

/-!
# Section IX: global tagged attachment assembly

This module sums the exact per-demand tagged-fibre cancellation identity over
all attained canonical demands.  It closes the finite global Fubini seam
between the dependent canonical demand/witness/residual law and the literal
Section IX event-restricted attachment numerators.

No asymptotic estimate, division by the cap/no-return event mass, or rare-seed
claim is made here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance instFintypeCanonicalResidualCellEventGlobalAssembly
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

/-- A fixed labelled witness for each attained canonical demand.  Existence is
forced by attainment: a matching in the corresponding canonical-demand fibre
transports to a witness/residual pair. -/
noncomputable def canonicalDemandReferenceWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (demand : canonicalDemandImage row col U) :
    PrescribedDemandWitness demand.1 row col := by
  let x : canonicalDemandEvent demand.1 row col U :=
    Classical.choice
      (nonempty_canonicalDemandEvent_of_canonicalDemandImage row col U demand)
  exact (canonicalDemandEventEquivSigmaResidual demand.1 row col U
    (canonicalDemandImage_high row col U demand) x).1

/-- Exact global finite assembly of the weighted tagged law.  The left side is
one sum over the full dependent canonical demand/witness/residual sigma space.
The right side is the sum of labelled-witness incidence times the literal
unnormalised, event-restricted Section IX attachment numerator in each attained
demand fibre. -/
theorem sum_global_taggedResidualAttachmentValue_eq_sum_incidence_mul_numerator
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    (Finset.univ.sum fun z :
      Sigma fun demand : canonicalDemandImage row col U =>
        Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          canonicalResidualCellEvent witness U =>
      uniformSigmaCanonicalDemandResidual row col U htotal z *
        taggedResidualAttachmentValue z.1.1 U z.2.1 z.2.2) =
      Finset.univ.sum fun demand : canonicalDemandImage row col U =>
        labelledWitnessIncidence demand.1 row col *
          residualActualAttachmentNumerator
            (positiveDemandSupport demand.1) (U / 2)
            (residualRowDegree
              (canonicalDemandReferenceWitness row col U demand))
            (residualColumnDegree
              (canonicalDemandReferenceWitness row col U demand))
            (sum_residualRowDegree_eq_sum_residualColumnDegree htotal
              (canonicalDemandReferenceWitness row col U demand)) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro demand _
  exact sum_taggedResidualAttachmentValue_eq_incidence_mul_numerator
    row col U htotal demand
      (canonicalDemandReferenceWitness row col U demand)

#print axioms canonicalDemandReferenceWitness
#print axioms sum_global_taggedResidualAttachmentValue_eq_sum_incidence_mul_numerator

end

end Erdos625
