import Erdos625.Section9SmallResidualAttachmentBound
import Erdos625.Section9ProfileAttachmentPolymerAssembly
import Erdos625.Section9CanonicalSupportMatching
import Mathlib.Tactic

/-!
# Section IX: canonical small-residual attachment specialization

The deterministic small-mass estimate is applied to the residual degrees of
one attained canonical demand.  The conclusion keeps the exact bare skeleton
weight outside the raw attachment bound, as required by the two-regime sum.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- One canonical raw attachment term is at most its exact bare skeleton
factor times the deterministic small-residual exponential. -/
theorem canonicalDemandRawAttachmentTerm_le_smallResidualBound
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : (∑ a, row a) = ∑ b, col b)
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (demand : canonicalDemandImage row col U) :
    canonicalDemandRawAttachmentTerm row col U htotal demand ≤
      (canonicalDemandLocalReward demand : ENNReal) *
        (labelledWitnessIncidence demand.1 row col *
          (2 : ENNReal) ^
            (U * canonicalDemandResidualTotal row col U demand / 2)) := by
  let witness := canonicalDemandReferenceWitness row col U demand
  have hmatching :
      IsBipartiteMatching (positiveDemandSupport demand.1) :=
    positiveDemandSupport_isBipartiteMatching_of_canonicalDemandImage
      U hrowCap hcolCap demand
  have hresidualTotal :
      (∑ a, residualRowDegree witness a) =
        ∑ b, residualColumnDegree witness b :=
    sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness
  have hsmall := residualActualAttachmentNumerator_le_two_pow_of_small_mass
    (positiveDemandSupport demand.1) (U / 2) U
    (canonicalDemandResidualTotal row col U demand)
    (residualRowDegree witness) (residualColumnDegree witness)
    hresidualTotal hmatching rfl (by
      simp only [canonicalDemandResidualTotal, witness])
  unfold canonicalDemandRawAttachmentTerm
  exact mul_le_mul_right (mul_le_mul_right hsmall _) _

#print axioms canonicalDemandRawAttachmentTerm_le_smallResidualBound

end

end Erdos625
