import Erdos625.Section9MatchingRestrictionEnvelope
import Erdos625.Section9CanonicalDemandProductSpecialization
import Erdos625.Section8ProfileSkeletonWeight

/-!
# Section IX: attained-profile matching-restriction envelope

This module specializes the direct finite matching-restriction attachment
bound to the canonical reference witness of an attained profile high skeleton.
It keeps the literal cap/no-return attachment observable and introduces no
cycle traversal or polymer majorant.

No asymptotic profile substitution or Section VIII skeleton summation is made.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The direct matching-restriction envelope applies uniformly to every
attained profile high skeleton, with the residual degrees supplied by its
canonical reference witness. -/
theorem exists_absolute_profileHighSkeletonAttachment_le_matchingEnvelope :
    ∃ kappaLambda kappaQ : ENNReal,
      0 < kappaLambda ∧ kappaLambda ≠ ∞ ∧
      0 < kappaQ ∧ kappaQ ≠ ∞ ∧
      ∀ {b n : ℕ} {k : ColoringProfile b}
          (row0 : OrderedProfilePartition n k) (U m : ℕ)
          (_hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U)
          (demand : ProfileCanonicalHighSkeleton k U),
        m = canonicalDemandResidualTotal
          (profileBlockMargin k) (profileBlockMargin k) U demand →
        0 < m →
        2 ^ U ≤ m ^ 3 →
        profileHighSkeletonAttachment row0 U demand ≤
          EReal.exp
            (((kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
              kappaQ * (U : ENNReal) ^ 2 : ENNReal) : EReal)) := by
  obtain ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, hbound⟩ :=
    exists_absolute_residualActualAttachmentNumerator_le_matchingEnvelope
  refine ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, ?_⟩
  intro b n k row0 U m _hcap demand hm hmpos hpow
  let witness := canonicalDemandReferenceWitness
    (profileBlockMargin k) (profileBlockMargin k) U demand
  have hparameters := canonicalReference_residual_parameters
    (profileBlockMargin k) (profileBlockMargin k) U
    (profileBlockMargin_total_eq_self row0) _hcap _hcap demand
  have hrowSum : (∑ a, residualRowDegree witness a) = m := by
    simpa only [canonicalDemandResidualTotal, witness] using hm.symm
  have hcolSum : (∑ a, residualColumnDegree witness a) = m := by
    exact hparameters.2.2.2.symm.trans hrowSum
  have hactual := hbound (positiveDemandSupport demand.1) U m
    (residualRowDegree witness) (residualColumnDegree witness)
    (sum_residualRowDegree_eq_sum_residualColumnDegree
      (profileBlockMargin_total_eq_self row0) witness)
    hparameters.1 hmpos hrowSum hcolSum hparameters.2.1 hparameters.2.2.1 hpow
  unfold profileHighSkeletonAttachment
  simpa only [witness] using hactual

#print axioms exists_absolute_profileHighSkeletonAttachment_le_matchingEnvelope

end

end Erdos625
