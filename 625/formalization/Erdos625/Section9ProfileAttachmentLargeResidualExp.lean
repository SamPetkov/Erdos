import Erdos625.Section9ERealENNRealExpTransport
import Erdos625.Section9CanonicalDemandProductSpecialization
import Erdos625.Section8ProfileSkeletonWeight

/-!
# Attained-profile large-residual attachment endpoint

This module specializes the finite large-residual attachment endpoint to the
canonical reference witness of an attained profile high skeleton.  The bound
retains the literal cap/no-return numerator and does not substitute a polymer
majorant.

The proof was returned by Aristotle project
`1905d738-1618-4c53-9677-b32ad19fdc8d`, task
`5aefcfe9-65cc-44ad-bcc2-043872f7a980`, and independently audited before
integration.  Only its proof body and a necessary closing parenthesis were
ported.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- One pair of absolute constants bounds the literal cap/no-return attachment
of every attained profile high skeleton at the finite large-residual
exponential endpoint. -/
theorem exists_absolute_profileHighSkeletonAttachment_le_largeResidualExp :
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
        kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal) <
          (1 / 3 : ENNReal) →
        profileHighSkeletonAttachment row0 U demand ≤
          ENNReal.ofReal
            (Real.exp
              ((kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
                2 * (Fintype.card (ProfileBlockIndex k) : ENNReal) *
                  (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 +
                (((6 * (positiveDemandSupport demand.1).card : ℕ) : ENNReal) *
                  (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) :
                  ENNReal)).toReal)) := by
  obtain ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, hbound⟩ :=
    exists_absolute_residualActualAttachmentNumerator_le_largeResidualEnvelope
  refine ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, ?_⟩
  intro b n k row0 U m _hcap demand hm hmpos hpow htau
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
    hparameters.1 hmpos hrowSum hcolSum hparameters.2.1 hparameters.2.2.1
    hpow htau
  have hexponent :
      (kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
        2 * (Fintype.card (ProfileBlockIndex k) : ENNReal) *
          (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 +
        (((6 * (positiveDemandSupport demand.1).card : ℕ) : ENNReal) *
          (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)))) ≠ ∞ :=
    residualLargeEnvelope_ne_top kappaLambda kappaQ
      (Fintype.card (ProfileBlockIndex k))
      (positiveDemandSupport demand.1).card U m hkLtop hkQtop hmpos
  unfold profileHighSkeletonAttachment
  apply ennreal_le_of_coe_le_ereal_exp_toReal _ _ hexponent
  simpa only [witness] using hactual

end


end Erdos625
