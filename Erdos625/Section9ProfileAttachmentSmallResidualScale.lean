import Erdos625.Section9ResidualRegimeScaleAdapters
import Erdos625.Section8ProfileSkeletonWeight

/-!
# Section IX: attained-profile small-residual attachment scale

This module applies the deterministic small-mass numerator estimate directly
to the literal capped/no-return attachment of one attained profile skeleton.
It deliberately does not replace that attachment by the unrestricted polymer
majorant and does not cancel any skeleton prefactor.

The proof was returned by Aristotle project
`0bbb4854-fb14-46ef-bb74-ae248f1e371f`, task
`0b4f1097-24f9-4024-932e-44491d77da1c`, and independently audited before
integration.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- For one attained profile high skeleton, the literal capped/no-return
attachment is at most the manuscript small-residual exponential scale. -/
theorem profileHighSkeletonAttachment_le_smallResidualExpScale
    {b n : ℕ} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k)
    (U : ℕ)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U)
    (demand : ProfileCanonicalHighSkeleton k U)
    (L C : ℝ)
    (hL : 0 < L)
    (hC : 0 ≤ C)
    (hU : (U : ℝ) ≤ C * L)
    (hm :
      (canonicalDemandResidualTotal
        (profileBlockMargin k) (profileBlockMargin k) U demand : ℝ) ≤
        (n : ℝ) / L ^ 6) :
    profileHighSkeletonAttachment row0 U demand ≤
      ENNReal.ofReal
        (Real.exp ((C * Real.log 2 / 2) * ((n : ℝ) / L ^ 5))) := by
  let witness := canonicalDemandReferenceWitness
    (profileBlockMargin k) (profileBlockMargin k) U demand
  have hmatching :
      IsBipartiteMatching (positiveDemandSupport demand.1) :=
    profileHighSkeleton_positiveSupport_isBipartiteMatching k U hcap demand
  have htotal :
      (∑ a, residualRowDegree witness a) =
        ∑ a, residualColumnDegree witness a :=
    sum_residualRowDegree_eq_sum_residualColumnDegree
      (profileBlockMargin_total_eq_self row0) witness
  have hsmall :
      residualActualAttachmentNumerator
          (positiveDemandSupport demand.1) (U / 2)
          (residualRowDegree witness) (residualColumnDegree witness) htotal ≤
        (2 : ENNReal) ^
          (U * canonicalDemandResidualTotal
            (profileBlockMargin k) (profileBlockMargin k) U demand / 2) :=
    residualActualAttachmentNumerator_le_two_pow_of_small_mass
      (positiveDemandSupport demand.1) (U / 2) U
      (canonicalDemandResidualTotal
        (profileBlockMargin k) (profileBlockMargin k) U demand)
      (residualRowDegree witness) (residualColumnDegree witness)
      htotal hmatching rfl (by
        simp only [canonicalDemandResidualTotal, witness])
  have hscale := smallResidual_two_pow_le_exp_scale
    (n : ℝ) L C U
    (canonicalDemandResidualTotal
      (profileBlockMargin k) (profileBlockMargin k) U demand)
    (Nat.cast_nonneg n) hL hC hU hm
  unfold profileHighSkeletonAttachment
  exact hsmall.trans hscale

end

end Erdos625
