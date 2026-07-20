import Erdos625.Section9CanonicalRawTwoRegimeSplit

/-!
# Section IX: profile-level raw two-regime bookkeeping

This module combines the exact zero/positive-residual decomposition with the
literal raw split of the positive branch.  Both the zero branch and the small
positive-residual branch retain `canonicalDemandRawAttachmentTerm`, including
its cap/no-return event.  Only the positive large-residual branch is replaced
by the already-proved polymer majorant.

The result is conditional bookkeeping: it supplies no quantitative estimate
for either raw branch and therefore does not close Section IX.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Profile-level raw two-regime assembly.  The threshold convention is
literal: `0 < residualTotal < T` is small and `T ≤ residualTotal` is large.
The raw cap/no-return numerator remains present on the zero and small branches.
This theorem alone is not a quantitative Section IX bound. -/
theorem uniformProfile_signedOverlapReward_le_zeroRaw_add_rawSmall_add_largePolymer
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U T : Nat)
    (hU : 2 ≤ U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row₀ column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) ≤
      (∑ demand ∈ (Finset.univ.filter fun demand :
          canonicalDemandImage (profileBlockMargin k) (profileBlockMargin k) U =>
            canonicalDemandResidualTotal (profileBlockMargin k)
              (profileBlockMargin k) U demand = 0),
        canonicalDemandRawAttachmentTerm (profileBlockMargin k)
          (profileBlockMargin k) U
            (profileBlockMargin_total_eq_self row₀) demand) +
      (∑ demand ∈ (Finset.univ.filter fun demand :
          canonicalDemandImage (profileBlockMargin k) (profileBlockMargin k) U =>
            0 < canonicalDemandResidualTotal (profileBlockMargin k)
              (profileBlockMargin k) U demand ∧
            canonicalDemandResidualTotal (profileBlockMargin k)
              (profileBlockMargin k) U demand < T),
        canonicalDemandRawAttachmentTerm (profileBlockMargin k)
          (profileBlockMargin k) U
            (profileBlockMargin_total_eq_self row₀) demand) +
      (∑ demand ∈ (Finset.univ.filter fun demand :
          canonicalDemandImage (profileBlockMargin k) (profileBlockMargin k) U =>
            0 < canonicalDemandResidualTotal (profileBlockMargin k)
              (profileBlockMargin k) U demand ∧
            T ≤ canonicalDemandResidualTotal (profileBlockMargin k)
              (profileBlockMargin k) U demand),
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k) *
            canonicalDemandPolymerMajorant (profileBlockMargin k)
              (profileBlockMargin k) U demand)) := by
  classical
  have hidentity :=
    sum_uniformProfile_signedOverlapReward_eq_zeroResidual_add_positiveResidual
      (row₀ := row₀) (U := U) hU
  have htwo := sum_canonicalDemandRawAttachmentTerm_positive_le_twoRegime
    (A := ProfileBlockIndex k) (B := ProfileBlockIndex k)
    (row := profileBlockMargin k) (col := profileBlockMargin k)
    (U := U) (T := T) (htotal := profileBlockMargin_total_eq_self row₀)
    (smallTerm := canonicalDemandRawAttachmentTerm (profileBlockMargin k)
      (profileBlockMargin k) U (profileBlockMargin_total_eq_self row₀))
    (largeTerm := fun demand =>
      (canonicalDemandLocalReward demand : ENNReal) *
        (labelledWitnessIncidence demand.1 (profileBlockMargin k)
          (profileBlockMargin k) *
          canonicalDemandPolymerMajorant (profileBlockMargin k)
            (profileBlockMargin k) U demand))
    (hsmall := by
      intro demand _ _
      rfl)
    (hlarge := by
      intro demand hpositive _
      unfold canonicalDemandRawAttachmentTerm
      apply mul_le_mul_right
      apply mul_le_mul_right
      unfold canonicalDemandPolymerMajorant
      exact residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct
        (positiveDemandSupport demand.1) (U / 2)
        (residualRowDegree
          (canonicalDemandReferenceWitness (profileBlockMargin k)
            (profileBlockMargin k) U demand))
        (residualColumnDegree
          (canonicalDemandReferenceWitness (profileBlockMargin k)
            (profileBlockMargin k) U demand))
        (sum_residualRowDegree_eq_sum_residualColumnDegree
          (profileBlockMargin_total_eq_self row₀)
          (canonicalDemandReferenceWitness (profileBlockMargin k)
            (profileBlockMargin k) U demand))
        (by simpa only [canonicalDemandResidualTotal] using hpositive))
  have add_two_regime {z p s l : ENNReal} (h : p ≤ s + l) :
      z + p ≤ z + s + l := by
    rw [add_assoc]
    exact add_le_add_right h z
  exact hidentity.le.trans (add_two_regime htwo)

#print axioms uniformProfile_signedOverlapReward_le_zeroRaw_add_rawSmall_add_largePolymer

end

end Erdos625
