import Erdos625.Section8AttainedWeightedQuotient
import Erdos625.Section8ProfileSkeletonWeight
import Erdos625.Section8CanonicalConditionalLaw
import Erdos625.Section9ProfileAttachmentPolymerAssembly
import Mathlib.Tactic

/-!
# Section VIII: attained profile weighted quotient

This module combines the exact profile signed-overlap decomposition with the
physical finite quotient over the attained canonical high-demand family.  The
result retains, separately and without cancellation,

* the physical row/column descending-factorial fibre coefficient and its
  single cell-factorial denominator;
* the exposed local signed reward and ambient descending-factorial
  normalization; and
* the exact residual attachment, or any supplied pointwise majorant for it.

All statements are finite identities or inequalities in `ENNReal`.  They
include zero entries and empty attained families, make no near/middle or
asymptotic assertion, and do not turn a pointwise estimate into a probability
statement.  The imported canonical conditional-law results explain the exact
uniform residual fibre, but no conditioning or event-mass division is used
below.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Every canonical profile demand is attained by a physical unlabelled typed
skeleton.  The witness comes from the defining canonical image; no numerical
feasibility relaxation is used. -/
theorem profileCanonicalHighSkeleton_mem_attainedUnlabelledTypeTables
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (L : ProfileCanonicalHighSkeleton k U) :
    L.1 ∈ attainedUnlabelledTypeTables
      (profileBlockMargin k) (profileBlockMargin k) := by
  let witness := canonicalDemandReferenceWitness
    (profileBlockMargin k) (profileBlockMargin k) U L
  let matching : TypedPartialMatching L.1 (profileBlockMargin k)
      (profileBlockMargin k) :=
    (typedPartialMatchingEquivPrescribedDemandWitness L.1
      (profileBlockMargin k) (profileBlockMargin k)).symm witness
  unfold attainedUnlabelledTypeTables
  exact Finset.mem_image.mpr ⟨typedPartialMatchingUnlabelledSkeleton matching,
    Finset.mem_univ _, typedPartialMatchingUnlabelledSkeleton_typeTable matching⟩

/-- Extend the exact per-physical-skeleton contribution from the attained
canonical family to all tables.  Outside that family it is zero. -/
noncomputable def profileExactPhysicalTableWeight
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat)
    (L : ProfileBlockIndex k → ProfileBlockIndex k → Nat) : ENNReal :=
  if hL : L ∈ canonicalDemandImage
      (profileBlockMargin k) (profileBlockMargin k) U then
    profileHighSkeletonWitnessWeight k U ⟨L, hL⟩ *
      profileHighSkeletonAttachment row0 U ⟨L, hL⟩
  else 0

/-- Extend a supplied pointwise residual majorant to the same table space,
while retaining the local reward and ambient normalization exactly. -/
noncomputable def profileMajorizedPhysicalTableWeight
    {b : Nat} {k : ColoringProfile b} (U : Nat)
    (majorant : ProfileCanonicalHighSkeleton k U → ENNReal)
    (L : ProfileBlockIndex k → ProfileBlockIndex k → Nat) : ENNReal :=
  if hL : L ∈ canonicalDemandImage
      (profileBlockMargin k) (profileBlockMargin k) U then
    profileHighSkeletonWitnessWeight k U ⟨L, hL⟩ * majorant ⟨L, hL⟩
  else 0

/-- The physical fibre cardinality as an `ENNReal` quotient.  This is the
endpoint-safe specialization missing from the semifield-valued generic
quotient: the factorial denominator is a finite positive natural cast, hence
is neither zero nor top. -/
theorem ennreal_card_unlabelledSkeleton_fibre_eq_descendingProducts_div_cellFactorials
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (k : I → Nat) (ell : J → Nat) (L : I → J → Nat) :
    (Fintype.card
      {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} : ENNReal) =
      ((typeTableRowDescendingProduct k L *
        typeTableColumnDescendingProduct ell L : Nat) : ENNReal) /
        (typeTableCellFactorialProduct L : ENNReal) := by
  apply (ENNReal.eq_div_iff
    (Nat.cast_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun _ _ =>
        Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _))
    (ENNReal.natCast_ne_top _)).2
  rw [mul_comm]
  exact cast_card_unlabelledSkeleton_fibre_mul_cellFactorials k ell L

/-- Exact profile-facing finite quotient.  The expectation is reindexed over
precisely the attained canonical family, and the physical fibre coefficient,
local reward, ambient normalization, and exact residual attachment all remain
visible. -/
theorem sum_uniformProfile_signedOverlapReward_eq_attainedWeightedQuotient
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat) (hU : 2 ≤ U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row0 column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row0 column).tableNat : ENNReal)) =
      ∑ L ∈ canonicalDemandImage
          (profileBlockMargin k) (profileBlockMargin k) U,
        (((typeTableRowDescendingProduct (profileBlockMargin k) L *
          typeTableColumnDescendingProduct (profileBlockMargin k) L : Nat) :
            ENNReal) / (typeTableCellFactorialProduct L : ENNReal)) *
          profileExactPhysicalTableWeight row0 U L := by
  rw [sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
    row0 U hU]
  rw [← Finset.sum_attach (canonicalDemandImage
    (profileBlockMargin k) (profileBlockMargin k) U)
    (fun L =>
      (((typeTableRowDescendingProduct (profileBlockMargin k) L *
        typeTableColumnDescendingProduct (profileBlockMargin k) L : Nat) :
          ENNReal) / (typeTableCellFactorialProduct L : ENNReal)) *
        profileExactPhysicalTableWeight row0 U L)]
  apply Finset.sum_congr rfl
  intro demand _
  unfold profileHighSkeletonContribution
  rw [profileHighSkeletonWeight_eq_sum_unlabelledSkeletonFibre k U demand]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ennreal_card_unlabelledSkeleton_fibre_eq_descendingProducts_div_cellFactorials]
  simp only [profileExactPhysicalTableWeight, demand.2, dite_true]
  ac_rfl

/-- Fully expanded form of the exact quotient.  Unlike the table-extension
presentation above, this subtype sum displays the local reward, the ambient
stub descending-factorial normalization, the physical fibre quotient, and the
residual attachment as four separate factors. -/
theorem sum_uniformProfile_signedOverlapReward_eq_expandedAttainedWeightedQuotient
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat) (hU : 2 ≤ U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row0 column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row0 column).tableNat : ENNReal)) =
      ∑ demand : ProfileCanonicalHighSkeleton k U,
        (((typeTableRowDescendingProduct (profileBlockMargin k) demand.1 *
          typeTableColumnDescendingProduct (profileBlockMargin k) demand.1 : Nat) :
            ENNReal) / (typeTableCellFactorialProduct demand.1 : ENNReal)) *
          ((canonicalDemandLocalReward demand : ENNReal) /
            (((Finset.univ.sum (profileBlockMargin k)).descFactorial
              (totalDemand demand.1) : Nat) : ENNReal)) *
          profileHighSkeletonAttachment row0 U demand := by
  rw [sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
    row0 U hU]
  apply Finset.sum_congr rfl
  intro demand _
  unfold profileHighSkeletonContribution
  rw [profileHighSkeletonWeight_eq_sum_unlabelledSkeletonFibre k U demand]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ennreal_card_unlabelledSkeleton_fibre_eq_descendingProducts_div_cellFactorials]
  unfold profileHighSkeletonWitnessWeight
  ac_rfl

/-- Transport an explicit pointwise attachment bound through the exact finite
quotient.  This is a weighted-sum inequality only; it asserts no probability
bound and requires no positivity of an event mass. -/
theorem sum_uniformProfile_signedOverlapReward_le_attainedWeightedQuotient_of_attachment_le
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat) (hU : 2 ≤ U)
    (majorant : ProfileCanonicalHighSkeleton k U → ENNReal)
    (hattachment : ∀ demand : ProfileCanonicalHighSkeleton k U,
      profileHighSkeletonAttachment row0 U demand ≤ majorant demand) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row0 column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row0 column).tableNat : ENNReal)) ≤
      ∑ L ∈ canonicalDemandImage
          (profileBlockMargin k) (profileBlockMargin k) U,
        (((typeTableRowDescendingProduct (profileBlockMargin k) L *
          typeTableColumnDescendingProduct (profileBlockMargin k) L : Nat) :
            ENNReal) / (typeTableCellFactorialProduct L : ENNReal)) *
          profileMajorizedPhysicalTableWeight U majorant L := by
  rw [sum_uniformProfile_signedOverlapReward_eq_attainedWeightedQuotient
    row0 U hU]
  apply Finset.sum_le_sum
  intro L hL
  apply mul_le_mul_right
  simp only [profileExactPhysicalTableWeight,
    profileMajorizedPhysicalTableWeight, hL, dite_true]
  apply mul_le_mul_right
  exact hattachment ⟨L, hL⟩

/-- The explicit Section IX polymer specialization of the preceding quotient
bound.  The strict positive-residual premise is exactly the premise required
by the available finite polymer estimate. -/
theorem sum_uniformProfile_signedOverlapReward_le_attainedPolymerWeightedQuotient
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat) (hU : 2 ≤ U)
    (hpositive : ∀ demand : ProfileCanonicalHighSkeleton k U,
      0 < Finset.univ.sum
        (residualRowDegree
          (canonicalDemandReferenceWitness (profileBlockMargin k)
            (profileBlockMargin k) U demand))) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row0 column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row0 column).tableNat : ENNReal)) ≤
      ∑ L ∈ canonicalDemandImage
          (profileBlockMargin k) (profileBlockMargin k) U,
        (((typeTableRowDescendingProduct (profileBlockMargin k) L *
          typeTableColumnDescendingProduct (profileBlockMargin k) L : Nat) :
            ENNReal) / (typeTableCellFactorialProduct L : ENNReal)) *
          profileMajorizedPhysicalTableWeight U
            (canonicalDemandPolymerMajorant
              (profileBlockMargin k) (profileBlockMargin k) U) L := by
  apply sum_uniformProfile_signedOverlapReward_le_attainedWeightedQuotient_of_attachment_le
    row0 U hU
  intro demand
  unfold profileHighSkeletonAttachment canonicalDemandPolymerMajorant
  exact residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct
    (positiveDemandSupport demand.1) (U / 2)
    (residualRowDegree
      (canonicalDemandReferenceWitness (profileBlockMargin k)
        (profileBlockMargin k) U demand))
    (residualColumnDegree
      (canonicalDemandReferenceWitness (profileBlockMargin k)
        (profileBlockMargin k) U demand))
    (sum_residualRowDegree_eq_sum_residualColumnDegree
      (profileBlockMargin_total_eq_self row0)
      (canonicalDemandReferenceWitness (profileBlockMargin k)
        (profileBlockMargin k) U demand))
    (hpositive demand)

#print axioms profileCanonicalHighSkeleton_mem_attainedUnlabelledTypeTables
#print axioms ennreal_card_unlabelledSkeleton_fibre_eq_descendingProducts_div_cellFactorials
#print axioms sum_uniformProfile_signedOverlapReward_eq_attainedWeightedQuotient
#print axioms sum_uniformProfile_signedOverlapReward_eq_expandedAttainedWeightedQuotient
#print axioms sum_uniformProfile_signedOverlapReward_le_attainedWeightedQuotient_of_attachment_le
#print axioms sum_uniformProfile_signedOverlapReward_le_attainedPolymerWeightedQuotient

end

end Erdos625

