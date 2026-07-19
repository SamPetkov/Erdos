import Erdos625.Section9SignedOverlapCanonicalDecomposition
import Erdos625.Section8WeightedSkeletonQuotient
import Mathlib.Tactic

/-!
# Section VIII: exact profile high-skeleton weights

For one fixed ordered profile, this module packages the bare high-skeleton
factor from manuscript (8.3): the product of the exposed local rewards times
the normalized incidence of its labelled prescribed-demand witnesses.  It
then reindexes that finite weight through literal typed partial matchings and
through the physical unlabelled-skeleton fibre of its type table.

The last two theorems compose this reindexing with the exact canonical
decomposition from Section IX.  They retain the residual attachment as an
explicit finite factor.  In particular, this file proves no near/middle
estimate, no attachment bound, and no asymptotic form of Lemma 8.3.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The finite family of high-demand tables that are actually attained by a
configuration matching with the fixed profile margins.  This is deliberately
an attained family: no unsupported feasibility relaxation is made here. -/
abbrev ProfileCanonicalHighSkeleton
    {b : Nat} (k : ColoringProfile b) (U : Nat) :=
  canonicalDemandImage (profileBlockMargin k) (profileBlockMargin k) U

/-- The bare high-skeleton weight for one attained profile demand.  The first
factor is the exposed local signed reward; the second is the normalized count
of labelled physical realizations.  This is the exact finite counterpart of
the weight `w_hi` in (8.3), with no residual attachment included. -/
noncomputable def profileHighSkeletonWeight
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) : ENNReal :=
  (canonicalDemandLocalReward demand : ENNReal) *
    labelledWitnessIncidence demand.1 (profileBlockMargin k)
      (profileBlockMargin k)

/-- The contribution of one labelled physical realization of an attained
profile high skeleton.  Summing this constant over all labelled witnesses
recovers `profileHighSkeletonWeight`. -/
noncomputable def profileHighSkeletonWitnessWeight
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) : ENNReal :=
  (canonicalDemandLocalReward demand : ENNReal) /
    (((Finset.univ.sum (profileBlockMargin k)).descFactorial
      (totalDemand demand.1) : Nat) : ENNReal)

/-- An attained profile high-demand table has total demand at most the total
profile vertex mass.  The conclusion is obtained from an actual labelled
witness; it is not assumed as a separate numerical feasibility condition. -/
theorem profileHighSkeleton_totalDemand_le
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) :
    totalDemand demand.1 <= Finset.univ.sum (profileBlockMargin k) := by
  exact totalDemand_le_rowTotal_of_witness
    (canonicalDemandReferenceWitness (profileBlockMargin k)
      (profileBlockMargin k) U demand)

/-- The completely expanded falling-factorial form of the bare profile
high-skeleton weight.  The feasibility premise needed by the incidence
identity is discharged by `profileHighSkeleton_totalDemand_le`. -/
theorem profileHighSkeletonWeight_eq_descendingFactorials
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) :
    profileHighSkeletonWeight k U demand =
      (canonicalDemandLocalReward demand : ENNReal) *
        (((rowDescendingProduct demand.1 (profileBlockMargin k) *
          columnDescendingProduct demand.1 (profileBlockMargin k) : Nat) :
            ENNReal) /
          (((Finset.univ.sum (profileBlockMargin k)).descFactorial
            (totalDemand demand.1) * demandFactorialProduct demand.1 : Nat) :
              ENNReal)) := by
  unfold profileHighSkeletonWeight
  rw [labelledWitnessIncidence_eq demand.1 (profileBlockMargin k)
    (profileBlockMargin k) (profileHighSkeleton_totalDemand_le k U demand)]

/-- Reindex one bare profile high-skeleton weight over its literal typed
partial matchings.  The equivalence with prescribed-demand witnesses is used
only to identify the finite cardinality; no probability law is invoked. -/
theorem profileHighSkeletonWeight_eq_sum_typedPartialMatching
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) :
    profileHighSkeletonWeight k U demand =
      ∑ _ : TypedPartialMatching demand.1 (profileBlockMargin k)
        (profileBlockMargin k), profileHighSkeletonWitnessWeight k U demand := by
  unfold profileHighSkeletonWeight profileHighSkeletonWitnessWeight
    labelledWitnessIncidence
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_congr
    (typedPartialMatchingEquivPrescribedDemandWitness demand.1
      (profileBlockMargin k) (profileBlockMargin k))]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp only [mul_left_comm]

/-- Reindex one bare profile high-skeleton weight through the exact fibre of
the physical unlabelled skeleton map.  This is the finite quotient seam that
keeps the labelled-witness multiplicity honest. -/
theorem profileHighSkeletonWeight_eq_sum_unlabelledSkeletonFibre
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) :
    profileHighSkeletonWeight k U demand =
      ∑ _ : {S : UnlabelledTypedSkeleton (profileBlockMargin k)
        (profileBlockMargin k) // S.typeTable = demand.1},
          profileHighSkeletonWitnessWeight k U demand := by
  calc
    profileHighSkeletonWeight k U demand =
        ∑ _ : TypedPartialMatching demand.1 (profileBlockMargin k)
          (profileBlockMargin k), profileHighSkeletonWitnessWeight k U demand :=
      profileHighSkeletonWeight_eq_sum_typedPartialMatching k U demand
    _ = ∑ _ : {S : UnlabelledTypedSkeleton (profileBlockMargin k)
          (profileBlockMargin k) // S.typeTable = demand.1},
          profileHighSkeletonWitnessWeight k U demand := by
      simpa using
        (sum_typedPartialMatching_skeletonWeight_eq_sum_unlabelledSkeletonFibre
          demand.1 (profileBlockMargin k) (profileBlockMargin k)
          (fun _ => profileHighSkeletonWitnessWeight k U demand))

/-- With an explicit profile degree cap, the positive support of every
attained high skeleton is a bipartite matching.  This is the exact structural
hypothesis used by the later Section VIII near/middle split. -/
theorem profileHighSkeleton_positiveSupport_isBipartiteMatching
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (hcap : forall a : ProfileBlockIndex k, profileBlockMargin k a <= U)
    (demand : ProfileCanonicalHighSkeleton k U) :
    IsBipartiteMatching (positiveDemandSupport demand.1) := by
  exact positiveDemandSupport_isBipartiteMatching_of_canonicalDemandImage
    U hcap hcap demand

/-- The exact residual attachment belonging to one attained profile high
skeleton.  The fixed row is retained to make the equal-total-degree proof
term explicit, even though the value depends only on the profile margins. -/
noncomputable def profileHighSkeletonAttachment
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) : ENNReal :=
  residualActualAttachmentNumerator
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

/-- One exact canonical high-skeleton contribution: its bare Section VIII
weight times its Section IX residual attachment. -/
noncomputable def profileHighSkeletonContribution
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U) : ENNReal :=
  profileHighSkeletonWeight k U demand *
    profileHighSkeletonAttachment row0 U demand

/-- The profile signed-overlap expectation reindexed exactly by attained
canonical high skeletons.  `hU` is explicit because the underlying reward/
support split uses it to identify positive demands with multiplicity-two
support edges. -/
theorem sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat) (hU : 2 <= U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row0 column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row0 column).tableNat : ENNReal)) =
      ∑ demand : ProfileCanonicalHighSkeleton k U,
        profileHighSkeletonContribution row0 U demand := by
  simpa only [profileHighSkeletonContribution, profileHighSkeletonWeight,
    profileHighSkeletonAttachment, mul_assoc] using
    (sum_uniformProfile_signedOverlapReward_eq_skeletonAttachmentSum row0 U hU)

/-- Reindex the exact canonical skeleton/attachment sum through the physical
unlabelled-skeleton fibre of each attained demand table.  The attachment is
kept unchanged across a fibre because the canonical decomposition already
standardizes it by a reference witness. -/
theorem sum_profileHighSkeletonContribution_eq_sum_unlabelledSkeletonFibre
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat) :
    (∑ demand : ProfileCanonicalHighSkeleton k U,
      profileHighSkeletonContribution row0 U demand) =
      ∑ demand : ProfileCanonicalHighSkeleton k U,
        ∑ _ : {S : UnlabelledTypedSkeleton (profileBlockMargin k)
          (profileBlockMargin k) // S.typeTable = demand.1},
          profileHighSkeletonWitnessWeight k U demand *
            profileHighSkeletonAttachment row0 U demand := by
  apply Finset.sum_congr rfl
  intro demand _
  unfold profileHighSkeletonContribution
  rw [profileHighSkeletonWeight_eq_sum_unlabelledSkeletonFibre k U demand]
  rw [Finset.sum_mul]

/-- The strongest finite profile-facing reindexing supplied here: the exact
signed-overlap expectation is a double finite sum over attained demand tables
and their physical unlabelled high-skeleton fibres.  No bound on this sum is
asserted. -/
theorem sum_uniformProfile_signedOverlapReward_eq_sum_profilePhysicalHighSkeletonContribution
    {b n : Nat} {k : ColoringProfile b}
    (row0 : OrderedProfilePartition n k) (U : Nat) (hU : 2 <= U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row0 column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row0 column).tableNat : ENNReal)) =
      ∑ demand : ProfileCanonicalHighSkeleton k U,
        ∑ _ : {S : UnlabelledTypedSkeleton (profileBlockMargin k)
          (profileBlockMargin k) // S.typeTable = demand.1},
          profileHighSkeletonWitnessWeight k U demand *
            profileHighSkeletonAttachment row0 U demand := by
  calc
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row0 column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row0 column).tableNat : ENNReal)) =
        ∑ demand : ProfileCanonicalHighSkeleton k U,
          profileHighSkeletonContribution row0 U demand :=
      sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
        row0 U hU
    _ = _ :=
      sum_profileHighSkeletonContribution_eq_sum_unlabelledSkeletonFibre row0 U

#print axioms profileHighSkeleton_totalDemand_le
#print axioms profileHighSkeletonWeight_eq_descendingFactorials
#print axioms profileHighSkeletonWeight_eq_sum_typedPartialMatching
#print axioms profileHighSkeletonWeight_eq_sum_unlabelledSkeletonFibre
#print axioms profileHighSkeleton_positiveSupport_isBipartiteMatching
#print axioms sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
#print axioms sum_profileHighSkeletonContribution_eq_sum_unlabelledSkeletonFibre
#print axioms sum_uniformProfile_signedOverlapReward_eq_sum_profilePhysicalHighSkeletonContribution

end

end Erdos625
