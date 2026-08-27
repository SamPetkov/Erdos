import Erdos625.Section8ProfilePartialAggregateWeight
import Erdos625.Section8AttainedAllDeficitReindexing
import Erdos625.Section8PartialCellPhysicalFibre
import Mathlib.Tactic

/-!
# Section VIII: attained four-endpoint partial aggregate weight

This file contains the exact finite bridge from one attained canonical
four-endpoint high demand to the native support/deficit aggregate weight.
It does not state a global skeleton sum, endpoint transport estimate, or
asymptotic conclusion.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The positive actual-block support and its transported abstract
four-endpoint support are exactly equivalent. -/
private noncomputable def fourEndpointDemandSupportEquiv
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    {e // e ∈ positiveDemandSupport demand.1} ≃
      {e // e ∈ (fourEndpointDemandBlockPairing
        alpha hAlpha k hcover slotIndex demand).1.edges} where
  toFun e := by
    refine ⟨(fourEndpointAtomOfProfileBlock
        alpha hAlpha k hcover slotIndex e.1.1,
      fourEndpointAtomOfProfileBlock
        alpha hAlpha k hcover slotIndex e.1.2), ?_⟩
    change
      (fourEndpointAtomOfProfileBlock
          alpha hAlpha k hcover slotIndex e.1.1,
        fourEndpointAtomOfProfileBlock
          alpha hAlpha k hcover slotIndex e.1.2) ∈
        fourEndpointDemandBlockEdges
          alpha hAlpha k hcover slotIndex demand
    rw [fourEndpointDemandBlockEdges, Finset.mem_image]
    exact ⟨e.1, e.2, rfl⟩
  invFun e := by
    refine ⟨(fourEndpointActualBlockOfAtom
        alpha hAlpha k slotIndex e.1.1,
      fourEndpointActualBlockOfAtom
        alpha hAlpha k slotIndex e.1.2), ?_⟩
    apply (mem_fourEndpointDemandBlockEdges_iff
      alpha hAlpha k hcover slotIndex demand e.1).mp
    change e.1 ∈ fourEndpointDemandBlockEdges
      alpha hAlpha k hcover slotIndex demand
    exact e.2
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · exact fourEndpointActualBlock_atomOfProfileBlock
        alpha hAlpha k hcover slotIndex e.1.1
    · exact fourEndpointActualBlock_atomOfProfileBlock
        alpha hAlpha k hcover slotIndex e.1.2
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · exact fourEndpointAtomOfProfileBlock_actualBlock
        alpha hAlpha k hcover slotIndex e.1.1
    · exact fourEndpointAtomOfProfileBlock_actualBlock
        alpha hAlpha k hcover slotIndex e.1.2

private theorem supportEquiv_actualBlock_fst
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : {e // e ∈ positiveDemandSupport demand.1}) :
    fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex
        ((fourEndpointDemandSupportEquiv
          alpha hAlpha k hcover slotIndex demand e).1.1) =
      e.1.1 := by
  change
    fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex
        (fourEndpointAtomOfProfileBlock
          alpha hAlpha k hcover slotIndex e.1.1) =
      e.1.1
  exact fourEndpointActualBlock_atomOfProfileBlock
    alpha hAlpha k hcover slotIndex e.1.1

private theorem supportEquiv_actualBlock_snd
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : {e // e ∈ positiveDemandSupport demand.1}) :
    fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex
        ((fourEndpointDemandSupportEquiv
          alpha hAlpha k hcover slotIndex demand e).1.2) =
      e.1.2 := by
  change
    fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex
        (fourEndpointAtomOfProfileBlock
          alpha hAlpha k hcover slotIndex e.1.2) =
      e.1.2
  exact fourEndpointActualBlock_atomOfProfileBlock
    alpha hAlpha k hcover slotIndex e.1.2

private theorem supportEquiv_rowMargin
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : {e // e ∈ positiveDemandSupport demand.1}) :
    profileBlockMargin k e.1.1 =
      fourEndpointSize alpha hAlpha
        ((fourEndpointDemandSupportEquiv
          alpha hAlpha k hcover slotIndex demand e).1.1).1 := by
  have h := profileBlockMargin_fourEndpointActualBlockOfAtom
    alpha hAlpha k slotIndex
      ((fourEndpointDemandSupportEquiv
        alpha hAlpha k hcover slotIndex demand e).1.1)
  rw [supportEquiv_actualBlock_fst
    alpha hAlpha k hcover slotIndex demand e] at h
  exact h

private theorem supportEquiv_columnMargin
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : {e // e ∈ positiveDemandSupport demand.1}) :
    profileBlockMargin k e.1.2 =
      fourEndpointSize alpha hAlpha
        ((fourEndpointDemandSupportEquiv
          alpha hAlpha k hcover slotIndex demand e).1.2).1 := by
  have h := profileBlockMargin_fourEndpointActualBlockOfAtom
    alpha hAlpha k slotIndex
      ((fourEndpointDemandSupportEquiv
        alpha hAlpha k hcover slotIndex demand e).1.2)
  rw [supportEquiv_actualBlock_snd
    alpha hAlpha k hcover slotIndex demand e] at h
  exact h

private theorem supportEquiv_cellMultiplicity
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : {e // e ∈ positiveDemandSupport demand.1}) :
    fourEndpointCellMultiplicityOfDeficit alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandSupportEquiv
          alpha hAlpha k hcover slotIndex demand e) =
      demand.1 e.1.1 e.1.2 := by
  have h := fourEndpointCellMultiplicity_demandDeficit_eq
    alpha hAlpha k hcover slotIndex demand
      (fourEndpointDemandSupportEquiv
        alpha hAlpha k hcover slotIndex demand e)
  rw [supportEquiv_actualBlock_fst
      alpha hAlpha k hcover slotIndex demand e,
    supportEquiv_actualBlock_snd
      alpha hAlpha k hcover slotIndex demand e] at h
  exact h

private theorem matchingDemandCellSelectionProduct_eq_fourEndpoint
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    matchingDemandCellSelectionProduct demand.1
        (profileBlockMargin k) (profileBlockMargin k) =
      fourEndpointPartialCellSelectionProduct alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) := by
  classical
  unfold matchingDemandCellSelectionProduct
    fourEndpointPartialCellSelectionProduct
  apply Fintype.prod_equiv
    (fourEndpointDemandSupportEquiv
      alpha hAlpha k hcover slotIndex demand)
  intro e
  rw [supportEquiv_rowMargin
      alpha hAlpha k hcover slotIndex demand e,
    supportEquiv_columnMargin
      alpha hAlpha k hcover slotIndex demand e,
    supportEquiv_cellMultiplicity
      alpha hAlpha k hcover slotIndex demand e]

private theorem matchingDemandCellFactorialProduct_eq_fourEndpoint
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    matchingDemandCellFactorialProduct demand.1 =
      fourEndpointPartialCellFactorialProduct alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) := by
  classical
  unfold matchingDemandCellFactorialProduct
    fourEndpointPartialCellFactorialProduct
  apply Fintype.prod_equiv
    (fourEndpointDemandSupportEquiv
      alpha hAlpha k hcover slotIndex demand)
  intro e
  rw [supportEquiv_cellMultiplicity
    alpha hAlpha k hcover slotIndex demand e]

private theorem canonicalDemandLocalReward_eq_fourEndpoint
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    (canonicalDemandLocalReward demand : ENNReal) =
      fourEndpointPartialRewardProduct alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) := by
  classical
  unfold canonicalDemandLocalReward fourEndpointPartialRewardProduct
  rw [Nat.cast_prod]
  calc
    (∏ e ∈ positiveDemandSupport demand.1,
        (localSignRewardNat (demand.1 e.1 e.2) : ENNReal)) =
        ∏ e : {e // e ∈ positiveDemandSupport demand.1},
          (localSignRewardNat (demand.1 e.1.1 e.1.2) : ENNReal) := by
      symm
      rw [show
        (Finset.univ :
          Finset {e // e ∈ positiveDemandSupport demand.1}) =
            (positiveDemandSupport demand.1).attach by
        ext e
        simp]
      rw [Finset.prod_attach
        (s := positiveDemandSupport demand.1)
        (f := fun e =>
          (localSignRewardNat (demand.1 e.1 e.2) : ENNReal))]
    _ = ∏ e :
          {e // e ∈ (fourEndpointDemandBlockPairing
            alpha hAlpha k hcover slotIndex demand).1.edges},
          (localSignRewardNat
            (fourEndpointCellMultiplicityOfDeficit alpha hAlpha
              (fourEndpointDemandBlockPairing
                alpha hAlpha k hcover slotIndex demand)
              (fourEndpointDemandDeficit
                alpha hAlpha k hcover slotIndex demand) e) : ENNReal) := by
      apply Fintype.prod_equiv
        (fourEndpointDemandSupportEquiv
          alpha hAlpha k hcover slotIndex demand)
      intro e
      rw [supportEquiv_cellMultiplicity
        alpha hAlpha k hcover slotIndex demand e]

private theorem totalDemand_eq_fourEndpointPartialTotalMultiplicity
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    totalDemand demand.1 =
      fourEndpointPartialTotalMultiplicity alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) := by
  classical
  have hsupport :
      totalDemand demand.1 =
        ∑ e : {e // e ∈ positiveDemandSupport demand.1},
          demand.1 e.1.1 e.1.2 := by
    unfold totalDemand
    rw [show
      (Finset.univ :
        Finset {e // e ∈ positiveDemandSupport demand.1}) =
          (positiveDemandSupport demand.1).attach by
      ext e
      simp]
    rw [Finset.sum_attach
      (s := positiveDemandSupport demand.1)
      (f := fun e => demand.1 e.1 e.2)]
    rw [← Fintype.sum_prod_type']
    unfold positiveDemandSupport
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e _he hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    exact not_ne_iff.mp hnot
  rw [hsupport]
  unfold fourEndpointPartialTotalMultiplicity
  apply Fintype.sum_equiv
    (fourEndpointDemandSupportEquiv
      alpha hAlpha k hcover slotIndex demand)
  intro e
  rw [supportEquiv_cellMultiplicity
    alpha hAlpha k hcover slotIndex demand e]

private theorem profileHighSkeletonWitnessWeight_eq_fourEndpointPartialAtomWeight
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    profileHighSkeletonWitnessWeight k
        (fourEndpointLargestSize alpha hAlpha) demand =
      fourEndpointPartialAtomWeight
        (Finset.univ.sum (profileBlockMargin k))
        alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) := by
  unfold profileHighSkeletonWitnessWeight
    fourEndpointPartialAtomWeight
  rw [canonicalDemandLocalReward_eq_fourEndpoint
      alpha hAlpha k hcover slotIndex demand,
    totalDemand_eq_fourEndpointPartialTotalMultiplicity
      alpha hAlpha k hcover slotIndex demand]

/-- The bare weight of one attained four-endpoint demand is exactly the
aggregate weight of its literal partial-cell fibre, indexed by its transported
block pairing and canonical deficit vector. -/
theorem profileHighSkeletonWeight_eq_fourEndpointPartialAggregateWeight
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand =
      fourEndpointPartialAggregateWeight
        (Finset.univ.sum (profileBlockMargin k))
        alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) := by
  rw [profileHighSkeletonWeight_eq_matchingDemandCellAggregateWeight_of_cap
    k (fourEndpointLargestSize alpha hAlpha)
      (profileBlockMargin_le_fourEndpointLargest_of_cover
        alpha hAlpha k hcover) demand]
  unfold matchingDemandCellAggregateWeight
    fourEndpointPartialAggregateWeight
  rw [matchingDemandCellSelectionProduct_eq_fourEndpoint
      alpha hAlpha k hcover slotIndex demand,
    matchingDemandCellFactorialProduct_eq_fourEndpoint
      alpha hAlpha k hcover slotIndex demand,
    profileHighSkeletonWitnessWeight_eq_fourEndpointPartialAtomWeight
      alpha hAlpha k hcover slotIndex demand]

end

end Erdos625
