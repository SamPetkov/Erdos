import Erdos625.Section8FourEndpointFullReferenceComparison
import Erdos625.Section8DirectReferenceGrouping

/-!
# Section VIII: encoded full-support charge

This file gives the exact comparison connecting one attained
canonical high-skeleton weight to the full-support reference carried by its
optional-deficit encoding. It is deliberately pointwise: no support sum,
endpoint-table transport, phase estimate, or asymptotic conclusion belongs
here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

private theorem prod_over_fourEndpointSupport_eq_typeTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (f : Fin 4 → Fin 4 → ENNReal) :
    (∏ e : ↥P.edges, f e.1.1.1 e.1.2.1) =
      ∏ i : Fin 4, ∏ j : Fin 4, (f i j) ^ P.typeTable i j := by
  classical
  rw [← Finset.prod_subtype P.edges (fun _ => Iff.rfl)
    (fun e => f e.1.1 e.2.1)]
  rw [← Finset.prod_fiberwise' P.edges
    (fun e => (e.1.1, e.2.1))
    (fun ij : Fin 4 × Fin 4 => f ij.1 ij.2)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_const]
  apply congrArg (fun count => (f i j) ^ count)
  calc
    (P.edges.filter (fun e => (e.1.1, e.2.1) = (i, j))).card =
        (P.edges.filter
          (fun e => e.1.1 = i ∧ e.2.1 = j)).card := by
      congr 1
      ext e
      simp [Prod.ext_iff]
    _ = P.typeTable i j := rfl

private theorem sum_over_fourEndpointSupport_eq_typeTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (f : Fin 4 → Fin 4 → Nat) :
    (∑ e : ↥P.edges, f e.1.1.1 e.1.2.1) =
      ∑ i : Fin 4, ∑ j : Fin 4, f i j * P.typeTable i j := by
  classical
  rw [← Finset.sum_subtype P.edges (fun _ => Iff.rfl)
    (fun e => f e.1.1 e.2.1)]
  rw [← Finset.sum_fiberwise' P.edges
    (fun e => (e.1.1, e.2.1))
    (fun ij : Fin 4 × Fin 4 => f ij.1 ij.2)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm]
  apply congrArg (fun count => f i j * count)
  calc
    (P.edges.filter (fun e => (e.1.1, e.2.1) = (i, j))).card =
        (P.edges.filter
          (fun e => e.1.1 = i ∧ e.2.1 = j)).card := by
      congr 1
      ext e
      simp [Prod.ext_iff]
    _ = P.typeTable i j := rfl

private theorem fourEndpointPartialZeroAtomWeight_eq_decoratedReferenceAtomWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L) :
    fourEndpointPartialAtomWeight n alpha hAlpha P (fun _ => 0) =
      fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L := by
  have hprod := prod_over_fourEndpointSupport_eq_typeTable alpha hAlpha P.1
    (fun i j =>
      (localSignRewardNat
        (fourEndpointOverlapSize alpha hAlpha i j) : ENNReal))
  have hsum := sum_over_fourEndpointSupport_eq_typeTable alpha hAlpha P.1
    (fourEndpointOverlapSize alpha hAlpha)
  rw [P.2] at hprod hsum
  unfold fourEndpointPartialAtomWeight fourEndpointPartialRewardProduct
    fourEndpointPartialTotalMultiplicity
    fourEndpointCellMultiplicityOfDeficit fourEndpointCellFullMultiplicity
    fourEndpointDecoratedReferenceAtomWeight fourEndpointFullRewardProduct
    fourEndpointJ
  simp only [Nat.sub_zero]
  rw [hprod, hsum]

private theorem fourEndpointPartialZeroAtomWeight_eq_fullSupportAtomWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    fourEndpointPartialAtomWeight n alpha hAlpha
        (fourEndpointBlockPairingOfSupport alpha hAlpha P) (fun _ => 0) =
      fourEndpointFullSupportAtomWeight n alpha hAlpha P := by
  unfold fourEndpointFullSupportAtomWeight
  exact fourEndpointPartialZeroAtomWeight_eq_decoratedReferenceAtomWeight
    n alpha hAlpha (fourEndpointBlockPairingOfSupport alpha hAlpha P)

private theorem fourEndpointPartialAggregateWeight_zero_eq_fullSupportReferenceWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    fourEndpointPartialAggregateWeight n alpha hAlpha
        (fourEndpointBlockPairingOfSupport alpha hAlpha P) (fun _ => 0) =
      fourEndpointFullSupportReferenceWeight n alpha hAlpha P := by
  rw [← sum_fourEndpointPartialAtomWeight_eq_aggregateWeight]
  unfold fourEndpointFullSupportReferenceWeight
  change
    (∑ _ : FourEndpointFullDecorationOfSupport alpha hAlpha P,
      fourEndpointPartialAtomWeight n alpha hAlpha
        (fourEndpointBlockPairingOfSupport alpha hAlpha P) (fun _ => 0)) =
      ∑ _ : FourEndpointFullDecorationOfSupport alpha hAlpha P,
        fourEndpointFullSupportAtomWeight n alpha hAlpha P
  rw [fourEndpointPartialZeroAtomWeight_eq_fullSupportAtomWeight]

private theorem fourEndpointDemandEncodedChoiceWeight_eq_deficitCharge
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    nearSkeletonChoiceWeight
        (fourEndpointHalfDeficitAllowed alpha hAlpha
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand).1)
        (fourEndpointHalfDeficitWeight n alpha hAlpha
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand).1)
        (fourEndpointDemandSupportChoiceEncoding
          alpha hAlpha k hcover slotIndex demand).2 =
      ∏ e : ↥(fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand).1.edges,
        nearCellTerm n
          (fourEndpointCellFullMultiplicity alpha hAlpha
            (fourEndpointDemandBlockPairing
              alpha hAlpha k hcover slotIndex demand) e)
          (Nat.dist e.1.1.1.val e.1.2.1.val)
          (fourEndpointDemandDeficit
            alpha hAlpha k hcover slotIndex demand e) := by
  classical
  unfold nearSkeletonChoiceWeight
  apply Finset.prod_congr rfl
  intro e _
  by_cases hz :
      fourEndpointDemandDeficit
        alpha hAlpha k hcover slotIndex demand e = 0
  · simp [fourEndpointDemandSupportChoiceEncoding,
      fourEndpointSupportDeficitToChoiceData,
      fourEndpointSupportDeficitToChoice,
      fourEndpointDemandSupportDeficitEncoding,
      fourEndpointCellFullMultiplicity, hz, nearCellTerm]
  · simp [fourEndpointDemandSupportChoiceEncoding,
      fourEndpointSupportDeficitToChoiceData,
      fourEndpointSupportDeficitToChoice,
      fourEndpointDemandSupportDeficitEncoding,
      fourEndpointHalfDeficitWeight, fourEndpointCellFullMultiplicity, hz]

theorem profileHighSkeletonWeight_le_fourEndpointEncodedFullSupportCharge
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand ≤
      fourEndpointSupportChoiceChargedWeight
        (Finset.univ.sum (profileBlockMargin k))
        alpha hAlpha
        (fourEndpointFullSupportReferenceWeight
          (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha)
        (fourEndpointDemandSupportChoiceEncoding
          alpha hAlpha k hcover slotIndex demand) := by
  have hsupport :
      (fourEndpointDemandSupportChoiceEncoding
        alpha hAlpha k hcover slotIndex demand).1 =
        fourEndpointDemandBlockSkeleton
          alpha hAlpha k hcover slotIndex demand := by
    simp [fourEndpointDemandSupportChoiceEncoding,
      fourEndpointSupportDeficitToChoiceData,
      fourEndpointDemandSupportDeficitEncoding]
  have hpairing :
      fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand =
        fourEndpointBlockPairingOfSupport alpha hAlpha
          (fourEndpointDemandBlockSkeleton
            alpha hAlpha k hcover slotIndex demand) := by
    apply Subtype.ext
    rfl
  have hreference :
      fourEndpointPartialAggregateWeight
          (Finset.univ.sum (profileBlockMargin k))
          alpha hAlpha
          (fourEndpointDemandBlockPairing
            alpha hAlpha k hcover slotIndex demand)
          (fun _ => 0) =
        fourEndpointFullSupportReferenceWeight
          (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand).1 := by
    rw [hsupport, hpairing]
    exact
      fourEndpointPartialAggregateWeight_zero_eq_fullSupportReferenceWeight
        (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha
        (fourEndpointDemandBlockSkeleton
          alpha hAlpha k hcover slotIndex demand)
  calc
    profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand ≤
      fourEndpointPartialAggregateWeight
          (Finset.univ.sum (profileBlockMargin k))
          alpha hAlpha
          (fourEndpointDemandBlockPairing
            alpha hAlpha k hcover slotIndex demand)
          (fun _ => 0) *
        ∏ e : ↥(fourEndpointDemandBlockPairing
            alpha hAlpha k hcover slotIndex demand).1.edges,
          nearCellTerm
            (Finset.univ.sum (profileBlockMargin k))
            (fourEndpointCellFullMultiplicity alpha hAlpha
              (fourEndpointDemandBlockPairing
                alpha hAlpha k hcover slotIndex demand) e)
            (Nat.dist e.1.1.1.val e.1.2.1.val)
            (fourEndpointDemandDeficit
              alpha hAlpha k hcover slotIndex demand e) :=
      profileHighSkeletonWeight_le_fourEndpointFullReference_mul_deficitCharge
        alpha hAlpha hHigh k hcover slotIndex demand
    _ = fourEndpointSupportChoiceChargedWeight
        (Finset.univ.sum (profileBlockMargin k))
        alpha hAlpha
        (fourEndpointFullSupportReferenceWeight
          (Finset.univ.sum (profileBlockMargin k)) alpha hAlpha)
        (fourEndpointDemandSupportChoiceEncoding
          alpha hAlpha k hcover slotIndex demand) := by
      rw [hreference]
      unfold fourEndpointSupportChoiceChargedWeight
      rw [fourEndpointDemandEncodedChoiceWeight_eq_deficitCharge]

#print axioms profileHighSkeletonWeight_le_fourEndpointEncodedFullSupportCharge

end

end Erdos625
