import Erdos625.Section8CanonicalThreeQuarterRho
import Erdos625.Section8DirectReferenceGrouping
import Mathlib.Tactic

/-!
# Section VIII: finite bare-skeleton reduction

This module combines the simplified finite interfaces.  For an abstract
endpoint block support, the number of selected block cells is at most the total
number of row blocks.  Hence the coarse optional-deficit factor may be replaced
by one common power.

The endpoint-table index is the finite attained image of the support space,
not the infinite type of all `Nat`-valued four-by-four tables.  Direct reference
grouping then replaces the remaining support sum by the attained-table sum of
`fourEndpointW`.

The canonical common local base is the sum of the sixteen endpoint-type bases.
Thus the final canonical theorem has only two nontrivial premises:

* a pointwise charged comparison for one attained demand;
* smallness of one explicit sixteen-term quantity.

No asymptotic statement is made here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- A physical typed partial matching has no more edges than available row
stubs. -/
theorem UnlabelledTypedSkeleton.edges_card_le_rowTotal
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {row : I → Nat} {col : J → Nat}
    (S : UnlabelledTypedSkeleton row col) :
    S.edges.card ≤ Finset.univ.sum row := by
  have hinj : Set.InjOn (fun e : RowStub row × ColumnStub col => e.1)
      (↑S.edges : Set (RowStub row × ColumnStub col)) := by
    intro e₁ he₁ e₂ he₂ hfirst
    exact S.leftUnique e₁ (by simpa using he₁) e₂ (by simpa using he₂) hfirst
  have hcard : (S.edges.image fun e => e.1).card = S.edges.card := by
    rw [Finset.card_image_of_injOn]
    exact hinj
  calc
    S.edges.card = (S.edges.image fun e => e.1).card := hcard.symm
    _ ≤ (Finset.univ : Finset (RowStub row)).card := by
      apply Finset.card_le_card
      exact Finset.subset_univ _
    _ = Fintype.card (RowStub row) := Finset.card_univ
    _ = Finset.univ.sum row := card_rowStub row

/-- Total number of row block slots in the four endpoint types. -/
def fourEndpointTotalBlockCount
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) : Nat :=
  ∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i

/-- Every abstract block matching has at most the total number of block slots. -/
theorem fourEndpointAbstractBlockSkeleton_edges_card_le
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k) :
    P.edges.card ≤ fourEndpointTotalBlockCount alpha hAlpha k := by
  simpa only [fourEndpointTotalBlockCount] using
    P.edges_card_le_rowTotal

/-- Generic finite endpoint with an arbitrary common local base. -/
theorem sum_profileCanonicalHighSkeleton_le_commonDeficitFactor_mul_sum_W
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (weightDemand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha) → ENNReal)
    (rho : ENNReal) (hrho : rho ≤ 1)
    (hweight : ∀ demand,
      weightDemand demand ≤
        fourEndpointSupportChoiceChargedWeight n alpha hAlpha
          (fourEndpointFullSupportReferenceWeight n alpha hAlpha)
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand))
    (hbase : ∀ (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
        (cell : ↥P.edges),
      threeQuarterCellBase n
        (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1) ≤ rho) :
    (∑ demand, weightDemand demand) ≤
      (∑ L : FourEndpointAttainedFullTable alpha hAlpha k,
        fourEndpointW n alpha hAlpha k L.1) *
      (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^
        fourEndpointTotalBlockCount alpha hAlpha k := by
  let common : ENNReal :=
    (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^
      fourEndpointTotalBlockCount alpha hAlpha k
  calc
    (∑ demand, weightDemand demand) ≤
        ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          fourEndpointFullSupportReferenceWeight n alpha hAlpha P *
            (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^ P.edges.card :=
      sum_profileCanonicalHighSkeleton_le_uniformHalfDeficitSupportSum
        n alpha hAlpha k hcover slotIndex weightDemand
          (fourEndpointFullSupportReferenceWeight n alpha hAlpha)
          rho hrho hweight hbase
    _ ≤ ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          fourEndpointFullSupportReferenceWeight n alpha hAlpha P * common := by
      apply Finset.sum_le_sum
      intro P _
      exact mul_le_mul_left
        (pow_le_pow_right₀ (by simp [common])
          (fourEndpointAbstractBlockSkeleton_edges_card_le alpha hAlpha P))
        (fourEndpointFullSupportReferenceWeight n alpha hAlpha P)
    _ = (∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          fourEndpointFullSupportReferenceWeight n alpha hAlpha P) * common := by
      rw [Finset.sum_mul]
    _ = (∑ L : FourEndpointAttainedFullTable alpha hAlpha k,
          fourEndpointW n alpha hAlpha k L.1) * common := by
      rw [sum_fourEndpointFullSupportReferenceWeight_eq_sum_attained_W]
    _ = _ := by rfl

/-- Canonical finite endpoint.  The support-dependent local-base premise has
been discharged by the explicit sum of the sixteen endpoint-type bases. -/
theorem sum_profileCanonicalHighSkeleton_le_canonicalDeficitFactor_mul_sum_W
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (weightDemand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha) → ENNReal)
    (hrho : fourEndpointThreeQuarterRho n alpha hAlpha ≤ 1)
    (hweight : ∀ demand,
      weightDemand demand ≤
        fourEndpointSupportChoiceChargedWeight n alpha hAlpha
          (fourEndpointFullSupportReferenceWeight n alpha hAlpha)
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand)) :
    (∑ demand, weightDemand demand) ≤
      (∑ L : FourEndpointAttainedFullTable alpha hAlpha k,
        fourEndpointW n alpha hAlpha k L.1) *
      (1 + ((alpha + 1 : Nat) : ENNReal) *
        fourEndpointThreeQuarterRho n alpha hAlpha) ^
          fourEndpointTotalBlockCount alpha hAlpha k := by
  let common : ENNReal :=
    (1 + ((alpha + 1 : Nat) : ENNReal) *
      fourEndpointThreeQuarterRho n alpha hAlpha) ^
        fourEndpointTotalBlockCount alpha hAlpha k
  calc
    (∑ demand, weightDemand demand) ≤
        ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          fourEndpointFullSupportReferenceWeight n alpha hAlpha P *
            (1 + ((alpha + 1 : Nat) : ENNReal) *
              fourEndpointThreeQuarterRho n alpha hAlpha) ^ P.edges.card :=
      sum_profileCanonicalHighSkeleton_le_canonicalThreeQuarterRhoSupportSum
        n alpha hAlpha k hcover slotIndex weightDemand
          (fourEndpointFullSupportReferenceWeight n alpha hAlpha)
          hrho hweight
    _ ≤ ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          fourEndpointFullSupportReferenceWeight n alpha hAlpha P * common := by
      apply Finset.sum_le_sum
      intro P _
      exact mul_le_mul_left
        (pow_le_pow_right₀ (by simp [common])
          (fourEndpointAbstractBlockSkeleton_edges_card_le alpha hAlpha P))
        (fourEndpointFullSupportReferenceWeight n alpha hAlpha P)
    _ = (∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          fourEndpointFullSupportReferenceWeight n alpha hAlpha P) * common := by
      rw [Finset.sum_mul]
    _ = (∑ L : FourEndpointAttainedFullTable alpha hAlpha k,
          fourEndpointW n alpha hAlpha k L.1) * common := by
      rw [sum_fourEndpointFullSupportReferenceWeight_eq_sum_attained_W]
    _ = _ := by rfl

#print axioms UnlabelledTypedSkeleton.edges_card_le_rowTotal
#print axioms fourEndpointAbstractBlockSkeleton_edges_card_le
#print axioms sum_profileCanonicalHighSkeleton_le_commonDeficitFactor_mul_sum_W
#print axioms sum_profileCanonicalHighSkeleton_le_canonicalDeficitFactor_mul_sum_W

end

end Erdos625
