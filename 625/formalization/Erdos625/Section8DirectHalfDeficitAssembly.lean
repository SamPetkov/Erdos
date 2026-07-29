import Erdos625.Section8AttainedAllDeficitReindexing
import Erdos625.Section8SharpDeficitProduct
import Erdos625.Section8EndpointAllHighDecoration
import Mathlib.Tactic

/-!
# Section VIII: direct support/choice assembly over the half-deficit envelope

The exact attained-demand encoding currently uses a dependent subtype carrying
one deficit in every selected endpoint cell.  The analytic product theorem uses
`NearSkeletonChoice`, where zero deficit is represented by `none` and every
positive deficit is represented by `some h`.

This module removes the later conversion burden.  It enlarges the admissible
window to the simpler condition `2 h < m`, which every attained high cell
already satisfies, and maps attained demands directly into the same optional
choice type used by the product expansion.  Since all weights are nonnegative,
the enlargement is harmless for an upper bound.

The final theorem is a generic finite assembly principle: once one has a
pointwise comparison of an attained demand with a reference support weight times
its optional-deficit charge, the entire attained sum is bounded by one sum over
block supports of reference weight times a product of local partition
functions.

No pointwise weight comparison, endpoint transportation estimate, or phase
asymptotic is asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Every four-endpoint overlap size is at most `alpha`.  This lets us use the
single ambient deficit type `Fin (alpha+1)` for all selected cells. -/
theorem fourEndpointOverlapSize_le_alpha
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointOverlapSize alpha hAlpha i j ≤ alpha := by
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointOverlapSize, fourEndpointSize,
      fourEndpointCoordinate, fourDeficitCoordinate, fourDeficit] <;> omega

/-- Positive deficits in the enlarged half-deficit envelope.  The original
strict global cutoff is not needed for the upper bound once `2 h < m` is known. -/
def fourEndpointHalfDeficitAllowed
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (cell : ↥P.edges) : Finset (FourEndpointDeficit alpha) :=
  let m := fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1
  Finset.univ.filter fun deficit => 0 < deficit.1 ∧ 2 * deficit.1 < m

/-- The already charged local ratio used for one positive deficit. -/
def fourEndpointHalfDeficitWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (cell : ↥P.edges) (deficit : FourEndpointDeficit alpha) : ENNReal :=
  nearCellTerm n
    (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1)
    (Nat.dist cell.1.1.1.val cell.1.2.1.val) deficit.1

/-- One abstract block matching together with the optional positive deficit in
every selected cell.  This is the same data structure used by the exact product
expansion. -/
abbrev FourEndpointSupportChoiceData
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  Σ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
    NearSkeletonChoice (↥P.edges) (FourEndpointDeficit alpha)
      (fourEndpointHalfDeficitAllowed alpha hAlpha P)

noncomputable instance instFintypeFourEndpointSupportChoiceData
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :
    Fintype (FourEndpointSupportChoiceData alpha hAlpha k) :=
  Fintype.ofFinite _

/-- Decode optional deficit choices to their multiplicity table.  `none` means
full containment, while `some h` means multiplicity `m-h`. -/
noncomputable def fourEndpointSupportChoiceTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (D : FourEndpointSupportChoiceData alpha hAlpha k) :
    FourEndpointBlockAtom alpha hAlpha k →
      FourEndpointBlockAtom alpha hAlpha k → Nat := fun a b =>
  if hab : (a, b) ∈ D.1.edges then
    let cell : ↥D.1.edges := ⟨(a, b), hab⟩
    let m := fourEndpointOverlapSize alpha hAlpha a.1 b.1
    match D.2 cell with
    | none => m
    | some deficit => m - deficit.1.1
  else 0

/-- Convert the older dependent support/deficit data to the optional-choice
representation.  Zero deficit becomes `none`; a positive deficit becomes the
corresponding `some` value. -/
noncomputable def fourEndpointSupportDeficitToChoice
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (D : FourEndpointSupportDeficitData alpha hAlpha k) :
    NearSkeletonChoice (↥D.1.edges) (FourEndpointDeficit alpha)
      (fourEndpointHalfDeficitAllowed alpha hAlpha D.1) := fun cell =>
  let h := (D.2 cell).1.1
  if hz : h = 0 then none else
    let deficit : FourEndpointDeficit alpha :=
      ⟨h, Nat.lt_succ_of_le
        ((Nat.le_of_lt_succ (D.2 cell).1.2).trans
          (fourEndpointOverlapSize_le_alpha
            alpha hAlpha cell.1.1.1 cell.1.2.1))⟩
    some ⟨deficit, by
      simp only [fourEndpointHalfDeficitAllowed, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨Nat.pos_of_ne_zero hz, (D.2 cell).2⟩⟩

/-- Support/deficit data regarded as support/optional-choice data. -/
noncomputable def fourEndpointSupportDeficitToChoiceData
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (D : FourEndpointSupportDeficitData alpha hAlpha k) :
    FourEndpointSupportChoiceData alpha hAlpha k :=
  ⟨D.1, fourEndpointSupportDeficitToChoice alpha hAlpha D⟩

/-- The optional-choice decoder agrees exactly with the older deficit-table
decoder. -/
theorem fourEndpointSupportChoiceTable_toChoice_eq
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (D : FourEndpointSupportDeficitData alpha hAlpha k) :
    fourEndpointSupportChoiceTable alpha hAlpha
        (fourEndpointSupportDeficitToChoiceData alpha hAlpha D) =
      fourEndpointSupportDeficitTable alpha hAlpha D := by
  funext a b
  by_cases hab : (a, b) ∈ D.1.edges
  · let cell : ↥D.1.edges := ⟨(a, b), hab⟩
    by_cases hz : (D.2 cell).1.1 = 0
    · simp [fourEndpointSupportChoiceTable,
        fourEndpointSupportDeficitToChoiceData,
        fourEndpointSupportDeficitToChoice,
        fourEndpointSupportDeficitTable, hab, cell, hz]
    · simp [fourEndpointSupportChoiceTable,
        fourEndpointSupportDeficitToChoiceData,
        fourEndpointSupportDeficitToChoice,
        fourEndpointSupportDeficitTable, hab, cell, hz]
  · simp [fourEndpointSupportChoiceTable,
      fourEndpointSupportDeficitToChoiceData,
      fourEndpointSupportDeficitTable, hab]

/-- Direct attained-demand encoding into the analytic optional-choice type. -/
noncomputable def fourEndpointDemandSupportChoiceEncoding
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    FourEndpointSupportChoiceData alpha hAlpha k :=
  fourEndpointSupportDeficitToChoiceData alpha hAlpha
    (fourEndpointDemandSupportDeficitEncoding
      alpha hAlpha k hcover slotIndex demand)

/-- Decoding the direct optional-choice encoding recovers the attained demand's
abstract multiplicity table. -/
theorem fourEndpointSupportChoiceTable_encoding_eq
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    fourEndpointSupportChoiceTable alpha hAlpha
        (fourEndpointDemandSupportChoiceEncoding
          alpha hAlpha k hcover slotIndex demand) =
      fourEndpointAbstractDemandTable alpha hAlpha k slotIndex demand := by
  rw [fourEndpointDemandSupportChoiceEncoding,
    fourEndpointSupportChoiceTable_toChoice_eq,
    fourEndpointSupportDeficitTable_encoding_eq]

/-- The direct support/optional-choice encoding is injective on attained
canonical high demands. -/
theorem fourEndpointDemandSupportChoiceEncoding_injective
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    Function.Injective
      (fourEndpointDemandSupportChoiceEncoding
        alpha hAlpha k hcover slotIndex) := by
  intro demand₁ demand₂ hdata
  apply fourEndpointAbstractDemandTable_injective
    alpha hAlpha k hcover slotIndex
  have hdecoded := congrArg
    (fourEndpointSupportChoiceTable alpha hAlpha) hdata
  simpa only [fourEndpointSupportChoiceTable_encoding_eq] using hdecoded

/-- A reference support weight times the exact product charge of one optional
deficit choice. -/
noncomputable def fourEndpointSupportChoiceChargedWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (reference : FourEndpointAbstractBlockSkeleton alpha hAlpha k → ENNReal)
    (D : FourEndpointSupportChoiceData alpha hAlpha k) : ENNReal :=
  reference D.1 *
    nearSkeletonChoiceWeight
      (fourEndpointHalfDeficitAllowed alpha hAlpha D.1)
      (fourEndpointHalfDeficitWeight n alpha hAlpha D.1) D.2

/-- Summing all support/choice data is exactly a sum over supports of reference
weight times the product of local deficit partition functions. -/
theorem sum_fourEndpointSupportChoiceChargedWeight_eq
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (reference : FourEndpointAbstractBlockSkeleton alpha hAlpha k → ENNReal) :
    (∑ D : FourEndpointSupportChoiceData alpha hAlpha k,
      fourEndpointSupportChoiceChargedWeight
        n alpha hAlpha reference D) =
      ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        reference P *
          ∏ cell : ↥P.edges,
            (1 + ∑ deficit ∈
              fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
              fourEndpointHalfDeficitWeight
                n alpha hAlpha P cell deficit) := by
  classical
  change
    (∑ D : Σ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        NearSkeletonChoice (↥P.edges) (FourEndpointDeficit alpha)
          (fourEndpointHalfDeficitAllowed alpha hAlpha P),
      reference D.1 *
        nearSkeletonChoiceWeight
          (fourEndpointHalfDeficitAllowed alpha hAlpha D.1)
          (fourEndpointHalfDeficitWeight n alpha hAlpha D.1) D.2) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro P _
  rw [← Finset.mul_sum]
  rw [sum_nearSkeletonChoiceWeight_eq_product]

/-- Generic global assembly theorem.  Any pointwise bound on attained demands by
their encoded support reference and optional-deficit charge immediately sums to
the product-form support bound, with no extra multiplicity factor. -/
theorem sum_profileCanonicalHighSkeleton_le_directSupportChoiceProduct
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (weightDemand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha) → ENNReal)
    (reference : FourEndpointAbstractBlockSkeleton alpha hAlpha k → ENNReal)
    (hweight : ∀ demand,
      weightDemand demand ≤
        fourEndpointSupportChoiceChargedWeight n alpha hAlpha reference
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand)) :
    (∑ demand, weightDemand demand) ≤
      ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        reference P *
          ∏ cell : ↥P.edges,
            (1 + ∑ deficit ∈
              fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
              fourEndpointHalfDeficitWeight
                n alpha hAlpha P cell deficit) := by
  classical
  let encode := fourEndpointDemandSupportChoiceEncoding
    alpha hAlpha k hcover slotIndex
  have hencode : Function.Injective encode :=
    fourEndpointDemandSupportChoiceEncoding_injective
      alpha hAlpha k hcover slotIndex
  calc
    (∑ demand, weightDemand demand) ≤
        ∑ demand,
          fourEndpointSupportChoiceChargedWeight
            n alpha hAlpha reference (encode demand) := by
      exact Finset.sum_le_sum fun demand _ => hweight demand
    _ = ∑ D ∈ Finset.image encode Finset.univ,
          fourEndpointSupportChoiceChargedWeight
            n alpha hAlpha reference D := by
      symm
      rw [Finset.sum_image]
      intro demand₁ _ demand₂ _ h
      exact hencode h
    _ ≤ ∑ D : FourEndpointSupportChoiceData alpha hAlpha k,
          fourEndpointSupportChoiceChargedWeight
            n alpha hAlpha reference D := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _
    _ = _ :=
      sum_fourEndpointSupportChoiceChargedWeight_eq
        n alpha hAlpha reference

/-- Cellwise-bounded form of the direct support assembly. -/
theorem sum_profileCanonicalHighSkeleton_le_directSupportChoiceBound
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (weightDemand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha) → ENNReal)
    (reference : FourEndpointAbstractBlockSkeleton alpha hAlpha k → ENNReal)
    (bound : FourEndpointAbstractBlockSkeleton alpha hAlpha k →
      FourEndpointBlockAtom alpha hAlpha k ×
        FourEndpointBlockAtom alpha hAlpha k → ENNReal)
    (hweight : ∀ demand,
      weightDemand demand ≤
        fourEndpointSupportChoiceChargedWeight n alpha hAlpha reference
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand))
    (hlocal : ∀ (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
      (cell : ↥P.edges),
      (∑ deficit ∈ fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
        fourEndpointHalfDeficitWeight n alpha hAlpha P cell deficit) ≤
          bound P cell.1) :
    (∑ demand, weightDemand demand) ≤
      ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        reference P * ∏ cell : ↥P.edges, (1 + bound P cell.1) := by
  calc
    (∑ demand, weightDemand demand) ≤
        ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          reference P *
            ∏ cell : ↥P.edges,
              (1 + ∑ deficit ∈
                fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
                fourEndpointHalfDeficitWeight
                  n alpha hAlpha P cell deficit) :=
      sum_profileCanonicalHighSkeleton_le_directSupportChoiceProduct
        n alpha hAlpha k hcover slotIndex weightDemand reference hweight
    _ ≤ ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          reference P * ∏ cell : ↥P.edges, (1 + bound P cell.1) := by
      apply Finset.sum_le_sum
      intro P _
      have hprod :
          (∏ cell : ↥P.edges,
              (1 + ∑ deficit ∈
                fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
                fourEndpointHalfDeficitWeight
                  n alpha hAlpha P cell deficit)) ≤
            ∏ cell : ↥P.edges, (1 + bound P cell.1) := by
        apply Finset.prod_le_prod'
        intro cell _
        exact add_le_add_left (hlocal P cell) 1
      simpa [mul_comm] using
        (mul_le_mul_right hprod (reference P))

#print axioms fourEndpointSupportChoiceTable_toChoice_eq
#print axioms fourEndpointDemandSupportChoiceEncoding_injective
#print axioms sum_fourEndpointSupportChoiceChargedWeight_eq
#print axioms sum_profileCanonicalHighSkeleton_le_directSupportChoiceProduct
#print axioms sum_profileCanonicalHighSkeleton_le_directSupportChoiceBound

end

end Erdos625
