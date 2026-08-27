import Erdos625.Section8AttainedAllDeficitReindexing
import Erdos625.Section8SharpDeficitProduct
import Erdos625.Section8EndpointAllHighDecoration
import Mathlib.Tactic

/-!
# Section VIII: direct support/choice assembly over the half-deficit envelope

An attained high demand is encoded directly by its abstract block matching and
one optional positive deficit in each selected cell.  The admissible window is
enlarged to the local condition `2 h < m`, which every attained high cell
satisfies.  Because all weights are nonnegative, this enlargement is harmless
for an upper bound and matches the hypothesis of the three-quarter exponent
estimate.

The exported assembly theorem has one premise: a pointwise comparison of each
attained demand with a support reference times its encoded deficit charge.  It
then sums the full attained family into a product of local partition functions,
with no additional fibre multiplicity.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Every four-endpoint overlap size is at most `alpha`. -/
theorem fourEndpointOverlapSize_le_alpha
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointOverlapSize alpha hAlpha i j ≤ alpha := by
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointOverlapSize, fourEndpointSize,
      fourEndpointCoordinate, fourDeficitCoordinate, fourDeficit] <;> omega

/-- Positive deficits in the enlarged half-deficit envelope. -/
def fourEndpointHalfDeficitAllowed
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (cell : ↥P.edges) : Finset (FourEndpointDeficit alpha) :=
  let m := fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1
  Finset.univ.filter fun deficit => 0 < deficit.1 ∧ 2 * deficit.1 < m

/-- Charged local ratio for one positive deficit. -/
def fourEndpointHalfDeficitWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (cell : ↥P.edges) (deficit : FourEndpointDeficit alpha) : ENNReal :=
  nearCellTerm n
    (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1)
    (Nat.dist cell.1.1.1.val cell.1.2.1.val) deficit.1

/-- One block matching together with one optional positive deficit in each
selected cell. -/
abbrev FourEndpointSupportChoiceData
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  Σ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
    NearSkeletonChoice (↥P.edges) (FourEndpointDeficit alpha)
      (fourEndpointHalfDeficitAllowed alpha hAlpha P)

/-- Decode optional choices to the corresponding multiplicity table. -/
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

/-- Convert dependent deficit data to the optional-choice representation. -/
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

/-- Support/deficit data viewed as support/optional-choice data. -/
noncomputable def fourEndpointSupportDeficitToChoiceData
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (D : FourEndpointSupportDeficitData alpha hAlpha k) :
    FourEndpointSupportChoiceData alpha hAlpha k :=
  ⟨D.1, fourEndpointSupportDeficitToChoice alpha hAlpha D⟩

/-- The optional-choice and dependent-deficit decoders agree. -/
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

/-- Direct attained-demand encoding into the optional-choice type. -/
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

/-- Decoding the direct encoding recovers the attained abstract demand table. -/
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

/-- The direct support/choice encoding is injective. -/
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

/-- Reference support weight times the exact optional-deficit charge. -/
noncomputable def fourEndpointSupportChoiceChargedWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (reference : FourEndpointAbstractBlockSkeleton alpha hAlpha k → ENNReal)
    (D : FourEndpointSupportChoiceData alpha hAlpha k) : ENNReal :=
  reference D.1 *
    nearSkeletonChoiceWeight
      (fourEndpointHalfDeficitAllowed alpha hAlpha D.1)
      (fourEndpointHalfDeficitWeight n alpha hAlpha D.1) D.2

/-- The support/choice sum factors exactly into local partition functions. -/
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
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro P _
  change
    (∑ choice : NearSkeletonChoice (↥P.edges) (FourEndpointDeficit alpha)
        (fourEndpointHalfDeficitAllowed alpha hAlpha P),
      reference P *
        nearSkeletonChoiceWeight
          (fourEndpointHalfDeficitAllowed alpha hAlpha P)
          (fourEndpointHalfDeficitWeight n alpha hAlpha P) choice) =
      reference P *
        ∏ cell : ↥P.edges,
          (1 + ∑ deficit ∈
            fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
            fourEndpointHalfDeficitWeight n alpha hAlpha P cell deficit)
  rw [← Finset.mul_sum]
  rw [sum_nearSkeletonChoiceWeight_eq_product]

/-- A pointwise charged comparison sums with no extra multiplicity factor. -/
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

#print axioms fourEndpointSupportChoiceTable_toChoice_eq
#print axioms fourEndpointDemandSupportChoiceEncoding_injective
#print axioms sum_fourEndpointSupportChoiceChargedWeight_eq
#print axioms sum_profileCanonicalHighSkeleton_le_directSupportChoiceProduct

end

end Erdos625
