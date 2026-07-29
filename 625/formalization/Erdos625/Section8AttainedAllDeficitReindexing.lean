import Erdos625.Section8FourDeficitProfileCover
import Mathlib.Tactic

/-!
# Section VIII: exact attained-demand reindexing by support and deficits

For a four-endpoint profile, an attained canonical high-demand table is
completely determined by

* its transported block-level matching support, and
* one bounded high deficit in every selected block cell.

This module packages those data in a finite type, defines the exact decoding
table, proves `decode (encode demand) = demand`, and deduces injectivity of the
encoding.  It then supplies the generic finite-sum domination needed to replace
the attained demand family by the full support/deficit family.

No weight comparison, endpoint transportation estimate, or asymptotic bound is
asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Abstract block-level matchings between the four endpoint slot families. -/
abbrev FourEndpointAbstractBlockSkeleton
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  UnlabelledTypedSkeleton
    (fun i : Fin 4 => fourEndpointMultiplicity alpha hAlpha k i)
    (fun j : Fin 4 => fourEndpointMultiplicity alpha hAlpha k j)

/-- The finite deficit choices in one selected block cell that remain in the
strict high range.  Zero is included and represents full containment. -/
abbrev FourEndpointHighDeficitAt
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (e : ↥P.edges) :=
  {h : Fin (fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1 + 1) //
    2 * h.1 < fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1}

/-- One block matching together with one admissible high deficit in each
selected block cell. -/
abbrev FourEndpointSupportDeficitData
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  Σ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
    ∀ e : ↥P.edges, FourEndpointHighDeficitAt alpha hAlpha P e

noncomputable instance instFintypeFourEndpointSupportDeficitData
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :
    Fintype (FourEndpointSupportDeficitData alpha hAlpha k) :=
  Fintype.ofFinite _

/-- Decode support/deficit data as a multiplicity table on abstract endpoint
block atoms. -/
noncomputable def fourEndpointSupportDeficitTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (D : FourEndpointSupportDeficitData alpha hAlpha k) :
    FourEndpointBlockAtom alpha hAlpha k →
      FourEndpointBlockAtom alpha hAlpha k → Nat := fun a b =>
  if h : (a, b) ∈ D.1.edges then
    fourEndpointOverlapSize alpha hAlpha a.1 b.1 -
      (D.2 ⟨(a, b), h⟩).1.1
  else 0

/-- Read one attained demand in the abstract four-endpoint block coordinates. -/
noncomputable def fourEndpointAbstractDemandTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    FourEndpointBlockAtom alpha hAlpha k →
      FourEndpointBlockAtom alpha hAlpha k → Nat := fun a b =>
  demand.1
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a)
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b)

/-- Encode an attained canonical demand by its transported support and its
literal cell deficits. -/
noncomputable def fourEndpointDemandSupportDeficitEncoding
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    FourEndpointSupportDeficitData alpha hAlpha k := by
  let P := fourEndpointDemandBlockSkeleton
    alpha hAlpha k hcover slotIndex demand
  refine ⟨P, ?_⟩
  intro e
  let h := fourEndpointDemandDeficit
    alpha hAlpha k hcover slotIndex demand e
  have hle : h ≤ fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1 := by
    exact Nat.sub_le _ _
  refine ⟨⟨h, Nat.lt_succ_of_le hle⟩, ?_⟩
  exact fourEndpointDemandDeficit_twice_lt
    alpha hAlpha k hcover slotIndex demand e

/-- Decoding the support and deficits of an attained demand recovers its exact
abstract multiplicity table. -/
theorem fourEndpointSupportDeficitTable_encoding_eq
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    fourEndpointSupportDeficitTable alpha hAlpha
        (fourEndpointDemandSupportDeficitEncoding
          alpha hAlpha k hcover slotIndex demand) =
      fourEndpointAbstractDemandTable alpha hAlpha k slotIndex demand := by
  funext a b
  by_cases hab : (a, b) ∈ (fourEndpointDemandBlockSkeleton
      alpha hAlpha k hcover slotIndex demand).edges
  · let e : ↥(fourEndpointDemandBlockPairing
        alpha hAlpha k hcover slotIndex demand).1.edges := ⟨(a, b), hab⟩
    have hle := fourEndpointDemandCell_le_fullMultiplicity
      alpha hAlpha k hcover slotIndex demand e
    simp [fourEndpointSupportDeficitTable,
      fourEndpointDemandSupportDeficitEncoding,
      fourEndpointAbstractDemandTable,
      fourEndpointDemandDeficit,
      fourEndpointCellFullMultiplicity, e, hab] at hle ⊢
    omega
  · have hz : demand.1
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a)
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b) = 0 := by
      by_contra hne
      have hsupp :
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a,
            fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b) ∈
            positiveDemandSupport demand.1 := by
        simpa only [positiveDemandSupport, Finset.mem_filter,
          Finset.mem_univ, true_and] using hne
      have hmem := (mem_fourEndpointDemandBlockEdges_iff
        alpha hAlpha k hcover slotIndex demand (a, b)).2 hsupp
      exact hab hmem
    simp [fourEndpointSupportDeficitTable,
      fourEndpointDemandSupportDeficitEncoding,
      fourEndpointAbstractDemandTable, hab, hz]

/-- Pullback through the endpoint slot indexing is injective on attained demand
tables. -/
theorem fourEndpointAbstractDemandTable_injective
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    Function.Injective
      (fourEndpointAbstractDemandTable alpha hAlpha k slotIndex) := by
  intro demand₁ demand₂ htable
  apply Subtype.ext
  funext a b
  have hcell := congrFun (congrFun htable
      (fourEndpointAtomOfProfileBlock
        alpha hAlpha k hcover slotIndex a))
    (fourEndpointAtomOfProfileBlock
      alpha hAlpha k hcover slotIndex b)
  simpa only [fourEndpointAbstractDemandTable,
    fourEndpointActualBlock_atomOfProfileBlock] using hcell

/-- The support/deficit encoding of attained canonical demands is injective. -/
theorem fourEndpointDemandSupportDeficitEncoding_injective
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    Function.Injective
      (fourEndpointDemandSupportDeficitEncoding
        alpha hAlpha k hcover slotIndex) := by
  intro demand₁ demand₂ hdata
  apply fourEndpointAbstractDemandTable_injective
    alpha hAlpha k hcover slotIndex
  have hdecoded := congrArg
    (fourEndpointSupportDeficitTable alpha hAlpha) hdata
  simpa only [fourEndpointSupportDeficitTable_encoding_eq] using hdecoded

/-- Any pointwise domination after the attained-demand encoding may be summed
over the full finite support/deficit family without an additional multiplicity
factor. -/
theorem sum_profileCanonicalHighSkeleton_le_sum_supportDeficitData
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (weightDemand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha) → ENNReal)
    (weightData : FourEndpointSupportDeficitData alpha hAlpha k → ENNReal)
    (hweight : ∀ demand,
      weightDemand demand ≤ weightData
        (fourEndpointDemandSupportDeficitEncoding
          alpha hAlpha k hcover slotIndex demand)) :
    (∑ demand, weightDemand demand) ≤ ∑ D, weightData D := by
  classical
  let encode := fourEndpointDemandSupportDeficitEncoding
    alpha hAlpha k hcover slotIndex
  have hencode : Function.Injective encode :=
    fourEndpointDemandSupportDeficitEncoding_injective
      alpha hAlpha k hcover slotIndex
  calc
    (∑ demand, weightDemand demand) ≤
        ∑ demand, weightData (encode demand) := by
      exact Finset.sum_le_sum fun demand _ => hweight demand
    _ = ∑ D ∈ Finset.image encode Finset.univ, weightData D := by
      symm
      rw [Finset.sum_image]
      intro demand₁ _ demand₂ _ h
      exact hencode h
    _ ≤ ∑ D ∈ (Finset.univ :
          Finset (FourEndpointSupportDeficitData alpha hAlpha k)),
          weightData D := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _
    _ = ∑ D, weightData D := by rfl

#print axioms fourEndpointSupportDeficitTable_encoding_eq
#print axioms fourEndpointAbstractDemandTable_injective
#print axioms fourEndpointDemandSupportDeficitEncoding_injective
#print axioms sum_profileCanonicalHighSkeleton_le_sum_supportDeficitData

end

end Erdos625
