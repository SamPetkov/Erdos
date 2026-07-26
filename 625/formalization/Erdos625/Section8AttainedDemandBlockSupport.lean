import Erdos625.Section8EndpointPhysicalEquiv
import Erdos625.Section8PartialCellPhysicalFibre
import Erdos625.Section8ProfileSkeletonWeight
import Erdos625.Section8EndpointAllHighDecoration
import Mathlib.Tactic

/-!
# Section VIII: block support and deficits of an attained canonical demand

For a profile whose blocks are covered by the four endpoint size classes, a
fixed slot indexing identifies every actual profile block with one abstract
four-type block atom.  The positive support of an attained canonical demand is
a matching; transporting it through this indexing therefore gives a literal
`FourEndpointBlockPairing`.

Every selected block cell carries one canonical all-high deficit.  This module
proves the exact reconstruction `m_e - h_e = j_e`, the pointwise feasibility
`j_e ≤ m_e`, and the strict half-deficit inequality `2 h_e < m_e`.

No weighted sum or asymptotic estimate is asserted here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Every profile block belongs to one of the four endpoint-size classes. -/
def IsFourEndpointProfileCover
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) : Prop :=
  ∀ a : ProfileBlockIndex k,
    ∃ i : Fin 4, a ∈ fourEndpointBlockSlots alpha hAlpha k i

/-- The abstract four-type block atom corresponding to one actual profile
block. -/
noncomputable def fourEndpointAtomOfProfileBlock
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (a : ProfileBlockIndex k) : FourEndpointBlockAtom alpha hAlpha k :=
  let i := Classical.choose (hcover a)
  let hi := Classical.choose_spec (hcover a)
  ⟨i, (slotIndex i).symm ⟨a, hi⟩⟩

/-- The abstract-to-physical block map is a right inverse of the cover-based
physical-to-abstract map. -/
theorem fourEndpointActualBlock_atomOfProfileBlock
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (a : ProfileBlockIndex k) :
    fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex
        (fourEndpointAtomOfProfileBlock alpha hAlpha k hcover slotIndex a) = a := by
  classical
  unfold fourEndpointAtomOfProfileBlock
  exact congrArg Subtype.val
    ((slotIndex (Classical.choose (hcover a))).apply_symm_apply
      ⟨a, Classical.choose_spec (hcover a)⟩)

/-- The cover-based inverse also recovers every abstract block atom. -/
theorem fourEndpointAtomOfProfileBlock_actualBlock
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (a : FourEndpointBlockAtom alpha hAlpha k) :
    fourEndpointAtomOfProfileBlock alpha hAlpha k hcover slotIndex
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a) = a := by
  apply fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
  rw [fourEndpointActualBlock_atomOfProfileBlock]

/-- Every covered profile block has size at most the largest endpoint size. -/
theorem profileBlockMargin_le_fourEndpointLargest_of_cover
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (a : ProfileBlockIndex k) :
    profileBlockMargin k a ≤ fourEndpointLargestSize alpha hAlpha := by
  obtain ⟨i, hi⟩ := hcover a
  have hsize : profileBlockMargin k a = fourEndpointSize alpha hAlpha i := by
    simpa only [fourEndpointBlockSlots, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
  rw [hsize]
  simpa [fourEndpointOverlapSize] using
    fourEndpointOverlapSize_le_largest alpha hAlpha i i

/-- Transport the positive support of one attained demand to abstract endpoint
block atoms. -/
noncomputable def fourEndpointDemandBlockEdges
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    Finset (FourEndpointBlockAtom alpha hAlpha k ×
      FourEndpointBlockAtom alpha hAlpha k) :=
  (positiveDemandSupport demand.1).image fun ab =>
    (fourEndpointAtomOfProfileBlock alpha hAlpha k hcover slotIndex ab.1,
      fourEndpointAtomOfProfileBlock alpha hAlpha k hcover slotIndex ab.2)

/-- Membership in the transported block support is exactly membership of the
corresponding actual block pair in the positive demand support. -/
theorem mem_fourEndpointDemandBlockEdges_iff
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : FourEndpointBlockAtom alpha hAlpha k ×
      FourEndpointBlockAtom alpha hAlpha k) :
    e ∈ fourEndpointDemandBlockEdges
        alpha hAlpha k hcover slotIndex demand ↔
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1,
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2) ∈
        positiveDemandSupport demand.1 := by
  classical
  constructor
  · intro he
    rw [fourEndpointDemandBlockEdges, Finset.mem_image] at he
    obtain ⟨ab, hab, rfl⟩ := he
    simpa only [fourEndpointActualBlock_atomOfProfileBlock] using hab
  · intro he
    rw [fourEndpointDemandBlockEdges, Finset.mem_image]
    refine ⟨(fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1,
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2), he, ?_⟩
    apply Prod.ext
    · exact fourEndpointAtomOfProfileBlock_actualBlock
        alpha hAlpha k hcover slotIndex e.1
    · exact fourEndpointAtomOfProfileBlock_actualBlock
        alpha hAlpha k hcover slotIndex e.2

/-- The transported positive support is a literal typed block matching. -/
noncomputable def fourEndpointDemandBlockSkeleton
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    UnlabelledTypedSkeleton
      (fun i : Fin 4 => fourEndpointMultiplicity alpha hAlpha k i)
      (fun j : Fin 4 => fourEndpointMultiplicity alpha hAlpha k j) where
  edges := fourEndpointDemandBlockEdges
    alpha hAlpha k hcover slotIndex demand
  leftUnique := by
    intro x hx y hy hleft
    have hmatching := profileHighSkeleton_positiveSupport_isBipartiteMatching
      k (fourEndpointLargestSize alpha hAlpha)
      (profileBlockMargin_le_fourEndpointLargest_of_cover
        alpha hAlpha k hcover) demand
    have hx' := (mem_fourEndpointDemandBlockEdges_iff
      alpha hAlpha k hcover slotIndex demand x).mp hx
    have hy' := (mem_fourEndpointDemandBlockEdges_iff
      alpha hAlpha k hcover slotIndex demand y).mp hy
    have hleftActual :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.1 =
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.1 :=
      congrArg (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex) hleft
    have hy'' :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.2) ∈
        positiveDemandSupport demand.1 := by
      rw [hleftActual]
      exact hy'
    have hrightActual := hmatching.1
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.1)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.2)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.2)
      hx' hy''
    exact Prod.ext hleft
      (fourEndpointActualBlockOfAtom_injective
        alpha hAlpha k slotIndex hrightActual)
  rightUnique := by
    intro x hx y hy hright
    have hmatching := profileHighSkeleton_positiveSupport_isBipartiteMatching
      k (fourEndpointLargestSize alpha hAlpha)
      (profileBlockMargin_le_fourEndpointLargest_of_cover
        alpha hAlpha k hcover) demand
    have hx' := (mem_fourEndpointDemandBlockEdges_iff
      alpha hAlpha k hcover slotIndex demand x).mp hx
    have hy' := (mem_fourEndpointDemandBlockEdges_iff
      alpha hAlpha k hcover slotIndex demand y).mp hy
    have hrightActual :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.2 =
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.2 :=
      congrArg (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex) hright
    have hy'' :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.2) ∈
        positiveDemandSupport demand.1 := by
      rw [hrightActual]
      exact hy'
    have hleftActual := hmatching.2
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.2)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.1)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.1)
      hx' hy''
    exact Prod.ext
      (fourEndpointActualBlockOfAtom_injective
        alpha hAlpha k slotIndex hleftActual) hright

/-- The endpoint reference table attached to the positive block support. -/
noncomputable def fourEndpointDemandSupportTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) : FourEndpointFullTable where
  toFun := (fourEndpointDemandBlockSkeleton
    alpha hAlpha k hcover slotIndex demand).typeTable

/-- The transported support, regarded as one block pairing over its exact
endpoint reference table. -/
noncomputable def fourEndpointDemandBlockPairing
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    FourEndpointBlockPairing alpha hAlpha k
      (fourEndpointDemandSupportTable
        alpha hAlpha k hcover slotIndex demand) :=
  ⟨fourEndpointDemandBlockSkeleton alpha hAlpha k hcover slotIndex demand, rfl⟩

/-- Every attained demand cell is bounded by its ambient row degree. -/
theorem profileCanonicalDemand_cell_le_row
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U)
    (a b' : ProfileBlockIndex k) :
    demand.1 a b' ≤ profileBlockMargin k a := by
  let witness := canonicalDemandReferenceWitness
    (profileBlockMargin k) (profileBlockMargin k) U demand
  let matching :=
    (typedPartialMatchingEquivPrescribedDemandWitness demand.1
      (profileBlockMargin k) (profileBlockMargin k)).symm witness
  have hcard := card_typedPartialMatching_rowCell matching a b'
  calc
    demand.1 a b' = ((matching.rowAllocation a).1 b').card := by
      simpa using hcard.symm
    _ ≤ (Finset.univ : Finset (Fin (profileBlockMargin k a))).card :=
      Finset.card_le_univ _
    _ = profileBlockMargin k a := by simp

/-- Every attained demand cell is bounded by its ambient column degree. -/
theorem profileCanonicalDemand_cell_le_column
    {b : Nat} (k : ColoringProfile b) (U : Nat)
    (demand : ProfileCanonicalHighSkeleton k U)
    (a b' : ProfileBlockIndex k) :
    demand.1 a b' ≤ profileBlockMargin k b' := by
  let witness := canonicalDemandReferenceWitness
    (profileBlockMargin k) (profileBlockMargin k) U demand
  let matching :=
    (typedPartialMatchingEquivPrescribedDemandWitness demand.1
      (profileBlockMargin k) (profileBlockMargin k)).symm witness
  have hcard := card_typedPartialMatching_columnCell matching a b'
  calc
    demand.1 a b' = ((matching.columnAllocation b').1 a).card := by
      simpa using hcard.symm
    _ ≤ (Finset.univ : Finset (Fin (profileBlockMargin k b'))).card :=
      Finset.card_le_univ _
    _ = profileBlockMargin k b' := by simp

/-- Canonical deficit of one selected block cell. -/
def fourEndpointDemandDeficit
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : ↥(fourEndpointDemandBlockPairing
      alpha hAlpha k hcover slotIndex demand).1.edges) : Nat :=
  fourEndpointCellFullMultiplicity alpha hAlpha
      (fourEndpointDemandBlockPairing
        alpha hAlpha k hcover slotIndex demand) e -
    demand.1
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2)

/-- The actual attained multiplicity is at most the full endpoint
multiplicity. -/
theorem fourEndpointDemandCell_le_fullMultiplicity
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : ↥(fourEndpointDemandBlockPairing
      alpha hAlpha k hcover slotIndex demand).1.edges) :
    demand.1
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2) ≤
      fourEndpointCellFullMultiplicity alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand) e := by
  have hr := profileCanonicalDemand_cell_le_row k
    (fourEndpointLargestSize alpha hAlpha) demand
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2)
  have hc := profileCanonicalDemand_cell_le_column k
    (fourEndpointLargestSize alpha hAlpha) demand
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2)
  rw [profileBlockMargin_fourEndpointActualBlockOfAtom] at hr hc
  simpa [fourEndpointCellFullMultiplicity, fourEndpointOverlapSize] using
    (le_min hr hc)

/-- Subtracting the canonical deficit reconstructs the attained cell
multiplicity exactly. -/
theorem fourEndpointCellMultiplicity_demandDeficit_eq
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : ↥(fourEndpointDemandBlockPairing
      alpha hAlpha k hcover slotIndex demand).1.edges) :
    fourEndpointCellMultiplicityOfDeficit alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) e =
      demand.1
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2) := by
  unfold fourEndpointCellMultiplicityOfDeficit fourEndpointDemandDeficit
  have hle := fourEndpointDemandCell_le_fullMultiplicity
    alpha hAlpha k hcover slotIndex demand e
  omega

/-- Every selected attained deficit lies strictly below half of its endpoint
multiplicity. -/
theorem fourEndpointDemandDeficit_twice_lt
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha))
    (e : ↥(fourEndpointDemandBlockPairing
      alpha hAlpha k hcover slotIndex demand).1.edges) :
    2 * fourEndpointDemandDeficit
        alpha hAlpha k hcover slotIndex demand e <
      fourEndpointCellFullMultiplicity alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand) e := by
  have hsupp := (mem_fourEndpointDemandBlockEdges_iff
    alpha hAlpha k hcover slotIndex demand e.1).mp e.2
  have hne : demand.1
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2) ≠ 0 := by
    simpa only [positiveDemandSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] using hsupp
  have hhigh := canonicalDemandImage_high
    (profileBlockMargin k) (profileBlockMargin k)
    (fourEndpointLargestSize alpha hAlpha) demand
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2) hne
  have hm :
      fourEndpointCellFullMultiplicity alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand) e ≤
        fourEndpointLargestSize alpha hAlpha := by
    exact fourEndpointOverlapSize_le_largest alpha hAlpha e.1.1.1 e.1.2.1
  have hle := fourEndpointDemandCell_le_fullMultiplicity
    alpha hAlpha k hcover slotIndex demand e
  have hhalf := highMultiplicity_deficit_twice_lt
    (fourEndpointLargestSize alpha hAlpha)
    (fourEndpointCellFullMultiplicity alpha hAlpha
      (fourEndpointDemandBlockPairing
        alpha hAlpha k hcover slotIndex demand) e)
    (demand.1
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2))
    hm hhigh hle
  simpa only [fourEndpointDemandDeficit] using hhalf

#print axioms fourEndpointActualBlock_atomOfProfileBlock
#print axioms fourEndpointAtomOfProfileBlock_actualBlock
#print axioms fourEndpointDemandBlockSkeleton
#print axioms profileCanonicalDemand_cell_le_row
#print axioms profileCanonicalDemand_cell_le_column
#print axioms fourEndpointCellMultiplicity_demandDeficit_eq
#print axioms fourEndpointDemandDeficit_twice_lt

end

end Erdos625
