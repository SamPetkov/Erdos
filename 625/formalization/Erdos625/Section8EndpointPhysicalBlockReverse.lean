import Erdos625.Section8EndpointDecoratedPhysicalInjective
import Mathlib.Tactic

/-!
# Section VIII: reconstruct the endpoint block pairing from a physical fibre

This module supplies the block-level half of the endpoint reverse
map.  It pulls the literal full block pairs of a physical endpoint skeleton
back through a fixed four-type slot indexing, proves that they form a typed
block matching, and proves that their four-by-four type table is the prescribed
endpoint table.

No local stub matching is reconstructed here.  That dependent step is isolated
in the next module.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Abstract block atoms used by the four endpoint coordinates. -/
abbrev FourEndpointBlockAtom (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :=
  Σ i : Fin 4, Fin (fourEndpointMultiplicity alpha hAlpha k i)

/-- A profile block cannot belong to two distinct endpoint-size slot families. -/
theorem fourEndpointBlockSlots_type_unique
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (a : ProfileBlockIndex k) (i j : Fin 4)
    (hi : a ∈ fourEndpointBlockSlots alpha hAlpha k i)
    (hj : a ∈ fourEndpointBlockSlots alpha hAlpha k j) :
    i = j := by
  have hsi : profileBlockMargin k a = fourEndpointSize alpha hAlpha i := by
    simpa only [fourEndpointBlockSlots, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
  have hsj : profileBlockMargin k a = fourEndpointSize alpha hAlpha j := by
    simpa only [fourEndpointBlockSlots, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj
  have hs : fourEndpointSize alpha hAlpha i =
      fourEndpointSize alpha hAlpha j := hsi.symm.trans hsj
  have hiCoord := (fourEndpoint_profile_indexing_facts alpha hAlpha k).1 i
  have hjCoord := (fourEndpoint_profile_indexing_facts alpha hAlpha k).1 j
  rw [hiCoord, hjCoord] at hs
  apply Fin.ext
  omega

/-- Pull back the physical full block pairs through the fixed endpoint slot
indexing. -/
noncomputable def fourEndpointPhysicalBlockEdges
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L) :
    Finset (FourEndpointBlockAtom alpha hAlpha k ×
      FourEndpointBlockAtom alpha hAlpha k) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun e =>
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1,
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2) ∈
        fourEndpointFullPairs alpha hAlpha k S.1.1

/-- A pulled-back block edge carries the literal full multiplicity associated
with its two endpoint types. -/
theorem fourEndpointPhysicalBlockEdge_typeTable
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : FourEndpointBlockAtom alpha hAlpha k ×
      FourEndpointBlockAtom alpha hAlpha k)
    (he : e ∈ fourEndpointPhysicalBlockEdges
      alpha hAlpha k L slotIndex S) :
    S.1.1.typeTable
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1)
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2) =
      fourEndpointOverlapSize alpha hAlpha e.1.1 e.2.1 := by
  rw [fourEndpointPhysicalBlockEdges, Finset.mem_filter] at he
  have hfull := he.2
  rw [fourEndpointFullPairs, Finset.mem_filter] at hfull
  obtain ⟨_, i, j, hi, hj, htable⟩ := hfull
  have hiOwn :
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1 ∈
        fourEndpointBlockSlots alpha hAlpha k e.1.1 :=
    (slotIndex e.1.1 e.1.2).2
  have hjOwn :
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2 ∈
        fourEndpointBlockSlots alpha hAlpha k e.2.1 :=
    (slotIndex e.2.1 e.2.2).2
  have hei : e.1.1 = i :=
    fourEndpointBlockSlots_type_unique alpha hAlpha k _ _ _ hiOwn hi
  have hej : e.2.1 = j :=
    fourEndpointBlockSlots_type_unique alpha hAlpha k _ _ _ hjOwn hj
  subst i
  subst j
  exact htable

/-- The pulled-back physical full pairs form a block-level matching. -/
noncomputable def fourEndpointPhysicalBlockSkeleton
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L) :
    UnlabelledTypedSkeleton
      (fun i : Fin 4 => fourEndpointMultiplicity alpha hAlpha k i)
      (fun j : Fin 4 => fourEndpointMultiplicity alpha hAlpha k j) where
  edges := fourEndpointPhysicalBlockEdges alpha hAlpha k L slotIndex S
  leftUnique := by
    intro x hx y hy hleft
    rw [fourEndpointPhysicalBlockEdges, Finset.mem_filter] at hx hy
    have hleftActual :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.1 =
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.1 :=
      congrArg (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex) hleft
    have hy' :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.2) ∈
        fourEndpointFullPairs alpha hAlpha k S.1.1 := by
      rw [hleftActual]
      exact hy.2
    have hrightActual :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.2 =
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.2 :=
      S.1.2.2.1 _ _ _ hx.2 hy'
    have hright : x.2 = y.2 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        hrightActual
    exact Prod.ext hleft hright
  rightUnique := by
    intro x hx y hy hright
    rw [fourEndpointPhysicalBlockEdges, Finset.mem_filter] at hx hy
    have hrightActual :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.2 =
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.2 :=
      congrArg (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex) hright
    have hy' :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.2) ∈
        fourEndpointFullPairs alpha hAlpha k S.1.1 := by
      rw [hrightActual]
      exact hy.2
    have hleftActual :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex x.1 =
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex y.1 :=
      S.1.2.2.2 _ _ _ hx.2 hy'
    have hleft : x.1 = y.1 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        hleftActual
    exact Prod.ext hleft hright

/-- The block skeleton reconstructed from a physical fibre has exactly the
prescribed full endpoint table. -/
theorem fourEndpointPhysicalBlockSkeleton_typeTable
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (i j : Fin 4) :
    (fourEndpointPhysicalBlockSkeleton alpha hAlpha k L slotIndex S).typeTable
        i j = L.toFun i j := by
  classical
  let source :=
    (fourEndpointPhysicalBlockEdges alpha hAlpha k L slotIndex S).filter
      (fun e => e.1.1 = i ∧ e.2.1 = j)
  let target :=
    ((fourEndpointBlockSlots alpha hAlpha k i).product
      (fourEndpointBlockSlots alpha hAlpha k j)).filter
        (fun ab => S.1.1.typeTable ab.1 ab.2 =
          fourEndpointOverlapSize alpha hAlpha i j)
  let F := fun e : FourEndpointBlockAtom alpha hAlpha k ×
      FourEndpointBlockAtom alpha hAlpha k =>
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1,
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2)
  have hfin : target = source.image F := by
    ext ab
    constructor
    · intro hab
      rw [Finset.mem_filter] at hab
      obtain ⟨hprod, htable⟩ := hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hprod
      let ai := (slotIndex i).symm ⟨ab.1, ha⟩
      let bj := (slotIndex j).symm ⟨ab.2, hb⟩
      let edge : FourEndpointBlockAtom alpha hAlpha k ×
          FourEndpointBlockAtom alpha hAlpha k :=
        (⟨i, ai⟩, ⟨j, bj⟩)
      have hrow :
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex edge.1 =
            ab.1 := by
        exact congrArg Subtype.val ((slotIndex i).apply_symm_apply ⟨ab.1, ha⟩)
      have hcol :
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex edge.2 =
            ab.2 := by
        exact congrArg Subtype.val ((slotIndex j).apply_symm_apply ⟨ab.2, hb⟩)
      have hedge : edge ∈
          fourEndpointPhysicalBlockEdges alpha hAlpha k L slotIndex S := by
        rw [fourEndpointPhysicalBlockEdges, Finset.mem_filter]
        constructor
        · simp
        · rw [fourEndpointFullPairs, Finset.mem_filter]
          refine ⟨by simp, i, j, ?_, ?_, ?_⟩
          · simpa only [hrow] using ha
          · simpa only [hcol] using hb
          · simpa only [hrow, hcol] using htable
      rw [Finset.mem_image]
      refine ⟨edge, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨hedge, rfl, rfl⟩
      · exact Prod.ext hrow hcol
    · intro hab
      rw [Finset.mem_image] at hab
      obtain ⟨edge, hedge, rfl⟩ := hab
      rw [Finset.mem_filter] at hedge
      obtain ⟨hedgeFull, hei, hej⟩ := hedge
      rw [Finset.mem_filter]
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · simpa only [F, fourEndpointActualBlockOfAtom, hei] using
            (slotIndex edge.1.1 edge.1.2).2
        · simpa only [F, fourEndpointActualBlockOfAtom, hej] using
            (slotIndex edge.2.1 edge.2.2).2
      · simpa only [hei, hej] using
          fourEndpointPhysicalBlockEdge_typeTable
            alpha hAlpha k L slotIndex S edge hedgeFull
  have hFinjective : Function.Injective F := by
    intro e₁ e₂ he
    exact Prod.ext
      (fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (congrArg Prod.fst he))
      (fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (congrArg Prod.snd he))
  have hSourceTarget : source.card = target.card := by
    rw [hfin, Finset.card_image_of_injective]
    exact hFinjective
  have hTable := congrArg FourEndpointFullTable.toFun S.2
  have hCell := congrFun (congrFun hTable i) j
  have hTarget : target.card = L.toFun i j := by
    simpa only [target, fourEndpointFullTableOfBlockTypeTable] using hCell
  change source.card = L.toFun i j
  exact hSourceTarget.trans hTarget

/-- Reconstructed block pairing over the prescribed full endpoint table. -/
noncomputable def fourEndpointPhysicalBlockPairing
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L) :
    FourEndpointBlockPairing alpha hAlpha k L :=
  ⟨fourEndpointPhysicalBlockSkeleton alpha hAlpha k L slotIndex S, by
    funext i j
    exact fourEndpointPhysicalBlockSkeleton_typeTable
      alpha hAlpha k L slotIndex S i j⟩

#print axioms fourEndpointBlockSlots_type_unique
#print axioms fourEndpointPhysicalBlockEdge_typeTable
#print axioms fourEndpointPhysicalBlockSkeleton_typeTable

end

end Erdos625
