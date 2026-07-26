import Erdos625.Section8EndpointPhysicalBlockReverse
import Mathlib.Tactic

/-!
# Section VIII: reconstruct local endpoint stub matchings

After the block-level endpoint pairing has been reconstructed, every selected
physical block cell can be pulled back to a unit-typed local stub matching.  We
use explicit finite equivalences for the dependent stub bounds, so no numerical
information is hidden in `Fin.cast` projections.

This module constructs the local reverse data and proves its exact cell
multiplicity.  The global round trips are isolated in the subsequent endpoint
equivalence module.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The finite equivalence from a physical stub index in one endpoint block to
its canonical local endpoint coordinate. -/
noncomputable def fourEndpointPhysicalStubToLocalEquiv
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (a : FourEndpointBlockAtom alpha hAlpha k) :
    Fin (profileBlockMargin k
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a)) ≃
      Fin (fourEndpointSize alpha hAlpha a.1) :=
  Equiv.cast (congrArg Fin
    (profileBlockMargin_fourEndpointActualBlockOfAtom
      alpha hAlpha k slotIndex a))

/-- Pull one physical cell edge back to the corresponding unit-typed local
stub edge. -/
noncomputable def fourEndpointPhysicalCellEdgeToLocal
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : ↥(fourEndpointPhysicalBlockPairing
      alpha hAlpha k L slotIndex S).1.edges) :
    Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)) ×
        Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2)) →
      RowStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.1.1) ×
        ColumnStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.2.1) :=
  fun p =>
    (⟨(), fourEndpointPhysicalStubToLocalEquiv
      alpha hAlpha k slotIndex e.1.1 p.1⟩,
     ⟨(), fourEndpointPhysicalStubToLocalEquiv
      alpha hAlpha k slotIndex e.1.2 p.2⟩)

/-- The local pullback map is injective because both coordinate maps are
finite equivalences. -/
theorem fourEndpointPhysicalCellEdgeToLocal_injective
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : ↥(fourEndpointPhysicalBlockPairing
      alpha hAlpha k L slotIndex S).1.edges) :
    Function.Injective
      (fourEndpointPhysicalCellEdgeToLocal
        alpha hAlpha k L slotIndex S e) := by
  intro p q hpq
  apply Prod.ext
  · apply (fourEndpointPhysicalStubToLocalEquiv
      alpha hAlpha k slotIndex e.1.1).injective
    exact eq_of_heq (Sigma.mk.inj_iff.mp
      (congrArg Prod.fst hpq)).2
  · apply (fourEndpointPhysicalStubToLocalEquiv
      alpha hAlpha k slotIndex e.1.2).injective
    exact eq_of_heq (Sigma.mk.inj_iff.mp
      (congrArg Prod.snd hpq)).2

/-- Local physical cell edges in canonical unit-typed coordinates. -/
noncomputable def fourEndpointPhysicalCellLocalEdgesValidated
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : ↥(fourEndpointPhysicalBlockPairing
      alpha hAlpha k L slotIndex S).1.edges) :
    Finset
      (RowStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.1.1) ×
        ColumnStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.2.1)) :=
  (S.1.1.cellEdges
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2)).image
    (fourEndpointPhysicalCellEdgeToLocal
      alpha hAlpha k L slotIndex S e)

/-- Public cell-cardinality identity for a physical typed matching. -/
theorem physicalCellEdges_card_eq_typeTable_public
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {row : I → Nat} {col : J → Nat}
    (S : UnlabelledTypedSkeleton row col) (i : I) (j : J) :
    (S.cellEdges i j).card = S.typeTable i j := by
  unfold UnlabelledTypedSkeleton.cellEdges UnlabelledTypedSkeleton.typeTable
  refine Finset.card_bij
    (fun p _ => ((⟨i, p.1⟩, ⟨j, p.2⟩) : RowStub row × ColumnStub col))
    ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.2, rfl, rfl⟩
  · intro p₁ hp₁ p₂ hp₂ hEq
    exact Prod.ext
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hEq)).2)
      (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hEq)).2)
  · intro edge hedge
    rw [Finset.mem_filter] at hedge
    obtain ⟨hEdge, hI, hJ⟩ := hedge
    obtain ⟨⟨i', r⟩, ⟨j', c⟩⟩ := edge
    simp only at hI hJ
    subst i'
    subst j'
    exact ⟨(r, c), by simp [hEdge], rfl⟩

/-- Pulled-back local physical cell matching. -/
noncomputable def fourEndpointPhysicalCellLocalSkeletonValidated
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : ↥(fourEndpointPhysicalBlockPairing
      alpha hAlpha k L slotIndex S).1.edges) :
    UnlabelledTypedSkeleton
      (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.1.1)
      (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.2.1) where
  edges := fourEndpointPhysicalCellLocalEdgesValidated
    alpha hAlpha k L slotIndex S e
  leftUnique := by
    classical
    intro x hx y hy hleft
    rw [fourEndpointPhysicalCellLocalEdgesValidated, Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    have hLocalFirst :
        fourEndpointPhysicalStubToLocalEquiv
            alpha hAlpha k slotIndex e.1.1 p.1 =
          fourEndpointPhysicalStubToLocalEquiv
            alpha hAlpha k slotIndex e.1.1 q.1 :=
      eq_of_heq (Sigma.mk.inj_iff.mp hleft).2
    have hpFirst : p.1 = q.1 :=
      (fourEndpointPhysicalStubToLocalEquiv
        alpha hAlpha k slotIndex e.1.1).injective hLocalFirst
    have hpEdge :
        ((⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, p.1⟩,
          ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, p.2⟩) :
          RowStub (profileBlockMargin k) ×
            ColumnStub (profileBlockMargin k)) ∈ S.1.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp
    have hqEdge :
        ((⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, q.1⟩,
          ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, q.2⟩) :
          RowStub (profileBlockMargin k) ×
            ColumnStub (profileBlockMargin k)) ∈ S.1.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hq
    have hrow :
        (⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, p.1⟩ :
          RowStub (profileBlockMargin k)) =
        ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, q.1⟩ :=
      Sigma.ext rfl (heq_of_eq hpFirst)
    have hglobal := S.1.1.leftUnique _ hpEdge _ hqEdge hrow
    have hpSecond : p.2 = q.2 :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hglobal)).2
    exact congrArg
      (fourEndpointPhysicalCellEdgeToLocal
        alpha hAlpha k L slotIndex S e)
      (Prod.ext hpFirst hpSecond)
  rightUnique := by
    classical
    intro x hx y hy hright
    rw [fourEndpointPhysicalCellLocalEdgesValidated, Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    have hLocalSecond :
        fourEndpointPhysicalStubToLocalEquiv
            alpha hAlpha k slotIndex e.1.2 p.2 =
          fourEndpointPhysicalStubToLocalEquiv
            alpha hAlpha k slotIndex e.1.2 q.2 :=
      eq_of_heq (Sigma.mk.inj_iff.mp hright).2
    have hpSecond : p.2 = q.2 :=
      (fourEndpointPhysicalStubToLocalEquiv
        alpha hAlpha k slotIndex e.1.2).injective hLocalSecond
    have hpEdge :
        ((⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, p.1⟩,
          ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, p.2⟩) :
          RowStub (profileBlockMargin k) ×
            ColumnStub (profileBlockMargin k)) ∈ S.1.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp
    have hqEdge :
        ((⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, q.1⟩,
          ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, q.2⟩) :
          RowStub (profileBlockMargin k) ×
            ColumnStub (profileBlockMargin k)) ∈ S.1.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hq
    have hcol :
        (⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, p.2⟩ :
          ColumnStub (profileBlockMargin k)) =
        ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, q.2⟩ :=
      Sigma.ext rfl (heq_of_eq hpSecond)
    have hglobal := S.1.1.rightUnique _ hpEdge _ hqEdge hcol
    have hpFirst : p.1 = q.1 :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hglobal)).2
    exact congrArg
      (fourEndpointPhysicalCellEdgeToLocal
        alpha hAlpha k L slotIndex S e)
      (Prod.ext hpFirst hpSecond)

/-- The pulled-back local skeleton has exactly the full endpoint multiplicity
of its selected block cell. -/
theorem fourEndpointPhysicalCellLocalSkeletonValidated_typeTable
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : ↥(fourEndpointPhysicalBlockPairing
      alpha hAlpha k L slotIndex S).1.edges) :
    (fourEndpointPhysicalCellLocalSkeletonValidated
      alpha hAlpha k L slotIndex S e).typeTable () () =
        fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1 := by
  change
    ((fourEndpointPhysicalCellLocalEdgesValidated
      alpha hAlpha k L slotIndex S e).filter
        (fun z => z.1.1 = () ∧ z.2.1 = ())).card =
      fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1
  have hAll :
      (fourEndpointPhysicalCellLocalEdgesValidated
        alpha hAlpha k L slotIndex S e).filter
          (fun z => z.1.1 = () ∧ z.2.1 = ()) =
        fourEndpointPhysicalCellLocalEdgesValidated
          alpha hAlpha k L slotIndex S e := by
    ext z
    simp
  rw [hAll]
  rw [fourEndpointPhysicalCellLocalEdgesValidated,
    Finset.card_image_of_injective]
  · rw [physicalCellEdges_card_eq_typeTable_public]
    exact fourEndpointPhysicalBlockEdge_typeTable
      alpha hAlpha k L slotIndex S e.1 e.2
  · exact fourEndpointPhysicalCellEdgeToLocal_injective
      alpha hAlpha k L slotIndex S e

/-- One reconstructed literal full-cell matching. -/
noncomputable def fourEndpointPhysicalCellStubMatchingValidated
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : ↥(fourEndpointPhysicalBlockPairing
      alpha hAlpha k L slotIndex S).1.edges) :
    FourEndpointSelectedCellStubMatching alpha hAlpha k L
      (fourEndpointPhysicalBlockPairing alpha hAlpha k L slotIndex S) e :=
  ⟨fourEndpointPhysicalCellLocalSkeletonValidated
      alpha hAlpha k L slotIndex S e,
    fourEndpointPhysicalCellLocalSkeletonValidated_typeTable
      alpha hAlpha k L slotIndex S e⟩

/-- Reverse decorated data reconstructed from one physical endpoint fibre
member. -/
noncomputable def fourEndpointPhysicalFibreToDecoratedBlockPairingValidated
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    FourEndpointPhysicalFibre alpha hAlpha k L →
      FourEndpointDecoratedBlockPairing alpha hAlpha k L := fun S =>
  ⟨fourEndpointPhysicalBlockPairing alpha hAlpha k L slotIndex S,
    fun e => fourEndpointPhysicalCellStubMatchingValidated
      alpha hAlpha k L slotIndex S e⟩

#print axioms fourEndpointPhysicalCellEdgeToLocal_injective
#print axioms physicalCellEdges_card_eq_typeTable_public
#print axioms fourEndpointPhysicalCellLocalSkeletonValidated_typeTable

end

end Erdos625
