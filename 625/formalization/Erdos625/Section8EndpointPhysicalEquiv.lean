import Erdos625.Section8EndpointPhysicalCellReverse
import Mathlib.Tactic

/-!
# Section VIII: endpoint decorated/physical equivalence

The forward map unions the physical edges supplied by the local full-cell
stub matchings.  The reverse map recovers the selected block pairs and pulls
each physical cell back to its canonical local coordinates.

This module proves both round trips.  It closes the endpoint-only physical
fibre equivalence, but makes no claim about nonendpoint deficits or the global
canonical high-skeleton sum.
-/

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- Pulling a physical cell edge to local coordinates and mapping it forward
again preserves the literal physical edge. -/
theorem fourEndpointPhysicalEdge_local_roundtrip
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L)
    (e : ↥(fourEndpointPhysicalBlockPairing
      alpha hAlpha k L slotIndex S).1.edges)
    (p : Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)) ×
      Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2))) :
    fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
        (fourEndpointPhysicalFibreToDecoratedBlockPairingValidated
          alpha hAlpha k L slotIndex S)
        e
        (fourEndpointPhysicalCellEdgeToLocal
          alpha hAlpha k L slotIndex S e p) =
      ((⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, p.1⟩,
        ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, p.2⟩) :
        RowStub (profileBlockMargin k) ×
          ColumnStub (profileBlockMargin k)) := by
  apply Prod.ext
  · simp only [fourEndpointPhysicalEdgeOfLocalEdge,
      fourEndpointPhysicalCellEdgeToLocal]
    refine congrArg
      (fun x : Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)) =>
        (⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1, x⟩ :
          RowStub (profileBlockMargin k))) ?_
    apply Fin.ext
    exact fourEndpointPhysicalStubToLocalEquiv_val
      alpha hAlpha k slotIndex e.1.1 p.1
  · simp only [fourEndpointPhysicalEdgeOfLocalEdge,
      fourEndpointPhysicalCellEdgeToLocal]
    refine congrArg
      (fun x : Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2)) =>
        (⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2, x⟩ :
          ColumnStub (profileBlockMargin k))) ?_
    apply Fin.ext
    exact fourEndpointPhysicalStubToLocalEquiv_val
      alpha hAlpha k slotIndex e.1.2 p.2

/-- The physical skeleton underlying forward-after-reverse is the original
physical skeleton. -/
theorem fourEndpointDecoratedPhysicalSkeleton_reverse_eq
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (S : FourEndpointPhysicalFibre alpha hAlpha k L) :
    fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex
        (fourEndpointPhysicalFibreToDecoratedBlockPairingValidated
          alpha hAlpha k L slotIndex S) =
      S.1.1 := by
  classical
  apply UnlabelledTypedSkeleton.ext
  ext z
  constructor
  · intro hz
    simp only [fourEndpointDecoratedPhysicalSkeleton,
      fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hz
    obtain ⟨e, p, hp, rfl⟩ := hz
    change p ∈ fourEndpointPhysicalCellLocalEdgesValidated
      alpha hAlpha k L slotIndex S e at hp
    rw [fourEndpointPhysicalCellLocalEdgesValidated, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [fourEndpointPhysicalEdge_local_roundtrip]
    simpa [UnlabelledTypedSkeleton.cellEdges] using hq
  · intro hz
    rcases z with ⟨⟨za, zx⟩, ⟨zb, zy⟩⟩
    obtain ⟨i, j, hi, hj, htable⟩ :=
      S.1.2.1 ((⟨za, zx⟩, ⟨zb, zy⟩) :
        RowStub (profileBlockMargin k) × ColumnStub (profileBlockMargin k)) hz
    let ai := (slotIndex i).symm ⟨za, hi⟩
    let bj := (slotIndex j).symm ⟨zb, hj⟩
    let a : FourEndpointBlockAtom alpha hAlpha k := ⟨i, ai⟩
    let b : FourEndpointBlockAtom alpha hAlpha k := ⟨j, bj⟩
    have ha :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a = za := by
      exact congrArg Subtype.val ((slotIndex i).apply_symm_apply ⟨za, hi⟩)
    have hb :
        fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b = zb := by
      exact congrArg Subtype.val ((slotIndex j).apply_symm_apply ⟨zb, hj⟩)
    let edge : FourEndpointBlockAtom alpha hAlpha k ×
        FourEndpointBlockAtom alpha hAlpha k := (a, b)
    have hedge : edge ∈ fourEndpointPhysicalBlockEdges
        alpha hAlpha k L slotIndex S := by
      rw [fourEndpointPhysicalBlockEdges, Finset.mem_filter]
      constructor
      · simp
      · rw [fourEndpointFullPairs, Finset.mem_filter]
        refine ⟨by simp, i, j, ?_, ?_, ?_⟩
        · simpa only [edge, ha] using hi
        · simpa only [edge, hb] using hj
        · simpa only [edge, ha, hb] using htable
    let e : ↥(fourEndpointPhysicalBlockPairing
        alpha hAlpha k L slotIndex S).1.edges := ⟨edge, hedge⟩
    let qa : Fin (profileBlockMargin k
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a)) :=
      Fin.cast (congrArg (profileBlockMargin k) ha).symm zx
    let qb : Fin (profileBlockMargin k
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b)) :=
      Fin.cast (congrArg (profileBlockMargin k) hb).symm zy
    let q : Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a)) ×
        Fin (profileBlockMargin k
          (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b)) :=
      (qa, qb)
    have hrow :
        (⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a, qa⟩ :
          RowStub (profileBlockMargin k)) = ⟨za, zx⟩ := by
      apply Sigma.ext ha
      apply (Fin.heq_ext_iff
        (congrArg Fin (congrArg (profileBlockMargin k) ha))).2
      rfl
    have hcol :
        (⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b, qb⟩ :
          ColumnStub (profileBlockMargin k)) = ⟨zb, zy⟩ := by
      apply Sigma.ext hb
      apply (Fin.heq_ext_iff
        (congrArg Fin (congrArg (profileBlockMargin k) hb))).2
      rfl
    have hglobal :
        ((⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a, qa⟩,
          ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b, qb⟩) :
          RowStub (profileBlockMargin k) × ColumnStub (profileBlockMargin k)) =
        (⟨za, zx⟩, ⟨zb, zy⟩) :=
      Prod.ext hrow hcol
    have hz' :
        ((⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a, qa⟩,
          ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b, qb⟩) :
          RowStub (profileBlockMargin k) × ColumnStub (profileBlockMargin k)) ∈
        S.1.1.edges := by
      rw [hglobal]
      exact hz
    have hq : q ∈ S.1.1.cellEdges
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a)
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex b) := by
      simpa only [UnlabelledTypedSkeleton.cellEdges, Finset.mem_filter,
        Finset.mem_univ, true_and, q] using hz'
    let p := fourEndpointPhysicalCellEdgeToLocal
      alpha hAlpha k L slotIndex S e q
    have hp : p ∈ fourEndpointPhysicalCellLocalEdgesValidated
        alpha hAlpha k L slotIndex S e := by
      rw [fourEndpointPhysicalCellLocalEdgesValidated, Finset.mem_image]
      exact ⟨q, hq, rfl⟩
    simp only [fourEndpointDecoratedPhysicalSkeleton,
      fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and]
    refine ⟨e, Finset.mem_image.mpr ⟨p, hp, ?_⟩⟩
    rw [fourEndpointPhysicalEdge_local_roundtrip]
    exact hglobal

/-- Forward after reverse is the identity on the endpoint physical fibre. -/
theorem fourEndpointDecoratedBlockPairingToPhysicalFibre_rightInverse
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    Function.RightInverse
      (fourEndpointPhysicalFibreToDecoratedBlockPairingValidated
        alpha hAlpha k L slotIndex)
      (fourEndpointDecoratedBlockPairingToPhysicalFibre
        alpha hAlpha k L slotIndex) := by
  intro S
  apply Subtype.ext
  apply Subtype.ext
  exact fourEndpointDecoratedPhysicalSkeleton_reverse_eq
    alpha hAlpha k L slotIndex S

/-- Reverse after forward is the identity on decorated endpoint block
pairings. -/
theorem fourEndpointDecoratedBlockPairingToPhysicalFibre_leftInverse
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    Function.LeftInverse
      (fourEndpointPhysicalFibreToDecoratedBlockPairingValidated
        alpha hAlpha k L slotIndex)
      (fourEndpointDecoratedBlockPairingToPhysicalFibre
        alpha hAlpha k L slotIndex) := by
  intro D
  apply fourEndpointDecoratedBlockPairingToPhysicalFibre_injective
    alpha hAlpha k L slotIndex
  exact fourEndpointDecoratedBlockPairingToPhysicalFibre_rightInverse
    alpha hAlpha k L slotIndex
    (fourEndpointDecoratedBlockPairingToPhysicalFibre
      alpha hAlpha k L slotIndex D)

/-- Exact finite equivalence between decorated full endpoint data and the
literal physical endpoint fibre. -/
noncomputable def fourEndpointDecoratedPhysicalEquiv
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    FourEndpointDecoratedBlockPairing alpha hAlpha k L ≃
      FourEndpointPhysicalFibre alpha hAlpha k L where
  toFun := fourEndpointDecoratedBlockPairingToPhysicalFibre
    alpha hAlpha k L slotIndex
  invFun := fourEndpointPhysicalFibreToDecoratedBlockPairingValidated
    alpha hAlpha k L slotIndex
  left_inv := fourEndpointDecoratedBlockPairingToPhysicalFibre_leftInverse
    alpha hAlpha k L slotIndex
  right_inv := fourEndpointDecoratedBlockPairingToPhysicalFibre_rightInverse
    alpha hAlpha k L slotIndex

#print axioms fourEndpointPhysicalEdge_local_roundtrip
#print axioms fourEndpointDecoratedPhysicalSkeleton_reverse_eq
#print axioms fourEndpointDecoratedBlockPairingToPhysicalFibre_rightInverse
#print axioms fourEndpointDecoratedBlockPairingToPhysicalFibre_leftInverse

end

end Erdos625
