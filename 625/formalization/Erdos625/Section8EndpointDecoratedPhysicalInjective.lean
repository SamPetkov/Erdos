import Erdos625.Section8EndpointDecoratedPhysicalFibre
import Mathlib.Tactic

/-!
# Section VIII: injectivity of the decorated endpoint physical map

The existing map from a block pairing with one literal full-cell stub matching
per selected cell to the physical endpoint fibre must not identify two
different decorated witnesses.  This module proves that injectivity directly.

The proof first recovers the block-level support from the physical full pairs.
After the block pairing is fixed, each local stub matching is recovered from
the physical edges in its selected block cell.
-/

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- Equality of two physical images of local edges forces equality of the local
stub edges, even when the surrounding decorations differ. -/
theorem fourEndpointPhysicalEdgeOfLocalEdge_eq_imp
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (dec₁ dec₂ : ∀ e : ↥P.1.edges,
      FourEndpointSelectedCellStubMatching alpha hAlpha k L P e)
    (e : ↥P.1.edges)
    (p q : RowStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.1.1) ×
      ColumnStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.2.1))
    (hEq : fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
        ⟨P, dec₁⟩ e p =
      fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
        ⟨P, dec₂⟩ e q) :
    p = q := by
  apply Prod.ext
  · apply Sigma.ext (x := p.1) (y := q.1) rfl
    apply heq_of_eq
    apply Fin.ext
    simpa only [fourEndpointPhysicalEdgeOfLocalEdge] using
      congrArg (fun z => z.1.2.val) hEq
  · apply Sigma.ext (x := p.2) (y := q.2) rfl
    apply heq_of_eq
    apply Fin.ext
    simpa only [fourEndpointPhysicalEdgeOfLocalEdge] using
      congrArg (fun z => z.2.2.val) hEq

/-- The physical endpoint skeleton determines the selected block-level edge
set of a decorated witness. -/
theorem fourEndpointDecoratedPhysicalSkeleton_eq_imp_blockEdges_eq
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D₁ D₂ : FourEndpointDecoratedBlockPairing alpha hAlpha k L)
    (hEq : fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D₁ =
      fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D₂) :
    D₁.1.1.edges = D₂.1.1.edges := by
  ext edge
  constructor
  · intro hedge
    let e₁ : ↥D₁.1.1.edges := ⟨edge, hedge⟩
    have hfull₁ :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₁.1.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₁.1.2) ∈
        fourEndpointFullPairs alpha hAlpha k
          (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D₁) :=
      (fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
        alpha hAlpha k L slotIndex D₁ _ _).2 ⟨e₁, rfl, rfl⟩
    have hfull₂ :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₁.1.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₁.1.2) ∈
        fourEndpointFullPairs alpha hAlpha k
          (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D₂) := by
      simpa only [hEq] using hfull₁
    obtain ⟨e₂, hrow, hcol⟩ :=
      (fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
        alpha hAlpha k L slotIndex D₂ _ _).1 hfull₂
    have hleft : e₁.1.1 = e₂.1.1 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex hrow
    have hright : e₁.1.2 = e₂.1.2 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex hcol
    have hedgeEq : edge = e₂.1 := Prod.ext hleft hright
    simpa only [hedgeEq] using e₂.2
  · intro hedge
    let e₂ : ↥D₂.1.1.edges := ⟨edge, hedge⟩
    have hfull₂ :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₂.1.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₂.1.2) ∈
        fourEndpointFullPairs alpha hAlpha k
          (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D₂) :=
      (fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
        alpha hAlpha k L slotIndex D₂ _ _).2 ⟨e₂, rfl, rfl⟩
    have hfull₁ :
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₂.1.1,
          fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e₂.1.2) ∈
        fourEndpointFullPairs alpha hAlpha k
          (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D₁) := by
      simpa only [hEq] using hfull₂
    obtain ⟨e₁, hrow, hcol⟩ :=
      (fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
        alpha hAlpha k L slotIndex D₁ _ _).1 hfull₁
    have hleft : e₂.1.1 = e₁.1.1 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex hrow
    have hright : e₂.1.2 = e₁.1.2 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex hcol
    have hedgeEq : edge = e₁.1 := Prod.ext hleft hright
    simpa only [hedgeEq] using e₁.2

/-- The map from decorated endpoint block pairings to the literal physical
endpoint fibre is injective. -/
theorem fourEndpointDecoratedBlockPairingToPhysicalFibre_injective
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    Function.Injective
      (fourEndpointDecoratedBlockPairingToPhysicalFibre
        alpha hAlpha k L slotIndex) := by
  rintro ⟨P₁, dec₁⟩ ⟨P₂, dec₂⟩ hPhysical
  have hSkeleton :
      fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex
          ⟨P₁, dec₁⟩ =
        fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex
          ⟨P₂, dec₂⟩ := by
    exact congrArg (fun S : FourEndpointPhysicalFibre alpha hAlpha k L => S.1.1)
      hPhysical
  have hEdges : P₁.1.edges = P₂.1.edges :=
    fourEndpointDecoratedPhysicalSkeleton_eq_imp_blockEdges_eq
      alpha hAlpha k L slotIndex ⟨P₁, dec₁⟩ ⟨P₂, dec₂⟩ hSkeleton
  have hPskel : P₁.1 = P₂.1 := UnlabelledTypedSkeleton.ext hEdges
  have hP : P₁ = P₂ := Subtype.ext hPskel
  subst P₂
  have hdec : dec₁ = dec₂ := by
    funext e
    have hImage :
        (dec₁ e).1.edges.image (fun p =>
          fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
            ⟨P₁, dec₁⟩ e p) =
        (dec₂ e).1.edges.image (fun p =>
          fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
            ⟨P₁, dec₂⟩ e p) := by
      rw [← fourEndpointDecoratedPhysicalSkeleton_cellEdges_selected
        alpha hAlpha k L slotIndex ⟨P₁, dec₁⟩ e]
      rw [← fourEndpointDecoratedPhysicalSkeleton_cellEdges_selected
        alpha hAlpha k L slotIndex ⟨P₁, dec₂⟩ e]
      rw [hSkeleton]
    have hLocalEdges : (dec₁ e).1.edges = (dec₂ e).1.edges := by
      ext p
      constructor
      · intro hp
        have hpImage :
            fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
                ⟨P₁, dec₁⟩ e p ∈
              (dec₁ e).1.edges.image (fun q =>
                fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
                  ⟨P₁, dec₁⟩ e q) :=
          Finset.mem_image.mpr ⟨p, hp, rfl⟩
        rw [hImage] at hpImage
        obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
        have hpq : p = q :=
          fourEndpointPhysicalEdgeOfLocalEdge_eq_imp
            alpha hAlpha k L slotIndex P₁ dec₁ dec₂ e p q hqp.symm
        simpa only [hpq] using hq
      · intro hp
        have hpImage :
            fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
                ⟨P₁, dec₂⟩ e p ∈
              (dec₂ e).1.edges.image (fun q =>
                fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex
                  ⟨P₁, dec₂⟩ e q) :=
          Finset.mem_image.mpr ⟨p, hp, rfl⟩
        rw [← hImage] at hpImage
        obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpImage
        have hpq : p = q :=
          fourEndpointPhysicalEdgeOfLocalEdge_eq_imp
            alpha hAlpha k L slotIndex P₁ dec₂ dec₁ e p q hqp.symm
        simpa only [hpq] using hq
    exact Subtype.ext (UnlabelledTypedSkeleton.ext hLocalEdges)
  subst dec₂
  rfl

#print axioms fourEndpointPhysicalEdgeOfLocalEdge_eq_imp
#print axioms fourEndpointDecoratedPhysicalSkeleton_eq_imp_blockEdges_eq
#print axioms fourEndpointDecoratedBlockPairingToPhysicalFibre_injective

end

end Erdos625
