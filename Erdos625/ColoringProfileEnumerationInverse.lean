import Erdos625.ColoringProfileEnumeration

/-!
# Inverse laws for coloring-profile enumeration

This module isolates the dependent equality calculations proving that the
explicit reconstruction from a canonical slot equivalence is inverse to
the decorated-partition map.
-/

namespace Erdos625

noncomputable section

/-- Transport between finite initial segments preserves the underlying
natural number. -/
@[simp] theorem cast_fin_val {a b : ℕ} (h : Fin a = Fin b) (x : Fin a) :
    ((cast h x : Fin b) : ℕ) = (x : ℕ) := by
  exact Fin.val_eq_val_of_heq (cast_heq h x)

/-- Transporting a vertex bundled in a partition part along equality of
parts preserves the underlying vertex. -/
@[simp] theorem cast_partitionPart_val {n : ℕ} (P : VertexPartition n)
    {B C : P.parts} (h : B = C) (z : B.1) :
    ((cast
        (congrArg (fun D : P.parts ↦ (↥D.1 : Type)) h) z : C.1) : Fin n) =
      z.1 := by
  cases h
  rfl

/-- The reconstructed part containing `v` is the kernel part indexed by
the first two coordinates of `e v`. -/
theorem profilePartAt_slotProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) (v : Fin n) :
    profilePartAt (slotProfilePartition e) v =
      slotBlockPart e (slotBlockMap e v) := by
  classical
  apply Subtype.ext
  change (slotKernelPartition e).part v =
    (slotKernelPartition e).part
      (slotBlockRepresentative e (slotBlockMap e v))
  have hmem : v ∈
      (slotKernelPartition e).part
        (slotBlockRepresentative e (slotBlockMap e v)) :=
    (mem_part_slotKernelPartition_iff e
      (slotBlockRepresentative e (slotBlockMap e v)) v).mpr (by
        rw [slotBlockMap_representative])
  exact ((slotKernelPartition e).mem_part_iff_part_eq_part
    (Finset.mem_univ _) (Finset.mem_univ _)).mp hmem

/-- The size coordinate recovered from the reconstructed part at `v` is
the first coordinate of `e v`. -/
theorem profilePartSize_slotProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) (v : Fin n) :
    profilePartSize (slotProfilePartition e)
        (profilePartAt (slotProfilePartition e) v) =
      (e v).1 := by
  apply Subtype.ext
  change
    (profilePartAt (slotProfilePartition e) v).1.card = ((e v).1 : ℕ)
  rw [profilePartAt_slotProfilePartition, card_slotBlockPart]
  rfl

/-- A kernel part bundled with its exact size. -/
noncomputable def slotBlockPartOfSize
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    ProfilePartsOfSize (slotProfilePartition e) (q.1 : ℕ) :=
  ⟨slotBlockPart e q, card_slotBlockPart e q⟩

/-- Pinning a block index at its own size returns its label coordinate. -/
theorem shapeBlockIndexOfSizeEquivFin_apply_self
    (m : Multiset ℕ) (q : ShapeBlockIndex m) :
    shapeBlockIndexOfSizeEquivFin m (q.1 : ℕ)
        (Multiset.mem_toFinset.mp q.1.2) ⟨q, rfl⟩ = q.2 := by
  apply Fin.ext
  rfl

/-- Restricting the block-index/part equivalence and then pulling a kernel
part back recovers its original block index. -/
theorem shapeBlockIndexOfSizeEquivKernelPartsOfSize_symm_slotBlockPart
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    (shapeBlockIndexOfSizeEquivKernelPartsOfSize e (q.1 : ℕ)).symm
        (slotBlockPartOfSize e q) = ⟨q, rfl⟩ := by
  apply (shapeBlockIndexOfSizeEquivKernelPartsOfSize e (q.1 : ℕ)).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (shapeBlockIndexEquivKernelParts_apply e q).symm

/-- The reconstructed equal-size label of a kernel part is its canonical
block-label coordinate. -/
theorem slotProfileLabels_apply_slotBlockPartOfSize
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    slotProfileLabels e q.1 (slotBlockPartOfSize e q) = q.2 := by
  change
    shapeBlockIndexOfSizeEquivFin (ColoringProfile.sizes k) (q.1 : ℕ)
      (Multiset.mem_toFinset.mp q.1.2)
      ((shapeBlockIndexOfSizeEquivKernelPartsOfSize e (q.1 : ℕ)).symm
        (slotBlockPartOfSize e q)) = q.2
  rw [shapeBlockIndexOfSizeEquivKernelPartsOfSize_symm_slotBlockPart]
  simpa only using
    shapeBlockIndexOfSizeEquivFin_apply_self (ColoringProfile.sizes k) q

/-- The kernel-part equivalence reads the third slot coordinate; casts of
the dependent bounds do not change its underlying natural value. -/
@[simp] theorem slotBlockPartEquivFin_val
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k))
    (z : (slotBlockPart e q).1) :
    ((slotBlockPartEquivFin e q z : Fin q.1.1) : ℕ) =
      (((e z.1).2.2 : Fin (e z.1).1.1) : ℕ) := by
  simp [slotBlockPartEquivFin, slotBlockPartEquivFiber,
    slotBlockVertexFiberEquivSlotFiber,
    slotBlockSlotFiberEquivNestedFiber,
    nestedShapeSlotFiberEquivFin]
  rfl

/-- Reconstructed within-part orders preserve the numerical third slot
coordinate of every vertex. -/
theorem slotProfilePartOrder_val
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (B : (slotProfilePartition e).1.parts) (z : B.1) :
    ((slotProfilePartOrder e B z : Fin B.1.card) : ℕ) =
      (((e z.1).2.2 : Fin (e z.1).1.1) : ℕ) := by
  let E := shapeBlockIndexEquivKernelParts e
  let q := E.symm B
  have hB : slotBlockPart e q = B := by
    simpa only [E, q, shapeBlockIndexEquivKernelParts_apply] using
      E.apply_symm_apply B
  have hsource : (↥B.1 : Type) = ↥(slotBlockPart e q).1 :=
    congrArg (fun C : (slotKernelPartition e).parts ↦ (↥C.1 : Type)) hB.symm
  have htarget : (q.1 : ℕ) = B.1.card := by
    exact (card_slotBlockPart e q).symm.trans <|
      congrArg (fun C : (slotKernelPartition e).parts ↦ C.1.card) hB
  have hz : ((cast hsource z : (slotBlockPart e q).1) : Fin n) = z.1 := by
    simpa only [hsource] using
      cast_partitionPart_val (slotKernelPartition e) hB.symm z
  change
    (((((Equiv.cast hsource).trans
      ((slotBlockPartEquivFin e q).trans
        (Equiv.cast (congrArg Fin htarget)))) z : Fin B.1.card)) : ℕ) =
      (((e z.1).2.2 : Fin (e z.1).1.1) : ℕ)
  simp only [Equiv.trans_apply, Equiv.cast_apply, cast_fin_val,
    slotBlockPartEquivFin_val]
  rw [hz]

/-- The label reconstructed at the part containing `v` has the numerical
value of the second slot coordinate of `e v`. -/
theorem slotProfileLabels_profilePartAt_val
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) (v : Fin n) :
    ((slotProfileLabels e
        (profilePartSize (slotProfilePartition e)
          (profilePartAt (slotProfilePartition e) v))
        ⟨profilePartAt (slotProfilePartition e) v, rfl⟩) : ℕ) =
      ((e v).2.1 : ℕ) := by
  let P := slotProfilePartition e
  let B := profilePartAt P v
  let s := profilePartSize P B
  let Bs : ProfilePartsOfSize P s.1 := ⟨B, rfl⟩
  let q := slotBlockMap e v
  have hB : B = slotBlockPart e q :=
    profilePartAt_slotProfilePartition e v
  have hs : s = (e v).1 :=
    profilePartSize_slotProfilePartition e v
  have hq : q.1 = (e v).1 := rfl
  have hsq : s = q.1 := hs.trans hq.symm
  have hsqVal : (s : ℕ) = (q.1 : ℕ) := congrArg Subtype.val hsq
  have hpair :
      (⟨s, Bs⟩ : Σ t : (ColoringProfile.sizes k).toFinset,
        ProfilePartsOfSize P t.1) =
      ⟨q.1, slotBlockPartOfSize e q⟩ := by
    apply Sigma.ext hsq
    apply (Subtype.heq_iff_coe_eq (fun C ↦ by
      change (C.1.card = (s : ℕ)) ↔ (C.1.card = (q.1 : ℕ))
      rw [hsqVal])).2
    exact hB
  have hlabel := congrArg
    (fun u : Σ t : (ColoringProfile.sizes k).toFinset,
      ProfilePartsOfSize P t.1 ↦ (slotProfileLabels e u.1 u.2 : ℕ)) hpair
  change (slotProfileLabels e s Bs : ℕ) = ((e v).2.1 : ℕ)
  calc
    (slotProfileLabels e s Bs : ℕ) =
        (slotProfileLabels e q.1 (slotBlockPartOfSize e q) : ℕ) := hlabel
    _ = (q.2 : ℕ) := congrArg
      (fun j : Fin ((ColoringProfile.sizes k).count (q.1 : ℕ)) ↦ j.1)
      (slotProfileLabels_apply_slotBlockPartOfSize e q)
    _ = ((e v).2.1 : ℕ) := rfl

/-- Reconstructing a decorated profile from `e` and reading its slots
returns `e` pointwise. -/
theorem decoratedProfileMap_slotProfileDecoration
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) (v : Fin n) :
    decoratedProfileMap (slotProfilePartition e)
        (slotProfileDecoration e) v = e v := by
  generalize hEv : e v = y
  rcases y with ⟨t, j, x⟩
  unfold decoratedProfileMap
  dsimp only [slotProfileDecoration]
  have hs : profilePartSize (slotProfilePartition e)
      (profilePartAt (slotProfilePartition e) v) = t := by
    rw [profilePartSize_slotProfilePartition, hEv]
  cases hs
  refine congrArg (@Sigma.mk
    (ColoringProfile.sizes k).toFinset
    (fun s ↦ Fin ((ColoringProfile.sizes k).count (s : ℕ)) × Fin s.1)
    (profilePartSize (slotProfilePartition e)
      (profilePartAt (slotProfilePartition e) v))) ?_
  apply Prod.ext
  · apply Fin.ext
    have h := slotProfileLabels_profilePartAt_val e v
    rw [hEv] at h
    exact h
  · apply Fin.ext
    have h := slotProfilePartOrder_val e
      (profilePartAt (slotProfilePartition e) v)
      ⟨v, mem_profilePartAt (slotProfilePartition e) v⟩
    rw [hEv] at h
    exact h

/-- The reconstructed decoration is a right inverse of the forgetful map
at the level of slot equivalences. -/
theorem decoratedProfileEquiv_slotProfileDecoration
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    decoratedProfileEquiv (slotProfilePartition e)
        (slotProfileDecoration e) = e := by
  apply Equiv.ext
  intro v
  exact decoratedProfileMap_slotProfileDecoration e v

/-- Read a reconstructed profile and decoration as one sigma value. -/
noncomputable def slotTotalProfileDecoration
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    TotalProfileDecoration n k :=
  ⟨slotProfilePartition e, slotProfileDecoration e⟩

/-- Forget a total decorated profile to its canonical slot equivalence. -/
def totalProfileDecorationMap
    {b n : ℕ} {k : ColoringProfile b} :
    TotalProfileDecoration n k →
      (Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) := fun z ↦
  decoratedProfileEquiv z.1 z.2

/-- Explicit right-inverse law for the total forgetful map. -/
theorem totalProfileDecorationMap_slotTotalProfileDecoration
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    totalProfileDecorationMap (slotTotalProfileDecoration e) = e :=
  decoratedProfileEquiv_slotProfileDecoration e

end

end Erdos625
