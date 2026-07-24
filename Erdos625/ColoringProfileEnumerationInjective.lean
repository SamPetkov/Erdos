import Erdos625.ColoringProfileEnumerationInverse

/-!
# Injectivity of coloring-profile enumeration

This module proves that a canonical slot equivalence determines the
decorated unordered partition from which it was read.
-/

namespace Erdos625

noncomputable section

/-- The `(size,label)` block index assigned to a decorated part. -/
def decoratedPartBlockIndexMap
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    P.1.parts → ShapeBlockIndex (ColoringProfile.sizes k) := fun B ↦ by
  let s := profilePartSize P B
  exact ⟨s, d.1 s ⟨B, rfl⟩⟩

/-- Recover the decorated part carrying a given block index. -/
def decoratedBlockIndexPartMap
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    ShapeBlockIndex (ColoringProfile.sizes k) → P.1.parts := fun q ↦
  ((d.1 q.1).symm q.2).1

/-- Recovering a block index immediately after reading it from a part
returns that part. -/
theorem decoratedBlockIndexPartMap_leftInverse
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    Function.LeftInverse (decoratedBlockIndexPartMap P d)
      (decoratedPartBlockIndexMap P d) := by
  intro B
  change
    ((d.1 (profilePartSize P B)).symm
      (d.1 (profilePartSize P B) ⟨B, rfl⟩)).1 = B
  exact congrArg Subtype.val <|
    (d.1 (profilePartSize P B)).symm_apply_apply ⟨B, rfl⟩

/-- Distinct decorated parts have distinct `(size,label)` indices. -/
theorem decoratedPartBlockIndexMap_injective
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    Function.Injective (decoratedPartBlockIndexMap P d) :=
  (decoratedBlockIndexPartMap_leftInverse P d).injective

/-- The first two coordinates of the decorated slot map are exactly the
index assigned to the part containing the vertex. -/
@[simp] theorem slotBlockMap_decoratedProfileEquiv
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) (v : Fin n) :
    slotBlockMap (decoratedProfileEquiv P d) v =
      decoratedPartBlockIndexMap P d (profilePartAt P v) := by
  rfl

/-- Membership in a partition part is equivalent to equality of the
corresponding bundled parts. -/
theorem mem_part_iff_profilePartAt_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (v w : Fin n) :
    w ∈ P.1.part v ↔ profilePartAt P w = profilePartAt P v := by
  constructor
  · intro hw
    exact profilePartAt_eq_of_mem P w (profilePartAt P v) hw
  · intro h
    have hw := mem_profilePartAt P w
    rw [h] at hw
    exact hw

/-- The kernel part of a decorated slot map at `v` is the original part
of `P` at `v`. -/
theorem part_slotKernelPartition_decoratedProfileEquiv
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) (v : Fin n) :
    (slotKernelPartition (decoratedProfileEquiv P d)).part v = P.1.part v := by
  classical
  ext w
  rw [mem_part_slotKernelPartition_iff, mem_part_iff_profilePartAt_eq,
    slotBlockMap_decoratedProfileEquiv,
    slotBlockMap_decoratedProfileEquiv]
  constructor
  · intro h
    exact (decoratedPartBlockIndexMap_injective P d h).symm
  · intro h
    exact congrArg (decoratedPartBlockIndexMap P d) h.symm

/-- Applying the kernel reconstruction to a decorated slot map recovers
the original unordered partition. -/
theorem slotKernelPartition_decoratedProfileEquiv
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    slotKernelPartition (decoratedProfileEquiv P d) = P.1 := by
  classical
  apply Finpartition.ext
  apply Finset.ext
  intro B
  constructor
  · intro hB
    obtain ⟨v, hv⟩ :=
      (slotKernelPartition (decoratedProfileEquiv P d)).nonempty_of_mem_parts hB
    have hpart :
        (slotKernelPartition (decoratedProfileEquiv P d)).part v = B :=
      (slotKernelPartition (decoratedProfileEquiv P d)).part_eq_of_mem hB hv
    have hBP : B = P.1.part v :=
      hpart.symm.trans (part_slotKernelPartition_decoratedProfileEquiv P d v)
    rw [hBP]
    exact P.1.part_mem.mpr (Finset.mem_univ v)
  · intro hB
    obtain ⟨v, hv⟩ := P.1.nonempty_of_mem_parts hB
    have hpart : P.1.part v = B := P.1.part_eq_of_mem hB hv
    have hBK : B =
        (slotKernelPartition (decoratedProfileEquiv P d)).part v :=
      hpart.symm.trans
        (part_slotKernelPartition_decoratedProfileEquiv P d v).symm
    rw [hBK]
    exact (slotKernelPartition
      (decoratedProfileEquiv P d)).part_mem.mpr (Finset.mem_univ v)

/-! ## Recovery of the decoration once the partition is fixed -/

/-- Equal size/part inputs give equal numerical label outputs for one
fixed decoration. -/
theorem decorationLabel_val_of_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P)
    (s t : (ColoringProfile.sizes k).toFinset)
    (Bs : ProfilePartsOfSize P s.1)
    (Bt : ProfilePartsOfSize P t.1)
    (hst : s = t) (hB : Bs.1 = Bt.1) :
    (d.1 s Bs : ℕ) = (d.1 t Bt : ℕ) := by
  subst t
  have hsub : Bs = Bt := Subtype.ext hB
  rw [hsub]

/-- Equal part/vertex inputs give equal numerical within-part outputs for
one fixed decoration. -/
theorem decorationOrder_val_of_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P)
    {B C : P.1.parts} (z : B.1) (w : C.1)
    (hBC : B = C) (hzw : z.1 = w.1) :
    (d.2 B z : ℕ) = (d.2 C w : ℕ) := by
  subst C
  have hsub : z = w := Subtype.ext hzw
  rw [hsub]

/-- Equality of decorated slot equivalences gives equality of the label
coordinate read at every vertex. -/
theorem decorationLabelAtVertex_val_of_equiv_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d e : ProfileDecoration P)
    (h : decoratedProfileEquiv P d = decoratedProfileEquiv P e)
    (v : Fin n) :
    (d.1 (profilePartSize P (profilePartAt P v))
        ⟨profilePartAt P v, rfl⟩ : ℕ) =
      (e.1 (profilePartSize P (profilePartAt P v))
        ⟨profilePartAt P v, rfl⟩ : ℕ) := by
  have hpoint := congrArg
    (fun E : Fin n ≃ ShapeSlot (ColoringProfile.sizes k) ↦ E v) h
  exact congrArg
    (fun y : ShapeSlot (ColoringProfile.sizes k) ↦ (y.2.1 : ℕ)) hpoint

/-- Equality of decorated slot equivalences gives equality of the
within-part coordinate read at every vertex. -/
theorem decorationOrderAtVertex_val_of_equiv_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d e : ProfileDecoration P)
    (h : decoratedProfileEquiv P d = decoratedProfileEquiv P e)
    (v : Fin n) :
    (d.2 (profilePartAt P v) ⟨v, mem_profilePartAt P v⟩ : ℕ) =
      (e.2 (profilePartAt P v) ⟨v, mem_profilePartAt P v⟩ : ℕ) := by
  have hpoint := congrArg
    (fun E : Fin n ≃ ShapeSlot (ColoringProfile.sizes k) ↦ E v) h
  exact congrArg
    (fun y : ShapeSlot (ColoringProfile.sizes k) ↦ (y.2.2 : ℕ)) hpoint

/-- With the partition fixed, equality of slot equivalences forces equality
of all equal-size labelings. -/
theorem profileDecoration_labels_eq_of_equiv_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d e : ProfileDecoration P)
    (h : decoratedProfileEquiv P d = decoratedProfileEquiv P e) :
    d.1 = e.1 := by
  funext s
  apply Equiv.ext
  intro Bs
  apply Fin.ext
  let B : P.1.parts := Bs.1
  obtain ⟨v, hv⟩ := P.1.nonempty_of_mem_parts B.2
  let Bv := profilePartAt P v
  let sv := profilePartSize P Bv
  let Bsv : ProfilePartsOfSize P sv.1 := ⟨Bv, rfl⟩
  have hBv : Bv = B := profilePartAt_eq_of_mem P v B hv
  have hs : sv = s := by
    apply Subtype.ext
    change Bv.1.card = (s : ℕ)
    rw [hBv]
    exact Bs.2
  have hcoord := decorationLabelAtVertex_val_of_equiv_eq P d e h v
  change (d.1 sv Bsv : ℕ) = (e.1 sv Bsv : ℕ) at hcoord
  calc
    (d.1 s Bs : ℕ) = (d.1 sv Bsv : ℕ) :=
      (decorationLabel_val_of_eq P d sv s Bsv Bs hs hBv).symm
    _ = (e.1 sv Bsv : ℕ) := hcoord
    _ = (e.1 s Bs : ℕ) :=
      decorationLabel_val_of_eq P e sv s Bsv Bs hs hBv

/-- With the partition fixed, equality of slot equivalences forces equality
of every within-part ordering. -/
theorem profileDecoration_orders_eq_of_equiv_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d e : ProfileDecoration P)
    (h : decoratedProfileEquiv P d = decoratedProfileEquiv P e) :
    d.2 = e.2 := by
  funext B
  apply Equiv.ext
  intro z
  apply Fin.ext
  let Bv := profilePartAt P z.1
  let zv : Bv.1 := ⟨z.1, mem_profilePartAt P z.1⟩
  have hBv : Bv = B := profilePartAt_eq_of_mem P z.1 B z.2
  have hcoord := decorationOrderAtVertex_val_of_equiv_eq P d e h z.1
  change (d.2 Bv zv : ℕ) = (e.2 Bv zv : ℕ) at hcoord
  calc
    (d.2 B z : ℕ) = (d.2 Bv zv : ℕ) :=
      decorationOrder_val_of_eq P d z zv hBv.symm rfl
    _ = (e.2 Bv zv : ℕ) := hcoord
    _ = (e.2 B z : ℕ) :=
      decorationOrder_val_of_eq P e zv z hBv rfl

/-- For a fixed profile partition, the decorated slot equivalence uniquely
determines the full decoration. -/
theorem profileDecoration_eq_of_equiv_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d e : ProfileDecoration P)
    (h : decoratedProfileEquiv P d = decoratedProfileEquiv P e) : d = e := by
  apply Prod.ext
  · exact profileDecoration_labels_eq_of_equiv_eq P d e h
  · exact profileDecoration_orders_eq_of_equiv_eq P d e h

/-! ## The total bijection and exact enumeration bridge -/

/-- The total decorated-profile map is injective. -/
theorem totalProfileDecorationMap_injective
    {b n : ℕ} {k : ColoringProfile b} :
    Function.Injective
      (totalProfileDecorationMap (b := b) (n := n) (k := k)) := by
  rintro ⟨P, d⟩ ⟨Q, e⟩ h
  have hparts : P.1 = Q.1 := by
    calc
      P.1 = slotKernelPartition (decoratedProfileEquiv P d) :=
        (slotKernelPartition_decoratedProfileEquiv P d).symm
      _ = slotKernelPartition (decoratedProfileEquiv Q e) :=
        congrArg
          (fun E : Fin n ≃ ShapeSlot (ColoringProfile.sizes k) ↦
            slotKernelPartition E) h
      _ = Q.1 := slotKernelPartition_decoratedProfileEquiv Q e
  have hP : P = Q := Subtype.ext hparts
  cases hP
  exact congrArg (Sigma.mk P) (profileDecoration_eq_of_equiv_eq P d e h)

/-- The explicit reconstruction proves surjectivity of the total
decorated-profile map. -/
theorem totalProfileDecorationMap_surjective
    {b n : ℕ} {k : ColoringProfile b} :
    Function.Surjective
      (totalProfileDecorationMap (b := b) (n := n) (k := k)) := by
  intro E
  exact ⟨slotTotalProfileDecoration E,
    totalProfileDecorationMap_slotTotalProfileDecoration E⟩

/-- Decorated unordered profile partitions are exactly canonical slot
equivalences. -/
noncomputable def totalProfileDecorationEquiv
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) :
    TotalProfileDecoration n k ≃
      (Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :=
  Equiv.ofBijective totalProfileDecorationMap
    ⟨totalProfileDecorationMap_injective,
      totalProfileDecorationMap_surjective⟩

/-- The combinatorial bijection obligation isolated by the enumeration
module is fully discharged. -/
theorem profileDecorationBijectionStatement
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) :
    ProfileDecorationBijectionStatement n k :=
  ⟨totalProfileDecorationEquiv n k⟩

/-- Exact unordered-profile enumeration under the necessary vertex-mass
constraint. -/
theorem profileEnumerationStatement
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n) :
    ProfileEnumerationStatement n k :=
  profileEnumerationStatement_of_decorationBijection n k hMass
    (profileDecorationBijectionStatement n k)

/-- Unconditional mass-constrained form of the exact profile first-moment
formula (4.2).  The enumeration bridge is now supplied internally. -/
theorem profileColoringExpectation_eq_formula
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n) :
    profileColoringExpectation n k =
      ((Nat.factorial n /
          ((∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i) *
            ∏ i : Fin b, Nat.factorial (k i)) : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k :=
  profileColoringExpectation_eq_formula_of_mass n k hMass
    (profileEnumerationStatement n k hMass)

end

end Erdos625
