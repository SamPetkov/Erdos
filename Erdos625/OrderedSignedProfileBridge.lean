import Erdos625.ColoringProfileEnumerationInjective
import Erdos625.OrderedOverlapLaw
import Erdos625.SignedProfileWitness
import Mathlib.Tactic

/-!
# The block-label-only ordered/unordered bridge

The ordered overlap calculation labels equal-sized blocks, but does not order
vertices inside a block.  This module isolates exactly that finite quotient.
The multiplier is therefore only the product of the factorials of the block
multiplicities, rather than the larger decoration multiplier used in the
enumeration proof.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A block slot records a positive block size occurring in the profile and
one label below its multiplicity. -/
abbrev ProfileBlockIndex {b : ℕ} (k : ColoringProfile b) :=
  ShapeBlockIndex (ColoringProfile.sizes k)

/-- The prescribed number of vertices in a profile block slot. -/
def profileBlockMargin {b : ℕ} (k : ColoringProfile b) :
    ProfileBlockIndex k → ℕ := fun q => q.1

/-- An ordered profile partition is a vertex labeling by block slots having
the prescribed fiber cardinality at every slot. -/
abbrev OrderedProfilePartition {b : ℕ} (n : ℕ)
    (k : ColoringProfile b) :=
  FixedFiberLabeling (V := Fin n) (profileBlockMargin k)

/-- Label equal-sized parts of an unordered profile partition.  No ordering
of vertices inside a part is included. -/
abbrev ProfileBlockLabeling {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) :=
  ∀ s : (ColoringProfile.sizes k).toFinset,
    ProfilePartsOfSize P s.1 ≃
      Fin ((ColoringProfile.sizes k).count (s : ℕ))

/-- Choosing a block slot and then a position inside it is exactly choosing a
canonical shape slot. -/
def profileBlockPositionEquivShapeSlot {b : ℕ}
    (k : ColoringProfile b) :
    (Σ q : ProfileBlockIndex k, Fin (profileBlockMargin k q)) ≃
      ShapeSlot (ColoringProfile.sizes k) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- All unordered profile partitions equipped with block labels. -/
abbrev LabeledProfilePartition {b : ℕ} (n : ℕ)
    (k : ColoringProfile b) :=
  Σ P : ProfilePartition n k, ProfileBlockLabeling P

/-- The block-label-only quotient multiplier. -/
def profileBlockLabelMultiplier {b : ℕ} (k : ColoringProfile b) : ℕ :=
  ∏ s : (ColoringProfile.sizes k).toFinset,
    Nat.factorial ((ColoringProfile.sizes k).count (s : ℕ))

/-- The block-label multiplier has the coordinate form used in the
manuscript. -/
theorem profileBlockLabelMultiplier_eq_coordinateProduct
    {b : ℕ} (k : ColoringProfile b) :
    profileBlockLabelMultiplier k =
      ∏ i : Fin b, Nat.factorial (k i) := by
  rw [profileBlockLabelMultiplier]
  rw [show
      (Finset.univ : Finset (ColoringProfile.sizes k).toFinset) =
        (ColoringProfile.sizes k).toFinset.attach by
    ext s
    simp]
  rw [Finset.prod_attach
    (s := (ColoringProfile.sizes k).toFinset)
    (f := fun s : ℕ =>
      Nat.factorial ((ColoringProfile.sizes k).count s))]
  have hzero : 0 ∉ (ColoringProfile.sizes k).toFinset := by
    simpa only [Multiset.mem_toFinset] using zero_not_mem_profileSizes k
  rw [← Finset.erase_eq_of_notMem hzero]
  exact ColoringProfile.prod_factorial_count_sizes k

/-- Every unordered partition of the fixed profile has exactly the same
number of block labelings. -/
theorem card_profileBlockLabeling {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) :
    Fintype.card (ProfileBlockLabeling P) =
      profileBlockLabelMultiplier k := by
  classical
  rw [Fintype.card_pi, profileBlockLabelMultiplier]
  apply Finset.prod_congr rfl
  intro s hs
  have hparts :
      Fintype.card (ProfilePartsOfSize P s.1) =
        (ColoringProfile.sizes k).count (s : ℕ) :=
    card_profilePartsOfSize P s.1
  let e : ProfilePartsOfSize P s ≃
      Fin ((ColoringProfile.sizes k).count (s : ℕ)) :=
    Fintype.equivOfCardEq
      (hparts.trans (Fintype.card_fin _).symm)
  calc
    Fintype.card
        (ProfilePartsOfSize P s ≃
          Fin ((ColoringProfile.sizes k).count (s : ℕ))) =
        Nat.factorial (Fintype.card (ProfilePartsOfSize P s)) :=
      Fintype.card_equiv e
    _ = Nat.factorial ((ColoringProfile.sizes k).count (s : ℕ)) := by
      rw [hparts]

/-- Summing the block-slot margins recovers the profile vertex mass. -/
theorem sum_profileBlockMargin_eq_vertexMass {b : ℕ}
    (k : ColoringProfile b) :
    ∑ q : ProfileBlockIndex k, profileBlockMargin k q =
      ColoringProfile.vertexMass k := by
  calc
    (∑ q : ProfileBlockIndex k, profileBlockMargin k q) =
        ∑ q : ProfileBlockIndex k,
          Fintype.card (Fin (profileBlockMargin k q)) := by
      simp
    _ = Fintype.card
          (Σ q : ProfileBlockIndex k, Fin (profileBlockMargin k q)) :=
      Fintype.card_sigma.symm
    _ = Fintype.card (ShapeSlot (ColoringProfile.sizes k)) :=
      Fintype.card_congr (profileBlockPositionEquivShapeSlot k)
    _ = (ColoringProfile.sizes k).sum :=
      card_shapeSlot (ColoringProfile.sizes k)
    _ = ColoringProfile.vertexMass k := rfl

/-- Existence of an ordered fixed-margin profile partition forces the same
vertex-mass equation as existence of an unordered profile partition. -/
theorem OrderedProfilePartition.vertexMass_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P : OrderedProfilePartition n k) :
    ColoringProfile.vertexMass k = n := by
  calc
    ColoringProfile.vertexMass k =
        ∑ q : ProfileBlockIndex k, profileBlockMargin k q :=
      (sum_profileBlockMargin_eq_vertexMass k).symm
    _ = ∑ q : ProfileBlockIndex k,
          labelingFiberCount P.1 q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (P.2 q).symm
    _ = Fintype.card (Fin n) := sum_labelingFiberCount P.1
    _ = n := Fintype.card_fin n

/-- The product of the factorials of the ordered-block margins is the
within-block factorial product. -/
theorem prod_factorial_profileBlockMargin {b : ℕ}
    (k : ColoringProfile b) :
    (∏ q : ProfileBlockIndex k,
        Nat.factorial (profileBlockMargin k q)) =
      ∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i := by
  let m := ColoringProfile.sizes k
  change (∏ q : ShapeBlockIndex m, Nat.factorial (q.1 : ℕ)) = _
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (Finset.univ : Finset m.toFinset) = m.toFinset.attach by
    ext s
    simp]
  rw [Finset.prod_attach
    (s := m.toFinset)
    (f := fun s : ℕ => Nat.factorial s ^ m.count s)]
  calc
    (∏ s ∈ m.toFinset, Nat.factorial s ^ m.count s) =
        (m.map Nat.factorial).prod := by
      rw [Finset.prod_multiset_map_count]
    _ = ∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i := by
      exact ColoringProfile.prod_map_factorial_sizes k

/-- Exact cross-multiplied cardinality of ordered profile partitions. -/
theorem card_orderedProfilePartition_mul_withinFactorials
    {b n : ℕ} (k : ColoringProfile b)
    (hmass : ColoringProfile.vertexMass k = n) :
    Fintype.card (OrderedProfilePartition n k) *
        (∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i) =
      Nat.factorial n := by
  have htotal :
      ∑ q : ProfileBlockIndex k, profileBlockMargin k q =
        Fintype.card (Fin n) := by
    rw [sum_profileBlockMargin_eq_vertexMass, hmass,
      Fintype.card_fin]
  simpa only [Fintype.card_fin, prod_factorial_profileBlockMargin] using
    card_fixedFiberLabeling_mul_factorials
      (V := Fin n) (profileBlockMargin k) htotal

/-- Exact factorial-quotient cardinality of ordered profile partitions. -/
theorem card_orderedProfilePartition {b n : ℕ}
    (k : ColoringProfile b)
    (hmass : ColoringProfile.vertexMass k = n) :
    Fintype.card (OrderedProfilePartition n k) =
      Nat.factorial n /
        (∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i) := by
  let A := ∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i
  have hA : A ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      pow_ne_zero _ (Nat.factorial_ne_zero _)
  apply Nat.eq_div_of_mul_eq_left hA
  simpa only [A] using
    card_orderedProfilePartition_mul_withinFactorials k hmass

/-- The total number of block-labeled unordered partitions is the unordered
cardinality times the constant label multiplier. -/
theorem card_labeledProfilePartition {b n : ℕ}
    (k : ColoringProfile b) :
    Fintype.card (LabeledProfilePartition n k) =
      Fintype.card (ProfilePartition n k) *
        profileBlockLabelMultiplier k := by
  classical
  calc
    Fintype.card (LabeledProfilePartition n k) =
        ∑ P : ProfilePartition n k,
          Fintype.card (ProfileBlockLabeling P) := Fintype.card_sigma
    _ = ∑ _P : ProfilePartition n k,
          profileBlockLabelMultiplier k := by
      apply Finset.sum_congr rfl
      intro P hP
      exact card_profileBlockLabeling P
    _ = Fintype.card (ProfilePartition n k) *
          profileBlockLabelMultiplier k := by simp

/-- Under the necessary mass constraint, block-labeled unordered partitions
and fixed-margin ordered partitions have the same cardinality. -/
theorem card_labeledProfilePartition_eq_orderedProfilePartition
    {b n : ℕ} (k : ColoringProfile b)
    (hmass : ColoringProfile.vertexMass k = n) :
    Fintype.card (LabeledProfilePartition n k) =
      Fintype.card (OrderedProfilePartition n k) := by
  classical
  let A := ∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i
  let M := profileBlockLabelMultiplier k
  have hunordered := profileEnumerationStatement n k hmass
  have hU : Fintype.card (ProfilePartition n k) * A * M =
      Nat.factorial n := by
    have henum :
        Fintype.card (ProfilePartition n k) =
          ColoringProfile.enumerativeCoefficient k := by
      simpa only [ProfileEnumerationStatement, Nat.card_eq_fintype_card]
        using hunordered
    calc
      Fintype.card (ProfilePartition n k) * A * M =
          ColoringProfile.enumerativeCoefficient k * A * M := by rw [henum]
      _ = Nat.factorial (ColoringProfile.vertexMass k) := by
        simp only [A, M]
        rw [profileBlockLabelMultiplier_eq_coordinateProduct]
        exact
          ColoringProfile.enumerativeCoefficient_mul_coordinateDenominator_eq k
      _ = Nat.factorial n := by rw [hmass]
  have hO : Fintype.card (OrderedProfilePartition n k) * A =
      Nat.factorial n := by
    simpa only [A] using
      card_orderedProfilePartition_mul_withinFactorials k hmass
  rw [card_labeledProfilePartition]
  have hA : 0 < A := by
    exact Finset.prod_pos fun i hi =>
      pow_pos (Nat.factorial_pos _) _
  apply Nat.eq_of_mul_eq_mul_right hA
  calc
    (Fintype.card (ProfilePartition n k) * M) * A =
        Nat.factorial n := by
      rw [← hU]
      ac_rfl
    _ = Fintype.card (OrderedProfilePartition n k) * A := hO.symm

/-- The cardinal equality holds without a separate feasibility hypothesis:
when the mass equation fails, both finite types are empty. -/
theorem card_labeledProfilePartition_eq_orderedProfilePartition_all
    {b n : ℕ} (k : ColoringProfile b) :
    Fintype.card (LabeledProfilePartition n k) =
      Fintype.card (OrderedProfilePartition n k) := by
  by_cases hmass : ColoringProfile.vertexMass k = n
  · exact card_labeledProfilePartition_eq_orderedProfilePartition k hmass
  · have hleft : Fintype.card (LabeledProfilePartition n k) = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun P => hmass P.1.vertexMass_eq⟩
    have hright : Fintype.card (OrderedProfilePartition n k) = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun P => hmass P.vertexMass_eq⟩
    rw [hleft, hright]

/-- The requested block-label-only equivalence.  Its existence is obtained
from the two independent exact cardinality computations above; no internal
vertex orders enter either side. -/
noncomputable def labeledProfilePartitionEquivOrdered
    {b n : ℕ} (k : ColoringProfile b) :
    LabeledProfilePartition n k ≃ OrderedProfilePartition n k :=
  Fintype.equivOfCardEq
    (card_labeledProfilePartition_eq_orderedProfilePartition_all k)

/-- A block-labeled signed witness.  The auxiliary block labels do not alter
the underlying partition or its signs. -/
abbrev OrderedSignedProfileWitness {b : ℕ} (n : ℕ)
    (k : ColoringProfile b) :=
  Σ w : SignedProfileWitness n k, ProfileBlockLabeling w.1

/-- Valid signed witnesses, bundled as a finite type. -/
abbrev ValidSignedProfileWitness {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) :=
  {w : SignedProfileWitness n k // validSignedProfileWitness G w}

/-- Valid block-labeled signed witnesses. -/
abbrev ValidOrderedSignedProfileWitness {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) :=
  Σ w : ValidSignedProfileWitness G k, ProfileBlockLabeling w.1.1

noncomputable instance instFintypeValidSignedProfileWitness
    {b n : ℕ} (G : LabeledGraph n) (k : ColoringProfile b) :
    Fintype (ValidSignedProfileWitness G k) :=
  Fintype.ofFinite _

noncomputable instance instFintypeValidOrderedSignedProfileWitness
    {b n : ℕ} (G : LabeledGraph n) (k : ColoringProfile b) :
    Fintype (ValidOrderedSignedProfileWitness G k) :=
  Fintype.ofFinite _

/-- The number of valid block-labeled signed profile witnesses. -/
noncomputable def orderedSignedProfileCount {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) : ℕ :=
  ∑ w : ValidSignedProfileWitness G k,
    Fintype.card (ProfileBlockLabeling w.1.1)

/-- The bundled valid-witness type has the cardinality used by the original
filter definition of `signedProfileCount`. -/
theorem card_validSignedProfileWitness {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) :
    Fintype.card (ValidSignedProfileWitness G k) =
      signedProfileCount G k := by
  classical
  unfold signedProfileCount
  rw [Fintype.card_subtype]

/-- The block-label-only multiplier cancels pointwise, before taking either
the first or the second moment. -/
theorem orderedSignedProfileCount_eq_mul_signedProfileCount
    {b n : ℕ} (G : LabeledGraph n) (k : ColoringProfile b) :
    orderedSignedProfileCount G k =
      signedProfileCount G k * profileBlockLabelMultiplier k := by
  classical
  rw [orderedSignedProfileCount]
  calc
    (∑ w : ValidSignedProfileWitness G k,
        Fintype.card (ProfileBlockLabeling w.1.1)) =
        ∑ _w : ValidSignedProfileWitness G k,
          profileBlockLabelMultiplier k := by
      apply Finset.sum_congr rfl
      intro w hw
      exact card_profileBlockLabeling w.1.1
    _ = Fintype.card (ValidSignedProfileWitness G k) *
          profileBlockLabelMultiplier k := by simp
    _ = signedProfileCount G k *
          profileBlockLabelMultiplier k := by
      rw [card_validSignedProfileWitness]

/-- Coordinate form of the pointwise ordered/unordered cancellation. -/
theorem orderedSignedProfileCount_eq_coordinateMultiplier
    {b n : ℕ} (G : LabeledGraph n) (k : ColoringProfile b) :
    orderedSignedProfileCount G k =
      signedProfileCount G k *
        ∏ i : Fin b, Nat.factorial (k i) := by
  rw [orderedSignedProfileCount_eq_mul_signedProfileCount,
    profileBlockLabelMultiplier_eq_coordinateProduct]

end

end Erdos625
