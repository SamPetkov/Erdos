import Erdos625.OrderedSignedProfileBridge
import Erdos625.ProfileOverlapDuplicateEdges
import Mathlib.Tactic

/-!
# Semantic ordered/unordered profile bridge

The cardinal equality in `OrderedSignedProfileBridge` is useful for the
second-moment normalization, but it deliberately does not choose a map between
the two finite sample spaces.  This file supplies that map.  A block-labelled
unordered profile partition is sent to the vertex-to-block-slot labeling that
records the labelled part containing each vertex.  Conversely, a fixed-margin
block-slot labeling is sent to its nonempty kernel partition.  Positivity of
the profile block sizes makes every slot a genuine part.

No equivalence in this file is obtained from a cardinality argument.  The
maps expose the actual slot/part correspondence, so Boolean signs and overlap
cells can be transported without changing their meaning.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-! ## From a labelled unordered partition to ordered block slots -/

/-- Repackage the `profilePartSize` fiber as the familiar subtype of parts
having the corresponding natural cardinality. -/
noncomputable def profilePartSizeFiberEquiv
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (s : (ColoringProfile.sizes k).toFinset) :
    {B : P.1.parts // profilePartSize P B = s} ≃ ProfilePartsOfSize P s.1 := by
  apply (Equiv.refl P.1.parts).subtypeEquiv
  intro B
  constructor
  · intro h
    change B.1.card = s.1
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    change B.1.card = s.1
    exact h

/-- The explicit bijection from the parts of a labelled profile partition to
the named block slots.  This uses only its supplied labels, not a cardinality
choice and not any ordering of vertices inside a part. -/
noncomputable def labeledPartsEquivBlockIndex
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) : x.1.1.parts ≃ ProfileBlockIndex k :=
  (Equiv.sigmaFiberEquiv (profilePartSize x.1)).symm.trans
    (Equiv.sigmaCongrRight fun s =>
      (profilePartSizeFiberEquiv x.1 s).trans (x.2 s))

@[simp] theorem labeledPartsEquivBlockIndex_fst
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (B : x.1.1.parts) :
    (labeledPartsEquivBlockIndex x B).1 = profilePartSize x.1 B := rfl

/-- The part bearing the label `q`. -/
noncomputable def labeledProfilePartOfSlot
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (q : ProfileBlockIndex k) : x.1.1.parts :=
  (labeledPartsEquivBlockIndex x).symm q

/-- The vertex-to-block-slot map read from a labelled unordered partition. -/
noncomputable def labeledProfileSlotMap
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) : Fin n → ProfileBlockIndex k :=
  fun v => labeledPartsEquivBlockIndex x (profilePartAt x.1 v)

/-- A vertex has block-slot label `q` exactly when it belongs to the part
carrying `q`. -/
theorem labeledProfileSlotMap_eq_iff_mem
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (v : Fin n) (q : ProfileBlockIndex k) :
    labeledProfileSlotMap x v = q ↔ v ∈ (labeledProfilePartOfSlot x q).1 := by
  change
    labeledPartsEquivBlockIndex x (profilePartAt x.1 v) = q ↔
      v ∈ ((labeledPartsEquivBlockIndex x).symm q).1
  rw [(labeledPartsEquivBlockIndex x).apply_eq_iff_eq_symm_apply]
  constructor
  · intro h
    rw [← h]
    exact mem_profilePartAt x.1 v
  · exact profilePartAt_eq_of_mem x.1 v ((labeledPartsEquivBlockIndex x).symm q)

/-- The vertex fiber of a slot is literally the finite set underlying its
labelled part. -/
noncomputable def labeledProfileVertexFiberEquivPart
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (q : ProfileBlockIndex k) :
    {v : Fin n // labeledProfileSlotMap x v = q} ≃
      (labeledProfilePartOfSlot x q).1 := by
  apply (Equiv.refl (Fin n)).subtypeEquiv
  intro v
  exact labeledProfileSlotMap_eq_iff_mem x v q

/-- The part named by a block slot has the prescribed cardinality. -/
theorem card_labeledProfilePartOfSlot
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (q : ProfileBlockIndex k) :
    (labeledProfilePartOfSlot x q).1.card = profileBlockMargin k q := by
  have h := congrArg (fun z : ProfileBlockIndex k => (z.1 : ℕ))
    ((labeledPartsEquivBlockIndex x).apply_symm_apply q)
  change (profilePartSize x.1 ((labeledPartsEquivBlockIndex x).symm q) : ℕ) =
    (q.1 : ℕ) at h
  change ((labeledProfilePartOfSlot x q).1.card : ℕ) = (q.1 : ℕ)
  simpa only [labeledProfilePartOfSlot, profilePartSize_val] using h

/-- The slot map has the fixed fiber sizes prescribed by the profile. -/
theorem labelingFiberCount_labeledProfileSlotMap
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (q : ProfileBlockIndex k) :
    labelingFiberCount (labeledProfileSlotMap x) q = profileBlockMargin k q := by
  calc
    labelingFiberCount (labeledProfileSlotMap x) q =
        Fintype.card {v : Fin n // labeledProfileSlotMap x v = q} :=
      (card_labelingFiber (labeledProfileSlotMap x) q).symm
    _ = (labeledProfilePartOfSlot x q).1.card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_congr (labeledProfileVertexFiberEquivPart x q)
    _ = profileBlockMargin k q := card_labeledProfilePartOfSlot x q

/-- Semantic forward map: read a labelled unordered profile partition as an
ordered fixed-margin block-slot labeling. -/
noncomputable def labeledProfilePartitionToOrdered
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) : OrderedProfilePartition n k :=
  ⟨labeledProfileSlotMap x, labelingFiberCount_labeledProfileSlotMap x⟩

@[simp] theorem labeledProfilePartitionToOrdered_apply
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (v : Fin n) :
    (labeledProfilePartitionToOrdered x).1 v = labeledProfileSlotMap x v :=
  rfl

/-! ## From ordered block slots to an unordered partition -/

/-- The kernel relation of an ordered block-slot labeling. -/
def orderedSlotKernelSetoid
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) : Setoid (Fin n) :=
  Setoid.ker L.1

/-- Forget block-slot names while retaining their fibers as the parts of a
finite partition. -/
noncomputable def orderedSlotKernelPartition
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) : VertexPartition n := by
  classical
  exact Finpartition.ofSetoid (orderedSlotKernelSetoid L)

/-- Membership in a kernel part is equality of the original block slots. -/
theorem mem_part_orderedSlotKernelPartition_iff
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (v w : Fin n) :
    w ∈ (orderedSlotKernelPartition L).part v ↔ L.1 v = L.1 w := by
  classical
  change w ∈ (Finpartition.ofSetoid (orderedSlotKernelSetoid L)).part v ↔
    (orderedSlotKernelSetoid L) v w
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- Every profile block slot has a positive prescribed margin. -/
theorem profileBlockMargin_pos
    {b : ℕ} (k : ColoringProfile b) (q : ProfileBlockIndex k) :
    0 < profileBlockMargin k q := by
  change 0 < (q.1 : ℕ)
  apply pos_of_mem_profileSizes
  exact Multiset.mem_toFinset.mp q.1.2

/-- Positivity of every actual fiber of a fixed-margin profile labeling. -/
theorem labelingFiberCount_pos_orderedSlot
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    0 < labelingFiberCount L.1 q := by
  rw [L.2 q]
  exact profileBlockMargin_pos k q

/-- A fixed-margin labeling has a vertex in every profile block slot. -/
theorem exists_vertex_of_orderedSlot
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    ∃ v : Fin n, L.1 v = q := by
  classical
  have hcard : 0 < labelingFiberCount L.1 q :=
    labelingFiberCount_pos_orderedSlot L q
  unfold labelingFiberCount at hcard
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
  refine ⟨v, ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hv

/-- A canonical chosen representative of each nonempty ordered block slot. -/
noncomputable def orderedSlotRepresentative
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) : Fin n :=
  Classical.choose (exists_vertex_of_orderedSlot L q)

theorem orderedSlotRepresentative_spec
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    L.1 (orderedSlotRepresentative L q) = q := by
  exact Classical.choose_spec (exists_vertex_of_orderedSlot L q)

/-- The kernel part corresponding to a named block slot. -/
noncomputable def orderedSlotPart
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    (orderedSlotKernelPartition L).parts := by
  classical
  exact ⟨(orderedSlotKernelPartition L).part (orderedSlotRepresentative L q),
    (orderedSlotKernelPartition L).part_mem.mpr
      (Finset.mem_univ (orderedSlotRepresentative L q))⟩

/-- A slot identifies its kernel part with the corresponding labeling fiber. -/
noncomputable def orderedSlotPartEquivFiber
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    (orderedSlotPart L q).1 ≃ {v : Fin n // L.1 v = q} := by
  classical
  apply (Equiv.refl (Fin n)).subtypeEquiv
  intro v
  change v ∈ (orderedSlotKernelPartition L).part (orderedSlotRepresentative L q) ↔ _
  rw [mem_part_orderedSlotKernelPartition_iff,
    orderedSlotRepresentative_spec]
  exact eq_comm

/-- The part corresponding to slot `q` has precisely its prescribed size. -/
theorem card_orderedSlotPart
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    (orderedSlotPart L q).1.card = profileBlockMargin k q := by
  calc
    (orderedSlotPart L q).1.card =
        Fintype.card {v : Fin n // L.1 v = q} := by
      simpa only [Fintype.card_coe] using
        Fintype.card_congr (orderedSlotPartEquivFiber L q)
    _ = labelingFiberCount L.1 q := card_labelingFiber L.1 q
    _ = profileBlockMargin k q := L.2 q

/-- Named block slots and kernel parts are constructively equivalent. -/
noncomputable def orderedSlotEquivKernelParts
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) :
    ProfileBlockIndex k ≃ (orderedSlotKernelPartition L).parts := by
  classical
  apply Equiv.ofBijective (orderedSlotPart L)
  constructor
  · intro q r hqr
    have hmem : orderedSlotRepresentative L q ∈
        (orderedSlotKernelPartition L).part (orderedSlotRepresentative L r) := by
      change orderedSlotRepresentative L q ∈ (orderedSlotPart L r).1
      rw [← hqr]
      exact (orderedSlotKernelPartition L).mem_part (Finset.mem_univ _)
    have hslots :=
      (mem_part_orderedSlotKernelPartition_iff L
        (orderedSlotRepresentative L r) (orderedSlotRepresentative L q)).mp hmem
    simpa [orderedSlotRepresentative_spec] using hslots.symm
  · intro B
    obtain ⟨v, hv⟩ := (orderedSlotKernelPartition L).nonempty_of_mem_parts B.2
    let q := L.1 v
    refine ⟨q, Subtype.ext ?_⟩
    change (orderedSlotKernelPartition L).part (orderedSlotRepresentative L q) = B.1
    have hrep : orderedSlotRepresentative L q ∈
        (orderedSlotKernelPartition L).part v :=
      (mem_part_orderedSlotKernelPartition_iff L v
        (orderedSlotRepresentative L q)).mpr (by
          simp [q, orderedSlotRepresentative_spec])
    calc
      (orderedSlotKernelPartition L).part (orderedSlotRepresentative L q) =
          (orderedSlotKernelPartition L).part v :=
        ((orderedSlotKernelPartition L).mem_part_iff_part_eq_part
          (Finset.mem_univ _) (Finset.mem_univ _)).mp hrep
      _ = B.1 := (orderedSlotKernelPartition L).part_eq_of_mem B.2 hv

@[simp] theorem orderedSlotEquivKernelParts_apply
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    orderedSlotEquivKernelParts L q = orderedSlotPart L q := rfl

/-- Restrict the named-slot/part equivalence to one block size. -/
noncomputable def shapeBlockIndexOfSizeEquivOrderedSlotPartsOfSize
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (s : ℕ) :
    {q : ProfileBlockIndex k // (q.1 : ℕ) = s} ≃
      {B : (orderedSlotKernelPartition L).parts // B.1.card = s} := by
  classical
  apply (orderedSlotEquivKernelParts L).subtypeEquiv
  intro q
  change (q.1 : ℕ) = s ↔ (orderedSlotPart L q).1.card = s
  rw [card_orderedSlotPart]
  rfl

/-- The kernel partition has the requested multiplicity of every block
size. -/
theorem count_partitionShape_orderedSlotKernelPartition
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (s : ℕ) :
    (partitionShape (orderedSlotKernelPartition L)).count s =
      (ColoringProfile.sizes k).count s := by
  classical
  calc
    (partitionShape (orderedSlotKernelPartition L)).count s =
        Fintype.card {B : (orderedSlotKernelPartition L).parts // B.1.card = s} :=
      (card_vertexPartitionPartsOfSize (orderedSlotKernelPartition L) s).symm
    _ = Fintype.card {q : ProfileBlockIndex k // (q.1 : ℕ) = s} :=
      (Fintype.card_congr
        (shapeBlockIndexOfSizeEquivOrderedSlotPartsOfSize L s)).symm
    _ = (ColoringProfile.sizes k).count s :=
      card_shapeBlockIndexOfSize (ColoringProfile.sizes k) s

/-- The profile partition obtained by forgetting the ordered slot names. -/
noncomputable def orderedSlotProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) : ProfilePartition n k := by
  refine ⟨orderedSlotKernelPartition L, ?_⟩
  apply Multiset.ext.mpr
  intro s
  exact count_partitionShape_orderedSlotKernelPartition L s

/-- The kernel part of the explicit forward slot map is the original
unordered part containing the vertex. -/
theorem part_orderedSlotKernelPartition_labeledProfilePartitionToOrdered
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (v : Fin n) :
    (orderedSlotKernelPartition (labeledProfilePartitionToOrdered x)).part v =
      x.1.1.part v := by
  classical
  ext w
  rw [mem_part_orderedSlotKernelPartition_iff,
    mem_part_iff_profilePartAt_eq]
  change
    labeledPartsEquivBlockIndex x (profilePartAt x.1 v) =
      labeledPartsEquivBlockIndex x (profilePartAt x.1 w) ↔
      profilePartAt x.1 w = profilePartAt x.1 v
  constructor
  · intro h
    exact ((labeledPartsEquivBlockIndex x).injective h).symm
  · intro h
    exact congrArg (labeledPartsEquivBlockIndex x) h.symm

/-- Forgetting the explicit forward block labels reconstructs the exact
original vertex partition, not merely one with the same cardinality. -/
theorem orderedSlotKernelPartition_labeledProfilePartitionToOrdered
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) :
    orderedSlotKernelPartition (labeledProfilePartitionToOrdered x) = x.1.1 := by
  classical
  apply Finpartition.ext
  apply Finset.ext
  intro B
  constructor
  · intro hB
    obtain ⟨v, hv⟩ :=
      (orderedSlotKernelPartition (labeledProfilePartitionToOrdered x)).nonempty_of_mem_parts hB
    have hpart :
        (orderedSlotKernelPartition (labeledProfilePartitionToOrdered x)).part v = B :=
      (orderedSlotKernelPartition (labeledProfilePartitionToOrdered x)).part_eq_of_mem hB hv
    have hBP : B = x.1.1.part v :=
      hpart.symm.trans
        (part_orderedSlotKernelPartition_labeledProfilePartitionToOrdered x v)
    rw [hBP]
    exact x.1.1.part_mem.mpr (Finset.mem_univ v)
  · intro hB
    obtain ⟨v, hv⟩ := x.1.1.nonempty_of_mem_parts hB
    have hpart : x.1.1.part v = B := x.1.1.part_eq_of_mem hB hv
    have hBK : B =
        (orderedSlotKernelPartition (labeledProfilePartitionToOrdered x)).part v :=
      hpart.symm.trans
        (part_orderedSlotKernelPartition_labeledProfilePartitionToOrdered x v).symm
    rw [hBK]
    exact (orderedSlotKernelPartition (labeledProfilePartitionToOrdered x)).part_mem.mpr
      (Finset.mem_univ v)

/-- The full profile object, including its shape certificate, is recovered by
the kernel reconstruction of the explicit forward map. -/
theorem orderedSlotProfilePartition_labeledProfilePartitionToOrdered
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) :
    orderedSlotProfilePartition (labeledProfilePartitionToOrdered x) = x.1 := by
  apply Subtype.ext
  exact orderedSlotKernelPartition_labeledProfilePartitionToOrdered x

/-- The canonical block labels recovered from an ordered block-slot
labeling. -/
noncomputable def orderedSlotProfileLabels
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) :
    ProfileBlockLabeling (orderedSlotProfilePartition L) := fun s =>
  (shapeBlockIndexOfSizeEquivOrderedSlotPartsOfSize L s.1).symm.trans
    (shapeBlockIndexOfSizeEquivFin (ColoringProfile.sizes k) s.1
      (Multiset.mem_toFinset.mp s.2))

/-- On the part named by `q`, the recovered profile labeling returns exactly
the second (within-size) coordinate of `q`. -/
theorem orderedSlotProfileLabels_apply_orderedSlotPart
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    orderedSlotProfileLabels L q.1
      ⟨orderedSlotPart L q, by simpa [profileBlockMargin] using card_orderedSlotPart L q⟩ = q.2 := by
  let F := shapeBlockIndexOfSizeEquivOrderedSlotPartsOfSize L (q.1 : ℕ)
  let Bq : {B : (orderedSlotKernelPartition L).parts // B.1.card = (q.1 : ℕ)} :=
    ⟨orderedSlotPart L q, by simpa [profileBlockMargin] using card_orderedSlotPart L q⟩
  have hF : F ⟨q, rfl⟩ = Bq := by
    apply Subtype.ext
    rfl
  have hFinv : F.symm Bq = ⟨q, rfl⟩ := by
    rw [← hF]
    exact F.symm_apply_apply ⟨q, rfl⟩
  change
    (shapeBlockIndexOfSizeEquivFin (ColoringProfile.sizes k) (q.1 : ℕ)
      (Multiset.mem_toFinset.mp q.1.2)) (F.symm Bq) = q.2
  rw [hFinv]
  rcases q with ⟨s, j⟩
  rfl

/-- Semantic reverse map: forget the ordered names only after using them to
label the resulting kernel parts. -/
noncomputable def orderedToLabeledProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) : LabeledProfilePartition n k :=
  ⟨orderedSlotProfilePartition L, orderedSlotProfileLabels L⟩

/-- A label at a part of the advertised size determines the complete block
slot.  The part is abstracted before eliminating the size equality; this is
the small dependent-type detail needed when recovering a semantic inverse. -/
theorem labeledPartsEquivBlockIndex_eq_of_size_label
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileBlockLabeling P)
    (s : (ColoringProfile.sizes k).toFinset)
    (j : Fin ((ColoringProfile.sizes k).count (s : ℕ)))
    (B : P.1.parts) (hs : profilePartSize P B = s)
    (hlabel : d s
      (⟨B, congrArg Subtype.val hs⟩ : ProfilePartsOfSize P s.1) = j) :
    labeledPartsEquivBlockIndex ⟨P, d⟩ B = ⟨s, j⟩ := by
  change
    (Sigma.mk (profilePartSize P B)
      (d (profilePartSize P B)
        (⟨B, rfl⟩ : ProfilePartsOfSize P (profilePartSize P B).1)) :
      ProfileBlockIndex k) = ⟨s, j⟩
  cases hs
  simpa using hlabel

/-- Reading the recovered labels at the part named by an ordered slot gives
that exact slot back. -/
theorem labeledPartsEquivBlockIndex_orderedToLabeled_orderedSlotPart
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (q : ProfileBlockIndex k) :
    labeledPartsEquivBlockIndex (orderedToLabeledProfilePartition L)
      (orderedSlotPart L q) = q := by
  rcases q with ⟨s, j⟩
  let B := orderedSlotPart L ⟨s, j⟩
  have hs : profilePartSize (orderedSlotProfilePartition L) B = s := by
    apply Subtype.ext
    change B.1.card = (s : ℕ)
    change (orderedSlotPart L ⟨s, j⟩).1.card = (s : ℕ)
    simpa [profileBlockMargin] using card_orderedSlotPart L ⟨s, j⟩
  have hlabel := orderedSlotProfileLabels_apply_orderedSlotPart L ⟨s, j⟩
  apply labeledPartsEquivBlockIndex_eq_of_size_label
    (orderedSlotProfilePartition L) (orderedSlotProfileLabels L) s j B hs
  simpa only [B] using hlabel

/-- The semantic reverse construction reads back the original ordered
block-slot labeling pointwise. -/
theorem labeledProfileSlotMap_orderedToLabeled
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (v : Fin n) :
    labeledProfileSlotMap (orderedToLabeledProfilePartition L) v = L.1 v := by
  let q := L.1 v
  have hmem : v ∈ (orderedSlotPart L q).1 := by
    change v ∈ (orderedSlotKernelPartition L).part (orderedSlotRepresentative L q)
    rw [mem_part_orderedSlotKernelPartition_iff]
    exact orderedSlotRepresentative_spec L q
  have hpart : profilePartAt (orderedSlotProfilePartition L) v =
      orderedSlotPart L q :=
    profilePartAt_eq_of_mem (orderedSlotProfilePartition L) v
      (orderedSlotPart L q) hmem
  change labeledPartsEquivBlockIndex (orderedToLabeledProfilePartition L)
    (profilePartAt (orderedSlotProfilePartition L) v) = L.1 v
  rw [hpart]
  simpa only [q] using
    labeledPartsEquivBlockIndex_orderedToLabeled_orderedSlotPart L q

/-- One of the two semantic inverse laws: rebuilding labelled parts from an
ordered labeling and reading their slots back is definitionally the original
fixed-margin labeling. -/
theorem labeledProfilePartitionToOrdered_orderedToLabeled
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) :
    labeledProfilePartitionToOrdered (orderedToLabeledProfilePartition L) = L := by
  apply Subtype.ext
  funext v
  exact labeledProfileSlotMap_orderedToLabeled L v

/-- The explicit semantic forward map is injective: its vertex-slot map
recovers both the underlying unordered partition and the supplied labels. -/
theorem labeledProfilePartitionToOrdered_injective
    {b n : ℕ} {k : ColoringProfile b} :
    Function.Injective
      (labeledProfilePartitionToOrdered (n := n) (k := k)) := by
  intro x y hxy
  rcases x with ⟨P, d⟩
  rcases y with ⟨Q, e⟩
  have hP : P = Q := by
    calc
      P = orderedSlotProfilePartition (labeledProfilePartitionToOrdered ⟨P, d⟩) :=
        (orderedSlotProfilePartition_labeledProfilePartitionToOrdered ⟨P, d⟩).symm
      _ = orderedSlotProfilePartition (labeledProfilePartitionToOrdered ⟨Q, e⟩) :=
        congrArg orderedSlotProfilePartition hxy
      _ = Q := orderedSlotProfilePartition_labeledProfilePartitionToOrdered ⟨Q, e⟩
  cases hP
  have hfun : labeledProfileSlotMap ⟨P, d⟩ = labeledProfileSlotMap ⟨P, e⟩ := by
    exact congrArg Subtype.val hxy
  have hde : d = e := by
    funext s
    apply Equiv.ext
    intro Bs
    obtain ⟨v, hv⟩ := P.1.nonempty_of_mem_parts Bs.1.2
    have hpart : profilePartAt P v = Bs.1 :=
      profilePartAt_eq_of_mem P v Bs.1 hv
    have hs : profilePartSize P Bs.1 = s := by
      apply Subtype.ext
      change Bs.1.1.card = (s : ℕ)
      exact Bs.2
    have hEd : labeledPartsEquivBlockIndex ⟨P, d⟩ Bs.1 = ⟨s, d s Bs⟩ := by
      apply labeledPartsEquivBlockIndex_eq_of_size_label P d s (d s Bs) Bs.1 hs
      have hBs :
          (⟨Bs.1, congrArg Subtype.val hs⟩ : ProfilePartsOfSize P s.1) = Bs := by
        apply Subtype.ext
        rfl
      rw [hBs]
    have hEe : labeledPartsEquivBlockIndex ⟨P, e⟩ Bs.1 = ⟨s, e s Bs⟩ := by
      apply labeledPartsEquivBlockIndex_eq_of_size_label P e s (e s Bs) Bs.1 hs
      have hBs :
          (⟨Bs.1, congrArg Subtype.val hs⟩ : ProfilePartsOfSize P s.1) = Bs := by
        apply Subtype.ext
        rfl
      rw [hBs]
    have hmap := congrFun hfun v
    change labeledPartsEquivBlockIndex ⟨P, d⟩ (profilePartAt P v) =
      labeledPartsEquivBlockIndex ⟨P, e⟩ (profilePartAt P v) at hmap
    rw [hpart, hEd, hEe] at hmap
    apply Fin.ext
    exact congrArg (fun z : ProfileBlockIndex k => (z.2 : ℕ)) hmap
  cases hde
  rfl

/-- The second semantic inverse law follows from injectivity of the explicit
forward map together with the already proved forward-after-reverse identity. -/
theorem orderedToLabeledProfilePartition_labeledProfilePartitionToOrdered
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) :
    orderedToLabeledProfilePartition (labeledProfilePartitionToOrdered x) = x := by
  apply labeledProfilePartitionToOrdered_injective
  rw [labeledProfilePartitionToOrdered_orderedToLabeled]

/-- The genuine constructive semantic equivalence between block-labelled
unordered profile partitions and ordered fixed-margin block-slot labelings.
Unlike `labeledProfilePartitionEquivOrdered`, this equivalence is built from
the explicit vertex/part/slot maps above, rather than from a cardinality
equality. -/
noncomputable def labeledProfilePartitionEquivOrderedSemantic
    {b n : ℕ} (k : ColoringProfile b) :
    LabeledProfilePartition n k ≃ OrderedProfilePartition n k where
  toFun := labeledProfilePartitionToOrdered
  invFun := orderedToLabeledProfilePartition
  left_inv := orderedToLabeledProfilePartition_labeledProfilePartitionToOrdered
  right_inv := labeledProfilePartitionToOrdered_orderedToLabeled

@[simp] theorem labeledProfilePartitionEquivOrderedSemantic_apply
    {b n : ℕ} (k : ColoringProfile b) (x : LabeledProfilePartition n k) :
    labeledProfilePartitionEquivOrderedSemantic k x =
      labeledProfilePartitionToOrdered x := rfl

@[simp] theorem labeledProfilePartitionEquivOrderedSemantic_symm_apply
    {b n : ℕ} (k : ColoringProfile b) (L : OrderedProfilePartition n k) :
    (labeledProfilePartitionEquivOrderedSemantic k).symm L =
      orderedToLabeledProfilePartition L := rfl

/-! ## Signed data and overlaps -/

/-- Validity for Boolean signs carried by named ordered block slots.  As in
`profileSignValid`, `false` means independent and `true` means clique. -/
def orderedSlotSignValid
    {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (L : OrderedProfilePartition n k)
    (τ : ProfileBlockIndex k → Bool) : Prop :=
  ∀ q : ProfileBlockIndex k,
    match τ q with
    | false => G.IsIndepSet ((orderedSlotPart L q).1 : Set (Fin n))
    | true => G.IsClique ((orderedSlotPart L q).1 : Set (Fin n))

/-- Forgetting labels after the explicit forward map recovers precisely the
part that originally carried each slot label. -/
theorem orderedSlotPart_labeledProfilePartitionToOrdered
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (q : ProfileBlockIndex k) :
    (orderedSlotPart (labeledProfilePartitionToOrdered x) q).1 =
      (labeledProfilePartOfSlot x q).1 := by
  ext v
  change
    v ∈ (orderedSlotKernelPartition (labeledProfilePartitionToOrdered x)).part
      (orderedSlotRepresentative (labeledProfilePartitionToOrdered x) q) ↔
      v ∈ (labeledProfilePartOfSlot x q).1
  rw [mem_part_orderedSlotKernelPartition_iff]
  constructor
  · intro h
    have hrep : labeledProfileSlotMap x
        (orderedSlotRepresentative (labeledProfilePartitionToOrdered x) q) = q :=
      orderedSlotRepresentative_spec (labeledProfilePartitionToOrdered x) q
    exact (labeledProfileSlotMap_eq_iff_mem x v q).mp (hrep.symm.trans h).symm
  · intro h
    have hv : labeledProfileSlotMap x v = q :=
      (labeledProfileSlotMap_eq_iff_mem x v q).mpr h
    have hrep : labeledProfileSlotMap x
        (orderedSlotRepresentative (labeledProfilePartitionToOrdered x) q) = q :=
      orderedSlotRepresentative_spec (labeledProfilePartitionToOrdered x) q
    exact hrep.trans hv.symm

/-- Transport a Boolean sign from the parts of a labelled unordered partition
to the corresponding named ordered slots. -/
def labeledSignsToOrderedSlots
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (σ : x.1.1.parts → Bool) :
    ProfileBlockIndex k → Bool :=
  fun q => σ (labeledProfilePartOfSlot x q)

/-- Transport a Boolean sign on ordered slots back to the kernel parts. -/
def orderedSlotSignsToParts
    {b n : ℕ} {k : ColoringProfile b}
    (L : OrderedProfilePartition n k) (τ : ProfileBlockIndex k → Bool) :
    (orderedSlotProfilePartition L).1.parts → Bool :=
  fun B => τ ((orderedSlotEquivKernelParts L).symm B)

/-- Boolean signed-part validity is invariant under the forward semantic
map from labelled parts to ordered block slots. -/
theorem profileSignValid_iff_orderedSlotSignValid_labeled
    {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (x : LabeledProfilePartition n k)
    (σ : x.1.1.parts → Bool) :
    profileSignValid G x.1 σ ↔
      orderedSlotSignValid G (labeledProfilePartitionToOrdered x)
        (labeledSignsToOrderedSlots x σ) := by
  constructor
  · intro h q
    unfold profileSignValid at h
    have hq := h (labeledProfilePartOfSlot x q)
    have hpart := orderedSlotPart_labeledProfilePartitionToOrdered x q
    cases hsign : σ (labeledProfilePartOfSlot x q) with
    | false => simpa [labeledSignsToOrderedSlots, hsign, hpart] using hq
    | true => simpa [labeledSignsToOrderedSlots, hsign, hpart] using hq
  · intro h B
    unfold orderedSlotSignValid at h
    let q := labeledPartsEquivBlockIndex x B
    have hB : labeledProfilePartOfSlot x q = B := by
      dsimp [q, labeledProfilePartOfSlot]
      exact (labeledPartsEquivBlockIndex x).symm_apply_apply B
    have hq := h q
    have hpart := orderedSlotPart_labeledProfilePartitionToOrdered x q
    cases hsign : σ B with
    | false => simpa [labeledSignsToOrderedSlots, hsign, hB, hpart] using hq
    | true => simpa [labeledSignsToOrderedSlots, hsign, hB, hpart] using hq

/-- Boolean signed-part validity is also invariant under the reverse kernel
construction from an ordered block-slot labeling. -/
theorem profileSignValid_iff_orderedSlotSignValid_kernel
    {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (L : OrderedProfilePartition n k)
    (τ : ProfileBlockIndex k → Bool) :
    profileSignValid G (orderedSlotProfilePartition L)
      (orderedSlotSignsToParts L τ) ↔ orderedSlotSignValid G L τ := by
  constructor
  · intro h q
    unfold profileSignValid at h
    have hq := h (orderedSlotPart L q)
    have hinv : (orderedSlotEquivKernelParts L).symm (orderedSlotPart L q) = q := by
      change (orderedSlotEquivKernelParts L).symm
        (orderedSlotEquivKernelParts L q) = q
      exact (orderedSlotEquivKernelParts L).symm_apply_apply q
    cases hsign : τ q with
    | false => simpa [orderedSlotSignsToParts, hsign, hinv] using hq
    | true => simpa [orderedSlotSignsToParts, hsign, hinv] using hq
  · intro h B
    unfold orderedSlotSignValid at h
    let q := (orderedSlotEquivKernelParts L).symm B
    have hB : orderedSlotPart L q = B := by
      change orderedSlotEquivKernelParts L q = B
      exact (orderedSlotEquivKernelParts L).apply_symm_apply B
    have hq := h q
    cases hsign : τ q with
    | false => simpa [orderedSlotSignsToParts, q, hsign, hB] using hq
    | true => simpa [orderedSlotSignsToParts, q, hsign, hB] using hq

/-- The block-slot map of a labelled profile gives the expected part under
the slot/part correspondence. -/
theorem labeledProfileSlotMap_part_of_slot
    {b n : ℕ} {k : ColoringProfile b}
    (x : LabeledProfilePartition n k) (q : ProfileBlockIndex k) (v : Fin n) :
    labeledProfileSlotMap x v = q ↔ v ∈ (labeledProfilePartOfSlot x q).1 :=
  labeledProfileSlotMap_eq_iff_mem x v q

/-- The overlap cell of two kernel partitions is exactly the ordered
overlap-table cell of their original block-slot labelings. -/
theorem orderedOverlapCount_eq_profileOverlapCellCount
    {b n : ℕ} {k : ColoringProfile b}
    (L M : OrderedProfilePartition n k)
    (q r : ProfileBlockIndex k) :
    orderedOverlapCount L.1 M.1 q r =
      ProfilePartition.overlapCellCount
        (orderedSlotProfilePartition L) (orderedSlotProfilePartition M)
        (orderedSlotPart L q) (orderedSlotPart M r) := by
  unfold orderedOverlapCount ProfilePartition.overlapCellCount profileOverlapCellCount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨hvq, hvr⟩
    constructor
    · change v ∈ (orderedSlotKernelPartition L).part (orderedSlotRepresentative L q)
      exact (mem_part_orderedSlotKernelPartition_iff L
        (orderedSlotRepresentative L q) v).mpr (by
          simpa [orderedSlotRepresentative_spec] using hvq.symm)
    · change v ∈ (orderedSlotKernelPartition M).part (orderedSlotRepresentative M r)
      exact (mem_part_orderedSlotKernelPartition_iff M
        (orderedSlotRepresentative M r) v).mpr (by
          simpa [orderedSlotRepresentative_spec] using hvr.symm)
  · rintro ⟨hvq, hvr⟩
    constructor
    · have h := (mem_part_orderedSlotKernelPartition_iff L
        (orderedSlotRepresentative L q) v).mp hvq
      simpa [orderedSlotRepresentative_spec] using h.symm
    · have h := (mem_part_orderedSlotKernelPartition_iff M
        (orderedSlotRepresentative M r) v).mp hvr
      simpa [orderedSlotRepresentative_spec] using h.symm

#print axioms labeledProfilePartitionToOrdered
#print axioms orderedSlotEquivKernelParts
#print axioms orderedSlotKernelPartition_labeledProfilePartitionToOrdered
#print axioms labeledProfilePartitionToOrdered_injective
#print axioms labeledProfilePartitionEquivOrderedSemantic
#print axioms profileSignValid_iff_orderedSlotSignValid_labeled
#print axioms profileSignValid_iff_orderedSlotSignValid_kernel
#print axioms orderedOverlapCount_eq_profileOverlapCellCount

end

end Erdos625
