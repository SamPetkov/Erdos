import Erdos625.ColoringProfileFirstMoment
import Mathlib.Data.Fintype.Perm

/-!
# Enumeration of unordered coloring profiles

This module develops the missing finite counting bridge isolated in
`ColoringProfileFirstMoment`.  The basic counting device is the type of
canonical labelled slots associated to a multiset of positive block sizes.
It is kept separate from the first-moment foundation so that the latter
remains independently auditable.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Canonical labelled positions for a multiset `m` of positive block sizes.
For every distinct size `s`, a slot records a block number below `m.count s`
and a position below `s` inside that block. -/
abbrev ShapeSlot (m : Multiset ℕ) :=
  Σ s : m.toFinset, Fin (m.count (s : ℕ)) × Fin s.1

/-- The canonical slot type contains exactly `m.sum` positions. -/
theorem card_shapeSlot (m : Multiset ℕ) :
    Fintype.card (ShapeSlot m) = m.sum := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  change (∑ s ∈ (Finset.univ : Finset m.toFinset),
    m.count (s : ℕ) * (s : ℕ)) = m.sum
  rw [show (Finset.univ : Finset m.toFinset) = m.toFinset.attach by
    ext s
    simp]
  rw [Finset.sum_attach
    (s := m.toFinset) (f := fun s : ℕ ↦ m.count s * s)]
  simpa [nsmul_eq_mul, mul_comm] using
    (Finset.sum_multiset_count m).symm

/-- Profile sizes are strictly positive; in particular the Bell denominator
does not acquire Mathlib's exceptional empty-block convention. -/
theorem zero_not_mem_profileSizes {b : ℕ} (k : ColoringProfile b) :
    0 ∉ ColoringProfile.sizes k := by
  intro h
  simp only [ColoringProfile.sizes, Multiset.mem_sum] at h
  obtain ⟨i, _hi, hzero⟩ := h
  have heq : 0 = i.1 + 1 := Multiset.eq_of_mem_replicate hzero
  omega

/-- Parts of a profile partition having a specified cardinality. -/
abbrev ProfilePartsOfSize {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (s : ℕ) :=
  {B : P.1.parts // B.1.card = s}

/-- The number of parts of size `s` in an arbitrary vertex partition is
the multiplicity of `s` in its shape multiset. -/
theorem card_vertexPartitionPartsOfSize {n : ℕ}
    (P : VertexPartition n) (s : ℕ) :
    Fintype.card {B : P.parts // B.1.card = s} =
      (partitionShape P).count s := by
  classical
  calc
    Fintype.card {B : P.parts // B.1.card = s} =
        (P.parts.filter fun B ↦ B.card = s).card := by
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun B : P.parts ↦ B.1.card = s) (by simp)]
      change (P.parts.attach.filter fun B ↦ B.1.card = s).card = _
      simpa only [Finset.card_map, Finset.card_attach] using congrArg Finset.card
        (Finset.filter_attach (fun B : Finset (Fin n) ↦ B.card = s) P.parts)
    _ = (partitionShape P).count s := by
      rw [partitionShape, Multiset.count_map]
      change
        (P.parts.1.filter fun B ↦ B.card = s).card =
          (P.parts.1.filter fun B ↦ s = B.card).card
      congr 2
      funext B
      exact propext eq_comm

/-- The number of parts of size `s` is the multiplicity of `s` in the
profile multiset. -/
theorem card_profilePartsOfSize {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (s : ℕ) :
    Fintype.card (ProfilePartsOfSize P s) =
      (ColoringProfile.sizes k).count s := by
  classical
  calc
    Fintype.card (ProfilePartsOfSize P s) =
        (P.1.parts.filter fun B ↦ B.card = s).card := by
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun B : P.1.parts ↦ B.1.card = s) (by simp)]
      change (P.1.parts.attach.filter fun B ↦ B.1.card = s).card = _
      simpa only [Finset.card_map, Finset.card_attach] using congrArg Finset.card
        (Finset.filter_attach (fun B : Finset (Fin n) ↦ B.card = s) P.1.parts)
    _ = (partitionShape P.1).count s := by
      rw [partitionShape, Multiset.count_map]
      change
        (P.1.parts.1.filter fun B ↦ B.card = s).card =
          (P.1.parts.1.filter fun B ↦ s = B.card).card
      congr 2
      funext B
      exact propext eq_comm
    _ = (ColoringProfile.sizes k).count s := by rw [P.2]

/-! ## The exact factorial size of a forgetful fiber -/

/-- A decoration labels equal-sized unordered parts and linearly orders the
vertices inside every part.  Forgetting these two pieces of information is
exactly the passage from a bijection with canonical slots to an unordered
partition. -/
abbrev ProfileDecoration {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) :=
  (∀ s : (ColoringProfile.sizes k).toFinset,
      ProfilePartsOfSize P s.1 ≃
        Fin ((ColoringProfile.sizes k).count (s : ℕ))) ×
    (∀ B : P.1.parts, B.1 ≃ Fin B.1.card)

/-- Every fixed unordered profile partition has exactly the factorial
decoration count occurring in `Multiset.bell_mul_eq`. -/
theorem card_profileDecoration {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) :
    Fintype.card (ProfileDecoration P) =
      ((ColoringProfile.sizes k).map Nat.factorial).prod *
        ∏ s ∈ (ColoringProfile.sizes k).toFinset,
          Nat.factorial ((ColoringProfile.sizes k).count s) := by
  classical
  let m := ColoringProfile.sizes k
  have hlabels :
      (∏ s : m.toFinset,
          Fintype.card
            (ProfilePartsOfSize P s.1 ≃ Fin (m.count (s : ℕ)))) =
        ∏ s ∈ m.toFinset, Nat.factorial (m.count s) := by
    have hcard (s : m.toFinset) :
        Fintype.card
            (ProfilePartsOfSize P s.1 ≃ Fin (m.count (s : ℕ))) =
          Nat.factorial (m.count (s : ℕ)) := by
      have hparts :
          Fintype.card (ProfilePartsOfSize P s.1) =
            m.count (s : ℕ) := by
        simpa only [m] using card_profilePartsOfSize P s.1
      let e : ProfilePartsOfSize P s.1 ≃ Fin (m.count (s : ℕ)) :=
        Fintype.equivOfCardEq (hparts.trans (Fintype.card_fin _).symm)
      calc
        Fintype.card
            (ProfilePartsOfSize P s.1 ≃ Fin (m.count (s : ℕ))) =
            Nat.factorial (Fintype.card (ProfilePartsOfSize P s.1)) :=
          Fintype.card_equiv e
        _ = Nat.factorial (m.count (s : ℕ)) := by rw [hparts]
    simp_rw [hcard]
    rw [show (Finset.univ : Finset m.toFinset) = m.toFinset.attach by
      ext s
      simp]
    rw [Finset.prod_attach
      (s := m.toFinset) (f := fun s : ℕ ↦ Nat.factorial (m.count s))]
  have horders :
      (∏ B : P.1.parts,
          Fintype.card (B.1 ≃ Fin B.1.card)) =
        (m.map Nat.factorial).prod := by
    have hcard (B : P.1.parts) :
        Fintype.card (B.1 ≃ Fin B.1.card) =
          Nat.factorial B.1.card := by
      simpa only [Fintype.card_coe] using
        (Fintype.card_equiv B.1.equivFin)
    simp_rw [hcard]
    rw [show (Finset.univ : Finset P.1.parts) = P.1.parts.attach by
      ext B
      simp]
    rw [Finset.prod_attach
      (s := P.1.parts) (f := fun B ↦ Nat.factorial B.card)]
    rw [← Finset.prod_map_val]
    calc
      (P.1.parts.1.map (fun B ↦ Nat.factorial B.card)).prod =
          ((P.1.parts.1.map Finset.card).map Nat.factorial).prod := by
        rw [Multiset.map_map]
        rfl
      _ = (m.map Nat.factorial).prod := by
        rw [show P.1.parts.1.map Finset.card = partitionShape P.1 from rfl,
          P.2]
  change
    Fintype.card
      ((∀ s : m.toFinset,
          ProfilePartsOfSize P s.1 ≃ Fin (m.count (s : ℕ))) ×
        (∀ B : P.1.parts, B.1 ≃ Fin B.1.card)) = _
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi,
    hlabels, horders]
  simp only [m]
  rw [mul_comm]

/-! ## From a decorated partition to a canonical slot bijection -/

/-- The unique part of `P` containing a vertex. -/
def profilePartAt {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (v : Fin n) : P.1.parts :=
  ⟨P.1.part v, P.1.part_mem.mpr (Finset.mem_univ v)⟩

@[simp] theorem profilePartAt_val {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (v : Fin n) :
    (profilePartAt P v).1 = P.1.part v := rfl

theorem mem_profilePartAt {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (v : Fin n) :
    v ∈ (profilePartAt P v).1 :=
  P.1.mem_part (Finset.mem_univ v)

theorem profilePartAt_eq_of_mem {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (v : Fin n) (B : P.1.parts)
    (hv : v ∈ B.1) : profilePartAt P v = B := by
  apply Subtype.ext
  exact P.1.part_eq_of_mem B.2 hv

/-- The size of a part, bundled as an element of the prescribed shape's
support. -/
def profilePartSize {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (B : P.1.parts) :
    (ColoringProfile.sizes k).toFinset := by
  refine ⟨B.1.card, ?_⟩
  apply Multiset.mem_toFinset.mpr
  have hmem : B.1.card ∈ partitionShape P.1 :=
    Multiset.mem_map.mpr ⟨B.1, B.2, rfl⟩
  simpa only [P.2] using hmem

@[simp] theorem profilePartSize_val {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (B : P.1.parts) :
    (profilePartSize P B : ℕ) = B.1.card := rfl

/-- The forward map that reads a decorated partition as canonical slots. -/
def decoratedProfileMap {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    Fin n → ShapeSlot (ColoringProfile.sizes k) := fun v ↦ by
  let B := profilePartAt P v
  let s := profilePartSize P B
  let Bs : ProfilePartsOfSize P s.1 := ⟨B, rfl⟩
  exact ⟨s, d.1 s Bs, d.2 B ⟨v, mem_profilePartAt P v⟩⟩

/-- The evident inverse operation: select the labelled part and then the
ordered vertex within it. -/
def decoratedProfileInv {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    ShapeSlot (ColoringProfile.sizes k) → Fin n := fun y ↦ by
  let s := y.1
  let Bs : ProfilePartsOfSize P s.1 := (d.1 s).symm y.2.1
  let B : P.1.parts := Bs.1
  let x : Fin B.1.card := Fin.cast Bs.2.symm y.2.2
  exact ((d.2 B).symm x).1

/-- Reading a decorated partition and selecting the resulting slot returns
the original vertex. -/
theorem decoratedProfileInv_map {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    Function.LeftInverse (decoratedProfileInv P d)
      (decoratedProfileMap P d) := by
  intro v
  let B := profilePartAt P v
  let s := profilePartSize P B
  let Bs : ProfilePartsOfSize P s.1 := ⟨B, rfl⟩
  have hBs : (d.1 s).symm (d.1 s Bs) = Bs :=
    Equiv.symm_apply_apply (d.1 s) Bs
  change
    ((d.2 ((d.1 s).symm (d.1 s Bs)).1).symm
      (Fin.cast ((d.1 s).symm (d.1 s Bs)).2.symm
        (d.2 B ⟨v, mem_profilePartAt P v⟩))).1 = v
  rw [hBs]
  exact congrArg Subtype.val (Equiv.symm_apply_apply (d.2 B)
    ⟨v, mem_profilePartAt P v⟩)

/-- A decorated unordered partition canonically enumerates all vertices by
the shape slots.  Surjectivity is obtained from the proved left inverse and
the exact equality of the two finite cardinalities. -/
def decoratedProfileEquiv {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (d : ProfileDecoration P) :
    Fin n ≃ ShapeSlot (ColoringProfile.sizes k) where
  toFun := decoratedProfileMap P d
  invFun := decoratedProfileInv P d
  left_inv := decoratedProfileInv_map P d
  right_inv :=
    (decoratedProfileInv_map P d).rightInverse_of_card_le (by
      rw [Fintype.card_fin, card_shapeSlot]
      change ColoringProfile.vertexMass k ≤ n
      rw [P.vertexMass_eq])

/-! ## Reconstructing the unordered partition from a slot equivalence -/

/-- Canonical block indices: a size together with a label among blocks of
that size. -/
abbrev ShapeBlockIndex (m : Multiset ℕ) :=
  Σ s : m.toFinset, Fin (m.count (s : ℕ))

/-- When a size occurs in `m`, canonical block indices carrying that size
are precisely their labels `Fin (m.count s)`. -/
noncomputable def shapeBlockIndexOfSizeEquivFin
    (m : Multiset ℕ) (s : ℕ) (hs : s ∈ m) :
    {q : ShapeBlockIndex m // (q.1 : ℕ) = s} ≃ Fin (m.count s) := by
  classical
  let t : m.toFinset := ⟨s, Multiset.mem_toFinset.mpr hs⟩
  let pin :
      {q : ShapeBlockIndex m // (q.1 : ℕ) = s} ≃
        {q : ShapeBlockIndex m // q.1 = t} := by
    apply (Equiv.refl (ShapeBlockIndex m)).subtypeEquiv
    intro q
    constructor
    · intro h
      apply Subtype.ext
      exact h
    · intro h
      simpa [t] using congrArg (fun u : m.toFinset ↦ (u : ℕ)) h
  exact pin.trans (Equiv.sigmaSubtype t)

/-- For every natural number `s`, the number of canonical block indices
carrying size `s` is exactly its multiplicity in `m`. -/
theorem card_shapeBlockIndexOfSize (m : Multiset ℕ) (s : ℕ) :
    Fintype.card {q : ShapeBlockIndex m // (q.1 : ℕ) = s} =
      m.count s := by
  classical
  by_cases hs : s ∈ m
  · simpa only [Fintype.card_fin] using
      Fintype.card_congr (shapeBlockIndexOfSizeEquivFin m s hs)
  · have hcount : m.count s = 0 := Multiset.count_eq_zero.mpr hs
    rw [hcount]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun q ↦ hs <|
      q.2 ▸ Multiset.mem_toFinset.mp q.1.1.2⟩

/-- The same canonical slot type, reassociated as two dependent sigma
bases followed by the within-block coordinate. -/
abbrev NestedShapeSlot (m : Multiset ℕ) :=
  Σ s : m.toFinset, Σ _j : Fin (m.count (s : ℕ)), Fin s.1

/-- Reassociate a slot's pair into nested dependent-sigma form. -/
def shapeSlotNestedEquiv (m : Multiset ℕ) :
    ShapeSlot m ≃ NestedShapeSlot m where
  toFun y := ⟨y.1, ⟨y.2.1, y.2.2⟩⟩
  invFun y := ⟨y.1, y.2.1, y.2.2⟩
  left_inv y := by rcases y with ⟨s, j, x⟩; rfl
  right_inv y := by rcases y with ⟨s, j, x⟩; rfl

/-- Forget the position inside a canonical slot, retaining only its block
index. -/
def shapeSlotBlockIndex {m : Multiset ℕ} :
    ShapeSlot m → ShapeBlockIndex m := fun y ↦ ⟨y.1, y.2.1⟩

/-- Every size occurring in a coloring profile is positive. -/
theorem pos_of_mem_profileSizes {b : ℕ} {k : ColoringProfile b} {s : ℕ}
    (hs : s ∈ ColoringProfile.sizes k) : 0 < s := by
  exact Nat.pos_of_ne_zero fun hs0 ↦
    zero_not_mem_profileSizes k (hs0 ▸ hs)

/-- A canonical witness slot in each block, using position zero. -/
def shapeBlockWitness {b : ℕ} (k : ColoringProfile b)
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    ShapeSlot (ColoringProfile.sizes k) := by
  have hqmem : (q.1 : ℕ) ∈ ColoringProfile.sizes k :=
    Multiset.mem_toFinset.mp q.1.2
  exact ⟨q.1, q.2, ⟨0, pos_of_mem_profileSizes hqmem⟩⟩

@[simp] theorem shapeSlotBlockIndex_shapeBlockWitness {b : ℕ}
    (k : ColoringProfile b)
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    shapeSlotBlockIndex (shapeBlockWitness k q) = q := by
  rfl

/-- The block-index map induced on vertices by a slot equivalence. -/
def slotBlockMap {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    Fin n → ShapeBlockIndex (ColoringProfile.sizes k) :=
  shapeSlotBlockIndex ∘ e

/-- The canonical representative vertex of a block index. -/
def slotBlockRepresentative {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) : Fin n :=
  e.symm (shapeBlockWitness k q)

@[simp] theorem slotBlockMap_representative {b n : ℕ}
    {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    slotBlockMap e (slotBlockRepresentative e q) = q := by
  simp [slotBlockMap, slotBlockRepresentative]

/-- Kernel relation identifying vertices with the same canonical block
index. -/
def slotKernelSetoid {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) : Setoid (Fin n) :=
  Setoid.ker (slotBlockMap e)

/-- The unordered partition obtained by forgetting block labels and internal
positions from a slot equivalence. -/
noncomputable def slotKernelPartition {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) : VertexPartition n := by
  classical
  exact Finpartition.ofSetoid (slotKernelSetoid e)

theorem mem_part_slotKernelPartition_iff {b n : ℕ}
    {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) (v w : Fin n) :
    w ∈ (slotKernelPartition e).part v ↔
      slotBlockMap e v = slotBlockMap e w := by
  classical
  change w ∈ (Finpartition.ofSetoid (slotKernelSetoid e)).part v ↔
    (slotKernelSetoid e) v w
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- The part corresponding to a canonical block index. -/
noncomputable def slotBlockPart {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    (slotKernelPartition e).parts := by
  classical
  exact ⟨(slotKernelPartition e).part (slotBlockRepresentative e q),
    (slotKernelPartition e).part_mem.mpr
      (Finset.mem_univ (slotBlockRepresentative e q))⟩

/-- Canonical block indices are in bijection with the parts of the kernel
partition. -/
noncomputable def shapeBlockIndexEquivKernelParts {b n : ℕ}
    {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    ShapeBlockIndex (ColoringProfile.sizes k) ≃
      (slotKernelPartition e).parts := by
  classical
  apply Equiv.ofBijective (slotBlockPart e)
  constructor
  · intro q r hqr
    have hmem : slotBlockRepresentative e q ∈
        (slotKernelPartition e).part (slotBlockRepresentative e r) := by
      change slotBlockRepresentative e q ∈ (slotBlockPart e r).1
      rw [← hqr]
      exact (slotKernelPartition e).mem_part (Finset.mem_univ _)
    have hindex :=
      (mem_part_slotKernelPartition_iff e
        (slotBlockRepresentative e r) (slotBlockRepresentative e q)).mp hmem
    simpa using hindex.symm
  · intro B
    obtain ⟨v, hv⟩ := (slotKernelPartition e).nonempty_of_mem_parts B.2
    let q := slotBlockMap e v
    refine ⟨q, Subtype.ext ?_⟩
    change (slotKernelPartition e).part (slotBlockRepresentative e q) = B.1
    have hrep : slotBlockRepresentative e q ∈
        (slotKernelPartition e).part v :=
      (mem_part_slotKernelPartition_iff e v
        (slotBlockRepresentative e q)).mpr (by simp [q])
    calc
      (slotKernelPartition e).part (slotBlockRepresentative e q) =
          (slotKernelPartition e).part v :=
        ((slotKernelPartition e).mem_part_iff_part_eq_part
          (Finset.mem_univ _) (Finset.mem_univ _)).mp hrep
      _ = B.1 := (slotKernelPartition e).part_eq_of_mem B.2 hv

@[simp] theorem shapeBlockIndexEquivKernelParts_apply {b n : ℕ}
    {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    shapeBlockIndexEquivKernelParts e q = slotBlockPart e q := rfl

/-- Membership in the kernel part indexed by `q` is exactly the fiber of
the vertex block-index map over `q`. -/
noncomputable def slotBlockPartEquivFiber {b n : ℕ}
    {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    (slotBlockPart e q).1 ≃ {v : Fin n // slotBlockMap e v = q} := by
  classical
  apply (Equiv.refl (Fin n)).subtypeEquiv
  intro v
  change v ∈ (slotKernelPartition e).part (slotBlockRepresentative e q) ↔ _
  rw [mem_part_slotKernelPartition_iff, slotBlockMap_representative]
  exact eq_comm

/-- Restricting the slot equivalence identifies a vertex block fiber with
the corresponding slot block fiber. -/
def slotBlockVertexFiberEquivSlotFiber {b n : ℕ}
    {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    {v : Fin n // slotBlockMap e v = q} ≃
      {y : ShapeSlot (ColoringProfile.sizes k) //
        shapeSlotBlockIndex y = q} := by
  apply e.subtypeEquiv
  intro v
  rfl

/-- Reassociation preserves the pinned block-index predicate. -/
def slotBlockSlotFiberEquivNestedFiber {b : ℕ}
    {k : ColoringProfile b}
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    {y : ShapeSlot (ColoringProfile.sizes k) //
        shapeSlotBlockIndex y = q} ≃
      {y : NestedShapeSlot (ColoringProfile.sizes k) //
        (⟨y.1, y.2.1⟩ : ShapeBlockIndex (ColoringProfile.sizes k)) = q} := by
  apply (shapeSlotNestedEquiv (ColoringProfile.sizes k)).subtypeEquiv
  intro y
  rfl

/-- The slot fiber over a fixed `(size,label)` block index is precisely its
within-block coordinate `Fin size`. -/
noncomputable def nestedShapeSlotFiberEquivFin {b : ℕ}
    {k : ColoringProfile b}
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    {y : NestedShapeSlot (ColoringProfile.sizes k) //
        (⟨y.1, y.2.1⟩ : ShapeBlockIndex (ColoringProfile.sizes k)) = q} ≃
      Fin q.1.1 := by
  classical
  exact Equiv.sigmaSigmaSubtype
    (fun ab : ShapeBlockIndex (ColoringProfile.sizes k) ↦ ab = q) rfl

/-- A kernel part has exactly the size recorded by its canonical block
index. -/
noncomputable def slotBlockPartEquivFin {b n : ℕ}
    {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    (slotBlockPart e q).1 ≃ Fin q.1.1 :=
  (slotBlockPartEquivFiber e q).trans <|
    (slotBlockVertexFiberEquivSlotFiber e q).trans <|
      (slotBlockSlotFiberEquivNestedFiber q).trans <|
        nestedShapeSlotFiberEquivFin q

/-- Exact cardinality of a reconstructed kernel part. -/
theorem card_slotBlockPart {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (q : ShapeBlockIndex (ColoringProfile.sizes k)) :
    (slotBlockPart e q).1.card = (q.1 : ℕ) := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_congr (slotBlockPartEquivFin e q)

/-- Restrict the block-index/part bijection to indices and parts of one
fixed size. -/
noncomputable def shapeBlockIndexOfSizeEquivKernelPartsOfSize
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) (s : ℕ) :
    {q : ShapeBlockIndex (ColoringProfile.sizes k) // (q.1 : ℕ) = s} ≃
      {B : (slotKernelPartition e).parts // B.1.card = s} := by
  classical
  apply (shapeBlockIndexEquivKernelParts e).subtypeEquiv
  intro q
  change (q.1 : ℕ) = s ↔ (slotBlockPart e q).1.card = s
  rw [card_slotBlockPart]

/-- The reconstructed kernel partition has the prescribed multiplicity of
every block size. -/
theorem count_partitionShape_slotKernelPartition
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) (s : ℕ) :
    (partitionShape (slotKernelPartition e)).count s =
      (ColoringProfile.sizes k).count s := by
  classical
  calc
    (partitionShape (slotKernelPartition e)).count s =
        Fintype.card
          {B : (slotKernelPartition e).parts // B.1.card = s} :=
      (card_vertexPartitionPartsOfSize (slotKernelPartition e) s).symm
    _ = Fintype.card
          {q : ShapeBlockIndex (ColoringProfile.sizes k) //
            (q.1 : ℕ) = s} :=
      (Fintype.card_congr
        (shapeBlockIndexOfSizeEquivKernelPartsOfSize e s)).symm
    _ = (ColoringProfile.sizes k).count s :=
      card_shapeBlockIndexOfSize (ColoringProfile.sizes k) s

/-- Forgetting labels and within-block positions from a slot equivalence
reconstructs an unordered partition with exactly the requested shape. -/
theorem partitionShape_slotKernelPartition
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    partitionShape (slotKernelPartition e) = ColoringProfile.sizes k := by
  apply Multiset.ext.mpr
  intro s
  exact count_partitionShape_slotKernelPartition e s

/-- The profile partition reconstructed from a canonical slot
equivalence. -/
noncomputable def slotProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    ProfilePartition n k :=
  ⟨slotKernelPartition e, partitionShape_slotKernelPartition e⟩

/-- Equal-sized reconstructed parts inherit their canonical slot labels. -/
noncomputable def slotProfileLabels
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    ∀ s : (ColoringProfile.sizes k).toFinset,
      ProfilePartsOfSize (slotProfilePartition e) s.1 ≃
        Fin ((ColoringProfile.sizes k).count (s : ℕ)) := fun s ↦
  (shapeBlockIndexOfSizeEquivKernelPartsOfSize e s.1).symm.trans
    (shapeBlockIndexOfSizeEquivFin (ColoringProfile.sizes k) s.1
      (Multiset.mem_toFinset.mp s.2))

/-- A reconstructed part inherits the within-block ordering carried by
the canonical slots. -/
noncomputable def slotProfilePartOrder
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k))
    (B : (slotProfilePartition e).1.parts) :
    B.1 ≃ Fin B.1.card := by
  classical
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
  exact (Equiv.cast hsource).trans <|
    (slotBlockPartEquivFin e q).trans <|
      Equiv.cast (congrArg Fin htarget)

/-- The complete decoration reconstructed from a canonical slot
equivalence. -/
noncomputable def slotProfileDecoration
    {b n : ℕ} {k : ColoringProfile b}
    (e : Fin n ≃ ShapeSlot (ColoringProfile.sizes k)) :
    ProfileDecoration (slotProfilePartition e) :=
  ⟨slotProfileLabels e, slotProfilePartOrder e⟩

/-! ## Algebraic closure once the forgetful bijection is constructed -/

/-- All profile partitions together with their factorial decorations. -/
abbrev TotalProfileDecoration {b : ℕ} (n : ℕ)
    (k : ColoringProfile b) :=
  Σ P : ProfilePartition n k, ProfileDecoration P

/-- The remaining explicit combinatorial construction is a bijection between
all decorated profile partitions and all bijections from the vertex set to
the canonical shape slots. -/
def ProfileDecorationBijectionStatement {b : ℕ} (n : ℕ)
    (k : ColoringProfile b) : Prop :=
  Nonempty
    (TotalProfileDecoration n k ≃
      (Fin n ≃ ShapeSlot (ColoringProfile.sizes k)))

/-- The decorated-partition bijection closes the exact arithmetic
enumeration bridge.  This theorem makes the sole remaining combinatorial
obligation explicit; it does not assume the desired cardinal equality. -/
theorem profileEnumerationStatement_of_decorationBijection
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n)
    (h : ProfileDecorationBijectionStatement n k) :
    ProfileEnumerationStatement n k := by
  let m := ColoringProfile.sizes k
  let D :=
    (m.map Nat.factorial).prod *
      ∏ s ∈ m.toFinset, Nat.factorial (m.count s)
  have hmSum : m.sum = n := hMass
  have hdecorationCard (P : ProfilePartition n k) :
      Fintype.card (ProfileDecoration P) = D := by
    simpa only [m, D] using card_profileDecoration P
  have htotal :
      Fintype.card (TotalProfileDecoration n k) =
        Fintype.card (ProfilePartition n k) * D := by
    calc
      Fintype.card (TotalProfileDecoration n k) =
          ∑ P : ProfilePartition n k,
            Fintype.card (ProfileDecoration P) := Fintype.card_sigma
      _ = ∑ _P : ProfilePartition n k, D :=
        Fintype.sum_congr _ _ hdecorationCard
      _ = Fintype.card (ProfilePartition n k) * D := by
        simp
  have hslotCard : Fintype.card (ShapeSlot m) = n := by
    rw [card_shapeSlot, hmSum]
  let e₀ : Fin n ≃ ShapeSlot m :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hslotCard.symm)
  have hallEquiv :
      Fintype.card (Fin n ≃ ShapeSlot m) = Nat.factorial n := by
    simpa only [Fintype.card_fin] using Fintype.card_equiv e₀
  obtain ⟨e⟩ := h
  have hprofileMul :
      Fintype.card (ProfilePartition n k) * D = Nat.factorial n := by
    calc
      Fintype.card (ProfilePartition n k) * D =
          Fintype.card (TotalProfileDecoration n k) := htotal.symm
      _ = Fintype.card (Fin n ≃ ShapeSlot m) := Fintype.card_congr e
      _ = Nat.factorial n := hallEquiv
  have hbellMul : m.bell * D = Nat.factorial n := by
    have hzero : 0 ∉ m.toFinset := by
      simpa only [Multiset.mem_toFinset, m] using zero_not_mem_profileSizes k
    have herase : m.toFinset.erase 0 = m.toFinset :=
      Finset.erase_eq_of_notMem hzero
    simpa only [D, hmSum, mul_assoc, herase] using Multiset.bell_mul_eq m
  unfold ProfileEnumerationStatement ColoringProfile.enumerativeCoefficient
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (ProfilePartition n k) = m.bell
  have hD : 0 < D := by
    dsimp only [D]
    apply Nat.mul_pos
    · apply Multiset.prod_pos
      intro a ha
      obtain ⟨x, _hx, rfl⟩ := Multiset.mem_map.mp ha
      exact Nat.factorial_pos x
    · apply Finset.prod_pos
      intro s hs
      exact Nat.factorial_pos (m.count s)
  apply Nat.mul_right_cancel hD
  exact hprofileMul.trans hbellMul.symm

end

end Erdos625
