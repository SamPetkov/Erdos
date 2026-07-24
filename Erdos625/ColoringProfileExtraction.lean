import Erdos625.ColoringProfileCountPositivity

/-!
# Extracting a bounded coloring profile from a vertex partition

This module supplies the deterministic extraction step used by the bounded
profile count.  A partition whose blocks have size at most `b` determines a
profile on the positive sizes `1, …, b`, and its shape is exactly the multiset
encoded by that profile.  The proof treats size zero and sizes above `b`
separately, so it also covers the empty partition with `b = 0` and `n = 0`.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The multiplicity profile of block sizes `1, …, b` in a vertex
partition. -/
def vertexPartitionProfile {n : ℕ} (b : ℕ) (P : VertexPartition n) :
    ColoringProfile b :=
  fun i ↦ (partitionShape P).count (i.1 + 1)

/-- Every size occurring in a vertex-partition shape is positive. -/
private theorem partitionShape_member_pos {n s : ℕ}
    (P : VertexPartition n) (hs : s ∈ partitionShape P) :
    0 < s := by
  rw [partitionShape, Multiset.mem_map] at hs
  obtain ⟨B, hB, hcard⟩ := hs
  have hBpos : 0 < B.card := Finset.card_pos.mpr (P.nonempty_of_mem_parts hB)
  omega

/-- A block-size bound transfers to every entry of the partition shape. -/
private theorem partitionShape_member_le {n b s : ℕ}
    (P : VertexPartition n)
    (hBound : ∀ B ∈ P.parts, B.card ≤ b)
    (hs : s ∈ partitionShape P) :
    s ≤ b := by
  rw [partitionShape, Multiset.mem_map] at hs
  obtain ⟨B, hB, hcard⟩ := hs
  have hBle : B.card ≤ b := hBound B hB
  omega

/-- Every size encoded by a bounded profile is positive. -/
private theorem profileSizes_member_pos {b s : ℕ}
    (k : ColoringProfile b) (hs : s ∈ ColoringProfile.sizes k) :
    0 < s := by
  simp only [ColoringProfile.sizes, Multiset.mem_sum] at hs
  obtain ⟨i, _hi, hs⟩ := hs
  simp only [Multiset.mem_replicate] at hs
  omega

/-- Every size encoded by a profile on `Fin b` is at most `b`. -/
private theorem profileSizes_member_le {b s : ℕ}
    (k : ColoringProfile b) (hs : s ∈ ColoringProfile.sizes k) :
    s ≤ b := by
  simp only [ColoringProfile.sizes, Multiset.mem_sum] at hs
  obtain ⟨i, _hi, hs⟩ := hs
  simp only [Multiset.mem_replicate] at hs
  omega

/-- A partition with all blocks of size at most `b` has exactly the shape
encoded by its extracted profile.  Size `0` occurs on neither side; a size
above `b` occurs on neither side; and sizes `1, …, b` have equal counts by
construction. -/
theorem partitionShape_eq_sizes_vertexPartitionProfile {n b : ℕ}
    (P : VertexPartition n)
    (hBound : ∀ B ∈ P.parts, B.card ≤ b) :
    partitionShape P =
      ColoringProfile.sizes (vertexPartitionProfile b P) := by
  rw [Multiset.ext]
  intro s
  by_cases hzero : s = 0
  · subst s
    rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
    · intro hs
      exact (profileSizes_member_pos (vertexPartitionProfile b P) hs).ne' rfl
    · intro hs
      exact (partitionShape_member_pos P hs).ne' rfl
  · by_cases hle : s ≤ b
    · have hspos : 0 < s := Nat.pos_of_ne_zero hzero
      have hslt : s - 1 < b := by omega
      let i : Fin b := ⟨s - 1, hslt⟩
      have hi : i.1 + 1 = s := by
        dsimp only [i]
        omega
      calc
        (partitionShape P).count s =
            (partitionShape P).count (i.1 + 1) := by rw [hi]
        _ = vertexPartitionProfile b P i := rfl
        _ = (ColoringProfile.sizes (vertexPartitionProfile b P)).count
            (i.1 + 1) :=
              (ColoringProfile.count_sizes_at
                (vertexPartitionProfile b P) i).symm
        _ = (ColoringProfile.sizes (vertexPartitionProfile b P)).count s := by
              rw [hi]
    · have hgt : b < s := Nat.lt_of_not_ge hle
      rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
      · intro hs
        exact (not_le_of_gt hgt)
          (profileSizes_member_le (vertexPartitionProfile b P) hs)
      · intro hs
        exact (not_le_of_gt hgt) (partitionShape_member_le P hBound hs)

/-- Regard a bounded vertex partition as a partition of its extracted
profile. -/
def vertexPartitionAsProfilePartition {n b : ℕ}
    (P : VertexPartition n)
    (hBound : ∀ B ∈ P.parts, B.card ≤ b) :
    ProfilePartition n (vertexPartitionProfile b P) :=
  ⟨P, partitionShape_eq_sizes_vertexPartitionProfile P hBound⟩

/-- A proper partition into exactly `parts` blocks of size at most `b`
witnesses positivity of the bounded aggregate coloring count. -/
theorem boundedProfileColoringCount_pos_of_partition {n : ℕ}
    (G : LabeledGraph n) (b parts : ℕ) (P : VertexPartition n)
    (hProper : G ∈ partitionColoringEvent P)
    (hParts : P.parts.card = parts)
    (hBound : ∀ B ∈ P.parts, B.card ≤ b) :
    0 < boundedProfileColoringCount G b parts := by
  rw [boundedProfileColoringCount_pos_iff]
  let k : ColoringProfile b := vertexPartitionProfile b P
  let Pk : ProfilePartition n k :=
    vertexPartitionAsProfilePartition P hBound
  refine ⟨k, ?_, Pk, ?_⟩
  · apply mem_boundedColoringProfiles_of_constraints
    · exact Pk.vertexMass_eq
    · rw [← Pk.card_parts_eq]
      exact hParts
  · exact hProper

end

end Erdos625
