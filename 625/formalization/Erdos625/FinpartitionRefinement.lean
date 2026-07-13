import Erdos625.ColoringProfileFirstMoment

/-!
# Exact refinements of finite partitions

This module supplies the deterministic splitting step used in manuscript
equation (4.5).  A finite partition with at most `k` nonempty parts can be
refined to one with exactly `k` nonempty parts whenever `k` does not exceed
the cardinality of the underlying finite set.

The construction is one-shot.  Reserve one representative in every old
part, choose the required number of other vertices, make the chosen vertices
singletons, and retain the nonempty residual of every old part.  This makes
the exact part count and all empty cases explicit.
-/

namespace Erdos625

open scoped BigOperators

/-! ## A singleton/residual refinement -/

/-- Refine `P` by making every element of `T` a singleton and replacing each
old part `B` by its residual `B \ T`.  The hypotheses say that `T` lies in the
partitioned set and that no old part is exhausted. -/
def singletonResidualRefinement {α : Type*} [DecidableEq α]
    {s T : Finset α} (P : Finpartition s) (hT : T ⊆ s)
    (hremain : ∀ B ∈ P.parts, (B \ T).Nonempty) : Finpartition s := by
  apply Finpartition.ofExistsUnique
    (T.image (fun x => ({x} : Finset α)) ∪
      P.parts.image fun B => B \ T)
  · intro A hA
    rw [Finset.mem_union] at hA
    rcases hA with hA | hA
    · obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hA
      exact Finset.singleton_subset_iff.mpr (hT hxT)
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      exact Finset.sdiff_subset.trans (P.subset hB)
  · intro x hx
    by_cases hxT : x ∈ T
    · refine ⟨{x}, ?_, ?_⟩
      · exact ⟨Finset.mem_union_left _ <|
          Finset.mem_image.mpr ⟨x, hxT, rfl⟩, Finset.mem_singleton_self x⟩
      · intro A hA
        rcases hA with ⟨hApart, hxA⟩
        rw [Finset.mem_union] at hApart
        rcases hApart with hAsing | hAres
        · obtain ⟨y, hyT, rfl⟩ := Finset.mem_image.mp hAsing
          simpa only [Finset.singleton_inj] using
            (Finset.eq_of_mem_singleton hxA).symm
        · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hAres
          exact False.elim ((Finset.mem_sdiff.mp hxA).2 hxT)
    · let B := P.part x
      have hB : B ∈ P.parts := P.part_mem.mpr hx
      have hxB : x ∈ B := P.mem_part hx
      refine ⟨B \ T, ?_, ?_⟩
      · exact ⟨Finset.mem_union_right _ <|
          Finset.mem_image.mpr ⟨B, hB, rfl⟩,
          Finset.mem_sdiff.mpr ⟨hxB, hxT⟩⟩
      · intro A hA
        rcases hA with ⟨hApart, hxA⟩
        rw [Finset.mem_union] at hApart
        rcases hApart with hAsing | hAres
        · obtain ⟨y, hyT, rfl⟩ := Finset.mem_image.mp hAsing
          have hxy : x = y := Finset.mem_singleton.mp hxA
          exact False.elim (hxT (hxy ▸ hyT))
        · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hAres
          have hpart : P.part x = C :=
            P.part_eq_of_mem hC (Finset.mem_sdiff.mp hxA).1
          exact congrArg (fun D : Finset α => D \ T) hpart.symm
  · intro hempty
    rw [Finset.mem_union] at hempty
    rcases hempty with hsing | hres
    · obtain ⟨x, hxT, hx⟩ := Finset.mem_image.mp hsing
      exact Finset.singleton_ne_empty x hx
    · obtain ⟨B, hB, hBempty⟩ := Finset.mem_image.mp hres
      obtain ⟨x, hx⟩ := hremain B hB
      rw [hBempty] at hx
      simp at hx

@[simp] theorem parts_singletonResidualRefinement {α : Type*}
    [DecidableEq α] {s T : Finset α} (P : Finpartition s)
    (hT : T ⊆ s) (hremain : ∀ B ∈ P.parts, (B \ T).Nonempty) :
    (singletonResidualRefinement P hT hremain).parts =
      T.image (fun x => ({x} : Finset α)) ∪
        P.parts.image (fun B => B \ T) :=
  rfl

/-- Every new singleton or residual part lies in an old part.  Recall that
the `Finpartition` order is the refinement order: `Q ≤ P` means that `Q`
refines `P`. -/
theorem singletonResidualRefinement_le {α : Type*} [DecidableEq α]
    {s T : Finset α} (P : Finpartition s) (hT : T ⊆ s)
    (hremain : ∀ B ∈ P.parts, (B \ T).Nonempty) :
    singletonResidualRefinement P hT hremain ≤ P := by
  intro A hA
  rw [parts_singletonResidualRefinement, Finset.mem_union] at hA
  rcases hA with hAsing | hAres
  · obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hAsing
    refine ⟨P.part x, P.part_mem.mpr (hT hxT), ?_⟩
    exact Finset.singleton_subset_iff.mpr (P.mem_part (hT hxT))
  · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hAres
    exact ⟨B, hB, Finset.sdiff_subset⟩

/-- The singleton family and the residual family are disjoint, and neither
family has collisions.  Consequently the refinement has exactly one new
part for every selected element in addition to one residual per old part. -/
theorem card_parts_singletonResidualRefinement {α : Type*}
    [DecidableEq α] {s T : Finset α} (P : Finpartition s)
    (hT : T ⊆ s) (hremain : ∀ B ∈ P.parts, (B \ T).Nonempty) :
    (singletonResidualRefinement P hT hremain).parts.card =
      T.card + P.parts.card := by
  have hdisjoint : Disjoint (T.image (fun x => ({x} : Finset α)))
      (P.parts.image fun B => B \ T) := by
    rw [Finset.disjoint_left]
    intro A hAsing hAres
    obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hAsing
    obtain ⟨B, hB, hEq⟩ := Finset.mem_image.mp hAres
    have hxres : x ∈ B \ T := by
      rw [hEq]
      exact Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.mp hxres).2 hxT
  have hinj : Set.InjOn (fun B : Finset α => B \ T) P.parts := by
    intro B hB C hC hEq
    obtain ⟨x, hx⟩ := hremain B hB
    have hxB : x ∈ B := (Finset.mem_sdiff.mp hx).1
    have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
    change B \ T = C \ T at hEq
    have hxCdiff : x ∈ C \ T := by
      rw [← hEq]
      exact Finset.mem_sdiff.mpr ⟨hxB, hxT⟩
    exact P.eq_of_mem_parts hB hC hxB (Finset.mem_sdiff.mp hxCdiff).1
  rw [parts_singletonResidualRefinement,
    Finset.card_union_of_disjoint hdisjoint,
    Finset.card_image_of_injective T Finset.singleton_injective,
    Finset.card_image_of_injOn hinj]

/-! ## Reserved representatives and every intermediate part count -/

/-- A finite partition admits a set of representatives containing one
vertex from every part and having the same cardinality as the part family. -/
theorem exists_representativeFinset {α : Type*} [DecidableEq α]
    {s : Finset α} (P : Finpartition s) :
    ∃ R : Finset α, R ⊆ s ∧ R.card = P.parts.card ∧
      ∀ B ∈ P.parts, ∃ r ∈ R, r ∈ B := by
  obtain ⟨R, hRs, hbij⟩ := P.exists_subset_part_bijOn
  refine ⟨R, hRs, ?_, ?_⟩
  · simpa using hbij.ncard_eq
  · intro B hB
    obtain ⟨r, hrR, hrpart⟩ := hbij.surjOn hB
    refine ⟨r, hrR, ?_⟩
    have hrs : r ∈ s := hRs hrR
    have hmem : r ∈ P.part r := P.mem_part hrs
    simpa [hrpart] using hmem

/-- Every integer between the number of parts of `P` and the cardinality of
the underlying finite set occurs as the exact number of parts of a refinement
of `P`.  This includes the empty-set case. -/
theorem exists_finpartition_refinement_card_eq {α : Type*}
    [DecidableEq α] {s : Finset α} (P : Finpartition s) {k : ℕ}
    (hlo : P.parts.card ≤ k) (hhi : k ≤ s.card) :
    ∃ Q : Finpartition s, Q.parts.card = k ∧ Q ≤ P := by
  obtain ⟨R, hRs, hRcard, hRmeet⟩ := exists_representativeFinset P
  have havailable : k - P.parts.card ≤ (s \ R).card := by
    rw [Finset.card_sdiff_of_subset hRs, hRcard]
    exact Nat.sub_le_sub_right hhi P.parts.card
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (s := s \ R) (n := k - P.parts.card) havailable
  have hTs : T ⊆ s := hTsub.trans Finset.sdiff_subset
  have hremain : ∀ B ∈ P.parts, (B \ T).Nonempty := by
    intro B hB
    obtain ⟨r, hrR, hrB⟩ := hRmeet B hB
    refine ⟨r, Finset.mem_sdiff.mpr ⟨hrB, ?_⟩⟩
    intro hrT
    exact (Finset.mem_sdiff.mp (hTsub hrT)).2 hrR
  let Q := singletonResidualRefinement P hTs hremain
  refine ⟨Q, ?_, singletonResidualRefinement_le P hTs hremain⟩
  rw [show Q.parts.card = T.card + P.parts.card from
    card_parts_singletonResidualRefinement P hTs hremain,
    hTcard, Nat.sub_add_cancel hlo]

/-! ## Preservation of properness and part-size bounds -/

/-- Refining a proper vertex partition preserves properness because every
new part is contained in an old independent part. -/
theorem mem_partitionColoringEvent_of_refines {n : ℕ}
    {G : LabeledGraph n} {P Q : VertexPartition n}
    (hQP : Q ≤ P) (hP : G ∈ partitionColoringEvent P) :
    G ∈ partitionColoringEvent Q := by
  intro C hC
  obtain ⟨B, hB, hCB⟩ := hQP hC
  exact Set.Pairwise.mono (by simpa using hCB) (hP B hB)

/-- A uniform upper bound on old part sizes is inherited by every part of a
refinement. -/
theorem part_card_bound_of_refines {n b : ℕ}
    {P Q : VertexPartition n} (hQP : Q ≤ P)
    (hP : ∀ B ∈ P.parts, B.card ≤ b) :
    ∀ C ∈ Q.parts, C.card ≤ b := by
  intro C hC
  obtain ⟨B, hB, hCB⟩ := hQP hC
  exact (Finset.card_le_card hCB).trans (hP B hB)

/-- Public deterministic refinement package for manuscript (4.5).  Starting
from a proper partition with `p` nonempty parts, every `k` with
`p ≤ k ≤ n` is realized by a refining proper partition.  The refinement
witness explicitly preserves a supplied maximum-part-size bound. -/
theorem exists_bounded_proper_refinement_card_eq
    {n p k b : ℕ} (G : LabeledGraph n) (P : VertexPartition n)
    (hproper : G ∈ partitionColoringEvent P)
    (hp : P.parts.card = p) (hpk : p ≤ k) (hkn : k ≤ n)
    (hbound : ∀ B ∈ P.parts, B.card ≤ b) :
    ∃ Q : VertexPartition n,
      Q.parts.card = k ∧ Q ≤ P ∧
        G ∈ partitionColoringEvent Q ∧
          ∀ C ∈ Q.parts, C.card ≤ b := by
  have hlo : P.parts.card ≤ k := hp.trans_le hpk
  have hhi : k ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hkn
  obtain ⟨Q, hQcard, hQP⟩ :=
    exists_finpartition_refinement_card_eq P hlo hhi
  exact ⟨Q, hQcard, hQP,
    mem_partitionColoringEvent_of_refines hQP hproper,
    part_card_bound_of_refines hQP hbound⟩

end Erdos625
