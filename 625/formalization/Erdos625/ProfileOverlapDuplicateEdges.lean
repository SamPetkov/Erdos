import Erdos625.ColoringProfileFirstMoment
import Mathlib.Tactic

/-!
# Duplicate internal edges of two profile partitions

This module isolates the elementary finite edge count used in the signed
second-moment calculation.  It deliberately contains no probability or
asymptotic statement.
-/

namespace Erdos625

open SimpleGraph
open scoped BigOperators

noncomputable section

/-- Number of vertices in the cell obtained by intersecting two parts. -/
def profileOverlapCellCount {n : ℕ}
    (A B : Finset (Fin n)) : ℕ :=
  (A ∩ B).card

/-- The same cell count with its two profile partitions and certified parts
kept in the type.  This is the profile-level object used by the signed
overlap table; its value is just the cardinality of the underlying
intersection. -/
def ProfilePartition.overlapCellCount {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k) (A : P.1.parts) (B : Q.1.parts) : ℕ :=
  profileOverlapCellCount A.1 B.1

@[simp] theorem ProfilePartition.overlapCellCount_eq {b n : ℕ}
    {k : ColoringProfile b} (P Q : ProfilePartition n k)
    (A : P.1.parts) (B : Q.1.parts) :
    P.overlapCellCount Q A B = (A.1 ∩ B.1).card := rfl

/-- The graph made of the complete graphs on all overlap cells.  Empty and
singleton cells are retained harmlessly: they contribute no edge. -/
def partitionOverlapGraph {n : ℕ} (P Q : VertexPartition n) : LabeledGraph n :=
  (P.parts.product Q.parts).sup fun e => completeOn (e.1 ∩ e.2)

private theorem completeOn_adj_iff {V : Type*} [DecidableEq V]
    (S : Finset V) (v w : V) :
    (completeOn S).Adj v w ↔ v ≠ w ∧ v ∈ S ∧ w ∈ S := by
  rw [completeOn, SimpleGraph.map_adj]
  constructor
  · rintro ⟨v', w', hvw', hv', hw'⟩
    have hne : v ≠ w := by
      intro h
      apply hvw'
      apply Subtype.ext
      change (v' : V) = (w' : V)
      calc
        (v' : V) = v := hv'
        _ = w := h
        _ = (w' : V) := hw'.symm
    refine ⟨hne, ?_, ?_⟩
    · rw [← hv']
      exact v'.property
    · rw [← hw']
      exact w'.property
  · rintro ⟨hvw, hv, hw⟩
    refine ⟨⟨v, hv⟩, ⟨w, hw⟩, ?_, rfl, rfl⟩
    change (⟨v, hv⟩ : S) ≠ ⟨w, hw⟩
    intro h
    apply hvw
    exact congrArg Subtype.val h

private theorem adj_finset_sup_iff {V I : Type*}
    [DecidableEq I] (s : Finset I) (f : I → SimpleGraph V) (v w : V) :
    (s.sup f).Adj v w ↔ ∃ i ∈ s, (f i).Adj v w := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sup_insert, SimpleGraph.sup_adj, ih]
      simp

private theorem partitionInternalGraph_adj_iff {n : ℕ}
    (P : VertexPartition n) (v w : Fin n) :
    (partitionInternalGraph P).Adj v w ↔
      P.part v = P.part w ∧ v ≠ w := by
  rw [partitionInternalGraph, adj_finset_sup_iff]
  constructor
  · rintro ⟨B, hB, hB_adj⟩
    obtain ⟨hvw, hvB, hwB⟩ := (completeOn_adj_iff B v w).mp hB_adj
    refine ⟨?_, hvw⟩
    calc
      P.part v = B := (P.part_eq_iff_mem hB).mpr hvB
      _ = P.part w := ((P.part_eq_iff_mem hB).mpr hwB).symm
  · rintro ⟨hpart, hvw⟩
    let B := P.part v
    have hB : B ∈ P.parts := by
      dsimp [B]
      exact P.part_mem.mpr (Finset.mem_univ v)
    have hvB : v ∈ B := by
      dsimp [B]
      exact (P.part_eq_iff_mem hB).mp rfl
    have hwB : w ∈ B := by
      apply (P.part_eq_iff_mem hB).mp
      dsimp [B]
      exact hpart.symm
    exact ⟨B, hB, (completeOn_adj_iff B v w).mpr ⟨hvw, hvB, hwB⟩⟩

private theorem partitionOverlapGraph_adj_iff {n : ℕ}
    (P Q : VertexPartition n) (v w : Fin n) :
    (partitionOverlapGraph P Q).Adj v w ↔
      P.part v = P.part w ∧ Q.part v = Q.part w ∧ v ≠ w := by
  rw [partitionOverlapGraph, adj_finset_sup_iff]
  constructor
  · rintro ⟨AB, hAB, hAB_adj⟩
    rcases Finset.mem_product.mp hAB with ⟨hA, hB⟩
    obtain ⟨hvw, hv, hw⟩ :=
      (completeOn_adj_iff (AB.1 ∩ AB.2) v w).mp hAB_adj
    have hvA : v ∈ AB.1 := Finset.mem_of_mem_inter_left hv
    have hwA : w ∈ AB.1 := Finset.mem_of_mem_inter_left hw
    have hvB : v ∈ AB.2 := Finset.mem_of_mem_inter_right hv
    have hwB : w ∈ AB.2 := Finset.mem_of_mem_inter_right hw
    refine ⟨?_, ?_, hvw⟩
    · calc
        P.part v = AB.1 := (P.part_eq_iff_mem hA).mpr hvA
        _ = P.part w := ((P.part_eq_iff_mem hA).mpr hwA).symm
    · calc
        Q.part v = AB.2 := (Q.part_eq_iff_mem hB).mpr hvB
        _ = Q.part w := ((Q.part_eq_iff_mem hB).mpr hwB).symm
  · rintro ⟨hP, hQ, hvw⟩
    let A := P.part v
    let B := Q.part v
    have hA : A ∈ P.parts := by
      dsimp [A]
      exact P.part_mem.mpr (Finset.mem_univ v)
    have hB : B ∈ Q.parts := by
      dsimp [B]
      exact Q.part_mem.mpr (Finset.mem_univ v)
    have hvA : v ∈ A := by
      dsimp [A]
      exact (P.part_eq_iff_mem hA).mp rfl
    have hwA : w ∈ A := by
      apply (P.part_eq_iff_mem hA).mp
      dsimp [A]
      exact hP.symm
    have hvB : v ∈ B := by
      dsimp [B]
      exact (Q.part_eq_iff_mem hB).mp rfl
    have hwB : w ∈ B := by
      apply (Q.part_eq_iff_mem hB).mp
      dsimp [B]
      exact hQ.symm
    refine ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, ?_⟩
    exact (completeOn_adj_iff (A ∩ B) v w).mpr
      ⟨hvw, Finset.mem_inter.mpr ⟨hvA, hvB⟩,
        Finset.mem_inter.mpr ⟨hwA, hwB⟩⟩

/-- The common internal edges of two partitions are precisely the internal
edges of their overlap cells. -/
theorem partitionInternalGraph_inf_eq_partitionOverlapGraph {n : ℕ}
    (P Q : VertexPartition n) :
    partitionInternalGraph P ⊓ partitionInternalGraph Q =
      partitionOverlapGraph P Q := by
  ext v w
  rw [SimpleGraph.inf_adj, partitionInternalGraph_adj_iff,
    partitionInternalGraph_adj_iff, partitionOverlapGraph_adj_iff]
  constructor
  · rintro ⟨⟨hP, _⟩, ⟨hQ, hvw⟩⟩
    exact ⟨hP, hQ, hvw⟩
  · rintro ⟨hP, hQ, hvw⟩
    exact ⟨⟨hP, hvw⟩, ⟨hQ, hvw⟩⟩

private theorem pairwiseDisjoint_completeOn_overlapCells {n : ℕ}
    (P Q : VertexPartition n) :
    ((↑(P.parts.product Q.parts) : Set
        (Finset (Fin n) × Finset (Fin n)))).PairwiseDisjoint
      (fun AB => completeOn (AB.1 ∩ AB.2)) := by
  intro AB hAB CD hCD hne
  apply disjoint_completeOn_of_disjoint
  rcases Finset.mem_product.mp hAB with ⟨hA, hB⟩
  rcases Finset.mem_product.mp hCD with ⟨hC, hD⟩
  by_cases hAC : AB.1 = CD.1
  · have hBD : AB.2 ≠ CD.2 := by
      intro hBD
      apply hne
      exact Prod.ext hAC hBD
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right
        (Q.disjoint hB hD hBD))
  · exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (P.disjoint hA hC hAC))

/-- The overlap-cell graph has one edge for each unordered pair inside an
overlap cell. -/
theorem ncard_partitionOverlapGraph {n : ℕ}
    (P Q : VertexPartition n) :
    (partitionOverlapGraph P Q).edgeSet.ncard =
      ∑ A ∈ P.parts, ∑ B ∈ Q.parts, (A ∩ B).card.choose 2 := by
  classical
  rw [partitionOverlapGraph,
    ncard_edgeSet_finset_sup_of_pairwise
      (P.parts.product Q.parts) (fun AB => completeOn (AB.1 ∩ AB.2))
      (pairwiseDisjoint_completeOn_overlapCells P Q)]
  simp_rw [ncard_edgeSet_completeOn]
  exact Finset.sum_product P.parts Q.parts
    (fun AB => (AB.1 ∩ AB.2).card.choose 2)

/-- Exact duplicated-edge count: an edge is shared by the two internal
graphs exactly when both endpoints lie in one overlap cell. -/
theorem ncard_partitionInternalGraph_edgeSet_inter {n : ℕ}
    (P Q : VertexPartition n) :
    ((partitionInternalGraph P).edgeSet ∩ (partitionInternalGraph Q).edgeSet).ncard =
      ∑ A ∈ P.parts, ∑ B ∈ Q.parts, (A ∩ B).card.choose 2 := by
  rw [← SimpleGraph.edgeSet_inf,
    partitionInternalGraph_inf_eq_partitionOverlapGraph]
  exact ncard_partitionOverlapGraph P Q

/-- Profile-indexed spelling of the overlap-cell count. -/
theorem ncard_profilePartitionInternalGraph_edgeSet_inter
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k) :
    ((partitionInternalGraph P.1).edgeSet ∩
      (partitionInternalGraph Q.1).edgeSet).ncard =
      ∑ A ∈ P.1.parts, ∑ B ∈ Q.1.parts,
        (profileOverlapCellCount A B).choose 2 := by
  simpa [profileOverlapCellCount] using
    ncard_partitionInternalGraph_edgeSet_inter P.1 Q.1

/-- Inclusion--exclusion for the prescribed internal-edge bits of arbitrary
partitions, with the overlap contribution written as the explicit cell sum. -/
theorem ncard_partitionInternalGraph_edgeSet_union {n : ℕ}
    (P Q : VertexPartition n) :
    (partitionInternalGraph P ⊔ partitionInternalGraph Q).edgeSet.ncard +
        ∑ A ∈ P.parts, ∑ B ∈ Q.parts, (A ∩ B).card.choose 2 =
      (partitionInternalGraph P).edgeSet.ncard +
        (partitionInternalGraph Q).edgeSet.ncard := by
  rw [SimpleGraph.edgeSet_sup,
    ← ncard_partitionInternalGraph_edgeSet_inter P Q]
  exact Set.ncard_union_add_ncard_inter _ _

/-- For two profile partitions of the same profile, the union of prescribed
internal edge bits has size `2 B_k - W`, recorded in cancellation-safe
addition form over `ℕ`. -/
theorem ncard_profilePartitionInternalGraph_edgeSet_union_add_overlap
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k) :
    (partitionInternalGraph P.1 ⊔ partitionInternalGraph Q.1).edgeSet.ncard +
        ∑ A ∈ P.1.parts, ∑ B ∈ Q.1.parts,
          (profileOverlapCellCount A B).choose 2 =
      2 * ColoringProfile.forbiddenEdges k := by
  simp only [profileOverlapCellCount]
  rw [ncard_partitionInternalGraph_edgeSet_union P.1 Q.1,
    P.ncard_partitionInternalGraph, Q.ncard_partitionInternalGraph]
  omega

/-- Subtraction form of the preceding identity; this is the exponent
`B_P + B_Q - W = 2 B_k - W` used in the joint signed-witness probability. -/
theorem ncard_profilePartitionInternalGraph_edgeSet_union
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k) :
    (partitionInternalGraph P.1 ⊔ partitionInternalGraph Q.1).edgeSet.ncard =
      2 * ColoringProfile.forbiddenEdges k -
        ∑ A ∈ P.1.parts, ∑ B ∈ Q.1.parts,
          (profileOverlapCellCount A B).choose 2 := by
  have h := ncard_profilePartitionInternalGraph_edgeSet_union_add_overlap P Q
  omega

end

end Erdos625
