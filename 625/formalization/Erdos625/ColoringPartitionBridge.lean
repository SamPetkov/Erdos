import Erdos625.FinpartitionRefinement

/-!
# From proper colorings to exact finite partitions

This module converts a Mathlib vertex coloring into the finite partition of
its nonempty color fibers.  The resulting partition is proper and has no more
parts than the palette has colors.  Combining this kernel construction with
`exists_finpartition_refinement_card_eq` produces exactly `k` nonempty proper
parts from the inequality `chromaticNumberNat G ≤ k`, provided `k ≤ n`.

Merely enlarging a palette can add empty colors and therefore cannot prove
exactness; the final step here genuinely refines the nonempty kernel parts.
-/

namespace Erdos625

noncomputable section

/-! ## The kernel partition of a coloring -/

/-- The partition of the labelled vertex set into the nonempty fibers of a
proper coloring. -/
def coloringVertexPartition {n q : ℕ} {G : LabeledGraph n}
    (C : G.Coloring (Fin q)) : VertexPartition n := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker C)

/-- Two vertices lie in the same kernel part exactly when they receive the
same color. -/
@[simp] theorem mem_part_coloringVertexPartition_iff {n q : ℕ}
    {G : LabeledGraph n} (C : G.Coloring (Fin q)) (v w : Fin n) :
    w ∈ (coloringVertexPartition C).part v ↔ C v = C w := by
  classical
  change w ∈ (Finpartition.ofSetoid (Setoid.ker C)).part v ↔
    (Setoid.ker C) v w
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- Every nonempty fiber of a proper coloring is independent, so the kernel
partition is a proper unordered coloring. -/
theorem coloringVertexPartition_mem_partitionColoringEvent
    {n q : ℕ} {G : LabeledGraph n} (C : G.Coloring (Fin q)) :
    G ∈ partitionColoringEvent (coloringVertexPartition C) := by
  intro B hB v hv w hw hvw hadj
  have hv' : v ∈ B := by
    simpa using hv
  have hw' : w ∈ B := by
    simpa using hw
  have hvpart : (coloringVertexPartition C).part v = B :=
    (coloringVertexPartition C).part_eq_of_mem hB hv'
  have hwv : w ∈ (coloringVertexPartition C).part v := by
    rw [hvpart]
    exact hw'
  exact (C.valid hadj) ((mem_part_coloringVertexPartition_iff C v w).mp hwv)

/-! ## The number of nonempty fibers -/

/-- The kernel partition of a coloring with palette `Fin q` has at most `q`
nonempty parts.  The proof assigns to each part the color of a chosen vertex;
distinct kernel parts receive distinct colors. -/
theorem card_parts_coloringVertexPartition_le {n q : ℕ}
    {G : LabeledGraph n} (C : G.Coloring (Fin q)) :
    (coloringVertexPartition C).parts.card ≤ q := by
  classical
  let P := coloringVertexPartition C
  change P.parts.card ≤ q
  let representative : P.parts → Fin n := fun B ↦
    (P.nonempty_of_mem_parts B.2).choose
  have representative_mem (B : P.parts) : representative B ∈ B.1 :=
    (P.nonempty_of_mem_parts B.2).choose_spec
  let partColor : P.parts → Fin q := fun B ↦ C (representative B)
  have hInjective : Function.Injective partColor := by
    intro B D hcolor
    have hcolor' : C (representative B) = C (representative D) := by
      simpa only [partColor] using hcolor
    have hmem : representative D ∈ P.part (representative B) := by
      simpa only [P] using
        (mem_part_coloringVertexPartition_iff C
          (representative B) (representative D)).mpr hcolor'
    have hparts : P.part (representative B) =
        P.part (representative D) :=
      ((P.mem_part_iff_part_eq_part
        (Finset.mem_univ (representative D))
        (Finset.mem_univ (representative B))).mp hmem).symm
    apply Subtype.ext
    calc
      B.1 = P.part (representative B) :=
        (P.part_eq_of_mem B.2 (representative_mem B)).symm
      _ = P.part (representative D) := hparts
      _ = D.1 := P.part_eq_of_mem D.2 (representative_mem D)
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective partColor hInjective

/-! ## Exactly `k` nonempty proper parts -/

/-- If the natural-valued chromatic number is at most `k` and `k ≤ n`,
then the labelled graph has a proper unordered partition into exactly `k`
nonempty parts.  This statement includes `n = k = 0`: the kernel partition
and its exact refinement are both empty. -/
theorem exists_exact_proper_partition_of_chromaticNumberNat_le
    {n k : ℕ} (G : LabeledGraph n)
    (hchi : chromaticNumberNat G ≤ k) (hkn : k ≤ n) :
    ∃ Q : VertexPartition n,
      Q.parts.card = k ∧ G ∈ partitionColoringEvent Q := by
  have hcolorable : G.Colorable k :=
    SimpleGraph.Colorable.mono hchi (colorable_chromaticNumberNat G)
  let C : G.Coloring (Fin k) := hcolorable.some
  let P : VertexPartition n := coloringVertexPartition C
  have hPcard : P.parts.card ≤ k := by
    simpa only [P] using card_parts_coloringVertexPartition_le C
  have hhi : k ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hkn
  obtain ⟨Q, hQcard, hQP⟩ :=
    exists_finpartition_refinement_card_eq P hPcard hhi
  refine ⟨Q, hQcard, mem_partitionColoringEvent_of_refines hQP ?_⟩
  simpa only [P] using coloringVertexPartition_mem_partitionColoringEvent C

end

end Erdos625
