import Erdos625.VertexBlockExpectation
import Mathlib.Data.Finset.Max

/-!
# Largest induced subgraph with bounded cochromatic number

This file formalizes the deterministic statistic used in the amplification
argument.  It first records that cocolourings pull back along an injective
adjacency-preserving map, so feasibility is hereditary under vertex deletion.
-/

open Finset Set MeasureTheory
open scoped ENNReal NNReal

namespace Erdos625

noncomputable section

namespace CoColoring

/-- Pull a cocolouring back along an injective map that preserves and reflects
adjacency. -/
def pullback {U V : Type*} {kappa : Type*} {G : SimpleGraph V}
    {H : SimpleGraph U} (C : CoColoring G kappa) (f : U → V)
    (hf : Function.Injective f)
    (hadj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) :
    CoColoring H kappa where
  color := fun u ↦ C.color (f u)
  kind := C.kind
  valid := by
    intro c
    cases hkind : C.kind c with
    | independent =>
        intro x hx y hy hxy hH
        exact (C.valid_independent hkind) hx hy (hf.ne hxy)
          ((hadj x y).mp hH)
    | clique =>
        intro x hx y hy hxy
        exact (hadj x y).mpr
          ((C.valid_clique hkind) hx hy (hf.ne hxy))

end CoColoring

/-- Cocolourability is hereditary when the ambient induced set is shrunk. -/
theorem coColorable_induce_mono {V : Type*} {G : SimpleGraph V}
    {U W : Set V} {k : ℕ} (hUW : U ⊆ W)
    (hW : CoColorable (G.induce W) k) : CoColorable (G.induce U) k := by
  let f : U → W := fun u ↦ ⟨u.val, hUW u.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : W ↦ z.val) h
  exact ⟨hW.some.pullback f hf (fun _ _ ↦ Iff.rfl)⟩

/-- Restrict a cocolouring of a graph to an induced vertex set. -/
theorem coColorable_induce_of_coColorable {V : Type*} {G : SimpleGraph V}
    {W : Set V} {k : ℕ} (h : CoColorable G k) :
    CoColorable (G.induce W) k := by
  exact ⟨h.some.pullback Subtype.val Subtype.val_injective
    (fun _ _ ↦ Iff.rfl)⟩

/-- Equality after deleting `i` implies equality on every smaller induced
vertex set that avoids `i`. -/
theorem induce_eq_of_induce_away_eq {n : ℕ} {G H : LabeledGraph n}
    {i : Fin n} (hGH : G.induce {v | v ≠ i} = H.induce {v | v ≠ i})
    {U : Set (Fin n)} (hU : U ⊆ {v | v ≠ i}) :
    G.induce U = H.induce U := by
  ext u v
  let u' : {x : Fin n // x ≠ i} := ⟨u.val, hU u.property⟩
  let v' : {x : Fin n // x ≠ i} := ⟨v.val, hU v.property⟩
  have hAdj : (G.induce {x | x ≠ i}).Adj u' v' ↔
      (H.induce {x | x ≠ i}).Adj u' v' := by
    rw [hGH]
  exact hAdj

/-- A feasible induced set remains feasible in the other graph after erasing
the one vertex whose exposure block may have changed. -/
theorem coColorable_erase_of_induce_away_eq {n k : ℕ}
    {G H : LabeledGraph n} {i : Fin n} {W : Finset (Fin n)}
    (hGH : G.induce {v | v ≠ i} = H.induce {v | v ≠ i})
    (hW : CoColorable (G.induce (↑W : Set (Fin n))) k) :
    CoColorable (H.induce (↑(W.erase i) : Set (Fin n))) k := by
  have hSubset : (↑(W.erase i) : Set (Fin n)) ⊆ (↑W : Set (Fin n)) := by
    intro v hv
    exact (Finset.mem_erase.mp hv).2
  have hAvoid : (↑(W.erase i) : Set (Fin n)) ⊆ {v | v ≠ i} := by
    intro v hv
    exact (Finset.mem_erase.mp hv).1
  have hRestricted :
      CoColorable (G.induce (↑(W.erase i) : Set (Fin n))) k :=
    coColorable_induce_mono hSubset hW
  rw [induce_eq_of_induce_away_eq hGH hAvoid] at hRestricted
  exact hRestricted

/-- The empty induced graph is cocolourable with every palette size, including
the empty palette. -/
theorem coColorable_induce_empty {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    CoColorable (G.induce (∅ : Set V)) k := by
  let C : CoColoring (G.induce (∅ : Set V)) (Fin k) := {
    color := fun v ↦ v.property.elim
    kind := fun _ ↦ .independent
    valid := by
      intro c
      simp only
      intro x
      exact x.property.elim }
  exact ⟨C⟩

/-- All vertex sets whose induced graph admits a cocolouring with at most
`k` parts. -/
noncomputable def cochromaticFeasibleSets {n : ℕ} (G : LabeledGraph n)
    (k : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.powerset.filter fun W ↦
    CoColorable (G.induce (↑W : Set (Fin n))) k

theorem empty_mem_cochromaticFeasibleSets {n : ℕ} (G : LabeledGraph n)
    (k : ℕ) : ∅ ∈ cochromaticFeasibleSets G k := by
  classical
  rw [cochromaticFeasibleSets, Finset.mem_filter]
  constructor
  · simp
  · rw [show (↑(∅ : Finset (Fin n)) : Set (Fin n)) = ∅ by ext; simp]
    exact coColorable_induce_empty G k

theorem cochromaticFeasibleSets_nonempty {n : ℕ} (G : LabeledGraph n)
    (k : ℕ) : (cochromaticFeasibleSets G k).Nonempty :=
  ⟨∅, empty_mem_cochromaticFeasibleSets G k⟩

/-- The largest number of vertices in an induced subgraph that is
cocolourable with at most `k` parts. -/
noncomputable def cochromaticInducedCapacity {n : ℕ} (G : LabeledGraph n)
    (k : ℕ) : ℕ :=
  ((cochromaticFeasibleSets G k).image Finset.card).max'
    (Finset.Nonempty.image (cochromaticFeasibleSets_nonempty G k) Finset.card)

theorem card_le_cochromaticInducedCapacity {n : ℕ} {G : LabeledGraph n}
    {k : ℕ} {W : Finset (Fin n)}
    (hW : CoColorable (G.induce (↑W : Set (Fin n))) k) :
    W.card ≤ cochromaticInducedCapacity G k := by
  classical
  apply Finset.le_max'
  apply Finset.mem_image_of_mem
  simp only [cochromaticFeasibleSets, Finset.mem_filter,
    Finset.mem_powerset]
  exact ⟨Finset.subset_univ W, hW⟩

theorem cochromaticInducedCapacity_le_card {n : ℕ} (G : LabeledGraph n)
    (k : ℕ) : cochromaticInducedCapacity G k ≤ n := by
  classical
  have hmem : cochromaticInducedCapacity G k ∈
      (cochromaticFeasibleSets G k).image Finset.card :=
    Finset.max'_mem _ _
  rw [Finset.mem_image] at hmem
  obtain ⟨W, _hW, hcard⟩ := hmem
  rw [← hcard]
  simpa using Finset.card_le_univ W

/-- A cocolouring of an induced graph whose vertex set contains every ambient
vertex transports back to the original graph. -/
theorem coColorable_of_induce_full {V : Type*} {G : SimpleGraph V}
    {W : Set V} {k : ℕ} (hFull : ∀ v, v ∈ W)
    (h : CoColorable (G.induce W) k) : CoColorable G k := by
  let f : V → W := fun v ↦ ⟨v, hFull v⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact congrArg Subtype.val hxy
  exact ⟨h.some.pullback f hf (fun _ _ ↦ Iff.rfl)⟩

/-- A cocolouring of the induced graph on `Set.univ` transports back to the
original graph. -/
theorem coColorable_of_induce_univ {V : Type*} {G : SimpleGraph V}
    {k : ℕ} (h : CoColorable (G.induce (Set.univ : Set V)) k) :
    CoColorable G k :=
  coColorable_of_induce_full (fun _ ↦ Set.mem_univ _) h

/-- The induced capacity reaches all `n` vertices exactly when the entire
graph is cocolourable with `k` parts. -/
theorem cochromaticInducedCapacity_eq_card_iff {n k : ℕ}
    (G : LabeledGraph n) :
    cochromaticInducedCapacity G k = n ↔ CoColorable G k := by
  classical
  constructor
  · intro hCapacity
    have hmem : cochromaticInducedCapacity G k ∈
        (cochromaticFeasibleSets G k).image Finset.card :=
      Finset.max'_mem _ _
    rw [Finset.mem_image] at hmem
    obtain ⟨W, hWmem, hWcard⟩ := hmem
    have hCard : W.card = n := by omega
    have hUniv : W = Finset.univ := by
      rw [← Finset.card_eq_iff_eq_univ]
      simpa using hCard
    subst W
    rw [cochromaticFeasibleSets, Finset.mem_filter] at hWmem
    exact coColorable_of_induce_full (W :=
      (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) (by simp) hWmem.2
  · intro hColorable
    apply Nat.le_antisymm (cochromaticInducedCapacity_le_card G k)
    have hInduced :
        CoColorable
          (G.induce (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) k :=
      coColorable_induce_of_coColorable hColorable
    simpa using
      (card_le_cochromaticInducedCapacity (G := G) (k := k)
        (W := Finset.univ) hInduced)

/-- Changing one vertex-exposure block can increase the largest feasible
induced set by at most one. -/
theorem cochromaticInducedCapacity_le_add_one_of_induce_away_eq
    {n k : ℕ} {G H : LabeledGraph n} {i : Fin n}
    (hGH : G.induce {v | v ≠ i} = H.induce {v | v ≠ i}) :
    cochromaticInducedCapacity G k ≤
      cochromaticInducedCapacity H k + 1 := by
  classical
  have hmem : cochromaticInducedCapacity G k ∈
      (cochromaticFeasibleSets G k).image Finset.card :=
    Finset.max'_mem _ _
  rw [Finset.mem_image] at hmem
  obtain ⟨W, hWmem, hWcard⟩ := hmem
  rw [cochromaticFeasibleSets, Finset.mem_filter] at hWmem
  have hFeasible :
      CoColorable (H.induce (↑(W.erase i) : Set (Fin n))) k :=
    coColorable_erase_of_induce_away_eq hGH hWmem.2
  have hErase : (W.erase i).card ≤ cochromaticInducedCapacity H k :=
    card_le_cochromaticInducedCapacity hFeasible
  have hCard : W.card ≤ (W.erase i).card + 1 := by
    by_cases hi : i ∈ W
    · have h := Finset.card_erase_add_one hi
      omega
    · rw [Finset.erase_eq_of_notMem hi]
      omega
  omega

/-- As a real-valued graph statistic, the induced capacity has vertex-deletion
oscillation one. -/
theorem cochromaticInducedCapacity_hasVertexDeletionOscillation
    (n k : ℕ) :
    HasVertexDeletionOscillation
      (fun G : LabeledGraph n ↦ (cochromaticInducedCapacity G k : ℝ))
      (fun _ ↦ (1 : NNReal)) := by
  intro i G H hGH
  have hForward :=
    cochromaticInducedCapacity_le_add_one_of_induce_away_eq (k := k) hGH
  have hBackward :=
    cochromaticInducedCapacity_le_add_one_of_induce_away_eq (k := k) hGH.symm
  have hForwardReal : (cochromaticInducedCapacity G k : ℝ) ≤
      (cochromaticInducedCapacity H k : ℝ) + 1 := by
    exact_mod_cast hForward
  have hBackwardReal : (cochromaticInducedCapacity H k : ℝ) ≤
      (cochromaticInducedCapacity G k : ℝ) + 1 := by
    exact_mod_cast hBackward
  change |(cochromaticInducedCapacity G k : ℝ) -
      (cochromaticInducedCapacity H k : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith

/-- The first vertex block is empty, so its true oscillation is zero; every
later vertex block has oscillation one. -/
def noninitialUnitOscillation {n : ℕ} (i : Fin n) : NNReal :=
  if i.val = 0 then 0 else 1

/-- A universal block-coordinate oscillation profile for the induced-capacity
statistic, retaining the zero contribution from the empty first block.  For
special values of `k`, an even smaller profile may be available. -/
theorem cochromaticInducedCapacity_hasBlockOscillation (n k : ℕ) :
    HasBlockOscillation
      (fun x : VertexBlocks n ↦
        (cochromaticInducedCapacity (blocksToGraph x) k : ℝ))
      noninitialUnitOscillation := by
  intro i x y hxy
  by_cases hi : i.val = 0
  · have hxi : x i = y i := by
      funext u
      have hu : u.val < 0 := by simpa [hi] using u.isLt
      omega
    have hAll : x = y := by
      funext j
      by_cases hji : j = i
      · subst j
        exact hxi
      · exact hxy j hji
    subst y
    simp [noninitialUnitOscillation, hi]
  · have h :=
      (cochromaticInducedCapacity_hasVertexDeletionOscillation n k).hasBlockOscillation
        i x y hxy
    simpa [noninitialUnitOscillation, hi] using h

/-- The exact value of the chosen McDiarmid variance profile: the empty initial
block contributes zero and each of the remaining `n - 1` blocks contributes
`1 / 4`. -/
theorem blockVariance_noninitialUnitOscillation (n : ℕ) :
    (blockVariance (noninitialUnitOscillation (n := n)) : ℝ) =
      ((n - 1 : ℕ) : ℝ) / 4 := by
  rw [blockVariance_eq_sum_sq_div_four]
  cases n with
  | zero => simp
  | succ m =>
      rw [Fin.sum_univ_succ]
      simp [noninitialUnitOscillation, div_eq_mul_inv]

/-- One-sided bounded-differences upper tail for the induced capacity under
`G(n, 1/2)`, centered at its actual random-graph expectation. -/
theorem randomGraph_cochromaticInducedCapacity_upperTail
    (n k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | t ≤
          (cochromaticInducedCapacity G k : ℝ) -
            ∫ H, (cochromaticInducedCapacity H k : ℝ)
              ∂(randomGraphMeasure n)} ≤
      Real.exp
        (-t ^ 2 / (2 * (((n - 1 : ℕ) : ℝ) / 4))) := by
  rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
  have hb := blockBoundedDifferences_upperTail
    (Omega := fun v : Fin n ↦ VertexBlock v)
    (cochromaticInducedCapacity_hasBlockOscillation n k) ht
  change (randomGraphMeasure n
    {G | t ≤
      (cochromaticInducedCapacity G k : ℝ) -
        randomGraphBlockExpectation
          (fun H : LabeledGraph n ↦
            (cochromaticInducedCapacity H k : ℝ))}).toReal ≤ _
  rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
  simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
    vertexBlockMeasure, Measure.real,
    blockVariance_noninitialUnitOscillation] using hb

/-- Two-sided bounded-differences tail for the maximum size of an induced
`k`-cocolorable subgraph under `G(n, 1/2)`.  The statistic is centered at its
actual random-graph expectation, and the denominator records the chosen
`(n - 1) / 4` vertex-block variance profile. -/
theorem randomGraph_cochromaticInducedCapacity_twoSidedTail
    (n k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | t ≤
          |(cochromaticInducedCapacity G k : ℝ) -
            ∫ H, (cochromaticInducedCapacity H k : ℝ)
              ∂(randomGraphMeasure n)|} ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (((n - 1 : ℕ) : ℝ) / 4))) := by
  rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
  have hb := blockBoundedDifferences_twoSidedTail
    (Omega := fun v : Fin n ↦ VertexBlock v)
    (cochromaticInducedCapacity_hasBlockOscillation n k) ht
  change (randomGraphMeasure n
    {G | t ≤
      |(cochromaticInducedCapacity G k : ℝ) -
        randomGraphBlockExpectation
          (fun H : LabeledGraph n ↦
            (cochromaticInducedCapacity H k : ℝ))|}).toReal ≤ _
  rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
  simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
    vertexBlockMeasure, Measure.real,
    blockVariance_noninitialUnitOscillation] using hb

end

end Erdos625
