import Erdos625.BlockBoundedDifferences
import Erdos625.Target

/-!
# Vertex-block representation of a labelled random graph

For `v : Fin n`, block `v` contains the indicators of the edges from the
earlier vertices `Fin v.val` to `v`.  Thus the dependent product has one
independent finite block per vertex and contains every unordered edge exactly
once.  This is the exposure required by the amplification argument; flattening
these blocks into individual bits would give the wrong concentration scale.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos625

/-- The edge indicators exposed when vertex `v` arrives. -/
abbrev VertexBlock {n : ℕ} (v : Fin n) := Fin v.val → Bool

/-- All vertex-exposure blocks for a labelled graph on `Fin n`. -/
abbrev VertexBlocks (n : ℕ) := ∀ v : Fin n, VertexBlock v

/-- Regard a local index in block `v` as the corresponding earlier vertex. -/
def lowerVertex {n : ℕ} (v : Fin n) (u : Fin v.val) : Fin n :=
  ⟨u.val, lt_trans u.isLt v.isLt⟩

@[simp]
theorem lowerVertex_val {n : ℕ} (v : Fin n) (u : Fin v.val) :
    (lowerVertex v u).val = u.val := rfl

theorem lowerVertex_lt {n : ℕ} (v : Fin n) (u : Fin v.val) :
    lowerVertex v u < v := u.isLt

/-- Construct the graph encoded by the vertex blocks.  `fromRel` supplies the
symmetry while the strict order makes the selected orientation unique. -/
def blocksToGraph {n : ℕ} (x : VertexBlocks n) : LabeledGraph n :=
  SimpleGraph.fromRel fun u v ↦
    ∃ h : u.val < v.val, x v ⟨u.val, h⟩ = true

/-- Read the earlier-neighbour indicators of a graph. -/
noncomputable def graphToBlocks {n : ℕ} (G : LabeledGraph n) : VertexBlocks n :=
  by
    classical
    exact fun v u ↦ decide (G.Adj (lowerVertex v u) v)

theorem blocksToGraph_adj_lower {n : ℕ} (x : VertexBlocks n)
    (v : Fin n) (u : Fin v.val) :
    (blocksToGraph x).Adj (lowerVertex v u) v ↔ x v u = true := by
  change
    (SimpleGraph.fromRel fun a b : Fin n ↦
      ∃ h : a.val < b.val, x b ⟨a.val, h⟩ = true).Adj
        (lowerVertex v u) v ↔ x v u = true
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨h, hx⟩ | ⟨h, _⟩⟩
    · simpa only [lowerVertex_val] using hx
    · exact (Nat.not_lt_of_ge (Nat.le_of_lt u.isLt) h).elim
  · intro hx
    refine ⟨?_, Or.inl ⟨u.isLt, ?_⟩⟩
    · exact ne_of_lt (lowerVertex_lt v u)
    · simpa only [lowerVertex_val] using hx

theorem graphToBlocks_blocksToGraph {n : ℕ} (x : VertexBlocks n) :
    graphToBlocks (blocksToGraph x) = x := by
  classical
  funext v u
  change decide ((blocksToGraph x).Adj (lowerVertex v u) v) = x v u
  rw [blocksToGraph_adj_lower]
  cases x v u <;> simp

theorem blocksToGraph_graphToBlocks {n : ℕ} (G : LabeledGraph n) :
    blocksToGraph (graphToBlocks G) = G := by
  ext u v
  rcases lt_trichotomy u.val v.val with huv | huv | huv
  · let a : Fin v.val := ⟨u.val, huv⟩
    have hua : lowerVertex v a = u := Fin.ext rfl
    rw [← hua, blocksToGraph_adj_lower]
    simp only [graphToBlocks, decide_eq_true_eq, hua]
  · have huv' : u = v := Fin.ext huv
    subst v
    simp
  · let a : Fin u.val := ⟨v.val, huv⟩
    have hva : lowerVertex u a = v := Fin.ext rfl
    calc
      (blocksToGraph (graphToBlocks G)).Adj u v ↔
          (blocksToGraph (graphToBlocks G)).Adj (lowerVertex u a) u := by
            rw [hva, SimpleGraph.adj_comm]
      _ ↔ graphToBlocks G u a = true := blocksToGraph_adj_lower _ _ _
      _ ↔ G.Adj (lowerVertex u a) u := by
        simp only [graphToBlocks, decide_eq_true_eq]
      _ ↔ G.Adj u v := by rw [hva, SimpleGraph.adj_comm]

/-- Vertex blocks are in exact bijection with labelled simple graphs. -/
noncomputable def vertexBlocksEquiv (n : ℕ) : VertexBlocks n ≃ LabeledGraph n where
  toFun := blocksToGraph
  invFun := graphToBlocks
  left_inv := graphToBlocks_blocksToGraph
  right_inv := blocksToGraph_graphToBlocks

/-- The block product contains one bit for every unordered pair of vertices. -/
theorem card_vertexBlocks (n : ℕ) :
    Fintype.card (VertexBlocks n) = 2 ^ n.choose 2 := by
  classical
  rw [Fintype.card_pi]
  simp only [VertexBlock, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  calc
    ∑ i : Fin n, i.val = ∑ i ∈ Finset.range n, i := by
      simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) n)
    _ = n * (n - 1) / 2 := Finset.sum_range_id n
    _ = n.choose 2 := (Nat.choose_two_right n).symm

/-- The canonical uniform law on the dependent vertex blocks. -/
noncomputable def vertexBlockMeasure (n : ℕ) :
    @Measure (VertexBlocks n) ⊤ :=
  blockUniformMeasure (fun v : Fin n ↦ VertexBlock v)

/-- Every vertex-block configuration has the same mass as a graph under
`G(n,1/2)`. -/
theorem vertexBlockMeasure_singleton (n : ℕ) (x : VertexBlocks n) :
    vertexBlockMeasure n {x} = (1 / 2 : ENNReal) ^ n.choose 2 := by
  letI : MeasurableSpace (VertexBlocks n) := ⊤
  unfold vertexBlockMeasure blockUniformMeasure blockUniformPMF finiteUniformPMF
  rw [PMF.toMeasure_apply_singleton _ _ (by simp)]
  rw [PMF.uniformOfFintype_apply, card_vertexBlocks]
  simpa only [Nat.cast_ofNat, Nat.cast_pow, one_div] using
    (ENNReal.inv_pow (a := (2 : ENNReal)) (n := n.choose 2))

/-- With the discrete measurable structure on the block product, graph
decoding is measurable. -/
theorem measurable_blocksToGraph_top (n : ℕ) :
    @Measurable (VertexBlocks n) (LabeledGraph n) ⊤ _ blocksToGraph := by
  letI : MeasurableSpace (VertexBlocks n) := ⊤
  exact measurable_of_finite _

/-- Pushing the uniform vertex-block law through graph decoding gives exactly
the binomial random-graph law at edge probability `1/2`. -/
theorem map_vertexBlockMeasure_eq_randomGraphMeasure (n : ℕ) :
    @Measure.map (VertexBlocks n) (LabeledGraph n) ⊤ _ blocksToGraph
        (vertexBlockMeasure n) = randomGraphMeasure n := by
  apply Measure.ext_of_singleton
  intro G
  rw [Measure.map_apply (measurable_blocksToGraph_top n)
    (measurableSet_singleton G)]
  have hpre : blocksToGraph ⁻¹' ({G} : Set (LabeledGraph n)) =
      {graphToBlocks G} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      rw [← hx]
      exact (graphToBlocks_blocksToGraph x).symm
    · intro hx
      rw [hx]
      exact blocksToGraph_graphToBlocks G
  rw [hpre, vertexBlockMeasure_singleton,
    randomGraphMeasure_singleton_uniform]

/-- Exact event transport from the random-graph law to the block product. -/
theorem vertexBlockMeasure_preimage_eq_randomGraphMeasure (n : ℕ)
    (A : Set (LabeledGraph n)) :
    vertexBlockMeasure n (blocksToGraph ⁻¹' A) = randomGraphMeasure n A := by
  have hA : MeasurableSet A := Set.toFinite A |>.measurableSet
  have h := congrArg (fun μ : Measure (LabeledGraph n) ↦ μ A)
    (map_vertexBlockMeasure_eq_randomGraphMeasure n)
  rw [Measure.map_apply (measurable_blocksToGraph_top n) hA] at h
  exact h

/-- If two block configurations agree away from block `i`, their decoded
graphs agree on every edge whose endpoints both avoid `i`. -/
theorem blocksToGraph_adj_iff_of_agree_away {n : ℕ}
    {x y : VertexBlocks n} {i u v : Fin n}
    (hxy : ∀ j, j ≠ i → x j = y j) (hu : u ≠ i) (hv : v ≠ i) :
    (blocksToGraph x).Adj u v ↔ (blocksToGraph y).Adj u v := by
  rcases lt_trichotomy u.val v.val with huv | huv | huv
  · let a : Fin v.val := ⟨u.val, huv⟩
    have hua : lowerVertex v a = u := Fin.ext rfl
    rw [← hua, blocksToGraph_adj_lower, blocksToGraph_adj_lower, hxy v hv]
  · have huv' : u = v := Fin.ext huv
    subst v
    simp
  · let a : Fin u.val := ⟨v.val, huv⟩
    have hva : lowerVertex u a = v := Fin.ext rfl
    calc
      (blocksToGraph x).Adj u v ↔
          (blocksToGraph x).Adj (lowerVertex u a) u := by
            rw [hva, SimpleGraph.adj_comm]
      _ ↔ x u a = true := blocksToGraph_adj_lower _ _ _
      _ ↔ y u a = true := by rw [hxy u hu]
      _ ↔ (blocksToGraph y).Adj (lowerVertex u a) u :=
        (blocksToGraph_adj_lower _ _ _).symm
      _ ↔ (blocksToGraph y).Adj u v := by
        rw [hva, SimpleGraph.adj_comm]

/-- Equivalently, deleting the affected vertex makes the two decoded graphs
literally equal. -/
theorem blocksToGraph_induce_away_eq {n : ℕ} {x y : VertexBlocks n}
    {i : Fin n} (hxy : ∀ j, j ≠ i → x j = y j) :
    (blocksToGraph x).induce {v | v ≠ i} =
      (blocksToGraph y).induce {v | v ≠ i} := by
  ext u v
  exact blocksToGraph_adj_iff_of_agree_away hxy u.property v.property

/-- A graph statistic has vertex-deletion oscillation `c i` when its values
on two graphs differ by at most `c i` whenever deleting `i` makes the graphs
equal. -/
def HasVertexDeletionOscillation {n : ℕ} (F : LabeledGraph n → ℝ)
    (c : Fin n → ℝ≥0) : Prop :=
  ∀ i G H, G.induce {v | v ≠ i} = H.induce {v | v ≠ i} →
    |F G - F H| ≤ (c i : ℝ)

/-- Vertex-deletion oscillation becomes coordinate oscillation under the exact
vertex-block encoding. -/
theorem HasVertexDeletionOscillation.hasBlockOscillation {n : ℕ}
    {F : LabeledGraph n → ℝ} {c : Fin n → ℝ≥0}
    (h : HasVertexDeletionOscillation F c) :
    HasBlockOscillation (fun x : VertexBlocks n ↦ F (blocksToGraph x)) c := by
  intro i x y hxy
  exact h i (blocksToGraph x) (blocksToGraph y)
    (blocksToGraph_induce_away_eq hxy)

/-- The expectation of a graph statistic, expressed on the exact vertex-block
probability space. -/
noncomputable def randomGraphBlockExpectation {n : ℕ}
    (F : LabeledGraph n → ℝ) : ℝ :=
  blockExpectation (fun v : Fin n ↦ VertexBlock v)
    (fun x : VertexBlocks n ↦ F (blocksToGraph x))

/-- One-sided bounded differences for a graph statistic under the actual
`G(n,1/2)` law, centered at its exact vertex-block expectation. -/
theorem randomGraph_vertexBlock_upperTail {n : ℕ}
    {F : LabeledGraph n → ℝ} {c : Fin n → ℝ≥0}
    (h : HasVertexDeletionOscillation F c) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | t ≤ F G - randomGraphBlockExpectation F} ≤
      Real.exp (-t ^ 2 / (2 * blockVariance c)) := by
  have hb := blockBoundedDifferences_upperTail
    (Omega := fun v : Fin n ↦ VertexBlock v)
    h.hasBlockOscillation ht
  change (randomGraphMeasure n
    {G | t ≤ F G - randomGraphBlockExpectation F}).toReal ≤ _
  rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
  simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
    vertexBlockMeasure, Measure.real] using hb

/-- Two-sided bounded differences for a graph statistic under the actual
`G(n,1/2)` law. -/
theorem randomGraph_vertexBlock_twoSidedTail {n : ℕ}
    {F : LabeledGraph n → ℝ} {c : Fin n → ℝ≥0}
    (h : HasVertexDeletionOscillation F c) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | t ≤ |F G - randomGraphBlockExpectation F|} ≤
      2 * Real.exp (-t ^ 2 / (2 * blockVariance c)) := by
  have hb := blockBoundedDifferences_twoSidedTail
    (Omega := fun v : Fin n ↦ VertexBlock v)
    h.hasBlockOscillation ht
  change (randomGraphMeasure n
    {G | t ≤ |F G - randomGraphBlockExpectation F|}).toReal ≤ _
  rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
  simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
    vertexBlockMeasure, Measure.real] using hb

end Erdos625
