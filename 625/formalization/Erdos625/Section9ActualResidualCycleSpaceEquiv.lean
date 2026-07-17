import Erdos625.Section9ActualResidualFamily
import Erdos625.Section9CycleRankResidual
import Erdos625.Section9CycleSpaceCardinality
import Mathlib.Tactic

/-!
# Section IX: exact actual-residual cell/edge and cycle-space equivalence

This finite module identifies supported row--column cell sets with graph edges
of the corresponding bipartite support graph.  It then identifies the literal
`ActualResidualEvenEdgeFamily` with its binary even-edge cycle space.

It contains no probability, cap/no-return, reward, or asymptotic assertion.
-/

namespace Erdos625

noncomputable section

/-- Supported row--column cells are exactly the edges of their bipartite
support graph.  The inverse identifies the two cross-edge orientations and
rejects same-side edges using the edge proof. -/
noncomputable def supportedCellEquivBipartiteGraphEdge
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : A -> B -> Prop) :
    {e : A × B // P e.1 e.2} ≃ (bipartiteGraph P).edgeSet := by
  classical
  let encode : {e : A × B // P e.1 e.2} →
      (bipartiteGraph P).edgeSet := fun e =>
    ⟨s(Sum.inl e.1.1, Sum.inr e.1.2), by
      simpa [bipartiteGraph, SimpleGraph.fromRel_adj] using e.2⟩
  refine Equiv.ofBijective encode ⟨?_, ?_⟩
  · intro e f hef
    apply Subtype.ext
    have hsym :
        s(Sum.inl e.1.1, Sum.inr e.1.2) =
          s(Sum.inl f.1.1, Sum.inr f.1.2) := congrArg Subtype.val hef
    have hp : e.1.1 = f.1.1 ∧ e.1.2 = f.1.2 := by
      simpa [Sym2.eq_iff] using hsym
    exact Prod.ext hp.1 hp.2
  · intro edge
    rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ u v =>
      rcases u with (a | b) <;> rcases v with (a' | b')
      · simp [bipartiteGraph, SimpleGraph.fromRel_adj] at hedge
      · refine ⟨⟨(a, b'), ?_⟩, ?_⟩
        · simpa [bipartiteGraph, SimpleGraph.fromRel_adj] using hedge
        · rfl
      · refine ⟨⟨(a', b), ?_⟩, ?_⟩
        · simpa [bipartiteGraph, SimpleGraph.fromRel_adj] using hedge
        · apply Subtype.ext
          exact Sym2.eq_swap
      · simp [bipartiteGraph, SimpleGraph.fromRel_adj] at hedge

/-- Map a supported finite cell set to the corresponding graph-edge set. -/
noncomputable def supportedCellFinsetToEdges
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : A → B → Prop) (F : Finset (A × B)) :
    Finset (bipartiteGraph P).edgeSet := by
  classical
  exact (Finset.subtype (fun e => P e.1 e.2) F).map
    (supportedCellEquivBipartiteGraphEdge P).toEmbedding

/-- Decode a finite set of graph edges back to its row--column cells. -/
noncomputable def supportedEdgesToCellFinset
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : A → B → Prop) (E : Finset (bipartiteGraph P).edgeSet) :
    Finset (A × B) := by
  classical
  exact (E.map (supportedCellEquivBipartiteGraphEdge P).symm.toEmbedding).map
    (Function.Embedding.subtype _)

@[simp] lemma supportedEdgesToCellFinset_supportedCellFinsetToEdges
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : A → B → Prop) (F : Finset (A × B))
    (hF : ∀ e ∈ F, P e.1 e.2) :
    supportedEdgesToCellFinset P (supportedCellFinsetToEdges P F) = F := by
  classical
  ext e
  simp [supportedEdgesToCellFinset, supportedCellFinsetToEdges]
  exact hF e

@[simp] lemma supportedCellFinsetToEdges_supportedEdgesToCellFinset
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : A → B → Prop) (E : Finset (bipartiteGraph P).edgeSet) :
    supportedCellFinsetToEdges P (supportedEdgesToCellFinset P E) = E := by
  classical
  ext edge
  simp [supportedEdgesToCellFinset, supportedCellFinsetToEdges]
  exact fun _ => ((supportedCellEquivBipartiteGraphEdge P).symm edge).2

/-- Under the cell/edge equivalence, row and column parity is precisely
parity at every vertex of the bipartite graph. -/
lemma supportedCellFinsetToEdges_even_iff
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : A → B → Prop) [DecidableRel (bipartiteGraph P).Adj]
    (F : Finset (A × B)) (hF : ∀ e ∈ F, P e.1 e.2) :
    BipartiteEvenEdgeSet F ↔
      ∀ v, Even (graphEdgeSubsetAtVertex
        (supportedCellFinsetToEdges P F) v).card := by
  classical
  have hrow (a : A) :
      (graphEdgeSubsetAtVertex (supportedCellFinsetToEdges P F)
        (Sum.inl a)).card = (bipartiteEdgeRow F a).card := by
    symm
    apply Finset.card_bij
      (fun b _ => (supportedCellEquivBipartiteGraphEdge P)
        ⟨(a, b), hF (a, b) (by simpa [bipartiteEdgeRow] using ‹b ∈ bipartiteEdgeRow F a›)⟩)
    · intro b hb
      simp only [graphEdgeSubsetAtVertex, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · simp [supportedCellFinsetToEdges, Finset.mem_subtype,
          bipartiteEdgeRow] at hb ⊢
        exact hb
      · simp [supportedCellEquivBipartiteGraphEdge]
    · intro b₁ hb₁ b₂ hb₂ heq
      have := (supportedCellEquivBipartiteGraphEdge P).injective heq
      simpa using congrArg (fun e => e.1.2) this
    · intro e he
      simp only [graphEdgeSubsetAtVertex, Finset.mem_filter,
        Finset.mem_univ, true_and] at he
      obtain ⟨heF, heVertex⟩ := he
      change e ∈ (Finset.subtype (fun e => P e.1 e.2) F).map
        (supportedCellEquivBipartiteGraphEdge P).toEmbedding at heF
      rw [Finset.mem_map] at heF
      obtain ⟨cell, hcell, rfl⟩ := heF
      have ha : cell.1.1 = a := by
        symm
        simpa [supportedCellEquivBipartiteGraphEdge] using heVertex
      subst a
      refine ⟨cell.1.2, ?_, rfl⟩
      simpa [bipartiteEdgeRow, Finset.mem_subtype] using hcell
  have hcolumn (b : B) :
      (graphEdgeSubsetAtVertex (supportedCellFinsetToEdges P F)
        (Sum.inr b)).card = (bipartiteEdgeColumn F b).card := by
    symm
    apply Finset.card_bij
      (fun a _ => (supportedCellEquivBipartiteGraphEdge P)
        ⟨(a, b), hF (a, b) (by simpa [bipartiteEdgeColumn] using ‹a ∈ bipartiteEdgeColumn F b›)⟩)
    · intro a ha
      simp only [graphEdgeSubsetAtVertex, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · simp [supportedCellFinsetToEdges, Finset.mem_subtype,
          bipartiteEdgeColumn] at ha ⊢
        exact ha
      · simp [supportedCellEquivBipartiteGraphEdge]
    · intro a₁ ha₁ a₂ ha₂ heq
      have := (supportedCellEquivBipartiteGraphEdge P).injective heq
      simpa using congrArg (fun e => e.1.1) this
    · intro e he
      simp only [graphEdgeSubsetAtVertex, Finset.mem_filter,
        Finset.mem_univ, true_and] at he
      obtain ⟨heF, heVertex⟩ := he
      change e ∈ (Finset.subtype (fun e => P e.1 e.2) F).map
        (supportedCellEquivBipartiteGraphEdge P).toEmbedding at heF
      rw [Finset.mem_map] at heF
      obtain ⟨cell, hcell, rfl⟩ := heF
      have hb : cell.1.2 = b := by
        symm
        simpa [supportedCellEquivBipartiteGraphEdge] using heVertex
      subst b
      refine ⟨cell.1.1, ?_, rfl⟩
      simpa [bipartiteEdgeColumn, Finset.mem_subtype] using hcell
  constructor
  · rintro ⟨hrows, hcolumns⟩ (a | b)
    · rw [hrow]
      exact hrows a
    · rw [hcolumn]
      exact hcolumns b
  · intro h
    constructor
    · intro a
      rw [← hrow]
      exact h (Sum.inl a)
    · intro b
      rw [← hcolumn]
      exact h (Sum.inr b)

/-- The literal actual residual even-edge family is exactly the even-edge
subtype of the graph supported on exposed cells or residual multiplicity at
least two. -/
noncomputable def actualResidualEvenEdgeFamilyEquivEvenEdgeSubset
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A -> B -> Nat) (M : A -> B -> Prop)
    [DecidableRel
      (bipartiteGraph
        (fun a b => M a b ∨ 2 ≤ cellCount a b)).Adj] :
    ActualResidualEvenEdgeFamily cellCount M ≃
      EvenEdgeSubset
        (bipartiteGraph
          (fun a b => M a b ∨ 2 ≤ cellCount a b)) := by
  classical
  let P : A → B → Prop := fun a b => M a b ∨ 2 ≤ cellCount a b
  refine
    { toFun := fun F => ⟨supportedCellFinsetToEdges P F.1,
        (supportedCellFinsetToEdges_even_iff P F.1 F.2.2).mp F.2.1⟩
      invFun := fun E => ⟨supportedEdgesToCellFinset P E.1, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (supportedCellFinsetToEdges_even_iff P _ ?_).mpr
    simpa using E.2
    intro e he
    change e ∈ ((E.1.map
      (supportedCellEquivBipartiteGraphEdge P).symm.toEmbedding).map
        (Function.Embedding.subtype _)) at he
    rw [Finset.mem_map] at he
    obtain ⟨cell, hcell, rfl⟩ := he
    exact cell.2
  · intro e he
    change e ∈ ((E.1.map
      (supportedCellEquivBipartiteGraphEdge P).symm.toEmbedding).map
        (Function.Embedding.subtype _)) at he
    rw [Finset.mem_map] at he
    obtain ⟨cell, hcell, rfl⟩ := he
    exact cell.2
  · intro F
    apply Subtype.ext
    exact supportedEdgesToCellFinset_supportedCellFinsetToEdges P F.1 F.2.2
  · intro E
    apply Subtype.ext
    exact supportedCellFinsetToEdges_supportedEdgesToCellFinset P E.1

/-- Exact binary cycle-space cardinality for the actual residual family. -/
theorem natCard_actualResidualEvenEdgeFamily_eq_two_pow_cycleRank
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A -> B -> Nat) (M : A -> B -> Prop)
    [DecidableRel
      (bipartiteGraph
        (fun a b => M a b ∨ 2 ≤ cellCount a b)).Adj] :
    Nat.card (ActualResidualEvenEdgeFamily cellCount M) =
      2 ^ cycleRank
        (bipartiteGraph
          (fun a b => M a b ∨ 2 ≤ cellCount a b)) := by
  rw [Nat.card_congr
    (actualResidualEvenEdgeFamilyEquivEvenEdgeSubset cellCount M)]
  exact natCard_evenEdgeSubset_eq_two_pow_cycleRank _

#print axioms supportedCellEquivBipartiteGraphEdge
#print axioms supportedCellFinsetToEdges_even_iff
#print axioms actualResidualEvenEdgeFamilyEquivEvenEdgeSubset
#print axioms natCard_actualResidualEvenEdgeFamily_eq_two_pow_cycleRank

end

end Erdos625
