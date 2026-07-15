import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# The cycle-rank residual bound in Section IX

This module formalizes the finite graph-theoretic inequality in manuscript
(9.20).  A bipartite matching is a forest, and adjoining an arbitrary residual
support relation increases its cyclomatic number by at most the number of
residual support cells.

No cycle decomposition, traversal estimate, probability bound, or asymptotic
attachment estimate is asserted here.
-/

namespace Erdos625

open SimpleGraph

/-- Turn a bipartite support relation into a simple graph on the disjoint union
of row and column vertices. -/
def bipartiteGraph {A B : Type*} (P : A → B → Prop) :
    SimpleGraph (A ⊕ B) :=
  SimpleGraph.fromRel fun u v ↦
    match u, v with
    | Sum.inl a, Sum.inr b => P a b
    | _, _ => False

/-- Finite cyclomatic number `|E| + c - |V|`, with `c` the number of connected
components (isolated vertices included). -/
noncomputable def cycleRank
    {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card + Fintype.card G.ConnectedComponent - Fintype.card V

/-- The finite set represented by a bipartite relation. -/
noncomputable def relationFinset
    {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) : Finset (A × B) := by
  classical
  exact Finset.univ.filter fun e ↦ R e.1 e.2

/-- A finite graph in which every vertex has at most one neighbour is acyclic. -/
lemma isAcyclic_of_adj_unique {V : Type*} (G : SimpleGraph V)
    (h : ∀ v w w', G.Adj v w → G.Adj v w' → w = w') : G.IsAcyclic := by
  by_contra hAcyclic
  simp_all +decide [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  obtain ⟨v, w, hvw, hNotBridge⟩ := hAcyclic
  simp_all +decide [SimpleGraph.isBridge_iff]
  obtain ⟨p, hp⟩ := hNotBridge
  · exact hvw.ne rfl
  · rename_i x hx p
    specialize h v x w
    simp_all +decide

/-- The matching hypotheses make the associated bipartite graph acyclic. -/
lemma bipartiteGraph_matching_isAcyclic
    {A B : Type*} (M : A → B → Prop)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hColumnMatching : ∀ b a₁ a₂, M a₁ b → M a₂ b → a₁ = a₂) :
    (bipartiteGraph M).IsAcyclic := by
  convert isAcyclic_of_adj_unique (bipartiteGraph M) _ using 1
  intro v w w' hv hw
  unfold bipartiteGraph at hv hw
  rw [SimpleGraph.fromRel_adj] at hv hw
  rcases v with (a | b) <;> rcases w with (c | d) <;>
    rcases w' with (e | f) <;> tauto

/-- The edge finsets of the connected components cover the ambient edge
finset after applying the subtype embedding. -/
lemma edgeFinset_eq_biUnion_component_edgeFinsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [∀ c : G.ConnectedComponent, Fintype c]
    [∀ c : G.ConnectedComponent, DecidableRel c.toSimpleGraph.Adj]
    [∀ c : G.ConnectedComponent, Fintype c.toSimpleGraph.edgeSet] :
    G.edgeFinset =
      Finset.biUnion (Finset.univ : Finset G.ConnectedComponent)
        (fun c => c.toSimpleGraph.edgeFinset.image
          (Sym2.map fun v : c => v.1)) := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_biUnion]
    induction e using Sym2.inductionOn
    rename_i u v
    have huv : G.Adj u v := by
      simpa [SimpleGraph.mem_edgeFinset] using he
    let c : G.ConnectedComponent := G.connectedComponentMk u
    have hu : u ∈ c.supp := by
      simp [c]
    have hv : v ∈ c.supp := c.mem_supp_of_adj_mem_supp hu huv
    let eu : c := ⟨u, hu⟩
    let ev : c := ⟨v, hv⟩
    refine ⟨c, Finset.mem_univ c, ?_⟩
    rw [Finset.mem_image]
    refine ⟨s(eu, ev), ?_, rfl⟩
    simpa [ConnectedComponent.toSimpleGraph, eu, ev,
      SimpleGraph.mem_edgeFinset] using huv
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨c, _hc, hImage⟩ := he
    rw [Finset.mem_image] at hImage
    obtain ⟨f, hf, rfl⟩ := hImage
    induction f using Sym2.inductionOn
    rename_i u v
    have huv : c.toSimpleGraph.Adj u v := by
      simpa [SimpleGraph.mem_edgeFinset] using hf
    have huv' : G.Adj u.1 v.1 :=
      (c.toSimpleGraph_adj u.2 v.2).mp huv
    simpa [SimpleGraph.mem_edgeFinset] using huv'

/-- For a finite forest, the number of edges plus the number of connected
components is at most the number of vertices. -/
lemma acyclic_edge_add_component_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hAcyclic : G.IsAcyclic) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≤ Fintype.card V := by
  letI : ∀ c : G.ConnectedComponent, Fintype c :=
    fun c ↦ Fintype.ofFinite c
  letI : ∀ c : G.ConnectedComponent, DecidableRel c.toSimpleGraph.Adj :=
    fun c ↦ Classical.decRel _
  letI : ∀ c : G.ConnectedComponent, Fintype c.toSimpleGraph.edgeSet :=
    fun c ↦ Fintype.ofFinite c.toSimpleGraph.edgeSet
  have hComponent : ∀ c : G.ConnectedComponent,
      c.toSimpleGraph.edgeFinset.card ≤ Fintype.card c - 1 := by
    intro c
    have hTree : c.toSimpleGraph.IsTree := hAcyclic.isTree_connectedComponent c
    have hCard := hTree.card_edgeFinset
    omega
  have hEdges : G.edgeFinset.card ≤
      ∑ c : G.ConnectedComponent, c.toSimpleGraph.edgeFinset.card := by
    rw [edgeFinset_eq_biUnion_component_edgeFinsets G]
    exact Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun (c : G.ConnectedComponent) _ ↦
        (Finset.card_image_le :
          (c.toSimpleGraph.edgeFinset.image
            (Sym2.map fun v : c ↦ v.1)).card ≤
          c.toSimpleGraph.edgeFinset.card))
  have hVertexPartition :
      ∑ c : G.ConnectedComponent, Fintype.card c = Fintype.card V := by
    let componentSigmaEquiv : V ≃ (Σ c : G.ConnectedComponent, c) :=
      (Equiv.sigmaFiberEquiv G.connectedComponentMk).symm
    calc
      ∑ c : G.ConnectedComponent, Fintype.card c =
          Fintype.card (Σ c : G.ConnectedComponent, c) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V := (Fintype.card_congr componentSigmaEquiv).symm
  calc
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≤
        (∑ c : G.ConnectedComponent,
          c.toSimpleGraph.edgeFinset.card) +
          Fintype.card G.ConnectedComponent := Nat.add_le_add_right hEdges _
    _ ≤ (∑ c : G.ConnectedComponent, (Fintype.card c - 1)) +
          Fintype.card G.ConnectedComponent := by
      gcongr with c
      exact hComponent c
    _ = ∑ c : G.ConnectedComponent, Fintype.card c := by
      have hPos : ∀ c : G.ConnectedComponent, 0 < Fintype.card c := by
        intro c
        exact Fintype.card_pos_iff.mpr ⟨c.out, c.out_eq⟩
      calc
        (∑ c : G.ConnectedComponent, (Fintype.card c - 1)) +
              Fintype.card G.ConnectedComponent =
            (∑ c : G.ConnectedComponent, (Fintype.card c - 1)) +
              ∑ _c : G.ConnectedComponent, 1 := by simp
        _ = ∑ c : G.ConnectedComponent, ((Fintype.card c - 1) + 1) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ c : G.ConnectedComponent, Fintype.card c := by
          apply Finset.sum_congr rfl
          intro c _
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (hPos c)))
    _ = Fintype.card V := hVertexPartition

/-- The bipartite graph of `M ∨ R` is the join of the two bipartite graphs. -/
lemma bipartiteGraph_or_eq_sup {A B : Type*} (M R : A → B → Prop) :
    bipartiteGraph (fun a b ↦ M a b ∨ R a b) =
      bipartiteGraph M ⊔ bipartiteGraph R := by
  ext u v
  simp [SimpleGraph.sup_adj]
  cases u <;> cases v <;> simp [bipartiteGraph]

/-- The number of graph edges represented by a bipartite relation is bounded
by the number of true row-column pairs. -/
lemma bipartiteGraph_edgeFinset_card_le
    {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) [DecidableRel (bipartiteGraph R).Adj] :
    (bipartiteGraph R).edgeFinset.card ≤ (relationFinset R).card := by
  classical
  let encode : A × B → Sym2 (A ⊕ B) :=
    fun p ↦ s(Sum.inl p.1, Sum.inr p.2)
  have hImage : (bipartiteGraph R).edgeFinset =
      (relationFinset R).image encode := by
    ext e
    induction e using Sym2.inductionOn
    rename_i u v
    rcases u with (a | b) <;> rcases v with (c | d) <;>
      simp [SimpleGraph.mem_edgeFinset, relationFinset, encode, bipartiteGraph,
        SimpleGraph.fromRel_adj, or_comm]
  rw [hImage]
  exact Finset.card_image_le

/-- The number of new edges after adjoining `R` is at most the number of
residual cells. -/
lemma edge_diff_le_card_residual
    {A B : Type*} [Fintype A] [Fintype B]
    (M R : A → B → Prop)
    [DecidableRel (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).Adj]
    [DecidableRel (bipartiteGraph M).Adj] :
    (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).edgeFinset.card -
        (bipartiteGraph M).edgeFinset.card ≤
      (relationFinset R).card := by
  classical
  letI : DecidableRel (bipartiteGraph R).Adj := Classical.decRel _
  have hUnion :
      (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).edgeFinset ⊆
        (bipartiteGraph M).edgeFinset ∪ (bipartiteGraph R).edgeFinset := by
    intro e he
    simpa [SimpleGraph.mem_edgeFinset, bipartiteGraph_or_eq_sup,
      SimpleGraph.sup_adj] using he
  have hCard :
      (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).edgeFinset.card ≤
        (bipartiteGraph M).edgeFinset.card +
          (bipartiteGraph R).edgeFinset.card := by
    exact (Finset.card_le_card hUnion).trans
      ((Finset.card_union_le _ _).trans_eq rfl)
  have hResidual := bipartiteGraph_edgeFinset_card_le R
  rw [Nat.sub_le_iff_le_add]
  calc
    (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).edgeFinset.card ≤
        (bipartiteGraph M).edgeFinset.card +
          (bipartiteGraph R).edgeFinset.card := hCard
    _ ≤ (bipartiteGraph M).edgeFinset.card + (relationFinset R).card :=
      Nat.add_le_add_left hResidual _
    _ = (relationFinset R).card + (bipartiteGraph M).edgeFinset.card :=
      Nat.add_comm _ _

/-- Adding an arbitrary residual bipartite relation to a genuine bipartite
matching creates at most one unit of cycle rank per residual cell. -/
theorem cycleRank_matching_union_le_card_residual
    {A B : Type*} [Fintype A] [Fintype B]
    (M R : A → B → Prop)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hColumnMatching : ∀ b a₁ a₂, M a₁ b → M a₂ b → a₁ = a₂) :
    cycleRank (bipartiteGraph fun a b ↦ M a b ∨ R a b) ≤
      (relationFinset R).card := by
  classical
  have hEdgeDiff :
      (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).edgeFinset.card -
          (bipartiteGraph M).edgeFinset.card ≤
      (relationFinset R).card := by
    exact edge_diff_le_card_residual M R
  have hForest :
      (bipartiteGraph M).edgeFinset.card +
          Nat.card (bipartiteGraph M).ConnectedComponent ≤
        Nat.card (A ⊕ B) := by
    simpa only [← Nat.card_eq_fintype_card] using
      acyclic_edge_add_component_le (bipartiteGraph M)
        (bipartiteGraph_matching_isAcyclic M hRowMatching hColumnMatching)
  have hComponents :
      Nat.card
          (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).ConnectedComponent ≤
        Nat.card (bipartiteGraph M).ConnectedComponent := by
    apply SimpleGraph.ConnectedComponent.card_le_card_of_le
    rw [bipartiteGraph_or_eq_sup]
    exact le_sup_left
  unfold cycleRank
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.sub_le_iff_le_add] at hEdgeDiff ⊢
  calc
    (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).edgeFinset.card +
          Nat.card
            (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).ConnectedComponent ≤
        ((relationFinset R).card + (bipartiteGraph M).edgeFinset.card) +
          Nat.card
            (bipartiteGraph (fun a b ↦ M a b ∨ R a b)).ConnectedComponent :=
      Nat.add_le_add_right hEdgeDiff _
    _ ≤ ((relationFinset R).card + (bipartiteGraph M).edgeFinset.card) +
          Nat.card (bipartiteGraph M).ConnectedComponent :=
      Nat.add_le_add_left hComponents _
    _ = (relationFinset R).card +
          ((bipartiteGraph M).edgeFinset.card +
            Nat.card (bipartiteGraph M).ConnectedComponent) := by
      omega
    _ ≤ (relationFinset R).card + Nat.card (A ⊕ B) :=
      Nat.add_le_add_left hForest _

#print axioms cycleRank_matching_union_le_card_residual

end Erdos625
