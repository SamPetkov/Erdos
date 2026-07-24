import Erdos625.Section9CyclePolymerBound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
# A minimal nonempty even bipartite edge set is one simple cycle

This is the traversal leaf that the mixed-cycle code requires.  The conclusion
produces an actual `SimpleGraph.Walk.IsCycle`, covers every edge of `C` exactly
once, and records the finite length bound.  No cyclic ordering is assumed.
-/

namespace Erdos625

open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- The simple graph represented by a bipartite cell set. -/
def cellGraph {A B : Type*} (C : Finset (A × B)) :
    SimpleGraph (A ⊕ B) :=
  SimpleGraph.fromRel fun u v ↦
    match u, v with
    | Sum.inl a, Sum.inr b => (a, b) ∈ C
    | _, _ => False

def cellSym2 {A B : Type*} (e : A × B) : Sym2 (A ⊕ B) :=
  s(Sum.inl e.1, Sum.inr e.2)

open Classical in
lemma degree_toSimpleGraph_connectedComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) (x : c) :
    c.toSimpleGraph.degree x = G.degree x.1 := by
  refine' Finset.card_bij ( fun y hy => y ) _ _ _ <;> simp +decide;
  · aesop;
  · exact fun v hv => ⟨ c.mem_supp_of_adj_mem_supp x.property hv, hv ⟩

lemma finite_nonempty_acyclic_graph_has_degree_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : G.IsAcyclic) (hne : G ≠ ⊥) :
    ∃ v, G.degree v = 1 := by
  -- Let $c$ be a connected component of $G$ that contains at least one edge.
  obtain ⟨c, hc⟩ : ∃ c : G.ConnectedComponent, Nontrivial c := by
    obtain ⟨ u, v, h ⟩ := show ∃ u v : V, G.Adj u v from by contrapose! hne; ext u v; aesop;
    refine' ⟨ G.connectedComponentMk u, _ ⟩;
    refine' ⟨ ⟨ u, _ ⟩, ⟨ v, _ ⟩, _ ⟩ <;> simp_all +decide;
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem;
    · exact Quot.sound ( SimpleGraph.Reachable.symm ( SimpleGraph.Adj.reachable h ) );
    · exact h.ne;
  have := @SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial ( c );
  contrapose! this;
  refine' ⟨ c.toSimpleGraph, _, hc, _, _, _ ⟩;
  exact Fintype.ofFinite ↥c;
  exact Classical.decRel c.toSimpleGraph.Adj;
  · exact SimpleGraph.IsAcyclic.isTree_connectedComponent hacyc c;
  · intro v;
    convert this v using 1;
    convert degree_toSimpleGraph_connectedComponent G c v

lemma finite_even_degree_graph_has_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v))
    (hne : G ≠ ⊥) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  by_contra h;
  -- Apply the theorem that states a finite nonempty acyclic graph has a vertex of degree 1.
  obtain ⟨v, hv⟩ : ∃ v : V, G.degree v = 1 := by
    apply finite_nonempty_acyclic_graph_has_degree_one G (by
    intro v p hp; specialize heven v; simp_all +decide ;) hne;
  exact absurd ( heven v ) ( by simp +decide [ hv ] )

lemma exists_cycleWalk_of_nonempty_even
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C : Finset (A × B)) (heven : IsBipartiteEven C) (hne : C.Nonempty) :
    ∃ (v : A ⊕ B) (p : (cellGraph C).Walk v v), p.IsCycle := by
  obtain ⟨ v, hv ⟩ := hne;
  -- Show that the graph is not bottom.
  have h_nonbottom : cellGraph C ≠ ⊥ := by
    intro h; have := congr_arg ( fun G => G.Adj ( Sum.inl v.1 ) ( Sum.inr v.2 ) ) h; simp +decide [ cellGraph ] at this;
    contradiction;
  convert finite_even_degree_graph_has_cycle ( cellGraph C ) _ h_nonbottom;
  exact Classical.decRel (cellGraph C).Adj;
  intro x; cases x <;> simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
  · convert heven.1 ‹_› using 1;
    refine' Finset.card_bij ( fun x hx => ( ‹_›, x.elim ( fun x => by aesop ) fun x => x ) ) _ _ _ <;> simp +decide [ cellGraph ];
    aesop;
  · convert heven.2 _ using 1;
    convert Finset.card_image_of_injective _ ( show Function.Injective ( fun a : A => Sum.inl a ) from fun a b h => by simpa using h ) using 2;
    any_goals exact Finset.image Prod.fst ( Finset.filter ( fun e => e.2 = ‹_› ) C );
    any_goals exact ‹B›;
    all_goals try infer_instance;
    · ext; simp [cellGraph];
      rename_i x; rcases x with ( _ | _ ) <;> simp +decide ;
    · rw [ Finset.card_image_of_injOn ] ; intro a ha b hb ; aesop

/-
Every intrinsic simple bipartite cycle admits a genuine cyclic traversal
whose edge set is exactly the supplied cell set.
-/
theorem exists_covering_cycleWalk_of_minimal_even
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C : Finset (A × B)) (hC : IsSimpleBipartiteCycle C) :
    ∃ (v : A ⊕ B) (p : (cellGraph C).Walk v v),
      p.IsCycle ∧
      p.edges.toFinset = C.image cellSym2 ∧
      p.length = C.card ∧
      p.length ≤ Fintype.card (A ⊕ B) := by
  obtain ⟨ v, p, hp ⟩ := exists_cycleWalk_of_nonempty_even C hC.1 hC.2.1;
  -- Let $D$ be the set of cells corresponding to the edges of $p$.
  set D := C.filter (fun e => cellSym2 e ∈ p.edges);
  -- Show that $D$ is bipartite even.
  have hD_even : IsBipartiteEven D := by
    constructor;
    · intro a
      have h_card : (Finset.filter (fun e => e.1 = a) D).card = (p.toSubgraph.neighborSet (Sum.inl a)).ncard := by
        rw [ ← Set.ncard_coe_finset ];
        fapply Set.ncard_congr;
        use fun e he => Sum.inr e.2;
        · simp +zetaDelta at *;
          rintro a' b' ha' hb' rfl; exact (by
          exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hb');
        · grind;
        · intro b hb
          obtain ⟨e, he⟩ : ∃ e ∈ p.edges, e = s(Sum.inl a, b) := by
            simp_all +decide;
            exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hb;
          rcases b with ( _ | b ) <;> simp_all +decide [ cellGraph ];
          · have := p.edges_subset_edgeSet he.1; simp_all +decide [cellGraph];
          · exact Finset.mem_filter.mpr ⟨ by
              have := p.edges_subset_edgeSet he.1; simp_all +decide [ cellGraph ] ;, by
              aesop ⟩;
      by_cases ha : Sum.inl a ∈ p.support <;> simp_all +decide [ SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two ];
      rw [ show p.toSubgraph.neighborSet ( Sum.inl a ) = ∅ from _ ] ; simp +decide;
      grind +suggestions;
    · intro b
      by_cases hb : Sum.inr b ∈ p.support;
      · have hD_even_b : (Finset.filter (fun e => e.2 = b) D).card = (p.toSubgraph.neighborSet (Sum.inr b)).ncard := by
          rw [ ← Set.ncard_coe_finset ];
          fapply Set.ncard_congr;
          use fun e he => Sum.inl e.1;
          · simp +zetaDelta at *;
            rintro a b ha hb rfl;
            have h_adj : p.toSubgraph.Adj (Sum.inl a) (Sum.inr b) := by
              (expose_names; exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hb_1);
            exact h_adj.symm;
          · aesop;
          · simp +decide;
            constructor;
            · intro a ha;
              have h_edge : cellSym2 (a, b) ∈ p.edges := by
                exact
                (SimpleGraph.Walk.mem_edges_toSubgraph p).mp
                  (id (SimpleGraph.Subgraph.adj_symm p.toSubgraph ha));
              exact Finset.mem_filter.mpr ⟨ hC.1 |> fun h => by
                have := p.edges_subset_edgeSet h_edge; simp_all +decide [ cellGraph ] ;
                cases this ; tauto, h_edge ⟩;
            · intro b' hb'
              have h_adj : (cellGraph C).Adj (Sum.inr b) (Sum.inr b') := by
                exact SimpleGraph.Subgraph.Adj.adj_sub hb';
              cases h_adj ; aesop;
        have := hp.ncard_neighborSet_toSubgraph_eq_two hb; aesop;
      · rw [ Finset.card_eq_zero.mpr ] <;> simp_all +decide [ Finset.ext_iff ];
        intro a b' hab' hb'; simp_all +decide [ D ] ;
        have := p.snd_mem_support_of_mem_edges hab'.2; simp_all +decide [ cellGraph ] ;
  -- Since $D$ is nonempty and bipartite even, by minimality, $D = C$.
  have hD_eq_C : D = C := by
    apply hC.2.2 D (Finset.filter_subset _ _) hD_even;
    obtain ⟨e, he⟩ : ∃ e ∈ p.edges, ∃ a b, e = s(Sum.inl a, Sum.inr b) := by
      rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ];
      · cases ‹ ( cellGraph C ).Adj v v › ; tauto;
      · cases v <;> cases ‹A ⊕ B› <;> simp_all +decide;
        · cases ‹A ⊕ B› <;> simp_all +decide [ cellGraph ];
          · cases ‹ ( cellGraph C ).Adj ( Sum.inl _ ) ( Sum.inl _ ) › ; tauto;
          · exact ⟨ _, _, Or.inl ⟨ rfl, rfl ⟩ ⟩;
        · cases ‹A ⊕ B› <;> aesop;
        · cases ‹A ⊕ B› <;> simp_all +decide [ cellGraph ];
          · exact ⟨ _, _, Or.inl ⟨ rfl, rfl ⟩ ⟩;
          · cases ‹ ( cellGraph C ).Adj ( Sum.inr _ ) ( Sum.inr _ ) › ; tauto;
        · cases ‹A ⊕ B› <;> simp_all +decide [ cellGraph ];
          · exact ⟨ _, _, Or.inl ⟨ rfl, rfl ⟩ ⟩;
          · cases ‹ ( cellGraph C ).Adj ( Sum.inr _ ) ( Sum.inr _ ) › ; tauto;
    obtain ⟨ a, b, rfl ⟩ := he.2;
    use (a, b);
    simp +zetaDelta at *;
    exact ⟨ by have := p.edges_subset_edgeSet he; unfold cellGraph at this; aesop, he ⟩;
  -- Since $D = C$, the edges of $p$ are exactly the images of the cells in $C$ under $cellSym2$.
  have h_edges_eq : p.edges.toFinset = Finset.image cellSym2 C := by
    ext e; simp;
    constructor;
    · intro he;
      have := p.edges_subset_edgeSet he;
      rcases e with ⟨ u, v ⟩ ; simp_all +decide [ cellGraph ] ;
      rcases u with ( u | u ) <;> rcases v with ( v | v ) <;> simp_all +decide [ cellSym2 ];
    · rintro ⟨ a, b, h, rfl ⟩ ; replace hD_eq_C := Finset.ext_iff.mp hD_eq_C ( a, b ) ; aesop;
  refine' ⟨ v, p, hp, h_edges_eq, _, _ ⟩;
  · have h_card_edges : p.edges.toFinset.card = C.card := by
      rw [ h_edges_eq, Finset.card_image_of_injective ];
      intro x y; simp +decide [ cellSym2 ] ;
      exact fun h1 h2 => Prod.ext h1 h2;
    rw [ ← h_card_edges, List.toFinset_card_of_nodup ];
    · exact Eq.symm (SimpleGraph.Walk.length_edges p);
    · exact hp.edges_nodup;
  · have := hp.isPath_tail.length_lt;
    cases p <;> aesop

end

end Erdos625
