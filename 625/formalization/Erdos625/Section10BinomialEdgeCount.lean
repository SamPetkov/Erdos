import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Tactic

/-!
# Section 10: edge-count law for a finite binomial random graph

This module proves the exact singleton distribution of the number of edges in
`G(V,p)`.  The statement is the `proof_wanted` currently recorded in
Mathlib's binomial-random-graph definitions and is the finite probability-law
bridge needed before applying the quarter-tail estimate to a fixed induced
vertex set.
-/

namespace Erdos625

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal Finset

/-- The edge count of a finite binomial random graph has the expected
binomial singleton mass. -/
theorem binomialRandom_map_ncard_edgeSet_singleton
    {V : Type*} {p : I} [Finite V] (n : ℕ) :
    (SimpleGraph.binomialRandom V p).map (fun G ↦ G.edgeSet.ncard) {n} =
      ((Nat.card V).choose 2).choose n * toNNReal p ^ n *
        toNNReal (σ p) ^ ((Nat.card V).choose 2 - n) := by
  classical
  cases nonempty_fintype V
  letI : MeasurableSingletonClass (SimpleGraph V) := by
    constructor
    intro G
    rw [← SimpleGraph.measurableEmbedding_edgeSet.measurableSet_image]
    simp
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton n)]
  have hpre : (fun G : SimpleGraph V ↦ G.edgeSet.ncard) ⁻¹' {n} =
      ↑(Finset.univ.filter fun G : SimpleGraph V ↦ G.edgeSet.ncard = n) := by
    ext G
    simp
  rw [hpre]
  rw [← MeasureTheory.sum_measure_singleton]
  simp_rw [SimpleGraph.binomialRandom_singleton]
  let U : Finset (Sym2 V) := Sym2.diagSetᶜ.toFinset
  have hcard :
      #(Finset.univ.filter fun G : SimpleGraph V ↦ G.edgeSet.ncard = n) =
        ((Fintype.card V).choose 2).choose n := by
    calc
      #(Finset.univ.filter fun G : SimpleGraph V ↦ G.edgeSet.ncard = n) =
          #(U.powersetCard n) := by
        apply Finset.card_bij (fun G _ ↦ G.edgeSet.toFinset)
        · intro G hG
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
          rw [Finset.mem_powersetCard]
          constructor
          · exact Set.toFinset_subset_toFinset.2 G.edgeSet_subset_compl_diagSet
          · rw [← Set.ncard_coe_finset]
            simpa using hG
        · intro G₁ h₁ G₂ h₂ h
          apply SimpleGraph.edgeSet_injective
          exact Set.toFinset_inj.mp h
        · intro s hs
          have hs' := Finset.mem_powersetCard.mp hs
          have hsub : (s : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by
            intro e he
            have : e ∈ U := hs'.1 he
            simpa [U] using this
          have hedge : (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet = s := by
            rw [SimpleGraph.edgeSet_fromEdgeSet]
            ext e
            simp only [Set.mem_sdiff, Finset.mem_coe]
            constructor
            · exact fun h ↦ h.1
            · exact fun he ↦ ⟨he, hsub he⟩
          refine ⟨SimpleGraph.fromEdgeSet s, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hedge, Set.ncard_coe_finset]
            exact hs'.2
          · apply Finset.coe_injective
            simpa using hedge
      _ = ((Fintype.card V).choose 2).choose n := by
        rw [Finset.card_powersetCard]
        congr 1
        rw [show U.card = Fintype.card (Sym2.diagSetᶜ : Set (Sym2 V)) by
          exact Set.toFinset_card _]
        exact Sym2.card_diagSet_compl
  have hsum :
      ∑ x ∈ (Finset.univ.filter fun G : SimpleGraph V ↦ G.edgeSet.ncard = n),
          (toNNReal p : ℝ≥0∞) ^ x.edgeSet.ncard *
            (toNNReal (σ p) : ℝ≥0∞) ^
              ((Nat.card V).choose 2 - x.edgeSet.ncard) =
        #(Finset.univ.filter fun G : SimpleGraph V ↦ G.edgeSet.ncard = n) •
          ((toNNReal p : ℝ≥0∞) ^ n *
            (toNNReal (σ p) : ℝ≥0∞) ^ ((Nat.card V).choose 2 - n)) := by
    rw [Finset.sum_congr rfl]
    · exact Finset.sum_const _
    · intro G hG
      rw [(Finset.mem_filter.mp hG).2]
  rw [hsum, nsmul_eq_mul, hcard, Nat.card_eq_fintype_card]
  ring

#print axioms binomialRandom_map_ncard_edgeSet_singleton

end Erdos625
