import Erdos625.Section10QuarterChainFailure
import Erdos625.Section10QuarterChainGreedyNumeric
import Mathlib.Tactic

/-!
# Section X: the uniform linear-cost colouring event

This module packages the deterministic quarter-chain recursion as the single
event used in the manuscript form of Lemma 10.1.  The universal quantifier over
all induced vertex sets remains inside the event:

`χ(G[U]) ≤ C |U| / log n + n^(1/3)`.

The proof deliberately keeps the greedy cost piecewise.  A set below the
quarter-chain cutoff is coloured one vertex at a time and therefore costs
exactly `|U|`; only the large-set branch invokes ceiling division.  Thus no
spurious additive `+ 1` is introduced in the small-set branch.
-/

namespace Erdos625

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The manuscript-form event from Lemma 10.1: one graph satisfies the same
linear-logarithmic chromatic bound for every induced vertex set. -/
def quarterChainLinearColoringEvent (C : ℝ) (n : ℕ) :
    Set (LabeledGraph n) :=
  {G | ∀ U : Finset (Fin n),
    (chromaticNumberNat (G.induce (U : Set (Fin n))) : ℝ) ≤
      C * (U.card : ℝ) / Real.log (n : ℝ) +
        (n : ℝ) ^ (1 / 3 : ℝ)}

/-- The chromatic number of a graph induced by a finite vertex set is at most
the cardinality of that set. -/
theorem chromaticNumberNat_induce_finset_le_card
    {n : ℕ} (G : LabeledGraph n) (U : Finset (Fin n)) :
    chromaticNumberNat (G.induce (U : Set (Fin n))) ≤ U.card := by
  classical
  have hColorable :
      (G.induce (U : Set (Fin n))).Colorable U.card := by
    simpa using (G.induce (U : Set (Fin n))).colorable_of_fintype
  exact Nat.cast_le.mp
    (le_trans
      (ENat.toNat_le_toNat
        (SimpleGraph.chromaticNumber_le_iff_colorable.mpr hColorable)
        (by simp +decide))
      (by simp +decide))

/-- On the uniform independent-block event, every induced subgraph is bounded
by the exact piecewise quarter-chain greedy cost. -/
theorem chromaticNumberNat_induce_le_quarterChainGreedyColorCost
    (n : ℕ) (G : LabeledGraph n)
    (hG : G ∈ quarterChainIndependentBlockEvent n)
    (hblock : 1 ≤ quarterChainSteps n) :
    ∀ U : Finset (Fin n),
      chromaticNumberNat (G.induce (U : Set (Fin n))) ≤
        quarterChainGreedyColorCost n U.card := by
  intro U
  by_cases hsmall : U.card < quarterChainStart n
  · rw [quarterChainGreedyColorCost, if_pos hsmall]
    exact chromaticNumberNat_induce_finset_le_card G U
  · rw [quarterChainGreedyColorCost, if_neg hsmall]
    exact
      chromaticNumberNat_induce_le_of_independentBlockEvent
        n G hG hblock U

/-- A fixed numerical bound on the piecewise greedy cost turns the
independent-block event into the manuscript linear-cost event. -/
theorem quarterChainIndependentBlockEvent_subset_linearColoringEvent
    (n : ℕ) (C : ℝ) (hblock : 1 ≤ quarterChainSteps n)
    (hCost : ∀ u : ℕ, u ≤ n →
      (quarterChainGreedyColorCost n u : ℝ) ≤
        C * (u : ℝ) / Real.log (n : ℝ) +
          (n : ℝ) ^ (1 / 3 : ℝ)) :
    quarterChainIndependentBlockEvent n ⊆
      quarterChainLinearColoringEvent C n := by
  intro G hG U
  have hUle : U.card ≤ n := by
    simpa using Finset.card_le_univ U
  have hNat :=
    chromaticNumberNat_induce_le_quarterChainGreedyColorCost
      n G hG hblock U
  have hReal :
      (chromaticNumberNat (G.induce (U : Set (Fin n))) : ℝ) ≤
        (quarterChainGreedyColorCost n U.card : ℝ) := by
    exact_mod_cast hNat
  exact hReal.trans (hCost U.card hUle)

/-- There is one positive absolute constant for which the event inclusion
holds eventually along the full natural-number sequence. -/
theorem
    exists_quarterChainIndependentBlockEvent_subset_linearColoringEvent_eventually :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        quarterChainIndependentBlockEvent n ⊆
          quarterChainLinearColoringEvent C n := by
  obtain ⟨C, hC, hCost⟩ :=
    quarterChainGreedyColorCost_eventually_le_linear_log_plus_cubeRoot
  refine ⟨C, hC, ?_⟩
  filter_upwards [one_le_quarterChainSteps_eventually, hCost]
    with n hblock hCostN
  exact
    quarterChainIndependentBlockEvent_subset_linearColoringEvent
      n C hblock hCostN

/-- Eventual enlargement of the accepted independent-block event transfers
its probability-one limit to the uniform linear-cost event. -/
theorem quarterChainLinearColoringEvent_probability_tendsto_one_of_subset
    (C : ℝ)
    (hSubset : ∀ᶠ n : ℕ in atTop,
      quarterChainIndependentBlockEvent n ⊆
        quarterChainLinearColoringEvent C n) :
    Tendsto
      (fun n ↦ randomGraphMeasure n (quarterChainLinearColoringEvent C n))
      atTop (nhds 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    quarterChainIndependentBlockEvent_probability_tendsto_one
    tendsto_const_nhds
    (hSubset.mono fun n hn ↦ measure_mono hn)
    (Filter.Eventually.of_forall fun n ↦ by
      calc
        randomGraphMeasure n (quarterChainLinearColoringEvent C n) ≤
            randomGraphMeasure n Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ)

/-- The manuscript-form uniform induced-colouring event holds with high
probability for one positive absolute constant. -/
theorem exists_quarterChainLinearColoringEvent_probability_tendsto_one :
    ∃ C : ℝ, 0 < C ∧
      Tendsto
        (fun n ↦ randomGraphMeasure n (quarterChainLinearColoringEvent C n))
        atTop (nhds 1) := by
  obtain ⟨C, hC, hSubset⟩ :=
    exists_quarterChainIndependentBlockEvent_subset_linearColoringEvent_eventually
  exact
    ⟨C, hC,
      quarterChainLinearColoringEvent_probability_tendsto_one_of_subset
        C hSubset⟩

/-- Quantitative complement form: whenever the deterministic event inclusion
holds, failure of the linear-cost event is bounded by the same
parameter-independent failure sequence as the independent-block event. -/
theorem quarterChainLinearColoringEvent_compl_probability_le_failure_eventually
    (C : ℝ)
    (hSubset : ∀ᶠ n : ℕ in atTop,
      quarterChainIndependentBlockEvent n ⊆
        quarterChainLinearColoringEvent C n) :
    ∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
          (quarterChainLinearColoringEvent C n)ᶜ ≤
        quarterChainIndependentBlockFailure n := by
  filter_upwards [hSubset] with n hn
  unfold quarterChainIndependentBlockFailure
  apply measureReal_mono (h₂ := by finiteness)
  exact Set.compl_subset_compl.mpr hn

/-- One positive constant simultaneously supplies the eventual event
inclusion, probability-one limit, and the quantitative complement bound. -/
theorem exists_quarterChainLinearColoringEvent_full_control :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ n : ℕ in atTop,
        quarterChainIndependentBlockEvent n ⊆
          quarterChainLinearColoringEvent C n) ∧
      Tendsto
        (fun n ↦ randomGraphMeasure n (quarterChainLinearColoringEvent C n))
        atTop (nhds 1) ∧
      (∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real
            (quarterChainLinearColoringEvent C n)ᶜ ≤
          quarterChainIndependentBlockFailure n) := by
  obtain ⟨C, hC, hSubset⟩ :=
    exists_quarterChainIndependentBlockEvent_subset_linearColoringEvent_eventually
  refine ⟨C, hC, hSubset, ?_, ?_⟩
  · exact
      quarterChainLinearColoringEvent_probability_tendsto_one_of_subset
        C hSubset
  · exact
      quarterChainLinearColoringEvent_compl_probability_le_failure_eventually
        C hSubset

#print axioms chromaticNumberNat_induce_finset_le_card
#print axioms chromaticNumberNat_induce_le_quarterChainGreedyColorCost
#print axioms quarterChainIndependentBlockEvent_subset_linearColoringEvent
#print axioms exists_quarterChainIndependentBlockEvent_subset_linearColoringEvent_eventually
#print axioms quarterChainLinearColoringEvent_probability_tendsto_one_of_subset
#print axioms exists_quarterChainLinearColoringEvent_probability_tendsto_one
#print axioms quarterChainLinearColoringEvent_compl_probability_le_failure_eventually
#print axioms exists_quarterChainLinearColoringEvent_full_control

end

end Erdos625
