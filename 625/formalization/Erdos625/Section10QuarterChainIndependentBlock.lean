import Erdos625.Section10QuarterChainAdapters
import Erdos625.Section10QuarterChainParameters
import Erdos625.Section10QuarterChainSurvivalTransport
import Erdos625.Section10UniformQuarterDensityEvent
import Erdos625.Section10QuarterDenseChain
import Erdos625.Section10SimultaneousGreedyColoring
import Mathlib.Tactic

/-!
# Section X: uniform independent blocks from the quarter-density event

This module composes the accepted all-larger complement-density event, finite
quarter-dense clique chain, and shifted-potential survival estimate.  On one
event, every sufficiently large vertex set contains an independent block of
the same deterministic cardinality.  The final theorem then exposes the exact
uniform hypothesis consumed by the accepted greedy-colouring recursion.

This is still a deterministic/probability-event bridge.  It does not prove the
numerical `O(|U| / log n) + n^(1/3)` estimate, the simultaneous leftover event
at a prescribed natural threshold, Lemma 10.2, or the final theorem.
-/

namespace Erdos625

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- One event with the necessary internal universal quantifier: every vertex
set at least as large as the chain start contains an independent block at
least as large as the deterministic chain length. -/
def quarterChainIndependentBlockEvent (n : ℕ) : Set (LabeledGraph n) :=
  {G | ∀ U : Finset (Fin n), quarterChainStart n ≤ U.card →
    ∃ I : Finset (Fin n),
      I ⊆ U ∧ quarterChainSteps n ≤ I.card ∧
        G.IsIndepSet (I : Set (Fin n))}

/-- At one fixed `n`, the all-larger complement-density event implies the
uniform independent-block event once the explicit cutoff positivity and
shifted-potential survival hypotheses are supplied. -/
theorem cutoffComplementAllLargerQuarterDenseEvent_subset_independentBlockEvent
    (n : ℕ) (hcutoff : 1 ≤ quarterDensityCutoff n)
    (hStart : ∀ j : ℕ, j < quarterChainSteps n →
      (quarterDensityCutoff n : ℝ) ≤
        (4 : ℝ)⁻¹ ^ j * ((quarterChainStart n : ℝ) + 1 / 3) - 1 / 3) :
    cutoffComplementAllLargerQuarterDenseEvent n ⊆
      quarterChainIndependentBlockEvent n := by
  intro G hG U hU
  have hSurvive :
      ∀ j : ℕ, j < quarterChainSteps n →
        (quarterDensityCutoff n : ℝ) ≤
          (4 : ℝ)⁻¹ ^ j * ((U.card : ℝ) + 1 / 3) - 1 / 3 :=
    quarterChain_shifted_survival_of_start_le_card n U hU hStart
  obtain ⟨C, _R, hCcard, hCsub, hClique, _hRsub, _hCRadj, _hRcard⟩ :=
    exists_quarterDense_clique_chain
      Gᶜ U (quarterDensityCutoff n) (quarterChainSteps n) hcutoff
      (fun T _hTU hTcard => hG T hTcard) hSurvive
  refine ⟨C, hCsub, ?_, isIndepSet_of_compl_isClique G C hClique⟩
  simp [hCcard]

/-- The fixed-`n` event inclusion above holds eventually along the full natural
sequence. -/
theorem cutoffComplementAllLargerQuarterDenseEvent_subset_independentBlockEvent_eventually :
    ∀ᶠ n : ℕ in atTop,
      cutoffComplementAllLargerQuarterDenseEvent n ⊆
        quarterChainIndependentBlockEvent n := by
  filter_upwards
    [one_le_quarterDensityCutoff_eventually,
      quarterChain_shifted_survival_eventually]
    with n hcutoff hStart
  exact
    cutoffComplementAllLargerQuarterDenseEvent_subset_independentBlockEvent
      n hcutoff hStart

/-- The one-event uniform independent-block property has probability tending
to one along the full natural sequence. -/
theorem quarterChainIndependentBlockEvent_probability_tendsto_one :
    Tendsto
      (fun n ↦ randomGraphMeasure n (quarterChainIndependentBlockEvent n))
      atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    cutoffComplementAllLargerQuarterDenseEvent_probability_tendsto_one
    tendsto_const_nhds ?_ ?_
  · exact
      cutoffComplementAllLargerQuarterDenseEvent_subset_independentBlockEvent_eventually.mono
        fun n hn ↦ measure_mono hn
  · exact Filter.Eventually.of_forall fun n ↦ by
      calc
        randomGraphMeasure n (quarterChainIndependentBlockEvent n) ≤
            randomGraphMeasure n Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ

/-- On the independent-block event, the accepted greedy recursion gives one
chromatic bound simultaneously for every induced vertex set. -/
theorem chromaticNumberNat_induce_le_of_independentBlockEvent
    (n : ℕ) (G : LabeledGraph n)
    (hG : G ∈ quarterChainIndependentBlockEvent n)
    (hblock : 1 ≤ quarterChainSteps n) :
    ∀ U : Finset (Fin n),
      chromaticNumberNat (G.induce (U : Set (Fin n))) ≤
        ceilDivNat U.card (quarterChainSteps n) + quarterChainStart n := by
  classical
  exact simultaneous_induced_chromatic_bound
    G (quarterChainStart n) (quarterChainSteps n) hblock hG

#print axioms cutoffComplementAllLargerQuarterDenseEvent_subset_independentBlockEvent
#print axioms cutoffComplementAllLargerQuarterDenseEvent_subset_independentBlockEvent_eventually
#print axioms quarterChainIndependentBlockEvent_probability_tendsto_one
#print axioms chromaticNumberNat_induce_le_of_independentBlockEvent

end

end Erdos625
