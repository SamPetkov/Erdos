import Erdos625.Section10QuarterDensityLift
import Erdos625.Section10QuarterDensityLimit
import Mathlib.Tactic

/-!
# Section X: high-probability all-larger quarter-density event

This module packages the accepted literal cutoff event, its probability-one
limit, and its deterministic larger-subset lift into one event whose
probability tends to one.  It does not construct a clique chain, transfer a
complement clique to an independent set, or invoke greedy colouring.
-/

namespace Erdos625

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- The event on which every vertex subset at least as large as the cutoff is
quarter-dense in the complement graph. -/
def cutoffComplementAllLargerQuarterDenseEvent (n : ℕ) : Set (LabeledGraph n) :=
  {G | ∀ S : Finset (Fin n), quarterDensityCutoff n ≤ S.card →
    QuarterDenseOn Gᶜ S}

/-- Once the cutoff is at least two, the literal cutoff event is contained in
the all-larger quarter-density event. -/
theorem cutoffComplementQuarterDensityEvent_subset_allLargerQuarterDenseEvent
    (n : ℕ) (hcutoff : 2 ≤ quarterDensityCutoff n) :
    cutoffComplementQuarterDensityEvent n ⊆
      cutoffComplementAllLargerQuarterDenseEvent n := by
  intro G hG S hS
  exact cutoffComplementQuarterDensityEvent_quarterDense_all_larger n G hG
    hcutoff S hS

/-- The all-larger complement quarter-density event has probability tending to
one along the full natural sequence. -/
theorem cutoffComplementAllLargerQuarterDenseEvent_probability_tendsto_one :
    Tendsto
      (fun n ↦ randomGraphMeasure n
        (cutoffComplementAllLargerQuarterDenseEvent n))
      atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    cutoffComplementQuarterDensityEvent_probability_tendsto_one
    tendsto_const_nhds ?_ ?_
  · filter_upwards [quarterDensityCutoff_tendsto_atTop.eventually_ge_atTop 2]
      with n hn
    exact measure_mono
      (cutoffComplementQuarterDensityEvent_subset_allLargerQuarterDenseEvent n hn)
  · exact Filter.Eventually.of_forall fun n ↦ by
      calc
        randomGraphMeasure n (cutoffComplementAllLargerQuarterDenseEvent n) ≤
            randomGraphMeasure n Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ

#print axioms cutoffComplementQuarterDensityEvent_subset_allLargerQuarterDenseEvent
#print axioms cutoffComplementAllLargerQuarterDenseEvent_probability_tendsto_one

end

end Erdos625
