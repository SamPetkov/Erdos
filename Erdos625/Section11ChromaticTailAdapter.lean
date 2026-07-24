import Erdos625.Section11ChromaticLowerTailBridge
import Erdos625.Section11EventAssembly
import Mathlib.Tactic

/-!
# Section XI D1: graph-specific chromatic-tail adapter

This task specializes the accepted generic strict-lower-tail complement lemma
to the actual random-graph chromatic number and Section XI event.
-/

namespace Erdos625

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- A probability-zero upper bound for the actual chromatic at-most event is
exactly the probability-one strict chromatic lower event used in Section XI.
-/
theorem chromaticLowerEvent_probability_tendsto_one_of_atMost_tendsto_zero
    (kChi : Nat -> Nat)
    (hAtMost : Tendsto
      (fun n => randomGraphMeasure n
        {G : LabeledGraph n | chromaticNumberNat G ≤ kChi n})
      atTop (nhds 0)) :
    Tendsto
      (fun n => randomGraphMeasure n (chromaticLowerEvent n (kChi n)))
      atTop (nhds 1) := by
  simpa only [chromaticLowerEvent] using
    (strictLower_probability_tendsto_one_of_atMost_tendsto_zero
      (Ω := fun n => LabeledGraph n)
      (mu := fun n => randomGraphMeasure n)
      (X := fun _ G => chromaticNumberNat G)
      (k := kChi)
      (hMeas := fun _ => Set.toFinite _ |>.measurableSet)
      hAtMost)

#print axioms chromaticLowerEvent_probability_tendsto_one_of_atMost_tendsto_zero

end Erdos625
