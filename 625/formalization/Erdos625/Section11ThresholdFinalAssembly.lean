import Erdos625.Section11AsymptoticAssembly
import Mathlib.Tactic

/-!
# Section XI D2: two-tail threshold assembly

This task closes only the generic final event seam.  Both probability-one
tails and the exact eventual threshold separation remain explicit inputs.
-/

namespace Erdos625

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- Two probability-one threshold events and the exact Section XI separation
imply the formal Erdős 625 target. -/
theorem erdos625Statement_of_chromatic_cochromatic_thresholds
    (kChi kCo : Nat -> Nat) (a : Nat -> Real)
    (hChromaticTail : Tendsto
      (fun n => randomGraphMeasure n (chromaticLowerEvent n (kChi n)))
      atTop (nhds 1))
    (hCochromaticTail : Tendsto
      (fun n => randomGraphMeasure n
        (cochromaticUpperEvent n (kCo n) (a n)))
      atTop (nhds 1))
    (hGapThreshold : ∀ᶠ n in atTop,
      gapScale n ≤
        (((kChi n) + 1 : Nat) : Real) - ((kCo n : Real) + a n)) :
    Erdos625Statement := by
  have hThresholdIntersection : Tendsto
      (fun n => randomGraphMeasure n
        (chromaticLowerEvent n (kChi n) ∩
          cochromaticUpperEvent n (kCo n) (a n)))
      atTop (nhds 1) :=
    tendsto_measure_inter_one randomGraphMeasure
      (fun n => chromaticLowerEvent n (kChi n))
      (fun n => cochromaticUpperEvent n (kCo n) (a n))
      (fun n => Set.toFinite
        (chromaticLowerEvent n (kChi n)) |>.measurableSet)
      (fun n => Set.toFinite
        (cochromaticUpperEvent n (kCo n) (a n)) |>.measurableSet)
      hChromaticTail hCochromaticTail
  unfold Erdos625Statement
  change Tendsto (fun n => randomGraphMeasure n (gapEvent n))
    atTop (nhds 1)
  apply tendsto_measure_one_of_eventually_subset randomGraphMeasure
    (fun n => chromaticLowerEvent n (kChi n) ∩
      cochromaticUpperEvent n (kCo n) (a n))
    gapEvent hThresholdIntersection
  filter_upwards [hGapThreshold] with n hThreshold
  exact thresholdIntersection_subset_gapEvent hThreshold

#print axioms erdos625Statement_of_chromatic_cochromatic_thresholds

end Erdos625
