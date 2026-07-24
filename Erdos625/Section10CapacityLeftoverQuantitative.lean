import Mathlib.MeasureTheory.Measure.Real

/-!
# Section 10: quantitative capacity/leftover intersection

This module records the elementary quantitative probability seam used when a
capacity event and the simultaneous leftover-colouring event are combined.
No independence hypothesis is needed: failure of their common consequence is
contained in the union of the two failure events.
-/

namespace Erdos625

open MeasureTheory Set

/-- If two success events together imply `Good`, then the failure probability
of `Good` is at most the sum of their two failure-probability bounds. -/
theorem failure_probability_le_add_of_two_success_events
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (A B Good : Set Ω)
    (_hAmeas : MeasurableSet A) (_hBmeas : MeasurableSet B)
    (hInter : A ∩ B ⊆ Good)
    (delta epsilon : ℝ)
    (hA : mu.real Aᶜ ≤ delta)
    (hB : mu.real Bᶜ ≤ epsilon) :
    mu.real Goodᶜ ≤ delta + epsilon := by
  have hcompl : Goodᶜ ⊆ Aᶜ ∪ Bᶜ := by
    simpa only [compl_inter] using Set.compl_subset_compl.mpr hInter
  calc
    mu.real Goodᶜ ≤ mu.real (Aᶜ ∪ Bᶜ) := measureReal_mono hcompl
    _ ≤ mu.real Aᶜ + mu.real Bᶜ := measureReal_union_le _ _
    _ ≤ delta + epsilon := add_le_add hA hB

#print axioms failure_probability_le_add_of_two_success_events

end Erdos625
