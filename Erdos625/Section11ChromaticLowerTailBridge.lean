import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Section 11: strict chromatic lower-tail bridge

For a natural-valued statistic, the strict lower event is exactly the
complement of the corresponding at-most event.  This module transports a
full-sequence probability-zero upper-tail statement to probability one for
the strict lower event, allowing the sample space to depend on `n`.
-/

namespace Erdos625

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- If the probability that `X n` is at most `k n` tends to zero, then the
probability of the complementary strict event tends to one. -/
theorem strictLower_probability_tendsto_one_of_atMost_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (mu : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (mu n)]
    (X : ∀ n, Ω n → ℕ) (k : ℕ → ℕ)
    (hMeas : ∀ n, MeasurableSet {ω | X n ω ≤ k n})
    (hAtMost : Tendsto
      (fun n ↦ mu n {ω | X n ω ≤ k n}) atTop (nhds 0)) :
    Tendsto (fun n ↦ mu n {ω | k n < X n ω}) atTop (nhds 1) := by
  have hmeasure (n : ℕ) :
      mu n {ω | k n < X n ω} = 1 - mu n {ω | X n ω ≤ k n} := by
    rw [show {ω | k n < X n ω} = {ω | X n ω ≤ k n}ᶜ by
      ext ω
      simp]
    simpa only [measure_univ] using
      measure_compl (hMeas n) (measure_ne_top (mu n) _)
  have hsub : Tendsto
      (fun n ↦ (1 : ℝ≥0∞) - mu n {ω | X n ω ≤ k n}) atTop
      (nhds ((1 : ℝ≥0∞) - 0)) :=
    (ENNReal.continuous_sub_left (by simp)).tendsto 0 |>.comp hAtMost
  simpa only [hmeasure, tsub_zero] using hsub

#print axioms strictLower_probability_tendsto_one_of_atMost_tendsto_zero

end Erdos625
