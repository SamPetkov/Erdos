import Erdos625.ColoringProfileChromaticBridge
import Erdos625.ColoringProfileFirstMomentBound

/-!
# Finite first-moment probability bound for bounded colorings

This module completes the measure-theoretic bookkeeping in manuscript (4.5).
The event that the aggregate bounded-profile count is positive has probability
at most its exact finite expectation.  Combining this Markov bound with the
deterministic chromatic-to-profile containment leaves only the exceptional
event that the independence number exceeds the block-size cap.

These are finite inequalities for arbitrary natural parameters.  No
continuous-profile estimate or asymptotic conclusion is asserted here.
-/

namespace Erdos625

open MeasureTheory

noncomputable section

/-- Event that at least one exactly-`parts`, size-`b` bounded profile coloring
exists. -/
def boundedProfileColoringCountPositiveEvent (n b parts : ℕ) :
    Set (LabeledGraph n) :=
  {G | 0 < boundedProfileColoringCount G b parts}

/-- Event that the chromatic number is at most `parts`. -/
def chromaticNumberAtMostEvent (n parts : ℕ) : Set (LabeledGraph n) :=
  {G | chromaticNumberNat G ≤ parts}

theorem measurableSet_boundedProfileColoringCountPositiveEvent
    (n b parts : ℕ) :
    MeasurableSet (boundedProfileColoringCountPositiveEvent n b parts) :=
  Set.toFinite (boundedProfileColoringCountPositiveEvent n b parts) |>.measurableSet

theorem measurableSet_chromaticNumberAtMostEvent (n parts : ℕ) :
    MeasurableSet (chromaticNumberAtMostEvent n parts) :=
  Set.toFinite (chromaticNumberAtMostEvent n parts) |>.measurableSet

/-- Finite-space Markov inequality at threshold one for the aggregate bounded
profile count. -/
theorem randomGraphMeasure_boundedProfileColoringCountPositive_le_expectation
    (n b parts : ℕ) :
    randomGraphMeasure n (boundedProfileColoringCountPositiveEvent n b parts) ≤
      boundedProfileColoringExpectation n b parts := by
  classical
  let T := (Finset.univ : Finset (LabeledGraph n)).filter
    (fun G ↦ 0 < boundedProfileColoringCount G b parts)
  calc
    randomGraphMeasure n (boundedProfileColoringCountPositiveEvent n b parts) =
        randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      congr 1
      ext G
      simp [T, boundedProfileColoringCountPositiveEvent]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = ∑ G : LabeledGraph n,
        if 0 < boundedProfileColoringCount G b parts
        then randomGraphMeasure n {G} else 0 := by
      simp only [T, Finset.sum_filter]
    _ ≤ ∑ G : LabeledGraph n,
        (boundedProfileColoringCount G b parts : ENNReal) *
          randomGraphMeasure n {G} := by
      apply Finset.sum_le_sum
      intro G _
      by_cases h : 0 < boundedProfileColoringCount G b parts
      · rw [if_pos h]
        have hone : (1 : ENNReal) ≤
            (boundedProfileColoringCount G b parts : ENNReal) := by
          exact_mod_cast (Nat.succ_le_iff.mpr h)
        calc
          randomGraphMeasure n {G} =
              1 * randomGraphMeasure n {G} := (one_mul _).symm
          _ ≤ (boundedProfileColoringCount G b parts : ENNReal) *
              randomGraphMeasure n {G} := mul_le_mul_left hone _
      · simp [h]
    _ = boundedProfileColoringExpectation n b parts := rfl

/-- Exact finite first-moment reduction for an unrestricted chromatic event.
If `parts ≤ n`, a graph with chromatic number at most `parts` either contributes
to the bounded-profile count or has an independent set larger than `b`. -/
theorem randomGraphMeasure_chromaticNumberAtMost_le_expectation_add_independence
    {n b parts : ℕ} (hparts : parts ≤ n) :
    randomGraphMeasure n (chromaticNumberAtMostEvent n parts) ≤
      boundedProfileColoringExpectation n b parts +
        randomGraphMeasure n (independenceNumberExceedsEvent n b) := by
  calc
    randomGraphMeasure n (chromaticNumberAtMostEvent n parts) ≤
        randomGraphMeasure n
          (boundedProfileColoringCountPositiveEvent n b parts ∪
            independenceNumberExceedsEvent n b) := by
      apply measure_mono
      exact chromaticNumberNat_le_set_subset_boundedProfileColoringCount_pos_union
        hparts
    _ ≤ randomGraphMeasure n
          (boundedProfileColoringCountPositiveEvent n b parts) +
        randomGraphMeasure n (independenceNumberExceedsEvent n b) :=
      measure_union_le _ _
    _ ≤ boundedProfileColoringExpectation n b parts +
        randomGraphMeasure n (independenceNumberExceedsEvent n b) := by
      simpa [add_comm] using
        add_le_add_right
          (randomGraphMeasure_boundedProfileColoringCountPositive_le_expectation
            n b parts)
          (randomGraphMeasure n (independenceNumberExceedsEvent n b))

/-- Fully finite form of the Section 4 first-moment reduction.  Once every
admissible profile has the displayed common logarithmic upper bound, the
chromatic event is bounded by the explicit profile-box exponential term plus
the independent-set first moment.  The later analytic task is to provide `L`
that tends sufficiently far to `-∞` at the manuscript's chosen parameters. -/
theorem randomGraphMeasure_chromaticNumberAtMost_le_box_mul_exp_add_mu
    {n b parts : ℕ} (L : ℝ) (hparts : parts ≤ n)
    (hL : ∀ k ∈ boundedColoringProfiles n b parts,
      profileStirlingUpperMain n k + factorialLogErrorBound n ≤ L) :
    randomGraphMeasure n (chromaticNumberAtMostEvent n parts) ≤
      (((n + 1) ^ b : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L) +
        ENNReal.ofReal (mu n (b + 1)) := by
  calc
    randomGraphMeasure n (chromaticNumberAtMostEvent n parts) ≤
        boundedProfileColoringExpectation n b parts +
          randomGraphMeasure n (independenceNumberExceedsEvent n b) :=
      randomGraphMeasure_chromaticNumberAtMost_le_expectation_add_independence
        hparts
    _ ≤ (((n + 1) ^ b : ℕ) : ENNReal) *
          ENNReal.ofReal (Real.exp L) + ENNReal.ofReal (mu n (b + 1)) := by
      exact add_le_add
        (boundedProfileColoringExpectation_le_box_mul_exp n b parts L hL)
        (randomGraphMeasure_independenceNumberExceeds_le_mu_succ n b)

end

end Erdos625
