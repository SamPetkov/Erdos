import Erdos625.Section10QuarterChainIndependentBlock
import Mathlib.Tactic

/-!
# Section X: parameter-independent independent-block failure sequence

The high-probability independent-block event is determined only by `n`.  This
module records the real probability of its complement as one deterministic
error sequence and proves that it tends to zero.  Consequently this error
cannot depend on the later seed, exponent, radius, or deficit parameters.

No deficit-indexed leftover threshold or Lemma 10.2 assembly is included.
-/

namespace Erdos625

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- The real failure probability of the one-event uniform independent-block
property. -/
def quarterChainIndependentBlockFailure (n : ℕ) : ℝ :=
  (randomGraphMeasure n).real (quarterChainIndependentBlockEvent n)ᶜ

theorem measurableSet_quarterChainIndependentBlockEvent (n : ℕ) :
    MeasurableSet (quarterChainIndependentBlockEvent n) :=
  Set.toFinite (quarterChainIndependentBlockEvent n) |>.measurableSet

theorem quarterChainIndependentBlockFailure_nonneg (n : ℕ) :
    0 ≤ quarterChainIndependentBlockFailure n :=
  measureReal_nonneg

/-- The deterministic failure sequence tends to zero along the full natural
sequence. -/
theorem quarterChainIndependentBlockFailure_tendsto_zero :
    Tendsto quarterChainIndependentBlockFailure atTop (nhds 0) := by
  have hSuccessReal :
      Tendsto
        (fun n : ℕ ↦
          (randomGraphMeasure n).real (quarterChainIndependentBlockEvent n))
        atTop (nhds (1 : ℝ)) := by
    simpa only [Measure.real, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal_iff
        (fun n ↦ measure_ne_top (randomGraphMeasure n)
          (quarterChainIndependentBlockEvent n))
        ENNReal.one_ne_top).mpr
        quarterChainIndependentBlockEvent_probability_tendsto_one
  have hFailureIdentity : ∀ n : ℕ,
      quarterChainIndependentBlockFailure n =
        1 - (randomGraphMeasure n).real
          (quarterChainIndependentBlockEvent n) := by
    intro n
    have hCompl := measureReal_compl
      (μ := randomGraphMeasure n)
      (measurableSet_quarterChainIndependentBlockEvent n)
    rw [probReal_univ] at hCompl
    unfold quarterChainIndependentBlockFailure
    linarith
  have hSub :
      Tendsto
        (fun n : ℕ ↦
          1 - (randomGraphMeasure n).real
            (quarterChainIndependentBlockEvent n))
        atTop (nhds (0 : ℝ)) := by
    convert (tendsto_const_nhds.sub hSuccessReal) using 1
    all_goals norm_num
  exact hSub.congr'
    (Filter.Eventually.of_forall fun n ↦ (hFailureIdentity n).symm)

#print axioms measurableSet_quarterChainIndependentBlockEvent
#print axioms quarterChainIndependentBlockFailure_nonneg
#print axioms quarterChainIndependentBlockFailure_tendsto_zero

end

end Erdos625
