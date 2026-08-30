import Erdos625.Section13GlobalFixedOffsetSeed
import Erdos625.Section10_11UniformSeedRootFinal
import Erdos625.Section11ConcreteChromaticLowerTail
import Erdos625.Section8FixedOffsetPhaseInputs

/-!
# Section XV: final Erdős 625 instantiation

This module supplies the concrete seed, chromatic tail, rounding budget, and
root corridor to the final theorem. No quantitative hypothesis remains.
-/

namespace Erdos625

open Filter MeasureTheory Set Asymptotics
open scoped ENNReal Topology

noncomputable section

/-- Erdős Problem 625: the manuscript-scale chromatic/cochromatic gap event
has probability tending to one along the full sequence. -/
theorem erdos625 : Erdos625Statement := by
  obtain ⟨Lambda, hLambdaNonneg, hLambdaSmall, hSeed⟩ :=
    exists_phaseCochromaticFixedOffset_real_seed
  refine erdos625Statement_of_uniform_seed_and_root
    phaseChromaticLowerIndex phaseCochromaticFixedOffsetIndex
    Lambda fixedOffsetRoundingBudget
    hLambdaNonneg hLambdaSmall hSeed
    randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero
    fixedOffset_rounding_budget_spec.1 ?_
  obtain ⟨c, hc, hgap⟩ :=
    exists_eventually_concrete_phase_fixedOffset_root_gap
  refine ⟨c, ?_, hgap⟩
  simpa only [gapConstant, q] using hc

#print axioms erdos625

end


end Erdos625
