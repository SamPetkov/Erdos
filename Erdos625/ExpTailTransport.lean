import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Generic exponential-tail transport

This module transports a real exponential tail through `ENNReal.ofReal`.
It intentionally contains no phase-specific asymptotic input.
-/

namespace Erdos625

open Filter

/-- If a real exponent tends to `-∞`, then its exponential tends to `0` after
embedding into `ENNReal`. -/
theorem tendsto_ennrealOfReal_exp_atTop_of_tendsto_atBot
    {f : Nat -> Real} (hf : Tendsto f atTop atBot) :
    Tendsto (fun n : Nat => ENNReal.ofReal (Real.exp (f n))) atTop (nhds 0) := by
  change Tendsto (ENNReal.ofReal ∘ Real.exp ∘ f) atTop (nhds 0)
  simpa only [ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp hf)

end Erdos625
