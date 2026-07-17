import Erdos625.Section10UniformAmplificationSpecialization
import Erdos625.Section11ChromaticTailAdapter
import Erdos625.Section11ThresholdFinalAssembly
import Mathlib.Tactic

/-!
# Sections X--XI D3: uniform seed/root final wrapper

The substantive seed, chromatic at-most tail, and root separation remain
explicit hypotheses.  This task only composes accepted amplification and
event-assembly theorems.
-/

namespace Erdos625

open Filter MeasureTheory Set Asymptotics
open scoped ENNReal Topology

noncomputable section

/-- A concrete nonnegative little-o cocolouring seed, a probability-zero
chromatic at-most tail, and the explicit root corridor imply the final target
through uniform amplification at the manuscript scales. -/
theorem erdos625Statement_of_uniform_seed_and_root
    (kChi kCo : Nat -> Nat) (Lambda rho : Nat -> Real)
    (hLambdaNonneg : ∀ᶠ n in atTop, 0 ≤ Lambda n)
    (hLambdaSmall : Lambda =o[atTop] amplificationBase)
    (hSeed : ∀ᶠ n in atTop,
      Real.exp (-Lambda n) ≤
        (randomGraphMeasure n).real {G | CoColorable G (kCo n)})
    (hChromaticAtMost : Tendsto
      (fun n => randomGraphMeasure n
        {G : LabeledGraph n | chromaticNumberNat G ≤ kChi n})
      atTop (nhds 0))
    (hrho : Tendsto rho atTop (nhds 0))
    (hroot : ∀ᶠ n in atTop,
      (((Real.log 2) ^ 2 / 16 * Real.log (200 / 153 : Real)) - rho n) *
          baseScale n ≤
        (kChi n : Real) - (kCo n : Real)) :
    Erdos625Statement := by
  obtain ⟨C, epsilon, hC, hEpsilon, hEpsilonNonneg, hUniform⟩ :=
    exists_uniform_cochromatic_amplification_at_manuscript_scales
  have hAmplification :=
    hUniform kCo Lambda hLambdaNonneg hLambdaSmall hSeed
  let a : ℕ → ℝ := fun n =>
    uniformAmplificationError C n (Lambda n) (amplificationRadius n)
  have haGap : a =o[atTop] gapBase := by
    simpa only [a] using hAmplification.1
  have haBase : a =o[atTop] baseScale := by
    change a =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ 3)
    change a =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ 3) at haGap
    exact haGap
  have hGapThreshold : ∀ᶠ n in atTop,
      gapScale n ≤
        ((kChi n + 1 : ℕ) : ℝ) - ((kCo n : ℝ) + a n) := by
    simpa only [gapScale, gapConstant, baseScale, mul_div_assoc] using
      eventually_explicit_gap_threshold kChi kCo a rho hrho haBase hroot
  have hCochromaticTail : Tendsto
      (fun n => randomGraphMeasure n
        (cochromaticUpperEvent n (kCo n) (a n)))
      atTop (nhds 1) := by
    simpa only [a] using hAmplification.2
  have hChromaticTail :=
    chromaticLowerEvent_probability_tendsto_one_of_atMost_tendsto_zero
      kChi hChromaticAtMost
  exact erdos625Statement_of_chromatic_cochromatic_thresholds
    kChi kCo a hChromaticTail hCochromaticTail hGapThreshold

#print axioms erdos625Statement_of_uniform_seed_and_root

end


end Erdos625
