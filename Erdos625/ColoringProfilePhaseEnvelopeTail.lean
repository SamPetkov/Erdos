import Erdos625.ColoringProfileDualLogReduction

/-!
# The phase-envelope chromatic tail adapter

This file packages the exact conditional implication needed by the chromatic
lower-tail argument.  Its hypothesis is the full selected phase envelope,
including the explicit factorial error.  In particular, no identification of
an externally supplied cap with `phaseNat n + 1` is assumed: that cap is built
directly into `profilePhaseObjective`.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- If the selected phase envelope (including the factorial correction) tends
to `-∞`, then the random-graph probability of admitting a coloring with the
given number of parts tends to zero.

The eventual hypotheses are exactly those needed by the finite profile
first-moment bound.  The selected dual tilt is inserted internally using
`profilePhaseObjective_eq_selected_core`; hence callers do not need to supply
or equate a separate phase cap. -/
theorem chromaticAtMost_tendsto_zero_of_phaseEnvelope_atBot
    (parts : ℕ → ℕ)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (henvelope : Tendsto
      (fun n : ℕ ↦
        profilePhaseObjective n (parts n : ℝ) + factorialLogErrorBound n)
      atTop atBot) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        (chromaticNumberAtMostEvent n (parts n)))
      atTop (𝓝 0) := by
  apply randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_log_dual
    parts
    (fun n : ℕ ↦
      profileDualTilt (phaseNat n + 1) ((n : ℝ) / (parts n : ℝ)))
    hpartsPos hpartsLe
  refine henvelope.congr' ?_
  filter_upwards [hpartsPos] with n hn
  have hparts_ne : (parts n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  rw [profilePhaseObjective_eq_selected_core n hparts_ne]

#print axioms chromaticAtMost_tendsto_zero_of_phaseEnvelope_atBot

end

end Erdos625
