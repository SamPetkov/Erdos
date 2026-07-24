import Erdos625.ColoringProfileDualBound
import Erdos625.ColoringProfileProbability

/-!
# Finite chromatic probability bound through the profile dual

This module composes the concrete Gibbs-dual first-moment estimate with the
already proved chromatic-event containment and the sharp shifted independent-
set first moment.  It leaves only the choice and asymptotic analysis of the
dual parameter.
-/

namespace Erdos625

noncomputable section

/-- For every positive support size and positive admissible part count, every
dual parameter gives a fully explicit finite upper bound for the unrestricted
chromatic event.  The shifted term is `mu n (b+1)`, exactly the form needed by
the phase consequence (2.9). -/
theorem randomGraphMeasure_chromaticNumberAtMost_le_profileDual_add_mu
    {n b parts : ℕ} (hb : 0 < b) (hpartsPos : 0 < parts)
    (hpartsLe : parts ≤ n) (t : ℝ) :
    randomGraphMeasure n (chromaticNumberAtMostEvent n parts) ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ b) *
        ENNReal.ofReal
          (Real.exp
            (profileDualUpper b (n : ℝ) (parts : ℝ) t +
              factorialLogErrorBound n)) +
        ENNReal.ofReal (mu n (b + 1)) := by
  calc
    randomGraphMeasure n (chromaticNumberAtMostEvent n parts) ≤
        boundedProfileColoringExpectation n b parts +
          randomGraphMeasure n (independenceNumberExceedsEvent n b) :=
      randomGraphMeasure_chromaticNumberAtMost_le_expectation_add_independence
        hpartsLe
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ b) *
          ENNReal.ofReal
            (Real.exp
              (profileDualUpper b (n : ℝ) (parts : ℝ) t +
                factorialLogErrorBound n)) +
          ENNReal.ofReal (mu n (b + 1)) := by
      exact add_le_add
        (boundedProfileColoringExpectation_le_profileDualUpper
          hb hpartsPos t)
        (randomGraphMeasure_independenceNumberExceeds_le_mu_succ n b)

end

end Erdos625
