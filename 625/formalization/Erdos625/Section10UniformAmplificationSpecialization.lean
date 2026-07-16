import Erdos625.Section10UniformAmplification
import Erdos625.Section10AmplificationScales

/-!
# Section X: specialization of uniform amplification to the manuscript scales

This module specializes the quantifier-correct uniform amplification theorem
to the deterministic radius

`r_n = sqrt (n / (log n)^4)`.

The seed exponent remains an arbitrary nonnegative sequence satisfying the
explicit little-`o` hypothesis from the manuscript.  In particular, no
Section IX rare-event estimate is assumed here.
-/

namespace Erdos625

open Filter MeasureTheory Set Asymptotics
open scoped ENNReal Topology

noncomputable section

/-- The error displayed by the uniform event theorem is exactly the
deterministic amplification error after inserting the manuscript radius. -/
theorem uniformAmplificationError_amplificationRadius_eq
    (C : ℝ) (Lambda : ℕ → ℝ) (n : ℕ) :
    uniformAmplificationError C n (Lambda n) (amplificationRadius n) =
      amplificationError C Lambda n := by
  rw [uniformAmplificationError, amplificationError]
  ring

/-- The exponential failure term attached to the manuscript radius vanishes
along the full natural-number sequence. -/
theorem exp_neg_amplificationRadius_tendsto_zero :
    Tendsto (fun n : ℕ => Real.exp (-amplificationRadius n))
      atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp amplificationRadius_tendsto_atTop)

/-- A vanishing real complement probability implies that the corresponding
events have probability tending to one.  The probability spaces may vary
with the index. -/
theorem tendsto_measure_one_of_compl_real_tendsto_zero
    {Omega : ℕ → Type*}
    [∀ n, MeasurableSpace (Omega n)]
    (mu : ∀ n, Measure (Omega n))
    [∀ n, IsProbabilityMeasure (mu n)]
    (A : ∀ n, Set (Omega n))
    (hMeas : ∀ n, MeasurableSet (A n))
    (hFailure :
      Tendsto (fun n => (mu n).real (A n)ᶜ) atTop (nhds 0)) :
    Tendsto (fun n => mu n (A n)) atTop (nhds 1) := by
  have hSuccessIdentity : ∀ n,
      (mu n).real (A n) = 1 - (mu n).real (A n)ᶜ := by
    intro n
    have hCompl := measureReal_compl (μ := mu n) (hMeas n)
    rw [probReal_univ] at hCompl
    linarith
  have hSuccessReal :
      Tendsto (fun n => (mu n).real (A n)) atTop (nhds (1 : ℝ)) := by
    have hSub :
        Tendsto (fun n => (1 : ℝ) - (mu n).real (A n)ᶜ)
          atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hFailure
    convert hSub using 1
    · funext n
      exact hSuccessIdentity n
    · norm_num
  exact
    (ENNReal.tendsto_toReal_iff
      (fun n => measure_ne_top (mu n) (A n))
      ENNReal.one_ne_top).mp (by
        simpa only [Measure.real, ENNReal.toReal_one] using hSuccessReal)

/-- Quantifier-faithful specialization of uniform amplification to the
manuscript radius.  One absolute constant and one parameter-independent
vanishing error sequence are chosen before the seed threshold and exponent
sequences.  Under only the displayed seed and little-`o` hypotheses, the
resulting deterministic loss is negligible on the target scale and the
cochromatic upper event has probability tending to one. -/
theorem exists_uniform_cochromatic_amplification_at_manuscript_scales :
    ∃ C : ℝ, ∃ epsilon : ℕ → ℝ,
      1 ≤ C ∧
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ n : ℕ, 0 ≤ epsilon n) ∧
      ∀ (k : ℕ → ℕ) (Lambda : ℕ → ℝ),
        (∀ᶠ n in atTop, 0 ≤ Lambda n) →
        Lambda =o[atTop] amplificationBase →
        (∀ᶠ n in atTop,
          Real.exp (-Lambda n) ≤
            (randomGraphMeasure n).real
              {G | CoColorable G (k n)}) →
        (fun n =>
          uniformAmplificationError C n
            (Lambda n) (amplificationRadius n)) =o[atTop] gapBase ∧
        Tendsto
          (fun n =>
            randomGraphMeasure n
              (cochromaticUpperEvent n (k n)
                (uniformAmplificationError C n
                  (Lambda n) (amplificationRadius n))))
          atTop (nhds 1) := by
  obtain ⟨C, epsilon, hC, hEpsilon, hEpsilonNonneg, hUniform⟩ :=
    exists_uniform_cochromatic_amplification
  refine ⟨C, epsilon, hC, hEpsilon, hEpsilonNonneg, ?_⟩
  intro k Lambda hLambdaNonneg hLambdaSmall hSeed
  have hError :
      (fun n =>
        uniformAmplificationError C n
          (Lambda n) (amplificationRadius n)) =o[atTop] gapBase := by
    simpa only [uniformAmplificationError_amplificationRadius_eq] using
      amplificationError_isLittleO_gapBase
        C Lambda hLambdaNonneg hLambdaSmall
  have hRadiusPos :
      ∀ᶠ n : ℕ in atTop, 0 < amplificationRadius n :=
    amplificationRadius_tendsto_atTop.eventually_gt_atTop 0
  have hFailureUpper :
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real
            (cochromaticUpperEvent n (k n)
              (uniformAmplificationError C n
                (Lambda n) (amplificationRadius n)))ᶜ ≤
          Real.exp (-amplificationRadius n) + epsilon n :=
    hUniform k Lambda amplificationRadius
      hLambdaNonneg hRadiusPos hSeed
  have hUpperZero :
      Tendsto
        (fun n => Real.exp (-amplificationRadius n) + epsilon n)
        atTop (nhds 0) := by
    convert exp_neg_amplificationRadius_tendsto_zero.add hEpsilon using 1
    norm_num
  have hFailure :
      Tendsto
        (fun n =>
          (randomGraphMeasure n).real
            (cochromaticUpperEvent n (k n)
              (uniformAmplificationError C n
                (Lambda n) (amplificationRadius n)))ᶜ)
        atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpperZero
      (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      hFailureUpper
  refine ⟨hError, ?_⟩
  exact tendsto_measure_one_of_compl_real_tendsto_zero
    randomGraphMeasure
    (fun n =>
      cochromaticUpperEvent n (k n)
        (uniformAmplificationError C n
          (Lambda n) (amplificationRadius n)))
    (fun n => Set.toFinite
      (cochromaticUpperEvent n (k n)
        (uniformAmplificationError C n
          (Lambda n) (amplificationRadius n))) |>.measurableSet)
    hFailure

#print axioms uniformAmplificationError_amplificationRadius_eq
#print axioms exp_neg_amplificationRadius_tendsto_zero
#print axioms tendsto_measure_one_of_compl_real_tendsto_zero
#print axioms exists_uniform_cochromatic_amplification_at_manuscript_scales

end

end Erdos625
