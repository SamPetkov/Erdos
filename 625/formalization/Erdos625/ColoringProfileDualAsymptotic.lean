import Erdos625.ColoringProfileDualProbability
import Erdos625.PhaseConsequences

/-!
# Asymptotic assembly interface for the chromatic lower location

The sharp shifted independent-set term in the finite dual probability bound
already tends to zero when the class-size cap is `phaseNat n + 1`.  This file
therefore isolates the exact remaining Section 4 obligation: prove that the
explicit dual first-moment term tends to zero for the selected part count and
dual parameter.  No root or optimizer is postulated.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- If the explicit dual first-moment term vanishes at the phase cap, then the
probability of the corresponding unrestricted chromatic upper event vanishes.
The positivity and `parts n ≤ n` requirements need hold only eventually. -/
theorem randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_dual
    (parts : ℕ → ℕ) (t : ℕ → ℝ)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (hdual : Tendsto
      (fun n : ℕ ↦
        ENNReal.ofReal (((n : ℝ) + 1) ^ (phaseNat n + 1)) *
          ENNReal.ofReal
            (Real.exp
              (profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
                factorialLogErrorBound n)))
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        (chromaticNumberAtMostEvent n (parts n)))
      atTop (𝓝 0) := by
  have hMoment : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (mu n (phaseNat n + 2)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal mu_phaseNat_add_two_tendsto_zero
  have hUpper : ∀ᶠ n : ℕ in atTop,
      randomGraphMeasure n (chromaticNumberAtMostEvent n (parts n)) ≤
        ENNReal.ofReal (((n : ℝ) + 1) ^ (phaseNat n + 1)) *
          ENNReal.ofReal
            (Real.exp
              (profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
                factorialLogErrorBound n)) +
          ENNReal.ofReal (mu n (phaseNat n + 2)) := by
    filter_upwards [hpartsPos, hpartsLe] with n hnPos hnLe
    simpa only [Nat.add_assoc, one_add_one_eq_two] using
      (randomGraphMeasure_chromaticNumberAtMost_le_profileDual_add_mu
        (n := n) (b := phaseNat n + 1) (parts := parts n)
        (Nat.succ_pos _) hnPos hnLe (t n))
  have hUpperTendsto : Tendsto
      (fun n : ℕ ↦
        ENNReal.ofReal (((n : ℝ) + 1) ^ (phaseNat n + 1)) *
          ENNReal.ofReal
            (Real.exp
              (profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
                factorialLogErrorBound n)) +
          ENNReal.ofReal (mu n (phaseNat n + 2)))
      atTop (𝓝 0) := by
    simpa using hdual.add hMoment
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpperTendsto
    (Filter.Eventually.of_forall fun _ ↦ bot_le) hUpper

end

end Erdos625
