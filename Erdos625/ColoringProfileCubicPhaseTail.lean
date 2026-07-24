import Erdos625.ColoringProfilePhaseEnvelopeTail

/-!
# Cubic-scale phase condition for the chromatic lower tail

This module gives a full-sequence reduction of the concrete chromatic at-most
probability to the phase estimate at its natural cubic logarithmic scale.  It
does not assert that estimate: the only substantive analytic input remains the
explicit limit of `profilePhaseObjective` below.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The factorial correction is negligible compared with the cubic logarithmic
scale. -/
theorem factorialLogErrorBound_div_logOrder_cubed_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ factorialLogErrorBound n / (logOrder n) ^ 3)
      atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹) atTop (𝓝 0) :=
    tendsto_logOrder_atTop.inv_tendsto_atTop
  have hProduct := factorialLogErrorBound_div_logOrder_tendsto_one.mul
    (hInv.pow 2)
  convert hProduct using 1
  · funext n
    by_cases hlog : logOrder n = 0
    · simp [hlog]
    · field_simp [hlog]
  · norm_num

/-- A negative cubic-scale limit for the selected phase objective implies the
full-sequence probability-zero chromatic at-most tail.  The natural threshold
is kept unchanged, so the complementary event remains the strict inequality
`kChi n < chromaticNumberNat G`.

This is a reduction, not an unconditional assertion of the analytic phase
limit. -/
theorem randomGraphMeasure_chromaticNumberAtMost_tendsto_zero_of_cubic_phase
    (kChi : ℕ → ℕ) (c : ℝ)
    (hc : c < 0)
    (hkChiPos : ∀ᶠ n in atTop, 0 < kChi n)
    (hkChiLe : ∀ᶠ n in atTop, kChi n ≤ n)
    (hphase : Tendsto
      (fun n : ℕ ↦
        profilePhaseObjective n (kChi n : ℝ) / (logOrder n) ^ 3)
      atTop (𝓝 c)) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        {G : LabeledGraph n | chromaticNumberNat G ≤ kChi n})
      atTop (𝓝 0) := by
  apply chromaticAtMost_tendsto_zero_of_phaseEnvelope_atBot
    kChi hkChiPos hkChiLe
  have hCorrection :=
    factorialLogErrorBound_div_logOrder_cubed_tendsto_zero
  have hNormalized := hphase.add hCorrection
  have hNormalized' : Tendsto
      (fun n : ℕ ↦
        (profilePhaseObjective n (kChi n : ℝ) + factorialLogErrorBound n) /
          (logOrder n) ^ 3)
      atTop (𝓝 c) := by
    convert hNormalized using 1
    · funext n
      by_cases hlog : logOrder n = 0
      · simp [hlog]
      · field_simp [hlog]
    · simp
  let envelope : ℕ → ℝ := fun n ↦
    profilePhaseObjective n (kChi n : ℝ) + factorialLogErrorBound n
  change Tendsto envelope atTop atBot
  change Tendsto (fun n ↦ envelope n / (logOrder n) ^ 3)
    atTop (𝓝 c) at hNormalized'
  have hcHalf : c < c / 2 := by linarith
  have hratio : ∀ᶠ n in atTop,
      envelope n / (logOrder n) ^ 3 < c / 2 :=
    hNormalized'.eventually (Iio_mem_nhds hcHalf)
  have hscale : Tendsto (fun n : ℕ ↦ (logOrder n) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      tendsto_logOrder_atTop
  have hscalePos : ∀ᶠ n in atTop, 0 < (logOrder n) ^ 3 :=
    hscale.eventually (eventually_gt_atTop 0)
  apply tendsto_atBot_mono' atTop (by
    filter_upwards [hratio, hscalePos] with n hn hpos
    calc
      envelope n = (envelope n / (logOrder n) ^ 3) * (logOrder n) ^ 3 := by
        exact (div_mul_cancel₀ _ hpos.ne').symm
      _ ≤ (c / 2) * (logOrder n) ^ 3 :=
        mul_le_mul_of_nonneg_right (le_of_lt hn) hpos.le)
  exact hscale.const_mul_atTop_of_neg (by linarith)

#print axioms factorialLogErrorBound_div_logOrder_cubed_tendsto_zero
#print axioms randomGraphMeasure_chromaticNumberAtMost_tendsto_zero_of_cubic_phase

end

end Erdos625
