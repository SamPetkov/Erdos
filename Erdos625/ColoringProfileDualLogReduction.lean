import Erdos625.ColoringProfileDualAsymptotic
import Erdos625.ColoringProfilePhaseObjective
import Erdos625.ProfileAsymptoticTools

/-!
# Logarithmic reductions for the chromatic profile tail

These lemmas isolate the remaining chromatic first-moment estimate as a scalar
logarithmic asymptotic.  They are conditional reductions: the concrete
phase/dual-core limit is still an explicit hypothesis.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- It is enough for the logarithm of the complete dual envelope to tend to
`-∞`. -/
theorem randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_log_dual
    (parts : ℕ → ℕ) (t : ℕ → ℝ)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (hlog : Tendsto
      (fun n : ℕ ↦
        ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
          profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
          factorialLogErrorBound n)
      atTop atBot) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        (chromaticNumberAtMostEvent n (parts n)))
      atTop (𝓝 0) := by
  apply randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_dual
    parts t hpartsPos hpartsLe
  have hExp : Tendsto
      (fun n : ℕ ↦ Real.exp
        (((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
          profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
          factorialLogErrorBound n))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlog
  have hOfReal := ENNReal.tendsto_ofReal hExp
  simpa only [ENNReal.ofReal_zero] using hOfReal.congr' (by
    filter_upwards with n
    have hnPos : 0 < (n : ℝ) + 1 := by positivity
    rw [show
      ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
          profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
          factorialLogErrorBound n =
        ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
          (profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
            factorialLogErrorBound n) by ring,
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _),
      Real.exp_nat_mul, Real.exp_log hnPos])

/-- It suffices to bound the logarithmic envelope eventually by
`-log (n + 1)`. -/
theorem randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_log_dual_le
    (parts : ℕ → ℕ) (t : ℕ → ℝ)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (hlogLe : ∀ᶠ n : ℕ in atTop,
      ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
          profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
          factorialLogErrorBound n ≤
        -Real.log ((n : ℝ) + 1)) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        (chromaticNumberAtMostEvent n (parts n)))
      atTop (𝓝 0) := by
  apply randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_log_dual
    parts t hpartsPos hpartsLe
  apply tendsto_atBot_mono' atTop hlogLe
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hcast
  apply tendsto_neg_atBot_iff.mpr
  exact Real.tendsto_log_atTop.comp hadd

/-- If the logarithmic envelope normalized by `log n` tends to a negative
constant, then the chromatic tail tends to zero. -/
theorem randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_normalized_log_dual
    (parts : ℕ → ℕ) (t : ℕ → ℝ) (c : ℝ)
    (hc : c < 0)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (hnorm : Tendsto
      (fun n : ℕ ↦
        (((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
            profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
            factorialLogErrorBound n) /
          logOrder n)
      atTop (𝓝 c)) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        (chromaticNumberAtMostEvent n (parts n)))
      atTop (𝓝 0) := by
  let envelope : ℕ → ℝ := fun n ↦
    ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
      profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n) +
      factorialLogErrorBound n
  change Tendsto (fun n ↦ envelope n / logOrder n) atTop (𝓝 c) at hnorm
  apply randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_log_dual
    parts t hpartsPos hpartsLe
  change Tendsto envelope atTop atBot
  have hcHalf : c < c / 2 := by linarith
  have hratio : ∀ᶠ n in atTop, envelope n / logOrder n < c / 2 :=
    hnorm.eventually (Iio_mem_nhds hcHalf)
  have hlogPos : ∀ᶠ n in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_gt_atTop 0)
  apply tendsto_atBot_mono' atTop (by
    filter_upwards [hratio, hlogPos] with n hn hlog
    calc
      envelope n = (envelope n / logOrder n) * logOrder n := by
        field_simp
      _ ≤ (c / 2) * logOrder n :=
        mul_le_mul_of_nonneg_right (le_of_lt hn) (le_of_lt hlog))
  exact tendsto_logOrder_atTop.const_mul_atTop_of_neg (by linarith)

/-- The zero-safe Robbins error contributes one logarithmic unit at first
order. -/
theorem factorialLogErrorBound_div_logOrder_tendsto_one :
    Tendsto (fun n : ℕ ↦ factorialLogErrorBound n / logOrder n)
      atTop (𝓝 1) := by
  have hInv : Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹) atTop (𝓝 0) :=
    tendsto_logOrder_atTop.inv_tendsto_atTop
  have hCorrection : Tendsto
      (fun n : ℕ ↦
        Real.log ((n : ℝ) / ((n : ℝ) + 1)) * (logOrder n)⁻¹)
      atTop (𝓝 0) := by
    simpa using tendsto_log_nat_div_nat_add_one.mul hInv
  have hFour : Tendsto (fun n : ℕ ↦ (4 : ℝ) * (logOrder n)⁻¹)
      atTop (𝓝 0) := by
    simpa using hInv.const_mul (4 : ℝ)
  have hOne : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have h := (hOne.sub hCorrection).add hFour
  have h' : Tendsto
      (fun n : ℕ ↦
        1 - Real.log ((n : ℝ) / ((n : ℝ) + 1)) * (logOrder n)⁻¹ +
          4 * (logOrder n)⁻¹)
      atTop (𝓝 1) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by positivity
  have hnAdd : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [Real.log_div hnReal hnAdd]
  simp only [factorialLogErrorBound, logOrder, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv]
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnNeOne : (n : ℝ) ≠ 1 := by
    exact_mod_cast (show n ≠ 1 by omega)
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hnPos hnNeOne
  field_simp [hlog]
  ring

/-- If the normalized phase-and-dual core tends to a constant below `-1`,
the explicit factorial contribution leaves a negative complete envelope. -/
theorem randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_normalized_core
    (parts : ℕ → ℕ) (t : ℕ → ℝ) (c : ℝ)
    (hc : c < -1)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (hcore : Tendsto
      (fun n : ℕ ↦
        (((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
            profileDualUpper (phaseNat n + 1) (n : ℝ) (parts n : ℝ) (t n)) /
          logOrder n)
      atTop (𝓝 c)) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        (chromaticNumberAtMostEvent n (parts n)))
      atTop (𝓝 0) := by
  apply randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_normalized_log_dual
    parts t (c + 1) (by linarith) hpartsPos hpartsLe
  have hsum := hcore.add factorialLogErrorBound_div_logOrder_tendsto_one
  convert hsum using 1
  · funext n
    by_cases hlog : logOrder n = 0
    · simp [hlog]
    · field_simp [hlog]

/-- Phase-objective version of the normalized chromatic-tail reduction.

This is a purely mechanical adapter around
`randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_normalized_core`:
it rewrites the selected dual core as the named `profilePhaseObjective`.  The
substantive asymptotic estimate remains the explicit hypothesis `hphase`.

This finite-limit interface is not the manuscript's concrete threshold: there
the phase objective is expected to be of order `-(log n)^3`, so division by
`logOrder n` tends to `-∞`, not to a finite constant.  The concrete manuscript
route must therefore use the `atBot` envelope theorem above (or an equivalent
cubic-scale adapter). -/
theorem randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_phaseObjective
    (parts : ℕ → ℕ) (c : ℝ)
    (hc : c < -1)
    (hpartsPos : ∀ᶠ n in atTop, 0 < parts n)
    (hpartsLe : ∀ᶠ n in atTop, parts n ≤ n)
    (hphase : Tendsto
      (fun n : ℕ ↦
        profilePhaseObjective n (parts n : ℝ) / logOrder n)
      atTop (𝓝 c)) :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        {G : LabeledGraph n | chromaticNumberNat G ≤ parts n})
      atTop (𝓝 0) := by
  apply
    randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_normalized_core
      parts
      (fun n : ℕ ↦
        profileDualTilt (phaseNat n + 1) ((n : ℝ) / (parts n : ℝ)))
      c hc hpartsPos hpartsLe
  refine hphase.congr' ?_
  filter_upwards [hpartsPos] with n hn
  have hparts_ne : (parts n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  rw [profilePhaseObjective_eq_selected_core n hparts_ne]

#print axioms randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_log_dual
#print axioms randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_log_dual_le
#print axioms randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_normalized_log_dual
#print axioms factorialLogErrorBound_div_logOrder_tendsto_one
#print axioms randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_normalized_core
#print axioms randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_phaseObjective

end

end Erdos625
