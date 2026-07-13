import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian

/-!
# Elementary probability tools for Erdős Problem 625

This module gives kernel-checked versions of the elementary probability
inequalities invoked in Section 1 of the manuscript.  It uses `Measure.real`
for real-valued probabilities, Bochner integrals for real expectations, and
Lebesgue integrals for the extended-nonnegative Paley--Zygmund statement.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos625

section Markov

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Markov's inequality in the real-valued form used in the manuscript. -/
theorem markov_measureReal_le {X : Omega → ℝ}
    (hX_nonneg : 0 ≤ᵐ[mu] X) (hX_int : Integrable X mu)
    {a : ℝ} (ha : 0 < a) :
    mu.real {ω | a ≤ X ω} ≤ (∫ ω, X ω ∂mu) / a := by
  rw [le_div_iff₀ ha]
  simpa [mul_comm] using
    (mul_meas_ge_le_integral_of_nonneg hX_nonneg hX_int a)

end Markov

section PaleyZygmund

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The Cauchy--Schwarz estimate underlying the zero-threshold
Paley--Zygmund inequality. -/
theorem lintegral_sq_le_measure_support_mul_lintegral_sq
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, Z ω ∂mu) ^ 2 ≤
      mu (Function.support Z) * (∫⁻ ω, (Z ω) ^ 2 ∂mu) := by
  let I : Omega → ℝ≥0∞ := (Function.support Z).indicator (fun _ ↦ 1)
  have hI : Measurable I :=
    measurable_const.indicator (measurableSet_support hZ)
  have hHolder :
      (∫⁻ ω, (I * Z) ω ∂mu) ≤
        (∫⁻ ω, I ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, Z ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    apply ENNReal.lintegral_mul_le_Lp_mul_Lq mu
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      hI.aemeasurable hZ.aemeasurable
  have hIZ : I * Z = Z := by
    funext ω
    by_cases hω : Z ω = 0 <;> simp [I, Function.support, hω]
  have hI_sq : (fun ω ↦ I ω ^ (2 : ℝ)) = I := by
    funext ω
    by_cases hω : Z ω = 0 <;> simp [I, Function.support, hω]
  have hI_int : (∫⁻ ω, I ω ∂mu) = mu (Function.support Z) := by
    simp [I, measurableSet_support hZ]
  have hHolder' :
      (∫⁻ ω, Z ω ∂mu) ≤
        (mu (Function.support Z)) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, Z ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    rw [hIZ, hI_sq, hI_int] at hHolder
    exact hHolder
  calc
    (∫⁻ ω, Z ω ∂mu) ^ 2 ≤
        ((mu (Function.support Z)) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, Z ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ))) ^ 2 :=
      ENNReal.pow_le_pow_left hHolder'
    _ = mu (Function.support Z) * (∫⁻ ω, (Z ω) ^ 2 ∂mu) := by
      rw [mul_pow]
      simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

/-- Zero-threshold Paley--Zygmund inequality for a measurable nonnegative
random variable.  The extended-real formulation handles zero or infinite
second moment without adding side conditions. -/
theorem paleyZygmund_zero_lintegral {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, Z ω ∂mu) ^ 2 / (∫⁻ ω, (Z ω) ^ 2 ∂mu) ≤
      mu (Function.support Z) := by
  let first := ∫⁻ ω, Z ω ∂mu
  let second := ∫⁻ ω, (Z ω) ^ 2 ∂mu
  have hCS : first ^ 2 ≤ mu (Function.support Z) * second := by
    simpa [first, second] using
      (lintegral_sq_le_measure_support_mul_lintegral_sq (mu := mu) hZ)
  by_cases hsecond_zero : second = 0
  · have hfirst_sq : first ^ 2 = 0 := by
      apply le_antisymm
      · simpa [hsecond_zero] using hCS
      · exact bot_le
    simp [first, second, hsecond_zero, hfirst_sq]
  by_cases hsecond_top : second = ∞
  · simp [second, hsecond_top]
  · apply (ENNReal.div_le_iff_le_mul (Or.inl hsecond_zero) (Or.inl hsecond_top)).2
    simpa [mul_comm] using hCS

/-- Event-notation form of `paleyZygmund_zero_lintegral`, matching (1.5). -/
theorem paleyZygmund_zero {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, Z ω ∂mu) ^ 2 / (∫⁻ ω, (Z ω) ^ 2 ∂mu) ≤
      mu {ω | 0 < Z ω} := by
  simpa [Function.support, pos_iff_ne_zero] using
    (paleyZygmund_zero_lintegral (mu := mu) hZ)

end PaleyZygmund

section SubGaussianTails

open ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Two-sided tail bound supplied by the sub-Gaussian analytic core of
McDiarmid's inequality.  For a function of `r` independent blocks with
coordinate oscillations at most one, the missing independent-block bridge
would instantiate `c` with `r / 4`. -/
theorem subgaussian_two_sided {X : Omega → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c mu) {t : ℝ} (ht : 0 ≤ t) :
    mu.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * c)) := by
  have hevent : {ω | t ≤ |X ω|} =
      {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    ext ω
    simp [le_abs]
  rw [hevent]
  calc
    mu.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) ≤
        mu.real {ω | t ≤ X ω} + mu.real {ω | t ≤ -X ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * c)) + Real.exp (-t ^ 2 / (2 * c)) := by
      gcongr
      · exact hX.measure_ge_le ht
      · simpa using hX.neg.measure_ge_le ht
    _ = 2 * Real.exp (-t ^ 2 / (2 * c)) := by ring

/-- The exact numerical McDiarmid tail once the centered variable has been
shown to be sub-Gaussian with variance proxy `r / 4`.  Establishing that proxy
from independent blocks and coordinate oscillations is a separate bridge.
The positive-`r` hypothesis avoids Lean's totalized division-by-zero spelling. -/
theorem mcdiarmid_two_sided_of_subgaussian {X : Omega → ℝ} (r : ℕ)
    (hr : 0 < r) (hX : HasSubgaussianMGF X ((r : ℝ≥0) / 4) mu)
    {t : ℝ} (ht : 0 ≤ t) :
    mu.real {ω | t ≤ |X ω|} ≤
      2 * Real.exp (-2 * t ^ 2 / (r : ℝ)) := by
  calc
    mu.real {ω | t ≤ |X ω|} ≤
        2 * Real.exp (-t ^ 2 / (2 * (((r : ℝ≥0) / 4 : ℝ≥0) : ℝ))) :=
      subgaussian_two_sided hX ht
    _ = 2 * Real.exp (-2 * t ^ 2 / (r : ℝ)) := by
      have hexponent :
          -t ^ 2 / (2 * (((r : ℝ≥0) / 4 : ℝ≥0) : ℝ)) =
            -2 * t ^ 2 / (r : ℝ) := by
        push_cast
        field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hr)]
        ring
      rw [hexponent]

end SubGaussianTails

section BinomialTail

open ProbabilityTheory

/-- Moment-generating function of the real-valued binomial distribution.
Mathlib v4.31 defines this distribution but does not yet supply this finite
identity. -/
theorem mgf_id_mapCastBinomial (m : ℕ) (p : unitInterval) (t : ℝ) :
    mgf id Bin(ℝ, m, p) t = (p * Real.exp t + (1 - p)) ^ m := by
  rw [mgf, integral_map_cast_binomial, ← Nat.range_succ_eq_Iic]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hexp : Real.exp (t * (k : ℝ)) = Real.exp t ^ k := by
    rw [mul_comm, Real.exp_nat_mul]
  simp only [id_eq, smul_eq_mul]
  rw [hexp]
  ring

/-- The exponential-Markov calculation for the lower quarter-tail of
`Bin(m, 1/2)`, before the final numerical simplification in (1.6). -/
theorem binomialHalf_lowerQuarter_le_chernoff (m : ℕ) :
    Bin(ℝ, m, (⟨1 / 2, by norm_num⟩ : unitInterval)).real
        {x | x ≤ (m : ℝ) / 4} ≤
      (Real.exp (Real.log 3 / 4) * (2 / 3 : ℝ)) ^ m := by
  have ht : -(Real.log 3) ≤ 0 :=
    neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  have hint : Integrable
      (fun x : ℝ ↦ Real.exp (-(Real.log 3) * x))
      Bin(ℝ, m, (⟨1 / 2, by norm_num⟩ : unitInterval)) :=
    integrable_map_cast_binomial _
  have hchernoff := measure_le_le_exp_mul_mgf
    (X := id) (μ := Bin(ℝ, m, (⟨1 / 2, by norm_num⟩ : unitInterval)))
    ((m : ℝ) / 4) ht hint
  calc
    Bin(ℝ, m, (⟨1 / 2, by norm_num⟩ : unitInterval)).real
        {x | x ≤ (m : ℝ) / 4} ≤
      Real.exp (-(-(Real.log 3)) * ((m : ℝ) / 4)) *
        mgf id Bin(ℝ, m, (⟨1 / 2, by norm_num⟩ : unitInterval)) (-(Real.log 3)) := by
          simpa only [id_eq] using hchernoff
    _ = (Real.exp (Real.log 3 / 4) * (2 / 3 : ℝ)) ^ m := by
      rw [mgf_id_mapCastBinomial]
      have hexp_log : Real.exp (-(Real.log 3)) = (1 / 3 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        simp [div_eq_mul_inv]
      rw [hexp_log]
      norm_num [div_eq_mul_inv]
      have hexp_m :
          Real.exp (Real.log 3 * ((m : ℝ) * (1 / 4))) =
            Real.exp (Real.log 3 * (1 / 4)) ^ m := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [hexp_m, mul_pow]

/-- The numerical one-step estimate used to simplify the Chernoff bound. -/
theorem chernoffQuarter_base_le :
    Real.exp (Real.log 3 / 4) * (2 / 3 : ℝ) ≤ Real.exp (-1 / 16) := by
  have hlog : Real.log 2 - (3 / 4 : ℝ) * Real.log 3 ≤ -1 / 16 := by
    have htwo := Real.log_two_lt_d9
    have hthree := Real.log_three_gt_d9
    linarith
  have hratio : (2 / 3 : ℝ) = Real.exp (Real.log 2 - Real.log 3) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  rw [hratio, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The binomial lower-tail estimate (1.6), stated directly for mathlib's
real-valued `Bin(m, 1/2)` probability measure. -/
theorem binomialHalf_lowerQuarter_le_exp (m : ℕ) :
    Bin(ℝ, m, (⟨1 / 2, by norm_num⟩ : unitInterval)).real
        {x | x ≤ (m : ℝ) / 4} ≤
      Real.exp (-(m : ℝ) / 16) := by
  calc
    Bin(ℝ, m, (⟨1 / 2, by norm_num⟩ : unitInterval)).real
        {x | x ≤ (m : ℝ) / 4} ≤
      (Real.exp (Real.log 3 / 4) * (2 / 3 : ℝ)) ^ m :=
        binomialHalf_lowerQuarter_le_chernoff m
    _ ≤ (Real.exp (-1 / 16)) ^ m :=
      pow_le_pow_left₀ (by positivity) chernoffQuarter_base_le m
    _ = Real.exp (-(m : ℝ) / 16) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end BinomialTail

end Erdos625
