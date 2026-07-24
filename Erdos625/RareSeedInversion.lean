import Erdos625.BlockBoundedDifferences

/-!
# Rare-seed inversion

This module formalizes the elementary analytic step behind the rare-seed
argument: if a bounded random variable reaches its upper endpoint with mass
at least `exp (-Lambda)`, while its upper tail about its expectation is
sub-Gaussian with variance proxy `v`, then its endpoint-to-mean gap is at
most `sqrt (2 * v * Lambda)`.

The proof is split into deterministic inversion, expectation comparison, and
event inclusion lemmas so that each bridge can be audited independently.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos625

section Deterministic

/-- Deterministic exponential inversion with the exact constant used by a
tail of the form `exp (-gap^2 / (2 * v))`. -/
theorem gap_le_sqrt_two_mul_of_exp_neg_le_exp_neg_sq_div
    {gap v Lambda : ℝ} (hv : 0 < v) (hLambda : 0 ≤ Lambda)
    (hExp : Real.exp (-Lambda) ≤ Real.exp (-gap ^ 2 / (2 * v))) :
    gap ≤ Real.sqrt (2 * v * Lambda) := by
  have hExponent : -Lambda ≤ -gap ^ 2 / (2 * v) :=
    Real.exp_le_exp.mp hExp
  have hDenominator : 0 < 2 * v := by positivity
  have hQuotient : gap ^ 2 / (2 * v) ≤ Lambda := by
    have hNegated := neg_le_neg hExponent
    simpa only [neg_div, neg_neg] using hNegated
  have hSquare : gap ^ 2 ≤ 2 * v * Lambda := by
    have h := (div_le_iff₀ hDenominator).mp hQuotient
    nlinarith
  have hProduct : 0 ≤ 2 * v * Lambda :=
    mul_nonneg (mul_nonneg (by norm_num) hv.le) hLambda
  have hSqrtSquare : (Real.sqrt (2 * v * Lambda)) ^ 2 = 2 * v * Lambda :=
    Real.sq_sqrt hProduct
  have hSqrtNonnegative : 0 ≤ Real.sqrt (2 * v * Lambda) := Real.sqrt_nonneg _
  nlinarith

end Deterministic

section Probability

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- An integrable real random variable bounded above almost surely has
expectation at most that bound under a probability measure. -/
theorem integral_le_const_of_ae_le [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {b : ℝ} (hX : Integrable X mu)
    (hBound : ∀ᵐ omega ∂mu, X omega ≤ b) :
    (∫ omega, X omega ∂mu) ≤ b := by
  calc
    (∫ omega, X omega ∂mu) ≤ ∫ _ : Omega, b ∂mu :=
      integral_mono_ae hX (integrable_const b) hBound
    _ = b := by simp

omit [MeasurableSpace Omega] in
/-- The endpoint level set is contained in the centered upper-tail event at
the endpoint-to-center gap. -/
theorem levelSet_subset_centeredUpperTail {X : Omega → ℝ} {b center : ℝ} :
    {omega | X omega = b} ⊆ {omega | b - center ≤ X omega - center} := by
  intro omega homega
  change X omega = b at homega
  change b - center ≤ X omega - center
  rw [homega]

/-- Measure form of the endpoint-to-centered-tail event inclusion. -/
theorem measureReal_levelSet_le_centeredUpperTail [IsFiniteMeasure mu]
    {X : Omega → ℝ} {b center : ℝ} :
    mu.real {omega | X omega = b} ≤
      mu.real {omega | b - center ≤ X omega - center} :=
  measureReal_mono levelSet_subset_centeredUpperTail

/-- Rare-seed inversion for a measurable, integrable, real random variable.

The upper-tail hypothesis is deliberately stated only for nonnegative
thresholds.  If the endpoint event has probability at least `exp (-Lambda)`
and the tail has variance proxy `v > 0`, then the endpoint-to-expectation gap
is at most `sqrt (2 * v * Lambda)`.
-/
theorem rareSeed_gap_le [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {b v Lambda : ℝ}
    (hXMeasurable : Measurable X) (hXIntegrable : Integrable X mu)
    (hBound : ∀ᵐ omega ∂mu, X omega ≤ b) (hv : 0 < v) (hLambda : 0 ≤ Lambda)
    (hSeed : Real.exp (-Lambda) ≤ mu.real {omega | X omega = b})
    (hTail : ∀ t : ℝ, 0 ≤ t →
      mu.real {omega | t ≤ X omega - ∫ eta, X eta ∂mu} ≤
        Real.exp (-t ^ 2 / (2 * v))) :
    b - ∫ omega, X omega ∂mu ≤ Real.sqrt (2 * v * Lambda) := by
  have hExpectation : (∫ omega, X omega ∂mu) ≤ b :=
    integral_le_const_of_ae_le hXIntegrable hBound
  have hGap : 0 ≤ b - ∫ omega, X omega ∂mu := sub_nonneg.mpr hExpectation
  have _hSeedMeasurable : MeasurableSet {omega | X omega = b} :=
    measurableSet_eq_fun hXMeasurable measurable_const
  have hEvent :
      mu.real {omega | X omega = b} ≤
        mu.real {omega | b - ∫ eta, X eta ∂mu ≤
          X omega - ∫ eta, X eta ∂mu} := by
    exact measureReal_levelSet_le_centeredUpperTail
  have hExp : Real.exp (-Lambda) ≤
      Real.exp (-(b - ∫ omega, X omega ∂mu) ^ 2 / (2 * v)) := by
    calc
      Real.exp (-Lambda) ≤ mu.real {omega | X omega = b} := hSeed
      _ ≤ mu.real {omega | b - ∫ eta, X eta ∂mu ≤
          X omega - ∫ eta, X eta ∂mu} := hEvent
      _ ≤ Real.exp (-(b - ∫ omega, X omega ∂mu) ^ 2 / (2 * v)) :=
        hTail _ hGap
  exact gap_le_sqrt_two_mul_of_exp_neg_le_exp_neg_sq_div
    hv hLambda hExp

/-- Direct specialization of `rareSeed_gap_le` to mathlib's
`HasSubgaussianMGF` interface for the centered random variable. -/
theorem rareSeed_gap_le_of_hasSubgaussianMGF [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {b Lambda : ℝ} {v : ℝ≥0}
    (hXMeasurable : Measurable X) (hXIntegrable : Integrable X mu)
    (hBound : ∀ᵐ omega ∂mu, X omega ≤ b) (hv : 0 < v) (hLambda : 0 ≤ Lambda)
    (hSeed : Real.exp (-Lambda) ≤ mu.real {omega | X omega = b})
    (hSubgaussian : HasSubgaussianMGF
      (fun omega ↦ X omega - ∫ eta, X eta ∂mu) v mu) :
    b - ∫ omega, X omega ∂mu ≤ Real.sqrt (2 * (v : ℝ) * Lambda) := by
  apply rareSeed_gap_le hXMeasurable hXIntegrable hBound
    (show 0 < (v : ℝ) by exact_mod_cast hv) hLambda hSeed
  intro t ht
  exact hSubgaussian.measure_ge_le ht

end Probability

end Erdos625
