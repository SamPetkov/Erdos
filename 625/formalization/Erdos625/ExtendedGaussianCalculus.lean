import Erdos625.ExtendedGaussianProfile
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Calculus of the extended tilted-Gaussian profile

This module differentiates the limiting profile on the countable support
`{-1, 0, 1, ...}`.  The termwise differentiations are justified locally on a
bounded open interval around the evaluation point, with the first two
tilted-Gaussian moments as summable derivative majorants.
-/

open Filter
open scoped Topology

namespace Erdos625

noncomputable section

private theorem hasDerivAt_extendedGaussianNaturalTerm
    (a lambda : ℝ) (d : ℕ) :
    HasDerivAt (fun t : ℝ ↦ extendedGaussianNaturalTerm a t d)
      ((d : ℝ) * extendedGaussianNaturalTerm a lambda d) lambda := by
  change HasDerivAt
    (fun t : ℝ ↦ Real.exp (t * (d : ℝ) - a / 2 * (d : ℝ) ^ 2))
    ((d : ℝ) * Real.exp
      (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) lambda
  have hraw :
      HasDerivAt
        (fun t : ℝ ↦ Real.exp
          (t * (d : ℝ) - a / 2 * (d : ℝ) ^ 2))
        (Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2) *
          (d : ℝ)) lambda := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id lambda).mul_const (d : ℝ)).sub_const
        (a / 2 * (d : ℝ) ^ 2)).exp
  exact hraw.congr_deriv (mul_comm _ _)

private theorem hasDerivAt_extendedGaussianExceptionalAtom
    (a lambda : ℝ) :
    HasDerivAt (extendedGaussianExceptionalAtom a)
      (-extendedGaussianExceptionalAtom a lambda) lambda := by
  change HasDerivAt (fun t : ℝ ↦ Real.exp (-t - a / 2))
    (-Real.exp (-lambda - a / 2)) lambda
  simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using
    (((hasDerivAt_id lambda).neg.sub_const (a / 2)).exp)

private theorem hasDerivAt_tsum_extendedGaussianNaturalTerm
    (a lambda : ℝ) (ha : 0 < a) :
    HasDerivAt
      (fun t : ℝ ↦ ∑' d : ℕ, extendedGaussianNaturalTerm a t d)
      (∑' d : ℕ, (d : ℝ) * extendedGaussianNaturalTerm a lambda d)
      lambda := by
  let B : ℝ := |lambda| + 1
  let u : ℕ → ℝ := fun d ↦
    (d : ℝ) * extendedGaussianNaturalTerm a B d
  have hu : Summable u := by
    simpa [u, B, extendedGaussianNaturalTerm] using
      summable_natPow_mul_tiltedGaussian (lambda := B) ha 1
  have hderiv : ∀ d : ℕ, ∀ y : ℝ,
      y ∈ Set.Ioo (lambda - 1) (lambda + 1) →
      HasDerivAt (fun t : ℝ ↦ extendedGaussianNaturalTerm a t d)
        ((d : ℝ) * extendedGaussianNaturalTerm a y d) y := by
    intro d y _
    exact hasDerivAt_extendedGaussianNaturalTerm a y d
  have hbound : ∀ d : ℕ, ∀ y : ℝ,
      y ∈ Set.Ioo (lambda - 1) (lambda + 1) →
      ‖(d : ℝ) * extendedGaussianNaturalTerm a y d‖ ≤ u d := by
    intro d y hy
    have hyB : y ≤ B := by
      dsimp [B]
      exact le_trans hy.2.le (by linarith [le_abs_self lambda])
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hexp :
        extendedGaussianNaturalTerm a y d ≤
          extendedGaussianNaturalTerm a B d := by
      apply Real.exp_le_exp.mpr
      change y * (d : ℝ) - a / 2 * (d : ℝ) ^ 2 ≤
        B * (d : ℝ) - a / 2 * (d : ℝ) ^ 2
      nlinarith
    rw [Real.norm_of_nonneg (mul_nonneg hd0
      (extendedGaussianNaturalTerm_pos a y d).le)]
    exact mul_le_mul_of_nonneg_left hexp hd0
  apply hasDerivAt_tsum_of_isPreconnected
    (u := u) (t := Set.Ioo (lambda - 1) (lambda + 1))
    (y₀ := lambda) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound
    (by constructor <;> linarith)
    (summable_extendedGaussianNaturalTerm ha)
    (by constructor <;> linarith)

private theorem hasDerivAt_tsum_extendedGaussianFirstMoment
    (a lambda : ℝ) (ha : 0 < a) :
    HasDerivAt
      (fun t : ℝ ↦
        ∑' d : ℕ, (d : ℝ) * extendedGaussianNaturalTerm a t d)
      (∑' d : ℕ, ((d : ℝ) ^ 2) *
        extendedGaussianNaturalTerm a lambda d)
      lambda := by
  let B : ℝ := |lambda| + 1
  let u : ℕ → ℝ := fun d ↦
    ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a B d
  have hu : Summable u := by
    simpa [u, B, extendedGaussianNaturalTerm] using
      summable_natPow_mul_tiltedGaussian (lambda := B) ha 2
  have hderiv : ∀ d : ℕ, ∀ y : ℝ,
      y ∈ Set.Ioo (lambda - 1) (lambda + 1) →
      HasDerivAt
        (fun t : ℝ ↦ (d : ℝ) * extendedGaussianNaturalTerm a t d)
        (((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a y d) y := by
    intro d y _
    simpa [pow_two, mul_assoc] using
      (hasDerivAt_extendedGaussianNaturalTerm a y d).const_mul (d : ℝ)
  have hbound : ∀ d : ℕ, ∀ y : ℝ,
      y ∈ Set.Ioo (lambda - 1) (lambda + 1) →
      ‖((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a y d‖ ≤ u d := by
    intro d y hy
    have hyB : y ≤ B := by
      dsimp [B]
      exact le_trans hy.2.le (by linarith [le_abs_self lambda])
    have hd20 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have hexp :
        extendedGaussianNaturalTerm a y d ≤
          extendedGaussianNaturalTerm a B d := by
      apply Real.exp_le_exp.mpr
      change y * (d : ℝ) - a / 2 * (d : ℝ) ^ 2 ≤
        B * (d : ℝ) - a / 2 * (d : ℝ) ^ 2
      nlinarith [show (0 : ℝ) ≤ d by positivity]
    rw [Real.norm_of_nonneg (mul_nonneg hd20
      (extendedGaussianNaturalTerm_pos a y d).le)]
    exact mul_le_mul_of_nonneg_left hexp hd20
  apply hasDerivAt_tsum_of_isPreconnected
    (u := u) (t := Set.Ioo (lambda - 1) (lambda + 1))
    (y₀ := lambda) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound
    (by constructor <;> linarith)
    (summable_extendedGaussianFirstMoment ha)
    (by constructor <;> linarith)

/-- The derivative of the extended limiting partition is its unnormalized
first deficit moment. -/
theorem hasDerivAt_extendedGaussianPartition
    (a lambda : ℝ) (ha : 0 < a) :
    HasDerivAt (extendedGaussianPartition a)
      (extendedGaussianFirstNumerator a lambda) lambda := by
  change HasDerivAt
    (fun t : ℝ ↦ extendedGaussianExceptionalAtom a t +
      ∑' d : ℕ, extendedGaussianNaturalTerm a t d)
    (-extendedGaussianExceptionalAtom a lambda +
      ∑' d : ℕ, (d : ℝ) * extendedGaussianNaturalTerm a lambda d)
    lambda
  exact (hasDerivAt_extendedGaussianExceptionalAtom a lambda).add
    (hasDerivAt_tsum_extendedGaussianNaturalTerm a lambda ha)

/-- The derivative of the unnormalized first moment is the unnormalized
second moment. -/
theorem hasDerivAt_extendedGaussianFirstNumerator
    (a lambda : ℝ) (ha : 0 < a) :
    HasDerivAt (extendedGaussianFirstNumerator a)
      (extendedGaussianSecondNumerator a lambda) lambda := by
  have hexc := (hasDerivAt_extendedGaussianExceptionalAtom a lambda).neg
  change HasDerivAt
    (-extendedGaussianExceptionalAtom a +
      fun t : ℝ ↦ ∑' d : ℕ, (d : ℝ) *
        extendedGaussianNaturalTerm a t d)
    (extendedGaussianExceptionalAtom a lambda +
      ∑' d : ℕ, ((d : ℝ) ^ 2) *
        extendedGaussianNaturalTerm a lambda d)
    lambda
  simpa only [neg_neg] using
    hexc.add (hasDerivAt_tsum_extendedGaussianFirstMoment a lambda ha)

/-- The derivative of the normalized limiting mean is its raw variance. -/
theorem hasDerivAt_extendedGaussianMean
    (a lambda : ℝ) (ha : 0 < a) :
    HasDerivAt (extendedGaussianMean a)
      (extendedGaussianRawVariance a lambda) lambda := by
  have hquot :=
    (hasDerivAt_extendedGaussianFirstNumerator a lambda ha).div
      (hasDerivAt_extendedGaussianPartition a lambda ha)
      (extendedGaussianPartition_ne_zero ha)
  have halg :
      extendedGaussianSecondNumerator a lambda /
          extendedGaussianPartition a lambda -
        (extendedGaussianFirstNumerator a lambda /
          extendedGaussianPartition a lambda) ^ 2 =
      (extendedGaussianSecondNumerator a lambda *
          extendedGaussianPartition a lambda -
        extendedGaussianFirstNumerator a lambda *
          extendedGaussianFirstNumerator a lambda) /
        extendedGaussianPartition a lambda ^ 2 := by
    field_simp [extendedGaussianPartition_ne_zero ha]
  change HasDerivAt
    (extendedGaussianFirstNumerator a / extendedGaussianPartition a)
    (extendedGaussianSecondNumerator a lambda /
        extendedGaussianPartition a lambda -
      (extendedGaussianFirstNumerator a lambda /
        extendedGaussianPartition a lambda) ^ 2)
    lambda
  rw [halg]
  simpa only [Pi.div_apply] using hquot

/-! ## Strict positivity of the variance -/

/-- Cauchy--Schwarz for the first two natural-deficit moments of the
extended Gaussian profile. -/
theorem extendedGaussianNatural_cauchySchwarz
    (a lambda : ℝ) (ha : 0 < a) :
    (∑' d : ℕ,
        (d : ℝ) * extendedGaussianNaturalTerm a lambda d) ^ 2 ≤
      (∑' d : ℕ,
          ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d) *
        (∑' d : ℕ, extendedGaussianNaturalTerm a lambda d) := by
  have hzero := summable_extendedGaussianNaturalTerm
    (a := a) (lambda := lambda) ha
  have hfirst := summable_extendedGaussianFirstMoment
    (a := a) (lambda := lambda) ha
  have hsecond := summable_extendedGaussianSecondMoment
    (a := a) (lambda := lambda) ha
  have hterm : ∀ d : ℕ, 0 ≤ extendedGaussianNaturalTerm a lambda d :=
    fun d ↦ (extendedGaussianNaturalTerm_pos a lambda d).le
  have hfinite : ∀ s : Finset ℕ,
      (∑ d ∈ s,
          (d : ℝ) * extendedGaussianNaturalTerm a lambda d) ^ 2 ≤
        (∑ d ∈ s,
            ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d) *
          (∑ d ∈ s, extendedGaussianNaturalTerm a lambda d) := by
    intro s
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun d : ℕ ↦
        (d : ℝ) * Real.sqrt (extendedGaussianNaturalTerm a lambda d))
      (fun d : ℕ ↦
        Real.sqrt (extendedGaussianNaturalTerm a lambda d))
    have hprod : ∀ d : ℕ,
        ((d : ℝ) * Real.sqrt (extendedGaussianNaturalTerm a lambda d)) *
            Real.sqrt (extendedGaussianNaturalTerm a lambda d) =
          (d : ℝ) * extendedGaussianNaturalTerm a lambda d := by
      intro d
      rw [mul_assoc, Real.mul_self_sqrt (hterm d)]
    have hleftSq : ∀ d : ℕ,
        ((d : ℝ) * Real.sqrt
            (extendedGaussianNaturalTerm a lambda d)) ^ 2 =
          ((d : ℝ) ^ 2) *
            extendedGaussianNaturalTerm a lambda d := by
      intro d
      rw [mul_pow, Real.sq_sqrt (hterm d)]
    have hrightSq : ∀ d : ℕ,
        (Real.sqrt (extendedGaussianNaturalTerm a lambda d)) ^ 2 =
          extendedGaussianNaturalTerm a lambda d := by
      intro d
      rw [Real.sq_sqrt (hterm d)]
    simpa only [hprod, hleftSq, hrightSq] using hcs
  have hzeroLimit :
      Tendsto
        (fun s : Finset ℕ ↦
          ∑ d ∈ s, extendedGaussianNaturalTerm a lambda d)
        atTop
        (nhds (∑' d : ℕ, extendedGaussianNaturalTerm a lambda d)) :=
    hzero.hasSum
  have hfirstLimit :
      Tendsto
        (fun s : Finset ℕ ↦
          ∑ d ∈ s,
            (d : ℝ) * extendedGaussianNaturalTerm a lambda d)
        atTop
        (nhds (∑' d : ℕ,
          (d : ℝ) * extendedGaussianNaturalTerm a lambda d)) :=
    hfirst.hasSum
  have hsecondLimit :
      Tendsto
        (fun s : Finset ℕ ↦
          ∑ d ∈ s,
            ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d)
        atTop
        (nhds (∑' d : ℕ,
          ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d)) :=
    hsecond.hasSum
  exact le_of_tendsto_of_tendsto'
    (hfirstLimit.pow 2) (hsecondLimit.mul hzeroLimit) hfinite

private theorem tsum_extendedGaussianFirstMoment_nonneg
    (a lambda : ℝ) :
    0 ≤ ∑' d : ℕ,
      (d : ℝ) * extendedGaussianNaturalTerm a lambda d := by
  exact tsum_nonneg (fun d ↦ mul_nonneg (by positivity)
    (extendedGaussianNaturalTerm_pos a lambda d).le)

private theorem tsum_extendedGaussianSecondMoment_nonneg
    (a lambda : ℝ) :
    0 ≤ ∑' d : ℕ,
      ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d := by
  exact tsum_nonneg (fun d ↦ mul_nonneg (sq_nonneg _)
    (extendedGaussianNaturalTerm_pos a lambda d).le)

/-- The limiting profile has positive mass at two distinct deficits (`-1`
and `0`), so its raw variance is strictly positive at every finite tilt. -/
theorem extendedGaussianRawVariance_pos
    (a lambda : ℝ) (ha : 0 < a) :
    0 < extendedGaussianRawVariance a lambda := by
  set exceptional := extendedGaussianExceptionalAtom a lambda with hexceptional
  set mass :=
    ∑' d : ℕ, extendedGaussianNaturalTerm a lambda d with hmass
  set firstMoment :=
    ∑' d : ℕ,
      (d : ℝ) * extendedGaussianNaturalTerm a lambda d with hfirst
  set secondMoment :=
    ∑' d : ℕ,
      ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d with hsecond
  have hexceptionalPos : 0 < exceptional :=
    extendedGaussianExceptionalAtom_pos a lambda
  have hmassPos : 0 < mass :=
    lt_of_lt_of_le zero_lt_one
      (one_le_tsum_extendedGaussianNaturalTerm
        (a := a) (lambda := lambda) ha)
  have hfirstNonneg : 0 ≤ firstMoment :=
    tsum_extendedGaussianFirstMoment_nonneg a lambda
  have hsecondNonneg : 0 ≤ secondMoment :=
    tsum_extendedGaussianSecondMoment_nonneg a lambda
  have hcauchy : firstMoment ^ 2 ≤ secondMoment * mass :=
    extendedGaussianNatural_cauchySchwarz a lambda ha
  have hpartitionPos : 0 < extendedGaussianPartition a lambda := by
    rw [extendedGaussianPartition, ← hexceptional, ← hmass]
    exact add_pos hexceptionalPos hmassPos
  have hnumerator :
      0 < extendedGaussianSecondNumerator a lambda *
          extendedGaussianPartition a lambda -
        extendedGaussianFirstNumerator a lambda ^ 2 := by
    rw [extendedGaussianSecondNumerator, extendedGaussianFirstNumerator,
      extendedGaussianPartition, ← hexceptional, ← hmass, ← hfirst,
      ← hsecond]
    nlinarith [mul_pos hexceptionalPos hmassPos,
      mul_nonneg hexceptionalPos.le hfirstNonneg,
      mul_nonneg hexceptionalPos.le hsecondNonneg, hcauchy]
  have hvarianceIdentity :
      extendedGaussianRawVariance a lambda =
        (extendedGaussianSecondNumerator a lambda *
            extendedGaussianPartition a lambda -
          extendedGaussianFirstNumerator a lambda ^ 2) /
          extendedGaussianPartition a lambda ^ 2 := by
    rw [extendedGaussianRawVariance, extendedGaussianMean]
    field_simp [ne_of_gt hpartitionPos]
  rw [hvarianceIdentity]
  exact div_pos hnumerator (sq_pos_of_pos hpartitionPos)

/-- The limiting normalized deficit mean is differentiable at every finite
tilt. -/
theorem differentiable_extendedGaussianMean
    (a : ℝ) (ha : 0 < a) :
    Differentiable ℝ (extendedGaussianMean a) :=
  fun lambda ↦ (hasDerivAt_extendedGaussianMean a lambda ha).differentiableAt

/-- In particular, the limiting normalized deficit mean is continuous. -/
theorem continuous_extendedGaussianMean
    (a : ℝ) (ha : 0 < a) :
    Continuous (extendedGaussianMean a) :=
  (differentiable_extendedGaussianMean a ha).continuous

/-- Strict variance positivity makes the limiting normalized deficit mean
strictly increasing. -/
theorem strictMono_extendedGaussianMean
    (a : ℝ) (ha : 0 < a) :
    StrictMono (extendedGaussianMean a) := by
  apply strictMono_of_deriv_pos
  intro lambda
  rw [(hasDerivAt_extendedGaussianMean a lambda ha).deriv]
  exact extendedGaussianRawVariance_pos a lambda ha

end

end Erdos625
