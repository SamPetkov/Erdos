import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Finite tilted-Gaussian tail bounds

This module turns a quadratic exponential weight on natural indices into a
geometric majorant.  If `a > 0` and `|lambda| ≤ M`, then each term satisfies

`exp (lambda * d - a / 2 * d ^ 2) ≤ exp (M ^ 2 / a) * exp (-a / 4) ^ d`.

Summing this pointwise estimate gives an explicit finite `Finset.Ico` tail
bound.  The result is purely finite and makes no claim about how a tilt bound
`|lambda| ≤ M` is obtained, convergence of partition functions, or any
asymptotic root location.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A bounded linear tilt of a Gaussian is dominated by a fixed wider
Gaussian, uniformly over the real coordinate.  This is a pointwise estimate;
it assumes the tilt bound and does not prove boundedness of an optimizer. -/
theorem gaussian_abs_tilt_domination
    {a M lambda x : ℝ} (ha : 0 < a) (hlambda : |lambda| ≤ M) :
    Real.exp (lambda * x - a / 2 * x ^ 2) ≤
      Real.exp (M ^ 2 / a) * Real.exp (-a / 4 * x ^ 2) := by
  rw [← Real.exp_add]
  have h_sq : M * |x| - a / 4 * x ^ 2 ≤ M ^ 2 / a := by
    rw [le_div_iff₀' ha]
    nlinarith [
      sq_nonneg (2 * M - a * |x|),
      abs_mul_abs_self x,
      mul_div_cancel₀ (a ^ 2) (ne_of_gt ha)]
  exact Real.exp_le_exp.mpr (by
    cases abs_cases x <;> nlinarith [abs_le.mp hlambda])

/-- A tilted Gaussian term on a natural index is bounded by an explicit
geometric term.  The exponent loss `a / 4` uses both completion of the square
and the natural-index inequality `d ≤ d ^ 2`. -/
theorem tiltedGaussianTerm_le_geometric
    {a M lambda : ℝ} (ha : 0 < a) (hlambda : |lambda| ≤ M) (d : ℕ) :
    Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2) ≤
      Real.exp (M ^ 2 / a) * (Real.exp (-a / 4)) ^ d := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  gcongr
  field_simp
  nlinarith [
    sq_nonneg (2 * lambda - (d : ℝ) * a),
    mul_le_mul_of_nonneg_left (show (0 : ℝ) ≤ d by positivity) ha.le,
    mul_le_mul_of_nonneg_left
      (show (d : ℝ) ≤ (d : ℝ) ^ 2 by
        norm_cast
        nlinarith)
      ha.le,
    abs_le.mp hlambda]

/-- Explicit finite upper tail for a tilted Gaussian sequence on natural
indices.  The statement also covers `m ≤ R`, when the `Finset.Ico R m` sum is
empty. -/
theorem finiteTiltedGaussianTail_le
    {a M lambda : ℝ} (ha : 0 < a) (hlambda : |lambda| ≤ M) (R m : ℕ) :
    (∑ d ∈ Finset.Ico R m,
      Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ≤
      Real.exp (M ^ 2 / a) *
        ((Real.exp (-a / 4)) ^ R /
          (1 - Real.exp (-a / 4))) := by
  calc
    (∑ d ∈ Finset.Ico R m,
        Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ≤
        ∑ d ∈ Finset.Ico R m,
          Real.exp (M ^ 2 / a) * (Real.exp (-a / 4)) ^ d :=
      Finset.sum_le_sum fun d _ ↦
        tiltedGaussianTerm_le_geometric ha hlambda d
    _ = Real.exp (M ^ 2 / a) *
          ∑ d ∈ Finset.Ico R m, (Real.exp (-a / 4)) ^ d := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (M ^ 2 / a) *
          ((Real.exp (-a / 4)) ^ R /
            (1 - Real.exp (-a / 4))) :=
      mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one
          (Real.exp_nonneg _)
          (Real.exp_lt_one_iff.mpr (by linarith)))
        (Real.exp_nonneg _)

end

end Erdos625
