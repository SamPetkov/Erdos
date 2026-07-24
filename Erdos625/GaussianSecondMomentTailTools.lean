import Erdos625.GaussianTailTools
import Erdos625.GeometricSecondMomentTools

/-!
# Finite tilted-Gaussian second-moment tails

This module combines the pointwise tilted-Gaussian majorant with the explicit
second-moment geometric tail.  For `a > 0` and `|lambda| ≤ M`, it bounds the
finite natural-index tail of

`d ^ 2 * exp (lambda * d - a / 2 * d ^ 2)`.

The result is finite and includes empty `Finset.Ico` intervals.  It assumes,
but does not produce, the bound on the tilt; it makes no convergence or
optimizer claim.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Explicit finite second-moment tail for a boundedly tilted Gaussian
sequence on natural indices. -/
theorem finiteTiltedGaussianSecondMomentTail_le
    {a M lambda : ℝ} (ha : 0 < a) (hlambda : |lambda| ≤ M)
    (R m : ℕ) :
    (∑ d ∈ Finset.Ico R m,
      ((d : ℝ) ^ 2) *
        Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ≤
      Real.exp (M ^ 2 / a) *
        ((Real.exp (-a / 4)) ^ R *
          (((R : ℝ) ^ 2) / (1 - Real.exp (-a / 4)) +
            (2 * (R : ℝ) * Real.exp (-a / 4)) /
              (1 - Real.exp (-a / 4)) ^ 2 +
            Real.exp (-a / 4) * (1 + Real.exp (-a / 4)) /
              (1 - Real.exp (-a / 4)) ^ 3)) := by
  have hrho0 : 0 ≤ Real.exp (-a / 4) := Real.exp_nonneg _
  have hrho1 : Real.exp (-a / 4) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hpointwise (d : ℕ) :
      ((d : ℝ) ^ 2) *
          Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2) ≤
        Real.exp (M ^ 2 / a) *
          (((d : ℝ) ^ 2) * (Real.exp (-a / 4)) ^ d) := by
    have hterm := tiltedGaussianTerm_le_geometric ha hlambda d
    have hscaled :=
      mul_le_mul_of_nonneg_left hterm (sq_nonneg (d : ℝ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
  calc
    (∑ d ∈ Finset.Ico R m,
        ((d : ℝ) ^ 2) *
          Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ≤
        ∑ d ∈ Finset.Ico R m,
          Real.exp (M ^ 2 / a) *
            (((d : ℝ) ^ 2) * (Real.exp (-a / 4)) ^ d) :=
      Finset.sum_le_sum fun d _ ↦ hpointwise d
    _ = Real.exp (M ^ 2 / a) *
          ∑ d ∈ Finset.Ico R m,
            ((d : ℝ) ^ 2) * (Real.exp (-a / 4)) ^ d := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (M ^ 2 / a) *
        ((Real.exp (-a / 4)) ^ R *
          (((R : ℝ) ^ 2) / (1 - Real.exp (-a / 4)) +
            (2 * (R : ℝ) * Real.exp (-a / 4)) /
              (1 - Real.exp (-a / 4)) ^ 2 +
            Real.exp (-a / 4) * (1 + Real.exp (-a / 4)) /
              (1 - Real.exp (-a / 4)) ^ 3)) :=
      mul_le_mul_of_nonneg_left
        (sum_Ico_cast_sq_mul_pow_le_geometric_tail
          hrho0 hrho1 R m)
        (Real.exp_nonneg _)

end

end Erdos625
