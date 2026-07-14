import Erdos625.GaussianTailTools
import Erdos625.GeometricMomentTools

/-!
# Finite tilted-Gaussian first-moment tails

This module combines the pointwise tilted-Gaussian majorant with the explicit
first-moment geometric tail.  For `a > 0` and `|lambda| ≤ M`, it bounds the
finite natural-index tail of

`d * exp (lambda * d - a / 2 * d ^ 2)`

with the same constants as the underlying geometric comparison.  The result
is finite and includes empty `Finset.Ico` intervals.  It does not supply the
tilt bound, a partition-function limit, or any root asymptotic.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Explicit finite first-moment tail for a boundedly tilted Gaussian
sequence on natural indices. -/
theorem finiteTiltedGaussianFirstMomentTail_le
    {a M lambda : ℝ} (ha : 0 < a) (hlambda : |lambda| ≤ M)
    (R m : ℕ) :
    (∑ d ∈ Finset.Ico R m,
      (d : ℝ) *
        Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ≤
      Real.exp (M ^ 2 / a) *
        ((Real.exp (-a / 4)) ^ R *
          ((R : ℝ) / (1 - Real.exp (-a / 4)) +
            Real.exp (-a / 4) /
              (1 - Real.exp (-a / 4)) ^ 2)) := by
  have hrho0 : 0 ≤ Real.exp (-a / 4) := Real.exp_nonneg _
  have hrho1 : Real.exp (-a / 4) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hpointwise (d : ℕ) :
      (d : ℝ) *
          Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2) ≤
        Real.exp (M ^ 2 / a) *
          ((d : ℝ) * (Real.exp (-a / 4)) ^ d) := by
    have hterm := tiltedGaussianTerm_le_geometric ha hlambda d
    have hscaled :=
      mul_le_mul_of_nonneg_left hterm (show (0 : ℝ) ≤ d by positivity)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
  calc
    (∑ d ∈ Finset.Ico R m,
        (d : ℝ) *
          Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ≤
        ∑ d ∈ Finset.Ico R m,
          Real.exp (M ^ 2 / a) *
            ((d : ℝ) * (Real.exp (-a / 4)) ^ d) :=
      Finset.sum_le_sum fun d _ ↦ hpointwise d
    _ = Real.exp (M ^ 2 / a) *
          ∑ d ∈ Finset.Ico R m,
            (d : ℝ) * (Real.exp (-a / 4)) ^ d := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (M ^ 2 / a) *
          ((Real.exp (-a / 4)) ^ R *
            ((R : ℝ) / (1 - Real.exp (-a / 4)) +
              Real.exp (-a / 4) /
                (1 - Real.exp (-a / 4)) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (sum_Ico_cast_mul_pow_le_geometric_tail hrho0 hrho1 R m)
        (Real.exp_nonneg _)

end

end Erdos625
