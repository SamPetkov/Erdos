import Erdos625.GaussianTailTools
import Erdos625.GeometricMomentTools

/-!
# Summability of tilted-Gaussian moments

A fixed positive quadratic coefficient dominates every fixed linear tilt on
the natural indices.  This module makes that comparison through the existing
pointwise tilted-Gaussian bound and Mathlib's summability theorem for a
polynomial times a geometric sequence.

The comparison includes `d = 0` directly.  For the zeroth moment Lean's
convention gives `0 ^ 0 = 1`, while the first and second moment factors vanish;
no division by the index or eventual-only ratio argument is used.
-/

namespace Erdos625

noncomputable section

/-- Every fixed natural power times a linearly tilted Gaussian with positive
quadratic coefficient is summable on the natural indices. -/
theorem summable_natPow_mul_tiltedGaussian
    {a lambda : ℝ} (ha : 0 < a) (k : ℕ) :
    Summable
      (fun d : ℕ ↦
        ((d : ℝ) ^ k) *
          Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) := by
  have hrho0 : 0 ≤ Real.exp (-a / 4) := Real.exp_nonneg _
  have hrho1 : Real.exp (-a / 4) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hrhoNorm : ‖Real.exp (-a / 4)‖ < 1 := by
    rwa [Real.norm_of_nonneg hrho0]
  have hgeometric :
      Summable
        (fun d : ℕ ↦
          ((d : ℝ) ^ k) * (Real.exp (-a / 4)) ^ d) :=
    summable_pow_mul_geometric_of_norm_lt_one k hrhoNorm
  have hmajorant :
      Summable
        (fun d : ℕ ↦
          Real.exp (|lambda| ^ 2 / a) *
            (((d : ℝ) ^ k) * (Real.exp (-a / 4)) ^ d)) :=
    hgeometric.mul_left _
  refine hmajorant.of_nonneg_of_le (fun d ↦ ?_) (fun d ↦ ?_)
  · exact mul_nonneg
      (pow_nonneg (by positivity) k)
      (Real.exp_nonneg _)
  · have hterm := tiltedGaussianTerm_le_geometric
      ha (show |lambda| ≤ |lambda| from le_rfl) d
    have hscaled := mul_le_mul_of_nonneg_left hterm
      (pow_nonneg (show (0 : ℝ) ≤ d by positivity) k)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- A Gaussian with any fixed linear tilt has summable zeroth, first, and
second natural-index moments. -/
theorem summable_tiltedGaussian_moments
    {a lambda : ℝ} (ha : 0 < a) :
    Summable
        (fun d : ℕ ↦
          Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ∧
      Summable
        (fun d : ℕ ↦
          (d : ℝ) *
            Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) ∧
      Summable
        (fun d : ℕ ↦
          ((d : ℝ) ^ 2) *
            Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using summable_natPow_mul_tiltedGaussian ha 0
  · simpa using summable_natPow_mul_tiltedGaussian ha 1
  · exact summable_natPow_mul_tiltedGaussian ha 2

end

end Erdos625
