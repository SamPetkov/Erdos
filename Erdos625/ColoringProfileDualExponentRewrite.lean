import Erdos625.ColoringProfileDualAsymptotic

/-!
# Exact exponent normalization for the coloring-profile dual bound

This is an algebraic rewrite only. It does not claim that the resulting
exponent tends to `-∞`; that analytic estimate remains a separate obligation.
-/

namespace Erdos625

noncomputable section

/-- The polynomial prefactor in the finite profile-dual bound can be absorbed
exactly into the exponential. The base `n + 1` is strictly positive, so this
does not need an eventual or asymptotic side condition. -/
theorem coloringProfileDualExponentRewrite
    (n b : ℕ) (L : ℝ) :
    ENNReal.ofReal (((n : ℝ) + 1) ^ b) * ENNReal.ofReal (Real.exp L) =
      ENNReal.ofReal
        (Real.exp ((b : ℝ) * Real.log ((n : ℝ) + 1) + L)) := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  rw [← ENNReal.ofReal_mul (le_of_lt (pow_pos hpos b))]
  congr 1
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hpos]

#print axioms Erdos625.coloringProfileDualExponentRewrite

end

end Erdos625
