import Erdos625.SignedFourSizeObjective
import Erdos625.ColoringProfilePhaseDerivativeAffineCore
import Mathlib.Tactic

/-!
# Quadratic-main reduction for the signed four-size derivative

The exact signed four-size derivative initially contains the target-dependent
terms

`B * T + optimizedValue(T) + (B - tilt(T)) * n / parts`.

Using the defining identity `T = alpha - n / parts` and the exact dual formula

`optimizedValue(T) = log partition(tilt(T)) - tilt(T) * T`,

these terms cancel to

`B * alpha - tilt(T) * alpha + log partition(tilt(T))`.

Consequently the only error in the quadratic affine core is the already proved
`factorialLogErrorBound`. This module records that exact cancellation and an
unconditional finite absolute-error envelope. It does not yet prove uniform
bounds for the selected tilt, partition logarithm, or `log parts`, and hence
does not by itself establish the derivative corridor or either root.
-/

namespace Erdos625

open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The lower-order remainder after extracting the quadratic affine core from
the signed four-size derivative. -/
noncomputable def signedFourDerivativeRemainder
    (n alpha : ℕ) (parts : ℝ) : ℝ :=
  (alpha : ℝ) - Real.log parts -
    ProfileEntropyS4.tilt (fourDeficitScore alpha)
        (fourSizeTarget n alpha parts) * (alpha : ℝ) +
    Real.log
      (ProfileEntropyS4.partition (fourDeficitScore alpha)
        (ProfileEntropyS4.tilt (fourDeficitScore alpha)
          (fourSizeTarget n alpha parts))) + q

/-- Exact cancellation of the target and `n / parts` terms in the derivative.
The middle summand is precisely the affine-core error controlled by
`abs_profileDeficitAffineCore_sub_quadratic_le`. -/
theorem signedFourSizeObjectiveDerivative_eq_quadraticMain_add_errors
    (n alpha : ℕ) (parts : ℝ) :
    signedFourSizeObjectiveDerivative n alpha parts =
      q / 2 * (alpha : ℝ) ^ 2 +
        (profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : ℝ) -
            (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ))) +
        signedFourDerivativeRemainder n alpha parts := by
  unfold signedFourSizeObjectiveDerivative signedFourDerivativeRemainder
    fourSizeFiniteEntropy ProfileEntropyS4.optimizedValue fourSizeTarget
  ring

private theorem abs_sub_sub_add_add_le
    (a b c d e : ℝ) :
    |a - b - c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc
    |a - b - c + d + e| = |(((a + -b) + -c) + d) + e| := by ring
    _ ≤ |((a + -b) + -c) + d| + |e| := abs_add _ _
    _ ≤ (|(a + -b) + -c| + |d|) + |e| :=
      add_le_add_right (abs_add _ _) _
    _ ≤ ((|a + -b| + |-c|) + |d|) + |e| :=
      add_le_add_right (add_le_add_right (abs_add _ _) _) _
    _ ≤ (((|a| + |-b|) + |-c|) + |d|) + |e| :=
      add_le_add_right
        (add_le_add_right (add_le_add_right (abs_add _ _) _) _) _
    _ = |a| + |b| + |c| + |d| + |e| := by
      simp only [abs_neg]
      ring

/-- Unconditional finite envelope for the lower-order derivative remainder. -/
theorem abs_signedFourDerivativeRemainder_le
    (n alpha : ℕ) (parts : ℝ) :
    |signedFourDerivativeRemainder n alpha parts| ≤
      (alpha : ℝ) + |Real.log parts| +
        |ProfileEntropyS4.tilt (fourDeficitScore alpha)
            (fourSizeTarget n alpha parts)| * (alpha : ℝ) +
        |Real.log
          (ProfileEntropyS4.partition (fourDeficitScore alpha)
            (ProfileEntropyS4.tilt (fourDeficitScore alpha)
              (fourSizeTarget n alpha parts)))| + |q| := by
  unfold signedFourDerivativeRemainder
  have h := abs_sub_sub_add_add_le
    (alpha : ℝ) (Real.log parts)
    (ProfileEntropyS4.tilt (fourDeficitScore alpha)
      (fourSizeTarget n alpha parts) * (alpha : ℝ))
    (Real.log
      (ProfileEntropyS4.partition (fourDeficitScore alpha)
        (ProfileEntropyS4.tilt (fourDeficitScore alpha)
          (fourSizeTarget n alpha parts)))) q
  simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg alpha)] using h

/-- Finite quadratic-main bound for the signed four-size derivative. The first
summand is the explicit factorial-log error; the remaining displayed terms are
all lower order on the manuscript root corridor once compact-target and
part-count bounds are supplied. -/
theorem abs_signedFourSizeObjectiveDerivative_sub_quadraticMain_le
    (n alpha : ℕ) (parts : ℝ) (halpha : 0 < alpha) :
    |signedFourSizeObjectiveDerivative n alpha parts -
        q / 2 * (alpha : ℝ) ^ 2| ≤
      factorialLogErrorBound alpha +
        ((alpha : ℝ) + |Real.log parts| +
          |ProfileEntropyS4.tilt (fourDeficitScore alpha)
              (fourSizeTarget n alpha parts)| * (alpha : ℝ) +
          |Real.log
            (ProfileEntropyS4.partition (fourDeficitScore alpha)
              (ProfileEntropyS4.tilt (fourDeficitScore alpha)
                (fourSizeTarget n alpha parts)))| + |q|) := by
  have hCore :=
    abs_profileDeficitAffineCore_sub_quadratic_le alpha halpha
  have hRemainder :=
    abs_signedFourDerivativeRemainder_le n alpha parts
  calc
    |signedFourSizeObjectiveDerivative n alpha parts -
        q / 2 * (alpha : ℝ) ^ 2| =
      |(profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : ℝ) -
            (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ))) +
        signedFourDerivativeRemainder n alpha parts| := by
          rw [signedFourSizeObjectiveDerivative_eq_quadraticMain_add_errors]
          congr 1
          ring
    _ ≤
      |profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : ℝ) -
            (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ))| +
        |signedFourDerivativeRemainder n alpha parts| := abs_add _ _
    _ ≤
      factorialLogErrorBound alpha +
        ((alpha : ℝ) + |Real.log parts| +
          |ProfileEntropyS4.tilt (fourDeficitScore alpha)
              (fourSizeTarget n alpha parts)| * (alpha : ℝ) +
          |Real.log
            (ProfileEntropyS4.partition (fourDeficitScore alpha)
              (ProfileEntropyS4.tilt (fourDeficitScore alpha)
                (fourSizeTarget n alpha parts)))| + |q|) :=
      add_le_add hCore hRemainder

#print axioms signedFourSizeObjectiveDerivative_eq_quadraticMain_add_errors
#print axioms abs_signedFourDerivativeRemainder_le
#print axioms abs_signedFourSizeObjectiveDerivative_sub_quadraticMain_le

end

end Erdos625