import Erdos625.PhaseSignedFourSizeDerivativeRewrite
import Erdos625.ColoringProfilePhaseDerivativeAffineCore
import Mathlib.Tactic

/-!
# Finite lower envelope for the signed four-size derivative

This exact finite seam inserts the existing factorial-error lower bound for
the affine core into the signed four-size derivative rewrite.  It leaves the
finite entropy, logarithm, and tilt-linear terms explicit for later uniform
estimates and makes no asymptotic or root-existence claim.
-/

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The signed finite-four derivative is bounded below by its quadratic
affine main term minus the exact factorial error, with every remaining
analytic term displayed unchanged. -/
theorem signedFourSizeObjectiveDerivative_quadratic_lower_envelope
    (n alpha : Nat) (parts : Real) (halpha : 0 < alpha) :
    q / 2 * (alpha : Real) ^ 2 + (alpha : Real) -
          factorialLogErrorBound alpha +
        fourSizeFiniteEntropy alpha (fourSizeTarget n alpha parts) + q -
        Real.log parts -
        ProfileEntropyS4.tilt (fourDeficitScore alpha)
            (fourSizeTarget n alpha parts) *
          (n : Real) / parts ≤
      signedFourSizeObjectiveDerivative n alpha parts := by
  rw [signedFourSizeObjectiveDerivative_eq_affineCore_sub_tiltTerm]
  have hcore := abs_profileDeficitAffineCore_sub_quadratic_le alpha halpha
  rw [abs_le] at hcore
  linarith

end

#print axioms signedFourSizeObjectiveDerivative_quadratic_lower_envelope

end Erdos625
