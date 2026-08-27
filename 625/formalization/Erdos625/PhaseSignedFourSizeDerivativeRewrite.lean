import Erdos625.SignedFourSizeObjective
import Mathlib.Tactic

/-!
# Exact affine-core rewrite for the signed finite-four derivative

This finite algebraic seam exposes the dominant affine core in the exact
signed four-size derivative.  It performs no asymptotic estimate and assumes
no derivative lower bound.
 -/

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The `profileDeficitAffineB` contributions from the target and chain-rule
terms combine exactly into `profileDeficitAffineB alpha * alpha`. -/
theorem signedFourSizeObjectiveDerivative_eq_affineCore_sub_tiltTerm
    (n alpha : Nat) (parts : Real) :
    signedFourSizeObjectiveDerivative n alpha parts =
      profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : Real) +
        fourSizeFiniteEntropy alpha (fourSizeTarget n alpha parts) + q -
        Real.log parts -
        ProfileEntropyS4.tilt (fourDeficitScore alpha)
            (fourSizeTarget n alpha parts) *
          (n : Real) / parts := by
  unfold signedFourSizeObjectiveDerivative fourSizeTarget
  ring

end

end Erdos625
