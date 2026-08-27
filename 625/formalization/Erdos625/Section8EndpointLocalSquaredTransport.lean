import Erdos625.Section8EndpointLocalCellFactor
import Mathlib.Tactic

/-!
# Section VIII: square-free local endpoint transport

This is the exact cross-multiplied one-cell identity underlying the local
factor in the manuscript's square-free endpoint transport. It deliberately
contains neither the global falling-factorial comparison nor the later
multinomial/asymptotic summation.
-/

namespace Erdos625

open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-- The square of one full endpoint-cell factor, after multiplication by its
explicit factorial and reward-transport denominator, is exactly the product
of the two diagonal endpoint factors and the remaining upper-endpoint falling
factorial. This division-free form includes the diagonal case `i = j`. -/
theorem fourEndpointLocalCellFactor_sq_mul_transportDenominator
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (i j : Fin 4) :
    (fourEndpointLocalCellFactor alpha hAlpha i j) ^ 2 *
        ((((fourEndpointDistance i j).factorial : Nat) : ENNReal) ^ 2 *
          (2 : ENNReal) ^
            (fourEndpointDistance i j *
                fourEndpointLowerSize alpha hAlpha i j +
              (fourEndpointDistance i j).choose 2)) =
      fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha i) *
        fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha j) *
          (((fourEndpointUpperSize alpha hAlpha i j).descFactorial
            (fourEndpointDistance i j) : Nat) : ENNReal) := by
  rw [fourEndpointLocalCellFactor_eq_lowerDiagonal_mul_choose]
  by_cases hij : fourEndpointSize alpha hAlpha i <=
      fourEndpointSize alpha hAlpha j
  · rw [fourEndpointLowerSize, min_eq_left hij,
      fourEndpointUpperSize, max_eq_right hij]
    rw [fourEndpointSizeDiagonalFactor_ratio alpha hAlpha hHigh i j hij]
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  · have hji : fourEndpointSize alpha hAlpha j <=
        fourEndpointSize alpha hAlpha i := le_of_not_ge hij
    have hdist : fourEndpointDistance j i = fourEndpointDistance i j := by
      simp [fourEndpointDistance, Nat.dist_comm]
    rw [fourEndpointLowerSize, min_eq_right hji,
      fourEndpointUpperSize, max_eq_left hji]
    rw [fourEndpointSizeDiagonalFactor_ratio alpha hAlpha hHigh j i hji]
    rw [hdist, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring

#print axioms fourEndpointLocalCellFactor_sq_mul_transportDenominator

end

end Erdos625
