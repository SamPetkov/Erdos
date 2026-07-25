import Mathlib.Tactic

/-!
# Section VIII: square-free AM--GM linearization

The endpoint transport is most naturally formalized as a squared,
cross-multiplied inequality.  The manuscript sum, however, only needs its
linear AM--GM consequence.  This file isolates that elementary ordered-real
bridge without introducing square roots.
-/

namespace Erdos625

set_option autoImplicit false

/-- A nonnegative square-product bound linearizes by AM--GM without taking a
square root.  This is the abstract bridge used after the endpoint factorial
normalizations have been exposed. -/
theorem two_mul_le_add_of_sq_le_mul
    (x y z : Real)
    (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z)
    (h : x ^ 2 <= y * z) :
    2 * x <= y + z := by
  have hsq : (2 * x) ^ 2 <= (y + z) ^ 2 := by
    nlinarith [sq_nonneg (y - z)]
  nlinarith [sq_nonneg (2 * x + y + z)]

/-- Weighted form used when the same nonnegative table factor multiplies both
one-sided endpoint contributions. -/
theorem two_mul_weight_le_add_of_sq_le_mul
    (x y z weight : Real)
    (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z) (hw : 0 <= weight)
    (h : x ^ 2 <= y * z) :
    2 * (x * weight) <= y * weight + z * weight := by
  have hlinear := two_mul_le_add_of_sq_le_mul x y z hx hy hz h
  nlinarith

#print axioms two_mul_le_add_of_sq_le_mul
#print axioms two_mul_weight_le_add_of_sq_le_mul

end Erdos625
