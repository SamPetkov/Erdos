import Erdos625.Section8AllHighDeficitArithmetic
import Mathlib.Tactic

/-!
# Section VIII: the sharp three-quarter exponent budget

For a high multiplicity `j=m-h`, the condition `2h<m` gives a stronger binary
exponent budget than the earlier two-thirds estimate.  The exact coefficient
`floor((3m-1)/4)` is the worst-case value at the largest admissible deficit.

This improves the common local charge from

`n*m / 2^floor(2m/3)`

to

`n*m / 2^floor((3m-1)/4)`.

No phase asymptotic or weighted-cell ratio is asserted in this module.
-/

namespace Erdos625

set_option autoImplicit false

/-- If `2h<m`, then the local binary exponent pays at least
`h * floor((3m-1)/4)`:

`h * floor((3m-1)/4) <= h*m - h*(h+1)/2`.
-/
theorem highDeficit_threeQuarter_exponent_budget
    (m h : Nat) (hhalf : 2 * h < m) :
    h * ((3 * m - 1) / 4) ≤ h * m - h * (h + 1) / 2 := by
  by_cases hh : h = 0
  · simp [hh]
  have hhpos : 0 < h := Nat.pos_of_ne_zero hh
  have hmpos : 0 < m := by omega
  let penalty := h * (h + 1) / 2
  have hh_m : h + 1 ≤ m := by omega
  have hpenalty_le_product : penalty ≤ h * (h + 1) := by
    dsimp only [penalty]
    exact Nat.div_le_self _ _
  have hpenalty_le : penalty ≤ h * m :=
    hpenalty_le_product.trans (Nat.mul_le_mul_left h hh_m)
  have hsub : (h * m - penalty) + penalty = h * m :=
    Nat.sub_add_cancel hpenalty_le
  have hstep : 2 * (h + 1) ≤ m + 1 := by omega
  have hstep_mul : 2 * (h * (h + 1)) ≤ h * (m + 1) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Nat.mul_le_mul_left h hstep
  have hpenalty_div : penalty * 2 ≤ h * (h + 1) := by
    dsimp only [penalty]
    exact Nat.div_mul_le_self _ _
  have hpenalty_four : 4 * penalty ≤ 2 * (h * (h + 1)) := by
    have hmul := Nat.mul_le_mul_left 2 hpenalty_div
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hpenalty_bound : 4 * penalty ≤ h * (m + 1) :=
    hpenalty_four.trans hstep_mul
  have h3m : 1 ≤ 3 * m := by omega
  have h3m_sub : (3 * m - 1) + 1 = 3 * m :=
    Nat.sub_add_cancel h3m
  have hmain : h * (3 * m - 1) ≤ 4 * (h * m - penalty) := by
    nlinarith [hsub, hpenalty_bound, h3m_sub]
  have hquarter := Nat.div_mul_le_self (3 * m - 1) 4
  have hquarter_mul :
      4 * (h * ((3 * m - 1) / 4)) ≤ h * (3 * m - 1) := by
    have hmul := Nat.mul_le_mul_left h hquarter
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hfour := hquarter_mul.trans hmain
  dsimp only [penalty] at hfour ⊢
  omega

#print axioms highDeficit_threeQuarter_exponent_budget

end Erdos625
