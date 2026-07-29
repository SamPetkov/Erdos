import Erdos625.Section8ExactLocalDeficitRatio
import Erdos625.Section8NearCellChoiceLink
import Mathlib.Tactic

/-!
# Section VIII: exact local deficit ratio in `ENNReal`

The natural-number module proves the local partial/full identity without any
division.  This file performs only the justified finite cancellations needed to
express that identity in the multiplicative language of the Section VIII
partition function.

The final theorem says exactly:

`partialWeightedCell * n^h = fullWeightedCell * nearCellTerm n m d h`.

Thus the existing `nearCellTerm` is not merely a majorant: before the later
three-quarter estimate it is the exact charged ratio between the physical
partial cell and its full-containment reference.
-/

namespace Erdos625

open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-- Exact uncharged local partial/full ratio. -/
def exactLocalDeficitRatioENNReal (m d h : Nat) : ENNReal :=
  ((m.choose h : ENNReal) /
    ((endpointDeficitDenominator d h : Nat) : ENNReal)) *
      ((2 : ENNReal) ^ (h * m - h * (h + 1) / 2))⁻¹

/-- The endpoint-distance denominator is a positive finite natural number. -/
theorem endpointDeficitDenominator_pos (d h : Nat) :
    0 < endpointDeficitDenominator d h := by
  rw [endpointDeficitDenominator_eq_descFactorial]
  exact Nat.descFactorial_pos.mpr (by omega)

/-- The exact natural identity, cancelled only through positive finite factors. -/
theorem lowerUpperCellWeightedCount_cast_eq_full_mul_exactRatio
    (m d h : Nat) (hh : h ≤ m) (hhigh : 3 ≤ m - h) :
    (lowerUpperCellWeightedCount m d (m - h) : ENNReal) =
      (lowerUpperCellWeightedCount m d m : ENNReal) *
        exactLocalDeficitRatioENNReal m d h := by
  let D : ENNReal := (endpointDeficitDenominator d h : Nat)
  let P : ENNReal := (2 : ENNReal) ^ (h * m - h * (h + 1) / 2)
  have hD0 : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (endpointDeficitDenominator_pos d h).ne'
  have hDtop : D ≠ ∞ := by
    dsimp [D]
    exact ENNReal.natCast_ne_top _
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact pow_ne_zero _ (by norm_num : (2 : ENNReal) ≠ 0)
  have hPtop : P ≠ ∞ := by
    dsimp [P]
    exact ENNReal.pow_ne_top (by norm_num : (2 : ENNReal) ≠ ∞)
  have hcross :
      (lowerUpperCellWeightedCount m d (m - h) : ENNReal) * D * P =
        (lowerUpperCellWeightedCount m d m : ENNReal) * (m.choose h : ENNReal) := by
    dsimp [D, P]
    exact_mod_cast
      lowerUpperCellWeightedCount_deficit_cross_mul m d h hh hhigh
  have hdivideP :
      (lowerUpperCellWeightedCount m d (m - h) : ENNReal) * D =
        ((lowerUpperCellWeightedCount m d m : ENNReal) *
          (m.choose h : ENNReal)) / P := by
    apply (ENNReal.eq_div_iff hP0 hPtop).2
    simpa only [mul_comm] using hcross
  have hdivideD :
      (lowerUpperCellWeightedCount m d (m - h) : ENNReal) =
        (((lowerUpperCellWeightedCount m d m : ENNReal) *
          (m.choose h : ENNReal)) / P) / D := by
    apply (ENNReal.eq_div_iff hD0 hDtop).2
    simpa only [mul_comm] using hdivideP
  rw [hdivideD]
  unfold exactLocalDeficitRatioENNReal
  dsimp only [D, P]
  simp only [div_eq_mul_inv]
  ring

/-- The manuscript's charged term is `n^h` times the exact uncharged ratio. -/
theorem nearCellTerm_eq_pow_mul_exactLocalDeficitRatio
    (n m d h : Nat) :
    nearCellTerm n m d h =
      (n : ENNReal) ^ h * exactLocalDeficitRatioENNReal m d h := by
  unfold nearCellTerm exactLocalDeficitRatioENNReal
    endpointDeficitDenominator
  simp only [div_eq_mul_inv]
  ring

/-- Exact charged one-cell identity used in the direct all-deficit product. -/
theorem lowerUpperCellWeightedCount_cast_mul_pow_eq_full_mul_nearCellTerm
    (n m d h : Nat) (hh : h ≤ m) (hhigh : 3 ≤ m - h) :
    (lowerUpperCellWeightedCount m d (m - h) : ENNReal) * (n : ENNReal) ^ h =
      (lowerUpperCellWeightedCount m d m : ENNReal) *
        nearCellTerm n m d h := by
  rw [lowerUpperCellWeightedCount_cast_eq_full_mul_exactRatio m d h hh hhigh,
    nearCellTerm_eq_pow_mul_exactLocalDeficitRatio]
  ring

#print axioms lowerUpperCellWeightedCount_cast_eq_full_mul_exactRatio
#print axioms nearCellTerm_eq_pow_mul_exactLocalDeficitRatio
#print axioms lowerUpperCellWeightedCount_cast_mul_pow_eq_full_mul_nearCellTerm

end

end Erdos625
