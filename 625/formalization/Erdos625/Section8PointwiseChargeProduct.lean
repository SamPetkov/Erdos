import Erdos625.Section8NearArithmeticFoundation
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# Section VIII: pointwise product reduction

The remaining charged comparison has two logically independent inputs:

* one local actual/full ratio in every selected cell;
* one global falling-factorial loss, paid only once.

This module packages their finite multiplication.  It deliberately contains no
endpoint-specific factorial algebra and no asymptotic estimate.  Its purpose is
to prevent the final proof from redistributing the global denominator loss
cell-by-cell before the exact aggregate identity has been established.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Multiply pointwise local comparisons and one independent global comparison.
The conclusion keeps the local and global charges visibly separate. -/
theorem finiteProduct_mul_global_le
    {Cell : Type*} [Fintype Cell]
    (actual full localCharge : Cell → ENNReal)
    (actualGlobal fullGlobal globalCharge : ENNReal)
    (hlocal : ∀ c, actual c ≤ full c * localCharge c)
    (hglobal : actualGlobal ≤ fullGlobal * globalCharge) :
    (∏ c, actual c) * actualGlobal ≤
      ((∏ c, full c) * fullGlobal) *
        (globalCharge * ∏ c, localCharge c) := by
  have hprod : (∏ c, actual c) ≤ ∏ c, full c * localCharge c := by
    apply Finset.prod_le_prod'
    intro c _
    exact hlocal c
  calc
    (∏ c, actual c) * actualGlobal ≤
        (∏ c, full c * localCharge c) *
          (fullGlobal * globalCharge) :=
      mul_le_mul' hprod hglobal
    _ = ((∏ c, full c) * fullGlobal) *
          (globalCharge * ∏ c, localCharge c) := by
      rw [Finset.prod_mul_distrib]
      ac_rfl

/-- Specialization in which the single global loss is `base` raised to the
sum of the cell deficits.  The global power is then absorbed into the local
charged factors `base^(deficit c) * localRatio c` exactly once. -/
theorem finiteProduct_mul_globalPower_le_chargedProduct
    {Cell : Type*} [Fintype Cell]
    (actual full localRatio : Cell → ENNReal)
    (deficit : Cell → Nat)
    (actualGlobal fullGlobal base : ENNReal)
    (hlocal : ∀ c, actual c ≤ full c * localRatio c)
    (hglobal : actualGlobal ≤
      fullGlobal * base ^ (∑ c, deficit c)) :
    (∏ c, actual c) * actualGlobal ≤
      ((∏ c, full c) * fullGlobal) *
        ∏ c, (base ^ deficit c * localRatio c) := by
  have h := finiteProduct_mul_global_le
    actual full localRatio actualGlobal fullGlobal
      (base ^ (∑ c, deficit c)) hlocal hglobal
  have hcharge :
      base ^ (∑ c, deficit c) * (∏ c, localRatio c) =
        ∏ c, (base ^ deficit c * localRatio c) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hcharge] at h
  exact h

/-- The reciprocal of the smaller falling factorial is at most the reciprocal
of the full falling factorial times the single global loss `n^H`.  This is the
reciprocal form of `denominatorLoss_eq_falling_and_le_pow` used by aggregate
weights. -/
theorem inv_descFactorial_sub_le_inv_mul_pow
    (n J H : Nat) (hH : H ≤ J) (hJ : J ≤ n) :
    (((n.descFactorial (J - H) : Nat) : ENNReal)⁻¹) ≤
      (((n.descFactorial J : Nat) : ENNReal)⁻¹) *
        (n : ENNReal) ^ H := by
  let fullDenom : ENNReal := ((n.descFactorial J : Nat) : ENNReal)
  let smallDenom : ENNReal := ((n.descFactorial (J - H) : Nat) : ENNReal)
  have hfull0 : fullDenom ≠ 0 := by
    dsimp [fullDenom]
    exact_mod_cast
      (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hJ : 0 < n.descFactorial J))
  have hfullTop : fullDenom ≠ ∞ := by
    dsimp [fullDenom]
    exact ENNReal.natCast_ne_top _
  have hloss : denominatorLoss n J H ≤ (n : ENNReal) ^ H :=
    (denominatorLoss_eq_falling_and_le_pow n J H hH hJ).2
  have hinv : smallDenom⁻¹ = fullDenom⁻¹ * denominatorLoss n J H := by
    unfold denominatorLoss
    change smallDenom⁻¹ = fullDenom⁻¹ * (fullDenom / smallDenom)
    rw [ENNReal.div_eq_inv_mul]
    calc
      smallDenom⁻¹ = smallDenom⁻¹ * (fullDenom⁻¹ * fullDenom) := by
        rw [ENNReal.inv_mul_cancel hfull0 hfullTop, mul_one]
      _ = fullDenom⁻¹ * (smallDenom⁻¹ * fullDenom) := by ac_rfl
  rw [hinv]
  simpa [mul_comm] using (mul_le_mul_right hloss fullDenom⁻¹)

/-- Exact aggregate endpoint for the denominator bookkeeping.  If each local
actual factor is bounded by its full factor times a literal local ratio, then
the aggregate actual weight with denominator `(n)_(J-H)` is bounded by the
full aggregate weight with denominator `(n)_J`, multiplied by the charged local
factors `n^(h_e) * localRatio_e`.

The global falling-factorial comparison is invoked only once. -/
theorem finiteProduct_mul_inv_descFactorial_sub_le_chargedProduct
    {Cell : Type*} [Fintype Cell]
    (actual full localRatio : Cell → ENNReal)
    (deficit : Cell → Nat)
    (n J : Nat)
    (hdeficit : (∑ c, deficit c) ≤ J)
    (hJ : J ≤ n)
    (hlocal : ∀ c, actual c ≤ full c * localRatio c) :
    (∏ c, actual c) *
        (((n.descFactorial (J - ∑ c, deficit c) : Nat) : ENNReal)⁻¹) ≤
      ((∏ c, full c) *
        (((n.descFactorial J : Nat) : ENNReal)⁻¹)) *
        ∏ c, ((n : ENNReal) ^ deficit c * localRatio c) := by
  apply finiteProduct_mul_globalPower_le_chargedProduct
    actual full localRatio deficit
      (((n.descFactorial (J - ∑ c, deficit c) : Nat) : ENNReal)⁻¹)
      (((n.descFactorial J : Nat) : ENNReal)⁻¹)
      (n : ENNReal) hlocal
  exact inv_descFactorial_sub_le_inv_mul_pow
    n J (∑ c, deficit c) hdeficit hJ

#print axioms finiteProduct_mul_global_le
#print axioms finiteProduct_mul_globalPower_le_chargedProduct
#print axioms inv_descFactorial_sub_le_inv_mul_pow
#print axioms finiteProduct_mul_inv_descFactorial_sub_le_chargedProduct

end

end Erdos625
