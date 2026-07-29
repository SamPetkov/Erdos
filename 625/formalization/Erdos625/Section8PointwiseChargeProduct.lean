import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# Section VIII: pointwise product reduction

The remaining charged comparison has two logically independent inputs:

* one local partial/full ratio in every selected cell;
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
    (partial full localCharge : Cell → ENNReal)
    (partialGlobal fullGlobal globalCharge : ENNReal)
    (hlocal : ∀ c, partial c ≤ full c * localCharge c)
    (hglobal : partialGlobal ≤ fullGlobal * globalCharge) :
    (∏ c, partial c) * partialGlobal ≤
      ((∏ c, full c) * fullGlobal) *
        (globalCharge * ∏ c, localCharge c) := by
  have hprod : (∏ c, partial c) ≤ ∏ c, full c * localCharge c := by
    apply Finset.prod_le_prod'
    intro c _
    exact hlocal c
  calc
    (∏ c, partial c) * partialGlobal ≤
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
    (partial full localRatio : Cell → ENNReal)
    (deficit : Cell → Nat)
    (partialGlobal fullGlobal base : ENNReal)
    (hlocal : ∀ c, partial c ≤ full c * localRatio c)
    (hglobal : partialGlobal ≤
      fullGlobal * base ^ (∑ c, deficit c)) :
    (∏ c, partial c) * partialGlobal ≤
      ((∏ c, full c) * fullGlobal) *
        ∏ c, (base ^ deficit c * localRatio c) := by
  have h := finiteProduct_mul_global_le
    partial full localRatio partialGlobal fullGlobal
      (base ^ (∑ c, deficit c)) hlocal hglobal
  have hcharge :
      base ^ (∑ c, deficit c) * (∏ c, localRatio c) =
        ∏ c, (base ^ deficit c * localRatio c) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simpa only [hcharge] using h

#print axioms finiteProduct_mul_global_le
#print axioms finiteProduct_mul_globalPower_le_chargedProduct

end

end Erdos625
