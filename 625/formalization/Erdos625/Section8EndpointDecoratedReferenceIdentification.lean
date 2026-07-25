import Erdos625.Section8EndpointDecoratedReferenceWeight
import Mathlib.Tactic

/-!
# Section VIII: identify the decorated endpoint reference with `W(L)`

The preceding modules count the block-pairing and full-stub fibres and attach
the common local reward.  This file performs the remaining finite algebraic
regrouping: the manuscript local product is exactly the quotient of the full
stub-selection product by the local stub-factorial product, multiplied by the
signed reward product.

Consequently the literal sum over decorated endpoint block pairings is exactly
`fourEndpointW`.  This is still a statement about the decorated
parameterization; the equivalence with `FourEndpointPhysicalFibre` is a
separate finite theorem.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The aggregate manuscript local factor is exactly the full-cell stub
selection quotient times the product of signed local rewards. -/
theorem fourEndpointLocalProduct_eq_stubQuotient_mul_reward
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) :
    fourEndpointLocalProduct alpha hAlpha L =
      ((fourEndpointCellStubSelectionProduct alpha hAlpha L : Nat) : ENNReal) /
          ((fourEndpointCellStubFactorialProduct alpha hAlpha L : Nat) : ENNReal) *
        fourEndpointFullRewardProduct alpha hAlpha L := by
  unfold fourEndpointLocalProduct fourEndpointLocalCellFactor
    fourEndpointCellStubSelectionProduct
    fourEndpointCellStubFactorialProduct
    fourEndpointFullRewardProduct
  push_cast
  simp only [mul_pow, div_pow, Finset.prod_mul_distrib,
    Finset.prod_div_distrib]
  ring

/-- The expanded decorated quotient weight is definitionally the manuscript
endpoint reference weight after the local-product regrouping. -/
theorem fourEndpointDecoratedReferenceQuotientWeight_eq_fourEndpointW
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    fourEndpointDecoratedReferenceQuotientWeight n alpha hAlpha k L =
      fourEndpointW n alpha hAlpha k L := by
  unfold fourEndpointDecoratedReferenceQuotientWeight
    fourEndpointDecoratedNumerator fourEndpointDecoratedDenominator
    fourEndpointDecoratedReferenceAtomWeight fourEndpointW
  rw [fourEndpointLocalProduct_eq_stubQuotient_mul_reward]
  push_cast
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv
    (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))]
  ring

/-- Exact full-endpoint normalization: summing the common reference atom over
all selected block pairings and all full-cell stub matchings gives `W(L)` with
no extra multiplicity. -/
theorem sum_fourEndpointDecoratedReferenceAtomWeight_eq_fourEndpointW
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    (∑ _ : FourEndpointDecoratedBlockPairing alpha hAlpha k L,
      fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L) =
        fourEndpointW n alpha hAlpha k L := by
  rw [sum_fourEndpointDecoratedReferenceAtomWeight_eq_quotientWeight,
    fourEndpointDecoratedReferenceQuotientWeight_eq_fourEndpointW]

#print axioms fourEndpointLocalProduct_eq_stubQuotient_mul_reward
#print axioms fourEndpointDecoratedReferenceQuotientWeight_eq_fourEndpointW
#print axioms sum_fourEndpointDecoratedReferenceAtomWeight_eq_fourEndpointW

end

end Erdos625
