import Erdos625.Section8EndpointDecoratedReferenceQuotient
import Mathlib.Tactic

/-!
# Section VIII: decorated full-endpoint reference weight

The combined quotient counts all block pairings and all full-cell stub
matchings for one endpoint table.  Every object in that finite family has the
same local signed reward and the same ambient falling-factorial normalization.
This module attaches those two factors and records the exact weighted sum.

The final identification with `fourEndpointW` is deliberately separated from
this theorem: it requires only an algebraic regrouping of the local product,
but no physical-fibre or asymptotic argument.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Product of the signed local rewards of all full endpoint cells in a table. -/
def fourEndpointFullRewardProduct
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) : ENNReal :=
  ∏ i : Fin 4, ∏ j : Fin 4,
    (localSignRewardNat (fourEndpointOverlapSize alpha hAlpha i j) : ENNReal) ^
      L.toFun i j

/-- Common contribution of one fully decorated endpoint block pairing after
its literal block and stub choices have been made. -/
def fourEndpointDecoratedReferenceAtomWeight
    (n alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) : ENNReal :=
  fourEndpointFullRewardProduct alpha hAlpha L /
    ((n.descFactorial (fourEndpointJ alpha hAlpha L) : Nat) : ENNReal)

/-- Expanded full-endpoint reference weight obtained by multiplying the exact
decorated cardinality quotient by the common reward/ambient factor. -/
def fourEndpointDecoratedReferenceQuotientWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) : ENNReal :=
  ((fourEndpointDecoratedNumerator alpha hAlpha k L : Nat) : ENNReal) /
      ((fourEndpointDecoratedDenominator alpha hAlpha L : Nat) : ENNReal) *
    fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L

/-- The literal finite sum over all block and full-stub decorations is exactly
the expanded endpoint reference weight. -/
theorem sum_fourEndpointDecoratedReferenceAtomWeight_eq_quotientWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    (∑ _ : FourEndpointDecoratedBlockPairing alpha hAlpha k L,
      fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L) =
        fourEndpointDecoratedReferenceQuotientWeight
          n alpha hAlpha k L := by
  simpa only [fourEndpointDecoratedReferenceQuotientWeight] using
    (sum_fourEndpointDecoratedBlockPairing_const_eq_quotient_mul
      alpha hAlpha k L
      (fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L))

#print axioms sum_fourEndpointDecoratedReferenceAtomWeight_eq_quotientWeight

end

end Erdos625
