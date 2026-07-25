import Erdos625.Section8EndpointDecoratedBlockPairings
import Mathlib.Tactic

/-!
# Section VIII: combined decorated endpoint reference quotient

A full endpoint table contains two independent finite fibres:

* the block-level pairing fibre, with its single table-cell factorial quotient;
* the physical full-stub matching fibre inside every selected block pair.

This module combines their two existing cross-multiplied cardinality identities
before any division.  It then casts the result to `ENNReal` and packages the
weighted constant-fibre sum used by the endpoint reference calculation.

No equivalence with the separately defined physical endpoint fibre, no deficit
sum, no endpoint transportation inequality, and no asymptotic estimate is
asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The two finite factorial denominators in the decorated endpoint
parameterization: one for grouping identical block-pair types and one for the
stub bijections inside the selected cells. -/
def fourEndpointDecoratedDenominator
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) : Nat :=
  fourEndpointCellFactorialProduct L *
    fourEndpointCellStubFactorialProduct alpha hAlpha L

/-- The corresponding numerator: row-block selections, column-block
selections, and the two endpoint-stub selections in every selected cell. -/
def fourEndpointDecoratedNumerator
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) : Nat :=
  (fourEndpointRowSelectionProduct alpha hAlpha k L *
      fourEndpointColumnSelectionProduct alpha hAlpha k L) *
    fourEndpointCellStubSelectionProduct alpha hAlpha L

/-- Combining the exact block-pairing and per-cell stub-matching identities
introduces no additional multiplicity or factorial. -/
theorem card_fourEndpointDecoratedBlockPairing_mul_denominator
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    Fintype.card (FourEndpointDecoratedBlockPairing alpha hAlpha k L) *
        fourEndpointDecoratedDenominator alpha hAlpha L =
      fourEndpointDecoratedNumerator alpha hAlpha k L := by
  have hDecor :=
    card_fourEndpointDecoratedBlockPairing_mul_cellStubFactorials
      alpha hAlpha k L
  have hPair := card_fourEndpointBlockPairing_mul_cellFactorials
    alpha hAlpha k L
  unfold fourEndpointDecoratedDenominator fourEndpointDecoratedNumerator
  calc
    Fintype.card (FourEndpointDecoratedBlockPairing alpha hAlpha k L) *
          (fourEndpointCellFactorialProduct L *
            fourEndpointCellStubFactorialProduct alpha hAlpha L) =
        (Fintype.card (FourEndpointDecoratedBlockPairing alpha hAlpha k L) *
          fourEndpointCellStubFactorialProduct alpha hAlpha L) *
            fourEndpointCellFactorialProduct L := by
      ac_rfl
    _ = (Fintype.card (FourEndpointBlockPairing alpha hAlpha k L) *
          fourEndpointCellStubSelectionProduct alpha hAlpha L) *
            fourEndpointCellFactorialProduct L := by
      rw [hDecor]
    _ = (Fintype.card (FourEndpointBlockPairing alpha hAlpha k L) *
          fourEndpointCellFactorialProduct L) *
            fourEndpointCellStubSelectionProduct alpha hAlpha L := by
      ac_rfl
    _ = (fourEndpointRowSelectionProduct alpha hAlpha k L *
          fourEndpointColumnSelectionProduct alpha hAlpha k L) *
            fourEndpointCellStubSelectionProduct alpha hAlpha L := by
      rw [hPair]

/-- The combined factorial denominator is a positive natural number. -/
theorem fourEndpointDecoratedDenominator_ne_zero
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) :
    fourEndpointDecoratedDenominator alpha hAlpha L ≠ 0 := by
  have hTable : 0 < fourEndpointCellFactorialProduct L := by
    unfold fourEndpointCellFactorialProduct
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    exact Nat.factorial_pos _
  have hStub : 0 < fourEndpointCellStubFactorialProduct alpha hAlpha L := by
    unfold fourEndpointCellStubFactorialProduct
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    exact pow_pos (Nat.factorial_pos _) _
  unfold fourEndpointDecoratedDenominator
  exact mul_ne_zero hTable.ne' hStub.ne'

/-- Division form of the exact decorated endpoint cardinality in `ENNReal`.
All factors are finite and the denominator is nonzero. -/
theorem ennreal_card_fourEndpointDecoratedBlockPairing_eq_quotient
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    (Fintype.card (FourEndpointDecoratedBlockPairing alpha hAlpha k L) : ENNReal) =
      (fourEndpointDecoratedNumerator alpha hAlpha k L : ENNReal) /
        (fourEndpointDecoratedDenominator alpha hAlpha L : ENNReal) := by
  apply (ENNReal.eq_div_iff
    (Nat.cast_ne_zero.mpr
      (fourEndpointDecoratedDenominator_ne_zero alpha hAlpha L))
    (ENNReal.natCast_ne_top _)).2
  simpa only [Nat.cast_mul, mul_comm] using
    congrArg (fun x : Nat => (x : ENNReal))
      (card_fourEndpointDecoratedBlockPairing_mul_denominator
        alpha hAlpha k L)

/-- A weight constant on the full decorated endpoint fibre sums with exactly
that quotient coefficient. -/
theorem sum_fourEndpointDecoratedBlockPairing_const_eq_quotient_mul
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable)
    (weight : ENNReal) :
    (∑ _ : FourEndpointDecoratedBlockPairing alpha hAlpha k L, weight) =
      ((fourEndpointDecoratedNumerator alpha hAlpha k L : ENNReal) /
        (fourEndpointDecoratedDenominator alpha hAlpha L : ENNReal)) * weight := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ennreal_card_fourEndpointDecoratedBlockPairing_eq_quotient]

#print axioms card_fourEndpointDecoratedBlockPairing_mul_denominator
#print axioms fourEndpointDecoratedDenominator_ne_zero
#print axioms ennreal_card_fourEndpointDecoratedBlockPairing_eq_quotient
#print axioms sum_fourEndpointDecoratedBlockPairing_const_eq_quotient_mul

end

end Erdos625
