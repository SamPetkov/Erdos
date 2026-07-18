import Erdos625.Section8UnlabelledTypedSkeleton
import Mathlib.Tactic

/-!
# E5: physical-skeleton fibre grouping by type table

This file groups the finite physical unlabelled skeleton space by the literal
`typeTable` map and applies the accepted one-factorial fibre identity.  No
additional ordering or factorial quotient is introduced.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The finite set of type tables actually attained by physical skeletons. -/
def attainedUnlabelledTypeTables
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (k : I -> Nat) (ell : J -> Nat) :
    Finset (I -> J -> Nat) := by
  classical
  exact (Finset.univ : Finset (UnlabelledTypedSkeleton k ell)).image
    (fun S => S.typeTable)

def typeTableCellFactorialProduct
    {I J : Type*}
    [Fintype I] [Fintype J]
    (L : I -> J -> Nat) : Nat :=
  ∏ i : I, ∏ j : J, (L i j).factorial

def typeTableRowDescendingProduct
    {I J : Type*}
    [Fintype I] [Fintype J]
    (k : I -> Nat) (L : I -> J -> Nat) : Nat :=
  ∏ i : I, (k i).descFactorial (∑ j : J, L i j)

def typeTableColumnDescendingProduct
    {I J : Type*}
    [Fintype I] [Fintype J]
    (ell : J -> Nat) (L : I -> J -> Nat) : Nat :=
  ∏ j : J, (ell j).descFactorial (∑ i : I, L i j)

/-- Exact finite grouping of any type-table weight by the fibres of the
physical skeleton's `typeTable` map. -/
theorem sum_unlabelledSkeleton_weight_eq_sum_typeTables
    {I J R : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [AddCommMonoid R]
    (k : I -> Nat) (ell : J -> Nat)
    (w : (I -> J -> Nat) -> R) :
    (∑ S : UnlabelledTypedSkeleton k ell, w S.typeTable) =
      ∑ L ∈ attainedUnlabelledTypeTables k ell,
        Fintype.card
          {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} • w L := by
  simp +decide only [attainedUnlabelledTypeTables, Fintype.card_subtype];
  rw [ Finset.sum_image' ];
  simp +contextual [ Finset.sum_filter ];
  simp +decide [ Finset.sum_ite ]

/-- Casted form of the accepted cross-multiplied fibre cardinality.  It has
exactly one cell-factorial product. -/
theorem cast_card_unlabelledSkeleton_fibre_mul_cellFactorials
    {I J R : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [CommSemiring R]
    (k : I -> Nat) (ell : J -> Nat) (L : I -> J -> Nat) :
    (Fintype.card
        {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} : R) *
      (typeTableCellFactorialProduct L : R) =
        ((typeTableRowDescendingProduct k L *
          typeTableColumnDescendingProduct ell L : Nat) : R) := by
  unfold typeTableCellFactorialProduct typeTableRowDescendingProduct
    typeTableColumnDescendingProduct
  simpa only [Nat.cast_mul] using congrArg ((↑) : Nat → R)
    (card_unlabelledTypedSkeleton_typeTable_mul_factorials L k ell)

/-- Combined weighted grouping after the exact fibre-cardinality rewrite.
The source contains the same single cell-factorial product as the accepted
cross-multiplied theorem and no additional multiplicity. -/
theorem sum_unlabelledSkeleton_cellFactorial_weight_eq_descendingProducts
    {I J R : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [CommSemiring R]
    (k : I -> Nat) (ell : J -> Nat)
    (w : (I -> J -> Nat) -> R) :
    (∑ S : UnlabelledTypedSkeleton k ell,
      (typeTableCellFactorialProduct S.typeTable : R) * w S.typeTable) =
      ∑ L ∈ attainedUnlabelledTypeTables k ell,
        ((typeTableRowDescendingProduct k L *
          typeTableColumnDescendingProduct ell L : Nat) : R) * w L := by
  change (∑ S : UnlabelledTypedSkeleton k ell,
      (↑(∏ i : I, ∏ j : J, (S.typeTable i j).factorial) : R) * w S.typeTable) = _
  rw [sum_unlabelledSkeleton_weight_eq_sum_typeTables k ell
    (fun L => (↑(∏ i : I, ∏ j : J, (L i j).factorial) : R) * w L)]
  refine Finset.sum_congr rfl fun L _hL => ?_
  rw [nsmul_eq_mul, ← mul_assoc]
  exact congrArg (fun x : R => x * w L)
    (cast_card_unlabelledSkeleton_fibre_mul_cellFactorials k ell L)

/-- The manuscript-facing weighted quotient rewrite.  Over a
characteristic-zero semifield, grouping physical skeletons by their type table
replaces the fibre multiplicity by the exact ratio of the row/column
descending-factorial products to the single cell-factorial product. -/
theorem sum_unlabelledSkeleton_weight_eq_descendingProducts_div_cellFactorials
    {I J R : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Semifield R] [CharZero R]
    (k : I -> Nat) (ell : J -> Nat)
    (w : (I -> J -> Nat) -> R) :
    (∑ S : UnlabelledTypedSkeleton k ell, w S.typeTable) =
      ∑ L ∈ attainedUnlabelledTypeTables k ell,
        (((typeTableRowDescendingProduct k L *
          typeTableColumnDescendingProduct ell L : Nat) : R) /
            (typeTableCellFactorialProduct L : R)) * w L := by
  rw [show (∑ S : UnlabelledTypedSkeleton k ell, w S.typeTable) =
      ∑ L ∈ attainedUnlabelledTypeTables k ell,
        (Fintype.card
          {S : UnlabelledTypedSkeleton k ell // S.typeTable = L} : R) * w L by
    convert sum_unlabelledSkeleton_weight_eq_sum_typeTables k ell w using 1
    grind]
  refine Finset.sum_congr rfl fun L _hL => ?_
  rw [div_mul_eq_mul_div, eq_div_iff]
  · convert congrArg (· * w L)
      (cast_card_unlabelledSkeleton_fibre_mul_cellFactorials k ell L) using 1
    all_goals ring
  · exact Nat.cast_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun _ _ =>
        Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)

/-- Cancellation form of the exact `W(L)` ratio: there is precisely one
cell-factorial denominator, and multiplying it back gives the two endpoint
descending-factorial products. -/
theorem typeTableCellFactorial_mul_descendingProducts_div_cellFactorials
    {I J R : Type*}
    [Fintype I] [Fintype J]
    [Semifield R] [CharZero R]
    (k : I -> Nat) (ell : J -> Nat) (L : I -> J -> Nat) :
    (typeTableCellFactorialProduct L : R) *
        (((typeTableRowDescendingProduct k L *
          typeTableColumnDescendingProduct ell L : Nat) : R) /
            (typeTableCellFactorialProduct L : R)) =
      ((typeTableRowDescendingProduct k L *
        typeTableColumnDescendingProduct ell L : Nat) : R) := by
  rw [mul_div_cancel₀]
  exact Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun _ _ =>
      Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)

#print axioms sum_unlabelledSkeleton_weight_eq_sum_typeTables
#print axioms cast_card_unlabelledSkeleton_fibre_mul_cellFactorials
#print axioms sum_unlabelledSkeleton_cellFactorial_weight_eq_descendingProducts
#print axioms sum_unlabelledSkeleton_weight_eq_descendingProducts_div_cellFactorials
#print axioms typeTableCellFactorial_mul_descendingProducts_div_cellFactorials

end

end Erdos625
