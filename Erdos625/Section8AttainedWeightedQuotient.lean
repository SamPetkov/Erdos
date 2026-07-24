import Erdos625.Section8PhysicalSkeletonFibreGrouping
import Mathlib.Tactic

/-!
# Section VIII: exact weighted quotient over an attained skeleton family

The existing physical-skeleton quotient groups the entire finite skeleton
space by every type table that occurs. The manuscript, however, sums over a
particular finite family of skeleton tables. This module records the exact
restricted quotient when that family is known to be attained.

The statement keeps the literal finite skeleton indexing and its fibre
multiplicity. All descending-factorial and cell-factorial factors are shown,
and no positivity, asymptotic, probability, or near/middle estimate is
asserted. In particular, this is a usable exact seam toward Section VIII, not
a claim of Lemmas 8.1--8.3.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Physical unlabelled skeletons whose type table belongs to the specified
finite family. Membership is retained in the type, so an attained manuscript
family is not silently replaced by all numerically feasible tables. -/
abbrev RestrictedUnlabelledTypedSkeleton
    {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (k : I → Nat) (ell : J → Nat) (tables : Finset (I → J → Nat)) :=
  {S : UnlabelledTypedSkeleton k ell // S.typeTable ∈ tables}

/-- Exact weighted physical-skeleton quotient over a finite *attained* family
of type tables. The endpoint cases are included: zero cell entries contribute
`0! = 1`, while an empty family gives two empty sums. There is exactly one
cell-factorial denominator, and the coefficient is the literal fibre
multiplicity supplied by the row and column descending-factorial products. -/
theorem sum_restrictedUnlabelledSkeleton_weight_eq_attainedQuotient
    {I J R : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Semifield R] [CharZero R]
    (k : I → Nat) (ell : J → Nat)
    (tables : Finset (I → J → Nat))
    (hattained : ∀ L ∈ tables, L ∈ attainedUnlabelledTypeTables k ell)
    (weight : (I → J → Nat) → R) :
    (∑ S : RestrictedUnlabelledTypedSkeleton k ell tables,
      weight S.1.typeTable) =
      ∑ L ∈ tables,
        (((typeTableRowDescendingProduct k L *
          typeTableColumnDescendingProduct ell L : Nat) : R) /
            (typeTableCellFactorialProduct L : R)) * weight L := by
  simp +decide only [attainedUnlabelledTypeTables, Finset.mem_image,
    Finset.mem_univ, true_and] at hattained
  convert sum_unlabelledSkeleton_weight_eq_descendingProducts_div_cellFactorials
      k ell (fun L => if L ∈ tables then weight L else 0) using 1
  · rw [← Finset.sum_filter]
    refine' Finset.sum_bij (fun S _ => S.val) _ _ _ _ <;> simp +decide
  · rw [← Finset.sum_subset (show tables ⊆ attainedUnlabelledTypeTables k ell from
        fun L hL => by
          obtain ⟨S, rfl⟩ := hattained L hL
          exact Finset.mem_image_of_mem _ (Finset.mem_univ S))]
    · aesop
    · aesop

#print axioms sum_restrictedUnlabelledSkeleton_weight_eq_attainedQuotient

end

end Erdos625
