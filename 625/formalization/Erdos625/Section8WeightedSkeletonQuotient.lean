import Erdos625.Section8UnlabelledTypedSkeleton
import Mathlib.Tactic

/-!
# Section VIII: weighted reindexing through the physical skeleton fibre

This is only a finite-equivalence reindexing statement. It makes no probability
claim and introduces no quotient multiplicity beyond the already constructed
equivalence.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Reindex a physical-skeleton weight from literal typed partial matchings
through the exact equivalence with the prescribed type-table fibre. -/
theorem sum_typedPartialMatching_skeletonWeight_eq_sum_unlabelledSkeletonFibre
    {I J R : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [AddCommMonoid R]
    (L : I -> J -> Nat) (k : I -> Nat) (ell : J -> Nat)
    (w : UnlabelledTypedSkeleton k ell -> R) :
    (∑ matching : TypedPartialMatching L k ell,
      w (typedPartialMatchingToUnlabelledSkeletonFibre L k ell matching).1) =
      ∑ S : {S : UnlabelledTypedSkeleton k ell // S.typeTable = L}, w S.1 := by
  simpa [typedPartialMatchingEquivUnlabelledSkeletonFibre] using
    (typedPartialMatchingEquivUnlabelledSkeletonFibre L k ell).sum_comp
      (fun S => w S.1)

end

end Erdos625
