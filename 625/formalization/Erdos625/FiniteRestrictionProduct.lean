import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# A generic finite restriction-product inequality

Suppose a finite family of finite subsets is uniquely determined by deleting a
fixed set of coordinates.  For nonnegative multiplicative weights, its total
restricted weight is then bounded by the full subset product on the remaining
coordinates.

The Section IX matching-restriction estimate is one instance.  The statement
itself does not mention graphs, parity, or matchings.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- If deletion of `frozen` is injective on `family`, the weighted family sum
is bounded by the full subset product outside `frozen`. -/
theorem weighted_finsetFamily_sdiff_le_subsetProduct
    {E : Type*} [Fintype E] [DecidableEq E]
    (family : Finset (Finset E))
    (frozen : Finset E)
    (q : E → ENNReal)
    (hinj : ∀ F ∈ family, ∀ G ∈ family,
      F \ frozen = G \ frozen → F = G) :
    (∑ F ∈ family, ∏ e ∈ F \ frozen, q e) ≤
      ∏ e ∈ (Finset.univ : Finset E) \ frozen, (1 + q e) := by
  classical
  calc
    (∑ F ∈ family, ∏ e ∈ F \ frozen, q e) =
        ∑ S ∈ Finset.image (fun F : Finset E => F \ frozen) family,
          ∏ e ∈ S, q e := by
      symm
      rw [Finset.sum_image]
      exact hinj
    _ ≤ ∑ S ∈ Finset.powerset
          ((Finset.univ : Finset E) \ frozen),
          ∏ e ∈ S, q e := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.image_subset_iff.mpr fun F _hF =>
        Finset.mem_powerset.mpr (by
          intro e he
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ e, (Finset.mem_sdiff.mp he).2⟩)
    _ = ∏ e ∈ (Finset.univ : Finset E) \ frozen, (1 + q e) := by
      simp +decide [Finset.prod_add, add_comm]

#print axioms weighted_finsetFamily_sdiff_le_subsetProduct

end

end Erdos625
