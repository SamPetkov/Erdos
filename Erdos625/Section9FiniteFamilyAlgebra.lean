import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite family product-to-exponential algebra for Section IX

This module isolates the algebra used after an injective finite decomposition
and its pointwise weight estimate have already been supplied.  It asserts no
graph-cycle decomposition and no configuration-model probability estimate.
-/

namespace Erdos625

open scoped BigOperators

/-- An injectively encoded finite family whose weights are bounded by products
of nonnegative atom weights is bounded first by the full subset product and
then by the exponential of the total atom weight. -/
theorem finiteInjectiveFamily_product_exp_bound
    {F C : Type*}
    [Fintype F] [Fintype C] [DecidableEq C]
    (wF : F → ℝ) (wC : C → ℝ)
    (cycles : F → Finset C)
    (hcycles : Function.Injective cycles)
    (hwF : ∀ f, wF f ≤ ∏ c ∈ cycles f, wC c)
    (hwC : ∀ c, 0 ≤ wC c) :
    (∑ f, wF f) ≤ ∏ c, (1 + wC c) ∧
      (∏ c, (1 + wC c)) ≤ Real.exp (∑ c, wC c) := by
  constructor
  · refine le_trans (Finset.sum_le_sum fun f _ => hwF f) ?_
    have h_sum_subset :
        (∑ f : F, ∏ c ∈ cycles f, wC c) ≤
          ∑ t ∈ Finset.powerset (Finset.univ : Finset C),
            ∏ c ∈ t, wC c := by
      have h_sum_image :
          (∑ f : F, ∏ c ∈ cycles f, wC c) ≤
            ∑ t ∈ Finset.image cycles Finset.univ,
              ∏ c ∈ t, wC c := by
        rw [Finset.sum_image <| by tauto]
      exact h_sum_image.trans
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr fun f _ =>
            Finset.mem_powerset.mpr <| Finset.subset_univ _)
          fun _ _ _ => Finset.prod_nonneg fun _ _ => hwC _)
    simpa only [Finset.prod_add, Finset.prod_const_one, mul_one, add_comm] using
      h_sum_subset
  · rw [Real.exp_sum]
    exact Finset.prod_le_prod
      (fun c _ => by linarith [hwC c])
      (fun c _ => by
        rw [add_comm]
        exact Real.add_one_le_exp (wC c))

#print axioms finiteInjectiveFamily_product_exp_bound

end Erdos625
