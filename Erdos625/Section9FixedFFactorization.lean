import Erdos625.Section9CappedFixedFExpansion
import Erdos625.Section9ActualResidualENNRealPolymerBridge

/-!
# Section IX: fixed-family local-factor separation

This module performs the finite algebraic step immediately after the capped
fixed-`F` prescribed-demand expansion.  It separates the common product of
local threshold increments from the physical `residualQ` weight of `F \ M`.

This theorem is still before the even-family sum and polymer decomposition.
It asserts no residual law, conditional expectation estimate, tagged-law
identity, residual-only cycle estimate, or attachment bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The capped fixed-`F` expectation factors into a common local-`lambda`
product and the physical `residualQ` weight outside the exposed matching. -/
theorem residualFixedFExpectation_le_lambdaProduct_mul_edgeWeight
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M F : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    residualFixedFExpectation M F R row col htotal ≤
      (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
        edgeWeightOutsideENN (residualQ M R row col) M F := by
  refine (capped_fixedF_prescribedDemand_expansion M F R row col htotal hm).trans ?_
  have hedge :
      edgeWeightOutsideENN (residualQ M R row col) M F =
        ∏ a : A, ∏ b : B,
          if (a, b) ∈ F then
            if (a, b) ∈ M then 1 else residualQ M R row col a b
          else 1 := by
    unfold edgeWeightOutsideENN
    rw [← Fintype.prod_ite_mem]
    calc
      (∏ e : A × B,
          if e ∈ F \ M then residualQ M R row col e.1 e.2 else 1) =
          ∏ e : A × B,
            if e ∈ F then
              if e ∈ M then 1 else residualQ M R row col e.1 e.2
            else 1 := by
              apply Fintype.prod_congr
              intro e
              simp only [Finset.mem_sdiff]
              by_cases heF : e ∈ F <;> by_cases heM : e ∈ M <;>
                simp [heF, heM]
      _ = ∏ a : A, ∏ b : B,
            if (a, b) ∈ F then
              if (a, b) ∈ M then 1 else residualQ M R row col a b
            else 1 :=
        Fintype.prod_prod_type'
          (fun a : A => fun b : B =>
            if (a, b) ∈ F then
              if (a, b) ∈ M then (1 : ENNReal)
              else residualQ M R row col a b
            else 1)
  rw [hedge]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro a ha
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro b hb
  by_cases habM : (a, b) ∈ M
  · simp [habM, residualLambda]
  · by_cases habF : (a, b) ∈ F
    · simp only [habM, habF, if_false, if_true]
      exact le_mul_of_one_le_left' (by simp)
    · simp [habM, habF]

#print axioms residualFixedFExpectation_le_lambdaProduct_mul_edgeWeight

end

end Erdos625
