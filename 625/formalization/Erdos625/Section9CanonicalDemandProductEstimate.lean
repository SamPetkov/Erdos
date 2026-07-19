import Erdos625.Section9ActualResidualENNRealExpBridge
import Mathlib.Tactic

/-!
# Section IX: finite product estimate, algebraic prefix

This module isolates two finite algebraic leaves used by the positive-residual
canonical-demand estimate. It does not assert the residual-q cycle bounds or
the eventual midpoint asymptotics.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The explicit exponent controlling the lambda and simple-cycle products. -/
noncomputable def residualProductExponentMajorant
    (kappaLambda kappaQ : ENNReal) (cardA matchingCard U m : ℕ) : ENNReal :=
  let tau := kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)
  let beta := tau * (1 - tau)⁻¹
  kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
    (cardA : ENNReal) * (tau ^ 4 * (1 - tau ^ 2)⁻¹) +
    (((2 * matchingCard : ℕ) : ENNReal) * (beta * (1 - beta)⁻¹))

/-- Every displayed exponent is finite under the strict small-parameter
hypotheses and finite absolute constants. -/
theorem residualProductExponentMajorant_ne_top
    (kappaLambda kappaQ : ENNReal) (cardA matchingCard U m : ℕ)
    (hkLtop : kappaLambda ≠ ∞) (_hkQtop : kappaQ ≠ ∞) (hm : 0 < m)
    (htau : kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal) < 1)
    (hbeta : let tau := kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)
      tau * (1 - tau)⁻¹ < 1) :
    residualProductExponentMajorant kappaLambda kappaQ cardA matchingCard U m ≠ ∞ := by
  let tau : ENNReal := kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)
  let beta : ENNReal := tau * (1 - tau)⁻¹
  have htau_lt : tau < 1 := by simpa [tau] using htau
  have hbeta_lt : beta < 1 := by simpa [beta, tau] using hbeta
  have htau_top : tau ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top htau_lt.le
  have hbeta_top : beta ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hbeta_lt.le
  have htau_sq_lt : tau ^ 2 < 1 := by
    simpa using ENNReal.pow_lt_pow_left htau_lt (by norm_num : (2 : ℕ) ≠ 0)
  have hone_sub_tau_sq : 1 - tau ^ 2 ≠ 0 :=
    (tsub_pos_iff_lt.mpr htau_sq_lt).ne'
  have hone_sub_beta : 1 - beta ≠ 0 :=
    (tsub_pos_iff_lt.mpr hbeta_lt).ne'
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hfirst :
      kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top
      (ENNReal.mul_ne_top hkLtop
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top U))) hm0
  have hsecond :
      (cardA : ENNReal) * (tau ^ 4 * (1 - tau ^ 2)⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top cardA)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top htau_top)
        (ENNReal.inv_ne_top.mpr hone_sub_tau_sq))
  have hthird :
      (((2 * matchingCard : ℕ) : ENNReal) * (beta * (1 - beta)⁻¹)) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top (2 * matchingCard))
      (ENNReal.mul_ne_top hbeta_top
        (ENNReal.inv_ne_top.mpr hone_sub_beta))
  change
    kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
      (cardA : ENNReal) * (tau ^ 4 * (1 - tau ^ 2)⁻¹) +
      (((2 * matchingCard : ℕ) : ENNReal) * (beta * (1 - beta)⁻¹)) ≠ ∞
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfirst, hsecond⟩, hthird⟩

/-- Generic finite-product algebra used after the lambda and split cycle-sum
estimates have been proved. -/
theorem lambda_cycle_products_le_exp_of_sum_bounds
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (lambda : A → B → ENNReal) (cycles : Finset (Finset (A × B)))
    (weight : Finset (A × B) → ENNReal) (lambdaBound cycleBound : ENNReal)
    (hlambda : (∑ a, ∑ b, lambda a b) ≤ lambdaBound)
    (hcycle : (∑ C ∈ cycles, weight C) ≤ cycleBound) :
    ((∏ a, ∏ b, (1 + lambda a b)) *
      (∏ C ∈ cycles, (1 + weight C))) ≤
      EReal.exp (((lambdaBound + cycleBound : ENNReal) : EReal)) := by
  have hlambdaProduct :
      (∏ a, ∏ b, (1 + lambda a b)) ≤
        EReal.exp (((∑ a, ∑ b, lambda a b : ENNReal) : EReal)) := by
    simpa only [Fintype.prod_prod_type', Fintype.sum_prod_type'] using
      (ennreal_polymer_product_le_ereal_exp_sum
        (Finset.univ : Finset (A × B)) (fun x => lambda x.1 x.2))
  have hcycleProduct :
      (∏ C ∈ cycles, (1 + weight C)) ≤
        EReal.exp (((∑ C ∈ cycles, weight C : ENNReal) : EReal)) :=
    ennreal_polymer_product_le_ereal_exp_sum cycles weight
  calc
    ((∏ a, ∏ b, (1 + lambda a b)) *
        (∏ C ∈ cycles, (1 + weight C))) ≤
      EReal.exp (((∑ a, ∑ b, lambda a b : ENNReal) : EReal)) *
        EReal.exp (((∑ C ∈ cycles, weight C : ENNReal) : EReal)) :=
      mul_le_mul' hlambdaProduct hcycleProduct
    _ = EReal.exp
        ((((∑ a, ∑ b, lambda a b : ENNReal) : EReal)) +
          (((∑ C ∈ cycles, weight C : ENNReal) : EReal))) := by
      rw [EReal.exp_add]
    _ = EReal.exp
        ((((∑ a, ∑ b, lambda a b : ENNReal) +
          ∑ C ∈ cycles, weight C : ENNReal) : EReal)) := by
      rw [EReal.coe_ennreal_add]
    _ ≤ EReal.exp (((lambdaBound + cycleBound : ENNReal) : EReal)) := by
      rw [EReal.exp_le_exp_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact add_le_add hlambda hcycle

#print axioms residualProductExponentMajorant_ne_top
#print axioms lambda_cycle_products_le_exp_of_sum_bounds

end

end Erdos625
