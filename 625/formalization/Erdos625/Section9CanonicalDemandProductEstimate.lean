import Erdos625.Section9ActualResidualENNRealExpBridge
import Erdos625.Section9CycleWeightSplit
import Erdos625.Section9ResidualLambdaTotalBound
import Erdos625.Section9ResidualQDegreeAssembly
import Erdos625.Section9ResidualQMixedCycleEnumeration
import Erdos625.Section9ResidualOnlyCycleEnumeration
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
    exact pow_lt_one₀ bot_le htau_lt (by norm_num : (2 : ℕ) ≠ 0)
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
    rw [← Fintype.prod_prod_type', ← Fintype.sum_prod_type']
    exact ennreal_polymer_product_le_ereal_exp_sum
      (Finset.univ : Finset (A × B)) (fun x => lambda x.1 x.2)
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

/-- Residual-only and mixed-cycle bounds combine into a bound for the complete
simple-cycle sum. This is the exact finite split used by the later product
assembly. -/
theorem simpleCycle_sum_le_of_residual_mixed_bounds
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B))
    (residualBound mixedBound : ENNReal)
    (hresidual :
      (∑ C ∈ (simpleBipartiteCycles A B).filter (fun C => Disjoint C M),
        edgeWeightOutsideENN q M C) ≤ residualBound)
    (hmixed :
      (∑ C : MixedSimpleCycle A B M,
        edgeWeightOutsideENN q M C.1) ≤ mixedBound) :
    (∑ C ∈ simpleBipartiteCycles A B,
      edgeWeightOutsideENN q M C) ≤ residualBound + mixedBound := by
  rw [sum_simpleBipartiteCycles_edgeWeight_split]
  exact add_le_add hresidual hmixed

/-- The literal positive-residual lambda and simple-cycle products have one
explicit exponential majorant, with absolute constants chosen before all
finite types and residual data. -/
theorem exists_absolute_residual_product_exponential_majorant :
    ∃ kappaLambda kappaQ : ENNReal,
      0 < kappaLambda ∧ kappaLambda ≠ ∞ ∧
      0 < kappaQ ∧ kappaQ ≠ ∞ ∧
      ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (M : Finset (A × B)) (U R m : ℕ)
          (row : A → ℕ) (col : B → ℕ),
        IsBipartiteMatching M →
        0 < m →
        (∑ a, row a) = m →
        (∑ b, col b) = m →
        (∀ a, row a ≤ U) →
        (∀ b, col b ≤ U) →
        R = U / 2 →
        2 ^ U ≤ m ^ 3 →
        let tau : ENNReal := kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)
        tau < (1 / 3 : ENNReal) →
        let beta : ENNReal := tau * (1 - tau)⁻¹
        beta < 1 ∧
        residualProductExponentMajorant kappaLambda kappaQ
          (Fintype.card A) M.card U m ≠ ∞ ∧
        ((∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
          (∏ C ∈ simpleBipartiteCycles A B,
            (1 + edgeWeightOutsideENN (residualQ M R row col) M C))) ≤
          EReal.exp
            ((residualProductExponentMajorant kappaLambda kappaQ
              (Fintype.card A) M.card U m : ENNReal) : EReal) := by
  obtain ⟨kappaLambda, hkLpos, hkLtop, hkL⟩ :=
    existsAbsoluteResidualLambdaTotalBound
  obtain ⟨kappaQ, hkQpos, hkQtop, hkQ⟩ :=
    existsAbsoluteResidualQRowColumnBound_of_degreeCaps
  refine ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, ?_⟩
  intro A B _ _ _ _ M U R m row col hM hm hrow hcol hrowCap hcolCap hR hpow
  dsimp only
  intro htau
  let tau : ENNReal := kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)
  let beta : ENNReal := tau * (1 - tau)⁻¹
  have hnorm := hkQ M U R m row col hm hrow hcol hrowCap hcolCap hR hpow
  have hmixed := mixedSimpleCycle_weighted_walk_enumeration
    (residualQ M R row col) M hM tau (by simpa [tau] using htau)
    (by simpa [tau] using hnorm.1) (by simpa [tau] using hnorm.2)
  have htauThird : tau < (1 / 3 : ENNReal) := by
    simpa [tau] using htau
  have htau1 : tau < 1 := htauThird.trans (by norm_num)
  have hresidual := residualOnlySimpleCycle_weighted_walk_enumeration
    (residualQ M R row col) M tau htau1
    (by simpa [tau] using hnorm.1) (by simpa [tau] using hnorm.2)
  have hlambda := hkL M U R m row col hm hrow hcol hrowCap hcolCap hR hpow
  have hbeta : beta < 1 := by simpa [beta] using hmixed.1
  refine ⟨hbeta, ?_, ?_⟩
  · exact residualProductExponentMajorant_ne_top
      kappaLambda kappaQ (Fintype.card A) M.card U m hkLtop hkQtop hm
      (by simpa [tau] using htau1)
      (by simpa [tau, beta] using hbeta)
  · have hcycles := simpleCycle_sum_le_of_residual_mixed_bounds
      (residualQ M R row col) M
      ((Fintype.card A : ENNReal) * (tau ^ 4 * (1 - tau ^ 2)⁻¹))
      (((2 * M.card : ℕ) : ENNReal) * (beta * (1 - beta)⁻¹))
      hresidual (by simpa [beta] using hmixed.2)
    have hproduct := lambda_cycle_products_le_exp_of_sum_bounds
      (residualLambda M R row col) (simpleBipartiteCycles A B)
      (edgeWeightOutsideENN (residualQ M R row col) M)
      (kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal))
      ((Fintype.card A : ENNReal) * (tau ^ 4 * (1 - tau ^ 2)⁻¹) +
        (((2 * M.card : ℕ) : ENNReal) * (beta * (1 - beta)⁻¹)))
      hlambda hcycles
    simpa [residualProductExponentMajorant, tau, beta, add_assoc] using hproduct

#print axioms residualProductExponentMajorant_ne_top
#print axioms lambda_cycle_products_le_exp_of_sum_bounds
#print axioms simpleCycle_sum_le_of_residual_mixed_bounds
#print axioms exists_absolute_residual_product_exponential_majorant

end

end Erdos625
