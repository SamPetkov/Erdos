import Erdos625.Section9ResidualLambdaCubic
import Erdos625.Section9ThetaCap
import Erdos625.ConfigurationThetaMoments
import Mathlib.Tactic

/-!
# Section IX: deterministic total residual-lambda estimate

This module sums the pointwise cubic residual-lambda bound using the global
configuration-theta cubic moment estimate.  It proves the deterministic
fourth-power degree-cap scale in manuscript (9.13).  No residual-law,
attachment, cycle, conditioning, or asymptotic assertion is made here.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- One absolute positive finite constant bounds the total literal residual
lambda by the deterministic fourth-power degree-cap scale. -/
theorem existsAbsoluteResidualLambdaTotalBound :
    ∃ κ : ENNReal, 0 < κ ∧ κ ≠ ∞ ∧
      ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (M : Finset (A × B)) (U R m : ℕ)
          (row : A → ℕ) (col : B → ℕ),
        0 < m →
        (∑ a, row a) = m →
        (∑ b, col b) = m →
        (∀ a, row a ≤ U) →
        (∀ b, col b ≤ U) →
        R = U / 2 →
        2 ^ U ≤ m ^ 3 →
        (∑ a, ∑ b, residualLambda M R row col a b) ≤
          κ * (U : ENNReal) ^ 4 / (m : ENNReal) := by
  obtain ⟨κ, hκPos, hκTop, hκ⟩ :=
    existsAbsoluteResidualLambdaCubicBound
  have heulerPos : 0 < eulerENNReal := by
    rw [eulerENNReal, ENNReal.ofReal_pos]
    exact Real.exp_pos 1
  have heulerTop : eulerENNReal ≠ ∞ := by
    unfold eulerENNReal
    exact ENNReal.ofReal_ne_top
  refine ⟨κ * eulerENNReal ^ 3, ?_, ?_, ?_⟩
  · exact ENNReal.mul_pos hκPos.ne'
      (pow_ne_zero 3 heulerPos.ne')
  · exact ENNReal.mul_ne_top hκTop
      (ENNReal.pow_ne_top heulerTop)
  · intro A B _ _ _ _ M U R m row col hm hrowTotal hcolTotal
      hrowCap hcolCap hR hpow
    have htheta : ∀ a b, (a, b) ∉ M →
        (configurationCellTheta row col m a b).toReal ≤
          Real.exp 1 * (U : ℝ) ^ 2 / (m : ℝ) := by
      intro a b _hab
      exact configurationCellTheta_toReal_le_of_caps
        row col m U a b hm (hrowCap a) (hcolCap b)
    have hpoint : ∀ a b,
        residualLambda M R row col a b ≤
          κ * configurationCellTheta row col m a b ^ 3 :=
      hκ M U R m row col hm hrowTotal hR htheta hpow
    calc
      (∑ a, ∑ b, residualLambda M R row col a b) ≤
          ∑ a, ∑ b,
            κ * configurationCellTheta row col m a b ^ 3 := by
        exact Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => hpoint a b
      _ = κ *
          (∑ a, ∑ b,
            configurationCellTheta row col m a b ^ 3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ ≤ κ *
          (eulerENNReal ^ 3 * (U : ENNReal) ^ 4 /
            (m : ENNReal)) := by
        simpa only [mul_comm] using
          (mul_le_mul_right
            (sum_configurationCellTheta_cube_le row col m U hm
              hrowCap hcolCap hrowTotal hcolTotal) κ)
      _ = (κ * eulerENNReal ^ 3) *
          (U : ENNReal) ^ 4 / (m : ENNReal) := by
        simp only [div_eq_mul_inv, mul_assoc]

#print axioms existsAbsoluteResidualLambdaTotalBound

end

end Erdos625
