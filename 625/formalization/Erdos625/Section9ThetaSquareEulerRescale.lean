import Erdos625.ConfigurationModelProbability
import Mathlib.Tactic

/-!
# Section IX: Euler rescaling of the cell parameter

This module is a finite algebraic bridge.  It rewrites a pointwise quadratic
bound in the configuration-cell parameter as a degree-square bound with the
required factor `e^2`.  It does not provide a residual conditioned law, a
degree cap, or an asymptotic estimate.
-/

universe u v

namespace Erdos625

open scoped ENNReal

noncomputable section

/-- A pointwise `K * theta^2` bound rewrites exactly as a degree-square bound
with coefficient `K * e^2`. -/
theorem rescale_configurationCellTheta_square_to_degreeSquare
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m : ℕ)
    (q : A → B → ℝ≥0∞) (K : ℝ≥0∞)
    (hKpos : 0 < K) (hKtop : K ≠ ∞)
    (hq : ∀ a b,
      q a b ≤ K * configurationCellTheta row col m a b ^ 2) :
    0 < K * eulerENNReal ^ 2 ∧
      K * eulerENNReal ^ 2 ≠ ∞ ∧
      ∀ a b,
        q a b ≤
          (K * eulerENNReal ^ 2) *
            (row a : ℝ≥0∞) ^ 2 * (col b : ℝ≥0∞) ^ 2 /
              (m : ℝ≥0∞) ^ 2 := by
  have heulerPos : 0 < eulerENNReal := by
    rw [eulerENNReal, ENNReal.ofReal_pos]
    exact Real.exp_pos 1
  have heulerFinite : eulerENNReal ≠ ∞ := by
    exact ENNReal.ofReal_ne_top
  have heulerNe : eulerENNReal ≠ 0 := heulerPos.ne'
  refine ⟨pos_iff_ne_zero.mpr
      (mul_ne_zero hKpos.ne' (pow_ne_zero 2 heulerNe)), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hKtop (ENNReal.pow_ne_top heulerFinite)
  · intro a b
    calc
      q a b ≤ K * configurationCellTheta row col m a b ^ 2 := hq a b
      _ = (K * eulerENNReal ^ 2) *
            (row a : ℝ≥0∞) ^ 2 * (col b : ℝ≥0∞) ^ 2 /
              (m : ℝ≥0∞) ^ 2 := by
        unfold configurationCellTheta
        simp only [div_eq_mul_inv]
        rw [ENNReal.inv_pow]
        ring

#print axioms rescale_configurationCellTheta_square_to_degreeSquare

end

end Erdos625
