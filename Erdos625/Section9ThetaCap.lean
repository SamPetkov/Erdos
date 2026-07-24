import Erdos625.ConfigurationModelProbability
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# Section IX: deterministic configuration-cell cap

This file records the elementary cap on the configuration-cell parameter that
follows directly from positive total mass and pointwise row and column degree
caps.  It is deliberately a deterministic inequality: it does not assert a
conditioned residual law or any attachment estimate.
-/

namespace Erdos625

open scoped ENNReal

noncomputable section

/-- A positive total mass and pointwise row and column caps imply the
configuration-cell theta cap used by the finite residual-kernel estimates. -/
theorem configurationCellTheta_toReal_le_of_caps
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ) (a : A) (b : B)
    (hm : 0 < m) (hrow : row a ≤ U) (hcol : col b ≤ U) :
    (configurationCellTheta row col m a b).toReal ≤
      Real.exp 1 * (U : ℝ) ^ 2 / (m : ℝ) := by
  have hrowENN : (row a : ℝ≥0∞) ≤ (U : ℝ≥0∞) := by
    exact_mod_cast hrow
  have hcolENN : (col b : ℝ≥0∞) ≤ (U : ℝ≥0∞) := by
    exact_mod_cast hcol
  have hproduct :
      (row a : ℝ≥0∞) * (col b : ℝ≥0∞) ≤
        (U : ℝ≥0∞) * (U : ℝ≥0∞) := by
    exact mul_le_mul hrowENN hcolENN bot_le bot_le
  have hnum :
      eulerENNReal * (row a : ℝ≥0∞) * (col b : ℝ≥0∞) ≤
        eulerENNReal * (U : ℝ≥0∞) ^ 2 := by
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_right hproduct eulerENNReal
  have htheta :
      configurationCellTheta row col m a b ≤
        eulerENNReal * (U : ℝ≥0∞) ^ 2 / (m : ℝ≥0∞) := by
    unfold configurationCellTheta
    exact ENNReal.div_le_div_right hnum _
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hm.ne'
  have heulerTop : eulerENNReal ≠ ∞ := ENNReal.ofReal_ne_top
  have hUTop : (U : ℝ≥0∞) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top U)
  have hcapTop :
      eulerENNReal * (U : ℝ≥0∞) ^ 2 / (m : ℝ≥0∞) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top heulerTop hUTop) hm0
  have hreal := ENNReal.toReal_mono hcapTop htheta
  have heulerToReal : eulerENNReal.toReal = Real.exp 1 := by
    rw [eulerENNReal, ENNReal.toReal_ofReal (Real.exp_pos 1).le]
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, heulerToReal] using hreal

#print axioms configurationCellTheta_toReal_le_of_caps

end

end Erdos625
