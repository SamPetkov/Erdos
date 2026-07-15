import Erdos625.Section9ResidualQQuadratic
import Erdos625.Section9ThetaSquareEulerRescale
import Erdos625.Section9QDegreeBound
import Erdos625.Section9ThetaCap

/-!
# Section IX: conditional residual-kernel row and column bound

This module composes the established finite analytic residual-q estimate with
the exact Euler rescaling and deterministic degree-sum bound.  The base
theorem keeps every configuration-model cap, total, and theta hypothesis
explicit; the second theorem discharges the theta cap deterministically from
the degree caps.  Neither theorem identifies a conditioned residual random
family or assembles the manuscript's Lemma 9.1.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Under the explicit finite endpoint, degree-cap, total-mass, and
configuration-cell hypotheses, one absolute constant bounds both residual-q
row and column sums at scale `U^3 / m`. -/
theorem existsAbsoluteResidualQRowColumnBound :
    ∃ κ : ℝ≥0∞, 0 < κ ∧ κ ≠ ∞ ∧
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
        (∀ a b, (a, b) ∉ M →
          (configurationCellTheta row col m a b).toReal ≤
            Real.exp 1 * (U : ℝ) ^ 2 / (m : ℝ)) →
        2 ^ U ≤ m ^ 3 →
        (∀ a, ∑ b, residualQ M R row col a b ≤
          κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) ∧
        (∀ b, ∑ a, residualQ M R row col a b ≤
          κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) := by
  obtain ⟨K, hKpos, hKtop, hquadratic⟩ :=
    existsAbsoluteResidualQQuadraticBound
  have heulerPos : 0 < eulerENNReal := by
    rw [eulerENNReal, ENNReal.ofReal_pos]
    exact Real.exp_pos 1
  have heulerFinite : eulerENNReal ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have heulerNe : eulerENNReal ≠ 0 := heulerPos.ne'
  refine ⟨K * eulerENNReal ^ 2, pos_iff_ne_zero.mpr
    (mul_ne_zero hKpos.ne' (pow_ne_zero 2 heulerNe)),
    ENNReal.mul_ne_top hKtop (ENNReal.pow_ne_top heulerFinite), ?_⟩
  intro A B _ _ _ _ M U R m row col hm hrowTotal hcolTotal hrowCap hcolCap
    hR htheta hpow
  have hqtheta : ∀ a b,
      residualQ M R row col a b ≤
        K * configurationCellTheta row col m a b ^ 2 :=
    hquadratic M U R m row col hm hrowTotal hR htheta hpow
  have hdegree := rescale_configurationCellTheta_square_to_degreeSquare
    row col m (residualQ M R row col) K hKpos hKtop hqtheta
  exact q_row_column_le_of_pointwise_degree_square
    row col (residualQ M R row col) U m (K * eulerENNReal ^ 2)
    hm hrowTotal hcolTotal hrowCap hcolCap hdegree.2.2

#print axioms existsAbsoluteResidualQRowColumnBound

/-- The preceding residual-q row and column estimate with its deterministic
theta-cap antecedent discharged from the row and column degree caps.  This
does not identify the conditioned residual family or prove any attachment
estimate. -/
theorem existsAbsoluteResidualQRowColumnBound_of_degreeCaps :
    ∃ κ : ℝ≥0∞, 0 < κ ∧ κ ≠ ∞ ∧
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
        (∀ a, ∑ b, residualQ M R row col a b ≤
          κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) ∧
        (∀ b, ∑ a, residualQ M R row col a b ≤
          κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) := by
  obtain ⟨κ, hκpos, hκtop, hκ⟩ :=
    existsAbsoluteResidualQRowColumnBound
  refine ⟨κ, hκpos, hκtop, ?_⟩
  intro A B _ _ _ _ M U R m row col hm hrowTotal hcolTotal hrowCap hcolCap
    hR hpow
  exact hκ M U R m row col hm hrowTotal hcolTotal hrowCap hcolCap hR
    (fun a b _ ↦ configurationCellTheta_toReal_le_of_caps
      row col m U a b hm (hrowCap a) (hcolCap b)) hpow

#print axioms existsAbsoluteResidualQRowColumnBound_of_degreeCaps

end

end Erdos625
