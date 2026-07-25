import Erdos625.Section9MatchingRestrictionProduct
import Erdos625.Section9ActualResidualENNRealExpBridge
import Erdos625.Section9FixedFFubiniBridge
import Erdos625.Section9ResidualQQuadratic
import Erdos625.Section9ResidualLambdaTotalBound
import Erdos625.Section9ThetaCap
import Erdos625.ConfigurationThetaMoments
import Mathlib.Tactic

/-!
# Section IX: direct matching-restriction attachment envelope

This module continues the direct matching-restriction route.  It first identifies
its fixed-even-family bound with the literal event-restricted attachment
numerator.  It then proves the global quadratic configuration-theta estimate,
sums the literal residual-q bound at scale `U^2`, and combines the two finite
products into one exponential envelope.

The result is pointwise in the finite residual data.  It does not perform the
Section VIII skeleton sum, specialize to the midpoint profile, or prove
`Erdos625Statement`.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Exact global factorization of the squared configuration-cell parameters. -/
theorem sum_configurationCellTheta_sq_global
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m : ℕ) :
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 2) =
      (eulerENNReal / (m : ENNReal)) ^ 2 *
        (∑ a, (row a : ENNReal) ^ 2) *
        (∑ b, (col b : ENNReal) ^ 2) := by
  calc
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 2) =
        ∑ a, ((eulerENNReal / (m : ENNReal)) ^ 2 *
          (row a : ENNReal) ^ 2) *
          (∑ b, (col b : ENNReal) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [mul_assoc] using
        (sum_configurationCellTheta_sq_row row col m a)
    _ = (∑ a, (eulerENNReal / (m : ENNReal)) ^ 2 *
          (row a : ENNReal) ^ 2) *
          (∑ b, (col b : ENNReal) ^ 2) := by
      rw [Finset.sum_mul]
    _ = ((eulerENNReal / (m : ENNReal)) ^ 2 *
          (∑ a, (row a : ENNReal) ^ 2)) *
          (∑ b, (col b : ENNReal) ^ 2) := by
      rw [Finset.mul_sum]
    _ = (eulerENNReal / (m : ENNReal)) ^ 2 *
        (∑ a, (row a : ENNReal) ^ 2) *
        (∑ b, (col b : ENNReal) ^ 2) := by
      rfl

/-- Under equal positive total mass and degree caps, the complete quadratic
configuration-theta mass is at most `e^2 U^2`. -/
theorem sum_configurationCellTheta_sq_le_euler_sq_cap_sq
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m U : ℕ)
    (hm : 0 < m)
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (hrowTotal : ∑ a, row a = m) (hcolTotal : ∑ b, col b = m) :
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 2) ≤
      eulerENNReal ^ 2 * (U : ENNReal) ^ 2 := by
  have hrow :=
    degreeSquareSum_ennreal_le_cap_mul_total row U m hrowCap hrowTotal
  have hcol :=
    degreeSquareSum_ennreal_le_cap_mul_total col U m hcolCap hcolTotal
  calc
    (∑ a, ∑ b, configurationCellTheta row col m a b ^ 2) =
        (eulerENNReal / (m : ENNReal)) ^ 2 *
          (∑ a, (row a : ENNReal) ^ 2) *
          (∑ b, (col b : ENNReal) ^ 2) :=
      sum_configurationCellTheta_sq_global row col m
    _ ≤ (eulerENNReal / (m : ENNReal)) ^ 2 *
          ((U : ENNReal) * (m : ENNReal)) *
          (∑ b, (col b : ENNReal) ^ 2) :=
      mul_le_mul_left
        (mul_le_mul_right hrow
          ((eulerENNReal / (m : ENNReal)) ^ 2))
        (∑ b, (col b : ENNReal) ^ 2)
    _ ≤ (eulerENNReal / (m : ENNReal)) ^ 2 *
          ((U : ENNReal) * (m : ENNReal)) *
          ((U : ENNReal) * (m : ENNReal)) :=
      mul_le_mul_right hcol
        ((eulerENNReal / (m : ENNReal)) ^ 2 *
          ((U : ENNReal) * (m : ENNReal)))
    _ = eulerENNReal ^ 2 * (U : ENNReal) ^ 2 := by
      have hm0 : (m : ENNReal) ≠ 0 := by
        exact_mod_cast hm.ne'
      have hmt : (m : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top m
      rw [div_eq_mul_inv]
      calc
        (eulerENNReal * (m : ENNReal)⁻¹) ^ 2 *
            ((U : ENNReal) * (m : ENNReal)) *
            ((U : ENNReal) * (m : ENNReal)) =
          eulerENNReal ^ 2 * (U : ENNReal) ^ 2 *
            ((m : ENNReal) * (m : ENNReal)⁻¹) ^ 2 := by
          ring
        _ = eulerENNReal ^ 2 * (U : ENNReal) ^ 2 := by
          rw [ENNReal.mul_inv_cancel hm0 hmt, one_pow, mul_one]

/-- One absolute finite constant bounds the total literal residual-q mass at
scale `U^2`, with no factor depending on the number of row or column types. -/
theorem existsAbsoluteResidualQTotalBound_of_degreeCaps :
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
        (∑ a, ∑ b, residualQ M R row col a b) ≤
          κ * (U : ENNReal) ^ 2 := by
  obtain ⟨K, hKpos, hKtop, hquadratic⟩ :=
    existsAbsoluteResidualQQuadraticBound
  have heulerPos : 0 < eulerENNReal := by
    rw [eulerENNReal, ENNReal.ofReal_pos]
    exact Real.exp_pos 1
  have heulerTop : eulerENNReal ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨K * eulerENNReal ^ 2,
    ENNReal.mul_pos hKpos.ne' (pow_ne_zero 2 heulerPos.ne'),
    ENNReal.mul_ne_top hKtop (ENNReal.pow_ne_top heulerTop), ?_⟩
  intro A B _ _ _ _ M U R m row col hm hrowTotal hcolTotal
    hrowCap hcolCap hR hpow
  have htheta : ∀ a b, (a, b) ∉ M →
      (configurationCellTheta row col m a b).toReal ≤
        Real.exp 1 * (U : ℝ) ^ 2 / (m : ℝ) := by
    intro a b _
    exact configurationCellTheta_toReal_le_of_caps
      row col m U a b hm (hrowCap a) (hcolCap b)
  have hqtheta : ∀ a b,
      residualQ M R row col a b ≤
        K * configurationCellTheta row col m a b ^ 2 :=
    hquadratic M U R m row col hm hrowTotal hR htheta hpow
  calc
    (∑ a, ∑ b, residualQ M R row col a b) ≤
        ∑ a, ∑ b,
          K * configurationCellTheta row col m a b ^ 2 := by
      exact Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ => hqtheta a b
    _ = K * (∑ a, ∑ b,
          configurationCellTheta row col m a b ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ ≤ K * (eulerENNReal ^ 2 * (U : ENNReal) ^ 2) :=
      mul_le_mul_right
        (sum_configurationCellTheta_sq_le_euler_sq_cap_sq
          row col m U hm hrowCap hcolCap hrowTotal hcolTotal) K
    _ = (K * eulerENNReal ^ 2) * (U : ENNReal) ^ 2 := by
      ring

/-- The literal event-restricted attachment numerator inherits the direct
matching-restriction product bound through the exact fixed-family Fubini
identity. -/
theorem residualActualAttachmentNumerator_le_lambdaProduct_mul_matchingProduct
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row)
    (hM : IsBipartiteMatching M) :
    residualActualAttachmentNumerator M R row col htotal ≤
      (∏ a : A, ∏ b : B, (1 + residualLambda M R row col a b)) *
      (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
        (1 + residualQ M R row col e.1 e.2)) := by
  rw [residualActualAttachmentNumerator_eq_residualCappedEvenFixedFSum]
  exact residualCappedEvenFixedFSum_le_lambdaProduct_mul_matchingProduct
    M R row col htotal hm hM

/-- Generic exponential endpoint for the lambda product and the direct
outside-matching residual-q product. -/
theorem lambda_matching_products_le_exp_of_sum_bounds
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (lambda q : A → B → ENNReal) (M : Finset (A × B))
    (lambdaBound qBound : ENNReal)
    (hlambda : (∑ a, ∑ b, lambda a b) ≤ lambdaBound)
    (hq : (∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
      q e.1 e.2) ≤ qBound) :
    ((∏ a, ∏ b, (1 + lambda a b)) *
      (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
        (1 + q e.1 e.2))) ≤
      EReal.exp (((lambdaBound + qBound : ENNReal) : EReal)) := by
  have hlambdaProduct :
      (∏ a, ∏ b, (1 + lambda a b)) ≤
        EReal.exp (((∑ a, ∑ b, lambda a b : ENNReal) : EReal)) := by
    rw [← Fintype.prod_prod_type', ← Fintype.sum_prod_type']
    exact ennreal_polymer_product_le_ereal_exp_sum
      (Finset.univ : Finset (A × B)) (fun x => lambda x.1 x.2)
  have hqProduct :
      (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
        (1 + q e.1 e.2)) ≤
        EReal.exp (((∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
          q e.1 e.2 : ENNReal) : EReal)) :=
    ennreal_polymer_product_le_ereal_exp_sum
      ((Finset.univ : Finset (A × B)) \ M) (fun e => q e.1 e.2)
  calc
    ((∏ a, ∏ b, (1 + lambda a b)) *
        (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
          (1 + q e.1 e.2))) ≤
      EReal.exp (((∑ a, ∑ b, lambda a b : ENNReal) : EReal)) *
        EReal.exp (((∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
          q e.1 e.2 : ENNReal) : EReal)) :=
      mul_le_mul' hlambdaProduct hqProduct
    _ = EReal.exp
        ((((∑ a, ∑ b, lambda a b : ENNReal) : EReal)) +
          (((∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
            q e.1 e.2 : ENNReal) : EReal))) := by
      rw [EReal.exp_add]
    _ = EReal.exp
        ((((∑ a, ∑ b, lambda a b : ENNReal) +
          ∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
            q e.1 e.2 : ENNReal) : EReal)) := by
      rw [EReal.coe_ennreal_add]
    _ ≤ EReal.exp (((lambdaBound + qBound : ENNReal) : EReal)) := by
      rw [EReal.exp_le_exp_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact add_le_add hlambda hq

/-- Direct finite large-residual attachment envelope.  It has no traversal
parameter and no dependence on the number of profile blocks or matching edges. -/
theorem exists_absolute_residualActualAttachmentNumerator_le_matchingEnvelope :
    ∃ kappaLambda kappaQ : ENNReal,
      0 < kappaLambda ∧ kappaLambda ≠ ∞ ∧
      0 < kappaQ ∧ kappaQ ≠ ∞ ∧
      ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (M : Finset (A × B)) (U m : ℕ)
          (row : A → ℕ) (col : B → ℕ)
          (htotal : Finset.univ.sum row = Finset.univ.sum col),
        IsBipartiteMatching M →
        0 < m →
        (∑ a, row a) = m →
        (∑ b, col b) = m →
        (∀ a, row a ≤ U) →
        (∀ b, col b ≤ U) →
        2 ^ U ≤ m ^ 3 →
        ((residualActualAttachmentNumerator M (U / 2) row col htotal :
          ENNReal) : EReal) ≤
          EReal.exp
            (((kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
              kappaQ * (U : ENNReal) ^ 2 : ENNReal) : EReal)) := by
  obtain ⟨kappaLambda, hkLpos, hkLtop, hkL⟩ :=
    existsAbsoluteResidualLambdaTotalBound
  obtain ⟨kappaQ, hkQpos, hkQtop, hkQ⟩ :=
    existsAbsoluteResidualQTotalBound_of_degreeCaps
  refine ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, ?_⟩
  intro A B _ _ _ _ M U m row col htotal hM hm hrow hcol
    hrowCap hcolCap hpow
  have hbridge :=
    residualActualAttachmentNumerator_le_lambdaProduct_mul_matchingProduct
      M (U / 2) row col htotal (by simpa [hrow] using hm) hM
  have hlambda :=
    hkL M U (U / 2) m row col hm hrow hcol hrowCap hcolCap rfl hpow
  have hqAll :=
    hkQ M U (U / 2) m row col hm hrow hcol hrowCap hcolCap rfl hpow
  have hqFull :
      (∑ e : A × B, residualQ M (U / 2) row col e.1 e.2) ≤
        kappaQ * (U : ENNReal) ^ 2 := by
    simpa only [Fintype.sum_prod_type'] using hqAll
  have hqOutside :
      (∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
        residualQ M (U / 2) row col e.1 e.2) ≤
        kappaQ * (U : ENNReal) ^ 2 := by
    calc
      (∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
          residualQ M (U / 2) row col e.1 e.2) ≤
        ∑ e ∈ (Finset.univ : Finset (A × B)),
          residualQ M (U / 2) row col e.1 e.2 := by
        exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
      _ = ∑ e : A × B,
          residualQ M (U / 2) row col e.1 e.2 := by
        simp
      _ ≤ kappaQ * (U : ENNReal) ^ 2 := hqFull
  have hproduct :=
    lambda_matching_products_le_exp_of_sum_bounds
      (residualLambda M (U / 2) row col)
      (residualQ M (U / 2) row col) M
      (kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal))
      (kappaQ * (U : ENNReal) ^ 2) hlambda hqOutside
  calc
    ((residualActualAttachmentNumerator M (U / 2) row col htotal :
        ENNReal) : EReal) ≤
      (((∏ a : A, ∏ b : B,
          (1 + residualLambda M (U / 2) row col a b)) *
        (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
          (1 + residualQ M (U / 2) row col e.1 e.2)) : ENNReal) : EReal) := by
      exact_mod_cast hbridge
    _ ≤ EReal.exp
        (((kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
          kappaQ * (U : ENNReal) ^ 2 : ENNReal) : EReal)) :=
      hproduct

#print axioms sum_configurationCellTheta_sq_global
#print axioms sum_configurationCellTheta_sq_le_euler_sq_cap_sq
#print axioms existsAbsoluteResidualQTotalBound_of_degreeCaps
#print axioms residualActualAttachmentNumerator_le_lambdaProduct_mul_matchingProduct
#print axioms lambda_matching_products_le_exp_of_sum_bounds
#print axioms exists_absolute_residualActualAttachmentNumerator_le_matchingEnvelope

end

end Erdos625
