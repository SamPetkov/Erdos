import Erdos625.Section9MatchingRestrictionEnvelope
import Mathlib.Tactic

/-!
# Section IX: absorb the local increment product into the residual-q mass

The direct matching-restriction route initially keeps two products: one for the
unselected local increments `residualLambda`, and one for the selected-edge
weight `residualQ`.  Since

`residualQ = theta^2 / 2 + residualLambda`

outside the exposed matching (and both quantities vanish on it), the lambda
mass is pointwise dominated by the q mass.  Consequently both products are
controlled by the same total q sum.  This removes the separate cubic
`U^4 / m` estimate from the final finite attachment envelope.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The local-increment weight is pointwise dominated by the selected-edge
weight. -/
theorem residualLambda_le_residualQ
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (a : A) (b : B) :
    residualLambda M R row col a b ≤ residualQ M R row col a b := by
  classical
  unfold residualQ residualLambda
  by_cases hM : (a, b) ∈ M
  · simp [hM]
  · simp only [hM, if_false]
    exact le_add_of_nonneg_left (by positivity)

/-- If `lambda` is pointwise bounded by `q`, then the lambda product and the
direct outside-matching q product are jointly bounded by twice one total q
mass. -/
theorem lambda_matching_products_le_exp_two_q_bound
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (lambda q : A → B → ENNReal) (M : Finset (A × B))
    (qBound : ENNReal)
    (hlq : ∀ a b, lambda a b ≤ q a b)
    (hqall : (∑ a, ∑ b, q a b) ≤ qBound) :
    ((∏ a, ∏ b, (1 + lambda a b)) *
      (∏ e ∈ (Finset.univ : Finset (A × B)) \ M,
        (1 + q e.1 e.2))) ≤
      EReal.exp (((2 * qBound : ENNReal) : EReal)) := by
  have hlambda : (∑ a, ∑ b, lambda a b) ≤ qBound := by
    apply le_trans _ hqall
    exact Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum fun b _ => hlq a b
  have hqOutside :
      (∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
        q e.1 e.2) ≤ qBound := by
    apply le_trans _ hqall
    calc
      (∑ e ∈ (Finset.univ : Finset (A × B)) \ M,
          q e.1 e.2) ≤
        ∑ e ∈ (Finset.univ : Finset (A × B)), q e.1 e.2 := by
          exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
      _ = ∑ e : A × B, q e.1 e.2 := by simp
      _ = ∑ a, ∑ b, q a b := by
        rw [Fintype.sum_prod_type']
  have h := lambda_matching_products_le_exp_of_sum_bounds
    lambda q M qBound qBound hlambda hqOutside
  simpa [two_mul] using h

/-- Natural ceiling of one third, written without introducing a dependency on
later Section X utilities. -/
def residualCeilThird (U : Nat) : Nat := (U + 2) / 3

/-- The ceiling-third exponent covers `U`. -/
theorem le_three_mul_residualCeilThird (U : Nat) :
    U ≤ 3 * residualCeilThird U := by
  unfold residualCeilThird
  omega

/-- If the quadratic large-residual hypothesis fails, the residual mass is
already below the natural power threshold `2^(ceil(U/3))`.  This gives an
intrinsic alternative to splitting at `n / (log n)^6`. -/
theorem residualMass_lt_two_pow_ceilThird_of_not_cube
    (U m : Nat) (hnot : ¬ 2 ^ U ≤ m ^ 3) :
    m < 2 ^ residualCeilThird U := by
  by_contra h
  have hm : 2 ^ residualCeilThird U ≤ m := Nat.le_of_not_gt h
  have hcube : (2 ^ residualCeilThird U) ^ 3 ≤ m ^ 3 :=
    pow_le_pow_left' hm 3
  have hpow : 2 ^ U ≤ 2 ^ (3 * residualCeilThird U) :=
    pow_le_pow_right₀ (by decide) (le_three_mul_residualCeilThird U)
  apply hnot
  calc
    2 ^ U ≤ 2 ^ (3 * residualCeilThird U) := hpow
    _ = (2 ^ residualCeilThird U) ^ 3 := by
      rw [Nat.mul_comm, pow_mul]
    _ ≤ m ^ 3 := hcube

/-- One absolute finite constant bounds the literal cap/no-return attachment
numerator at scale `U^2`.  No separate lambda-total or cubic degree-moment
estimate is needed. -/
theorem exists_absolute_residualActualAttachmentNumerator_le_qOnlyEnvelope :
    ∃ kappa : ENNReal, 0 < kappa ∧ kappa ≠ ∞ ∧
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
        residualActualAttachmentNumerator M (U / 2) row col htotal ≤
          EReal.exp ((((kappa * (U : ENNReal) ^ 2 : ENNReal)) : EReal)) := by
  obtain ⟨kappaQ, hkQpos, hkQtop, hkQ⟩ :=
    existsAbsoluteResidualQTotalBound_of_degreeCaps
  let kappa : ENNReal := 2 * kappaQ
  have hkappaPos : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hkappaTop : kappa ≠ ∞ := by
    dsimp [kappa]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hkQtop
  refine ⟨kappa, hkappaPos, hkappaTop, ?_⟩
  intro A B _ _ _ _ M U m row col htotal hM hm hrow hcol
    hrowCap hcolCap hpow
  have hbridge :=
    residualActualAttachmentNumerator_le_lambdaProduct_mul_matchingProduct
      M (U / 2) row col htotal (by simpa [hrow] using hm) hM
  have hqAll :=
    hkQ M U (U / 2) m row col hm hrow hcol hrowCap hcolCap rfl hpow
  have hproduct := lambda_matching_products_le_exp_two_q_bound
    (residualLambda M (U / 2) row col)
    (residualQ M (U / 2) row col) M
    (kappaQ * (U : ENNReal) ^ 2)
    (residualLambda_le_residualQ M (U / 2) row col)
    hqAll
  exact hbridge.trans (by
    simpa [kappa, mul_assoc] using hproduct)

#print axioms residualLambda_le_residualQ
#print axioms lambda_matching_products_le_exp_two_q_bound
#print axioms le_three_mul_residualCeilThird
#print axioms residualMass_lt_two_pow_ceilThird_of_not_cube
#print axioms exists_absolute_residualActualAttachmentNumerator_le_qOnlyEnvelope

end

end Erdos625
