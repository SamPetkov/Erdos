import Erdos625.Section9ERealENNRealExpTransport

/-!
# Section IX finite large-residual attachment endpoint

This module transports the established `EReal.exp` large-residual envelope to
a finite `ENNReal.ofReal (Real.exp ...)` bound while retaining the literal
cap/no-return residual attachment numerator.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- One pair of absolute constants bounds the literal cap/no-return residual
attachment numerator by the finite large-residual exponential endpoint. -/
theorem exists_absolute_residualActualAttachmentNumerator_le_largeResidualExp :
    ∃ kappaLambda kappaQ : ENNReal,
      0 < kappaLambda ∧ kappaLambda ≠ ∞ ∧
      0 < kappaQ ∧ kappaQ ≠ ∞ ∧
      ∀ {A B : Type*} [Fintype A] [Fintype B]
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
        kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal) <
          (1 / 3 : ENNReal) →
        residualActualAttachmentNumerator M (U / 2) row col htotal ≤
          ENNReal.ofReal
            (Real.exp
              ((kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
                2 * (Fintype.card A : ENNReal) *
                  (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 +
                (((6 * M.card : ℕ) : ENNReal) *
                  (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) :
                  ENNReal)).toReal)) := by
  obtain ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, henvelope⟩ :=
    exists_absolute_residualActualAttachmentNumerator_le_largeResidualEnvelope
  refine ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, ?_⟩
  intro A B _ _ _ _ M U m row col htotal hM hm hrow hcol
    hrowCap hcolCap hpow htau
  apply ennreal_le_of_coe_le_ereal_exp_toReal
  · exact residualLargeEnvelope_ne_top kappaLambda kappaQ
      (Fintype.card A) M.card U m hkLtop hkQtop hm
  · exact henvelope M U m row col htotal hM hm hrow hcol
      hrowCap hcolCap hpow htau

end


end Erdos625
