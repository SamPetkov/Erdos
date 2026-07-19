import Erdos625.Section9ActualAttachmentPolymerBridge
import Erdos625.Section9LargeResidualEnvelope
import Mathlib.Tactic

/-!
# Section IX: strict large-residual envelope for the literal attachment numerator

This is the finite large-residual branch before any skeleton summation or
asymptotic scale comparison.  In particular, the cap/no-return indicator
remains inside `residualActualAttachmentNumerator`; no conditional-event
probability is introduced or divided out.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- One pair of absolute constants bounds the literal event-restricted
attachment numerator by the coarse strict-regime large-residual envelope.
The result is pointwise in the finite residual data and makes no claim about
the later `O((log n)^8)` comparison or a global skeleton sum. -/
theorem exists_absolute_residualActualAttachmentNumerator_le_largeResidualEnvelope :
    ∃ kappaLambda kappaQ : ENNReal,
      0 < kappaLambda ∧ kappaLambda ≠ ∞ ∧
      0 < kappaQ ∧ kappaQ ≠ ∞ ∧
      ∀ {A B : Type*} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (M : Finset (A × B)) (U m : Nat)
          (row : A → Nat) (col : B → Nat)
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
        ((residualActualAttachmentNumerator M (U / 2) row col htotal :
          ENNReal) : EReal) ≤
          EReal.exp
            ((kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
              2 * (Fintype.card A : ENNReal) *
                (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 +
              (((6 * M.card : Nat) : ENNReal) *
                (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal))) :
                ENNReal) : EReal) := by
  obtain ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, hproduct⟩ :=
    exists_absolute_residual_product_exponential_majorant
  refine ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, ?_⟩
  intro A B _ _ _ _ M U m row col htotal hM hm hrow hcol
    hrowCap hcolCap hpow htau
  have hbridge :=
    residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct
      M (U / 2) row col htotal (by simpa [hrow] using hm)
  have hmajorant := hproduct M U (U / 2) m row col hM hm hrow hcol
    hrowCap hcolCap rfl hpow htau
  have henvelope :=
    residualProductExponentMajorant_le_largeResidualEnvelope
      kappaLambda kappaQ (Fintype.card A) M.card U m (le_of_lt htau)
  calc
    ((residualActualAttachmentNumerator M (U / 2) row col htotal :
        ENNReal) : EReal) ≤
        (((∏ a : A, ∏ b : B,
            (1 + residualLambda M (U / 2) row col a b)) *
          (∏ C ∈ simpleBipartiteCycles A B,
            (1 + edgeWeightOutsideENN
              (residualQ M (U / 2) row col) M C)) : ENNReal) : EReal) := by
      exact_mod_cast hbridge
    _ ≤ (EReal.exp
        ((residualProductExponentMajorant kappaLambda kappaQ
          (Fintype.card A) M.card U m : ENNReal) : EReal) : ENNReal) := by
      exact_mod_cast hmajorant.2.2
    _ ≤ (EReal.exp
        ((kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
          2 * (Fintype.card A : ENNReal) *
            (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 +
          (((6 * M.card : Nat) : ENNReal) *
            (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal))) :
            ENNReal) : EReal) : ENNReal) := by
      rw [EReal.coe_ennreal_le_coe_ennreal_iff, EReal.exp_le_exp_iff,
        EReal.coe_ennreal_le_coe_ennreal_iff]
      exact henvelope

#print axioms exists_absolute_residualActualAttachmentNumerator_le_largeResidualEnvelope

end

end Erdos625
