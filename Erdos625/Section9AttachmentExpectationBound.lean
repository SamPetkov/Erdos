import Erdos625.Section9FixedFFubiniBridge
import Mathlib.Tactic

/-!
# Section IX: raw attachment numerator from a pointwise event bound

This target is deliberately only the elementary finite-PMF step.  It keeps
the cap/no-return indicator inside the numerator and never divides by the
event probability.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- A pointwise upper bound for the literal actual attachment integrand on
the cap/no-return event bounds the raw (not conditional) residual numerator. -/
theorem residualActualAttachmentNumerator_le_of_forall_event_integrand_le
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : Nat) (row : A → Nat) (col : B → Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) (K : ENNReal)
    (hK : ∀ matching : ConfigurationMatching row col,
      matching ∈ ResidualCapNoReturnEvent M R row col →
        (∏ a : A, ∏ b : B,
          (residualReward (configurationCellCount matching a b) : ENNReal)) *
          ((actualResidualEvenEdgeSets M matching).card : ENNReal) ≤ K) :
    residualActualAttachmentNumerator M R row col htotal ≤ K := by
  classical
  unfold residualActualAttachmentNumerator
  calc
    _ ≤ ∑ matching : ConfigurationMatching row col,
        uniformConfigurationMatching row col htotal matching * K := by
      apply Finset.sum_le_sum
      intro matching _
      by_cases hevent : matching ∈ ResidualCapNoReturnEvent M R row col
      · simp only [hevent, if_pos, mul_one]
        rw [mul_assoc]
        exact mul_le_mul_right (hK matching hevent) _
      · simp [hevent]
    _ = (∑ matching : ConfigurationMatching row col,
        uniformConfigurationMatching row col htotal matching) * K := by
      rw [Finset.sum_mul]
    _ = K := by
      rw [show (∑ matching : ConfigurationMatching row col,
          uniformConfigurationMatching row col htotal matching) = 1 by
        rw [← tsum_fintype (L := SummationFilter.unconditional _)]
        exact (uniformConfigurationMatching row col htotal).tsum_coe,
        one_mul]

end

end Erdos625
