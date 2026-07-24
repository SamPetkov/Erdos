import Erdos625.ProfileValueStabilityS4
import Mathlib.Tactic

namespace Erdos625.ProfileEntropyS4

noncomputable section

set_option autoImplicit false

/-- At an interior target, the optimized entropy-plus-score value is monotone in every score coordinate. -/
theorem optimizedValue_mono_scores
    (h g : Fin 4 → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5)
    (h_le : ∀ i, h i ≤ g i) :
    optimizedValue h T ≤ optimizedValue g T := by
  have hscore :
      (∑ i : Fin 4, optimizer h T i * h i) ≤
        ∑ i : Fin 4, optimizer h T i * g i := by
    apply Finset.sum_le_sum
    intro i _hi
    exact mul_le_mul_of_nonneg_left (h_le i) (optimizer_nonneg h T i)
  have hhEq :=
    optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target h hT
  have hgLe := entropy_score_le_log_partition_sub_tilt_mul_target
    g (optimizer h T) hT (optimizer_nonneg h T) (sum_optimizer h T)
      (sum_optimizer_mul_support h hT)
  simp only [optimizedValue]
  linarith

end

end Erdos625.ProfileEntropyS4
