import Erdos625.SPlusEntropySupremumDualInterior
import Erdos625.UniformExplicitPartitionRatio

/-!
# Uniform limiting entropy certificate

This assembles the verified limiting entropy-dual and explicit four-size
ratio estimates uniformly over the full phase interval.  The separate module
`SPlusPrimalRepresentation` proves that the entropy value used here is exactly
the direct manuscript primal supremum: its older finite all-tilts field follows
automatically from coordinatewise Gibbs inequalities and nonnegativity.

The proof was returned by Aristotle project
`f916811d-4971-44ae-9c9b-c1d731298958`, task
`d4d1264a-d9da-4673-b646-ff82a272aa71`, and independently audited before
integration.
-/

namespace Erdos625

set_option autoImplicit false

noncomputable section

/-- Limiting form of the Section V uniform entropy certificate. -/
theorem uniform_limiting_entropy_certificate_for_delta
    (delta : ℝ)
    (hDelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ fourEntropyLoss (1 + 2 / q - delta) ∧
      fourEntropyLoss (1 + 2 / q - delta) <
        Real.log (153 / 100 : ℝ) ∧
      Real.log (200 / 153 : ℝ) <
        q - fourEntropyLoss (1 + 2 / q - delta) := by
  rcases hDelta with ⟨hDeltaLower, hDeltaUpper⟩
  have hq_lt_one : q < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num [q] at h ⊢
    exact h
  have hq_gt_half : (1 / 2 : ℝ) < q := by
    have h := Real.log_two_gt_d9
    unfold q
    norm_num at h ⊢
    linarith
  have htwo_div_q_lower : 2 < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    linarith
  have htwo_div_q_upper : 2 / q < 4 := by
    rw [div_lt_iff₀ q_pos]
    linarith
  have hTarget : 1 + 2 / q - delta ∈ Set.Ioo (2 : ℝ) 5 := by
    constructor <;> linarith
  let lambda := ProfileEntropyS4.tilt fourGaussianScore
    (1 + 2 / q - delta)
  have hMean : ProfileEntropyS4.mean fourGaussianScore lambda =
      1 + 2 / q - delta := by
    exact ProfileEntropyS4.mean_tilt_eq fourGaussianScore hTarget
  have hLossLt : fourEntropyLoss (1 + 2 / q - delta) <
      Real.log (153 / 100 : ℝ) := by
    have hDual := extendedGaussianEntropyValue_le_dual_interior
      (tilt := lambda) hTarget
    have hRatio := uniform_four_size_partition_ratio_for_delta delta lambda
      hDeltaLower hDeltaUpper hMean
    simpa [fourEntropyLoss] using
      (entropy_loss_lt_log_153_div_100_of_dual_ratio hMean hDual hRatio)
  exact ⟨fourEntropyLoss_nonneg_interior hTarget, hLossLt,
    signed_margin_gt_log_200_div_153_of_entropy_loss_lt hLossLt⟩

end

end Erdos625
