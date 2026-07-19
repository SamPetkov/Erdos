import Erdos625.SignedFourSizeObjective
import Erdos625.ExtendedGaussianProfile
import Erdos625.ExplicitPartitionRatio
import Mathlib.Tactic

/-!
# Conditional entropy certificate for the signed four-size profile

This module formalizes the *algebraic endpoint* of manuscript Lemma 5.1.
It deliberately does not claim the missing analytic estimate

`D₄ < log (153 / 100)`.

The current development contains the four-point optimizer and the limiting
extended-Gaussian `S₊` partition, but it does not yet define an `S₊` entropy
value or prove the omitted-tail partition-ratio estimate.  Accordingly, the
two hypotheses carrying those obligations below are named
`h_unrestricted_dual_upper` and `h_partition_ratio_bound`.
-/

open scoped Topology

namespace Erdos625

noncomputable section

/-! ## The exact numerical endpoint -/

/-- The two logarithmic constants in Lemma 5.1 fit exactly. -/
theorem q_sub_log_153_div_100_eq_log_200_div_153 :
    q - Real.log (153 / 100 : ℝ) = Real.log (200 / 153 : ℝ) := by
  unfold q
  rw [← Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (153 / 100 : ℝ) ≠ 0)]
  norm_num

/-- The explicit manuscript margin is positive. -/
theorem log_200_div_153_pos : 0 < Real.log (200 / 153 : ℝ) := by
  exact Real.log_pos (by norm_num : (1 : ℝ) < 200 / 153)

/-- The smallest conditional endpoint of the entropy certificate: a strict
loss bound by `log (153 / 100)` leaves the stated signed margin. -/
theorem signed_margin_gt_log_200_div_153_of_entropy_loss_lt
    {entropyLoss : ℝ}
    (h_entropy_loss_lt : entropyLoss < Real.log (153 / 100 : ℝ)) :
    Real.log (200 / 153 : ℝ) < q - entropyLoss := by
  rw [← q_sub_log_153_div_100_eq_log_200_div_153]
  linarith

/-! ## A dual-ratio bridge to the endpoint -/

/-- The `S₊` dual expression evaluated at an arbitrary tilt.  This is only a
dual test value; it is not presented as a defined or optimized `S₊` entropy. -/
noncomputable def extendedGaussianDualTestValue (target tilt : ℝ) : ℝ :=
  Real.log (extendedGaussianPartition q tilt) - tilt * target

/-- At its own mean, the limiting four-point entropy is exactly its dual
expression at the given tilt. -/
theorem fourGaussianEntropy_eq_dual_at_mean (tilt : ℝ) :
    ProfileEntropyS4.optimizedValue fourGaussianScore
        (ProfileEntropyS4.mean fourGaussianScore tilt) =
      Real.log (ProfileEntropyS4.partition fourGaussianScore tilt) -
        tilt * ProfileEntropyS4.mean fourGaussianScore tilt := by
  have h_target : ProfileEntropyS4.mean fourGaussianScore tilt ∈
      Set.Ioo (2 : ℝ) 5 :=
    ProfileEntropyS4.mean_mem_Ioo fourGaussianScore tilt
  have h_tilt : tilt =
      ProfileEntropyS4.tilt fourGaussianScore
        (ProfileEntropyS4.mean fourGaussianScore tilt) :=
    ProfileEntropyS4.eq_tilt_of_mean_eq fourGaussianScore h_target rfl
  unfold ProfileEntropyS4.optimizedValue
  rw [← h_tilt]

/-- A dual upper bound for an explicitly supplied unrestricted entropy value
converts to a bound by the ratio of its partition function to the four-point
partition function.  `h_unrestricted_dual_upper` is the variational direction
that remains to be supplied for the manuscript's actual `S₊` entropy. -/
theorem entropy_loss_le_log_partition_ratio
    {unrestrictedEntropy target tilt : ℝ}
    (h_mean : ProfileEntropyS4.mean fourGaussianScore tilt = target)
    (h_unrestricted_dual_upper :
      unrestrictedEntropy ≤ extendedGaussianDualTestValue target tilt) :
    unrestrictedEntropy -
        ProfileEntropyS4.optimizedValue fourGaussianScore target ≤
      Real.log
        (extendedGaussianPartition q tilt /
          ProfileEntropyS4.partition fourGaussianScore tilt) := by
  have h_target : target ∈ Set.Ioo (2 : ℝ) 5 := by
    simpa only [h_mean] using
      (ProfileEntropyS4.mean_mem_Ioo fourGaussianScore tilt)
  have h_tilt : tilt = ProfileEntropyS4.tilt fourGaussianScore target :=
    ProfileEntropyS4.eq_tilt_of_mean_eq fourGaussianScore h_target h_mean
  have h_four : ProfileEntropyS4.optimizedValue fourGaussianScore target =
      Real.log (ProfileEntropyS4.partition fourGaussianScore tilt) -
        tilt * target := by
    unfold ProfileEntropyS4.optimizedValue
    rw [← h_tilt]
  have h_extended_pos : 0 < extendedGaussianPartition q tilt :=
    extendedGaussianPartition_pos q_pos
  have h_four_pos : 0 < ProfileEntropyS4.partition fourGaussianScore tilt :=
    ProfileEntropyS4.partition_pos fourGaussianScore tilt
  rw [h_four]
  calc
    unrestrictedEntropy -
        (Real.log (ProfileEntropyS4.partition fourGaussianScore tilt) -
          tilt * target) ≤
        extendedGaussianDualTestValue target tilt -
          (Real.log (ProfileEntropyS4.partition fourGaussianScore tilt) -
            tilt * target) :=
      sub_le_sub_right h_unrestricted_dual_upper _
    _ = Real.log
        (extendedGaussianPartition q tilt /
          ProfileEntropyS4.partition fourGaussianScore tilt) := by
      unfold extendedGaussianDualTestValue
      rw [Real.log_div h_extended_pos.ne' h_four_pos.ne']
      ring

/-- The still-unproved explicit tail-ratio estimate, together with the
unrestricted dual upper bound, supplies exactly the manuscript entropy-loss
inequality.  No numerical approximation is used here. -/
theorem entropy_loss_lt_log_153_div_100_of_dual_ratio
    {unrestrictedEntropy target tilt : ℝ}
    (h_mean : ProfileEntropyS4.mean fourGaussianScore tilt = target)
    (h_unrestricted_dual_upper :
      unrestrictedEntropy ≤ extendedGaussianDualTestValue target tilt)
    (h_partition_ratio_bound :
      extendedGaussianPartition q tilt /
          ProfileEntropyS4.partition fourGaussianScore tilt <
        (153 / 100 : ℝ)) :
    unrestrictedEntropy -
        ProfileEntropyS4.optimizedValue fourGaussianScore target <
      Real.log (153 / 100 : ℝ) := by
  have h_loss := entropy_loss_le_log_partition_ratio h_mean
    h_unrestricted_dual_upper
  have h_ratio_pos : 0 <
      extendedGaussianPartition q tilt /
        ProfileEntropyS4.partition fourGaussianScore tilt :=
    div_pos (extendedGaussianPartition_pos q_pos)
      (ProfileEntropyS4.partition_pos fourGaussianScore tilt)
  have h_log_ratio_lt :
      Real.log
        (extendedGaussianPartition q tilt /
          ProfileEntropyS4.partition fourGaussianScore tilt) <
        Real.log (153 / 100 : ℝ) :=
    Real.strictMonoOn_log h_ratio_pos (by norm_num) h_partition_ratio_bound
  exact h_loss.trans_lt h_log_ratio_lt

/-- At the manuscript-selected tilt and its induced target, the numerical
partition-ratio input is unconditional. -/
theorem entropy_loss_lt_log_153_div_100_at_selected_tilt
    {unrestrictedEntropy : ℝ}
    (h_unrestricted_dual_upper :
      unrestrictedEntropy ≤ extendedGaussianDualTestValue
        signedFourSelectedTarget signedFourSelectedTilt) :
    unrestrictedEntropy -
        ProfileEntropyS4.optimizedValue fourGaussianScore
          signedFourSelectedTarget <
      Real.log (153 / 100 : ℝ) := by
  exact entropy_loss_lt_log_153_div_100_of_dual_ratio
    selectedTilt_mean_eq_target h_unrestricted_dual_upper
    selectedTilt_partition_ratio_lt

/-- A complete conditional bridge from the two named missing analytic inputs
to the explicit signed four-size margin `log (200 / 153)`. -/
theorem signed_margin_gt_log_200_div_153_of_dual_ratio
    {unrestrictedEntropy target tilt : ℝ}
    (h_mean : ProfileEntropyS4.mean fourGaussianScore tilt = target)
    (h_unrestricted_dual_upper :
      unrestrictedEntropy ≤ extendedGaussianDualTestValue target tilt)
    (h_partition_ratio_bound :
      extendedGaussianPartition q tilt /
          ProfileEntropyS4.partition fourGaussianScore tilt <
        (153 / 100 : ℝ)) :
    Real.log (200 / 153 : ℝ) <
      q -
        (unrestrictedEntropy -
          ProfileEntropyS4.optimizedValue fourGaussianScore target) := by
  apply signed_margin_gt_log_200_div_153_of_entropy_loss_lt
  exact entropy_loss_lt_log_153_div_100_of_dual_ratio h_mean
    h_unrestricted_dual_upper h_partition_ratio_bound

end

#print axioms q_sub_log_153_div_100_eq_log_200_div_153
#print axioms log_200_div_153_pos
#print axioms signed_margin_gt_log_200_div_153_of_entropy_loss_lt
#print axioms fourGaussianEntropy_eq_dual_at_mean
#print axioms entropy_loss_le_log_partition_ratio
#print axioms entropy_loss_lt_log_153_div_100_of_dual_ratio
#print axioms signed_margin_gt_log_200_div_153_of_dual_ratio

end Erdos625
