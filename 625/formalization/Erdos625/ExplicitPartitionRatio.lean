import Erdos625.SignedFourSizeObjective
import Erdos625.ExtendedGaussianProfile
import Mathlib.Tactic

/-!
# Explicit extended-Gaussian partition ratio

This file verifies the partition-ratio estimate at the symmetric manuscript
choice `lambda = 7 log(2) / 2`.  At this tilt all exponents are integral
powers of two.  The natural tail from deficit nine onward is bounded by the
geometric series with first term `2⁻⁹` and ratio `2⁻⁶`.
-/

open scoped BigOperators Topology

namespace Erdos625

noncomputable section

/-- The explicit tilt used for the four-deficit comparison. -/
def signedFourSelectedTilt : ℝ := 7 * q / 2

/-- The corresponding target is the mean of the four-point profile. -/
def signedFourSelectedTarget : ℝ :=
  ProfileEntropyS4.mean fourGaussianScore signedFourSelectedTilt

/-- Beyond deficit nine, the selected-tilt natural term is bounded by a
geometric sequence of ratio `1/64`. -/
theorem selectedTilt_naturalTerm_add_nine_le (k : ℕ) :
    extendedGaussianNaturalTerm q signedFourSelectedTilt (k + 9) ≤
      (1 / 512 : ℝ) * (1 / 64 : ℝ) ^ k := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [extendedGaussianNaturalTerm, signedFourSelectedTilt, q]
  have he9 : Real.exp (-9 * Real.log 2) = (1 / 512 : ℝ) := by
    rw [show -9 * Real.log 2 = -((9 : ℕ) * Real.log 2) by norm_num,
      Real.exp_neg, Real.exp_nat_mul]
    norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have he6 : Real.exp (-6 * Real.log 2) = (1 / 64 : ℝ) := by
    rw [show -6 * Real.log 2 = -((6 : ℕ) * Real.log 2) by norm_num,
      Real.exp_neg, Real.exp_nat_mul]
    norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hrhs : (1 / 512 : ℝ) * (1 / 64 : ℝ) ^ k =
      Real.exp ((-9 - 6 * (k : ℝ)) * Real.log 2) := by
    rw [← he9, ← he6, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hrhs]
  apply Real.exp_le_exp.mpr
  have hk : (k : ℝ) * ((k : ℝ) - 1) ≥ 0 := by
    by_cases hz : k = 0
    · simp [hz]
    · have hk1 : 1 ≤ k := by omega
      have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hk1r)
  push_cast
  nlinarith

/-- The complete natural tail from deficit nine is at most `1/504`.
This is the sum of the explicit geometric majorant. -/
theorem selectedTilt_naturalTail_le :
    (∑' k : ℕ,
      extendedGaussianNaturalTerm q signedFourSelectedTilt (k + 9)) ≤
      (1 / 504 : ℝ) := by
  have hsummableLeft : Summable (fun k : ℕ ↦
      extendedGaussianNaturalTerm q signedFourSelectedTilt (k + 9)) :=
    (summable_extendedGaussianNaturalTerm (a := q)
      (lambda := signedFourSelectedTilt) q_pos).comp_injective
        (fun _ _ h ↦ Nat.add_right_cancel h)
  have hnorm : ‖(1 / 64 : ℝ)‖ < 1 := by norm_num
  have hsummableRight : Summable (fun k : ℕ ↦
      (1 / 512 : ℝ) * (1 / 64 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one hnorm).mul_left _
  calc
    (∑' k : ℕ,
        extendedGaussianNaturalTerm q signedFourSelectedTilt (k + 9)) ≤
        ∑' k : ℕ, (1 / 512 : ℝ) * (1 / 64 : ℝ) ^ k := by
      apply Summable.tsum_le_tsum selectedTilt_naturalTerm_add_nine_le
        hsummableLeft hsummableRight
    _ = (1 / 504 : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
      norm_num

/-- The exceptional atom and the first nine natural atoms have exact total
`1681/8` at the selected tilt. -/
theorem selectedTilt_initialMass_exact :
    extendedGaussianExceptionalAtom q signedFourSelectedTilt +
      ∑ d ∈ Finset.range 9,
        extendedGaussianNaturalTerm q signedFourSelectedTilt d =
      (1681 / 8 : ℝ) := by
  norm_num [extendedGaussianExceptionalAtom, extendedGaussianNaturalTerm,
    signedFourSelectedTilt, q, Finset.sum_range_succ]
  ring_nf
  rw [show Real.exp (-(Real.log 2 * 4)) = (1 / 16 : ℝ) by
    rw [show -(Real.log 2 * 4) = -((4 : ℕ) * Real.log 2) by ring,
      Real.exp_neg, Real.exp_nat_mul]
    norm_num [Real.exp_log]]
  rw [show Real.exp (Real.log 2 * 3) = (8 : ℝ) by
    rw [show Real.log 2 * 3 = (3 : ℕ) * Real.log 2 by ring,
      Real.exp_nat_mul]
    norm_num [Real.exp_log]]
  rw [show Real.exp (Real.log 2 * 5) = (32 : ℝ) by
    rw [show Real.log 2 * 5 = (5 : ℕ) * Real.log 2 by ring,
      Real.exp_nat_mul]
    norm_num [Real.exp_log]]
  rw [show Real.exp (Real.log 2 * 6) = (64 : ℝ) by
    rw [show Real.log 2 * 6 = (6 : ℕ) * Real.log 2 by ring,
      Real.exp_nat_mul]
    norm_num [Real.exp_log]]
  norm_num

/-- The four retained atoms (deficits 2 through 5) have exact mass `192`. -/
theorem selectedTilt_fourPartition_exact :
    ProfileEntropyS4.partition fourGaussianScore signedFourSelectedTilt =
      (192 : ℝ) := by
  norm_num [ProfileEntropyS4.partition, ProfileEntropyS4.unnormalized,
    fourGaussianScore, ProfileEntropyS4.support, signedFourSelectedTilt, q]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring_nf
  rw [show Real.exp (Real.log 2 * 5) = (32 : ℝ) by
    rw [show Real.log 2 * 5 = (5 : ℕ) * Real.log 2 by ring,
      Real.exp_nat_mul]
    norm_num [Real.exp_log]]
  rw [show Real.exp (Real.log 2 * 6) = (64 : ℝ) by
    rw [show Real.log 2 * 6 = (6 : ℕ) * Real.log 2 by ring,
      Real.exp_nat_mul]
    norm_num [Real.exp_log]]
  norm_num

/-- Rigorous explicit partition-ratio estimate at the selected tilt. -/
theorem selectedTilt_partition_ratio_lt :
    extendedGaussianPartition q signedFourSelectedTilt /
        ProfileEntropyS4.partition fourGaussianScore signedFourSelectedTilt <
      (153 / 100 : ℝ) := by
  have hsum := (summable_extendedGaussianNaturalTerm
    (a := q) (lambda := signedFourSelectedTilt) q_pos).sum_add_tsum_nat_add 9
  have hpart : extendedGaussianPartition q signedFourSelectedTilt =
      (extendedGaussianExceptionalAtom q signedFourSelectedTilt +
        ∑ d ∈ Finset.range 9,
          extendedGaussianNaturalTerm q signedFourSelectedTilt d) +
        ∑' k : ℕ,
          extendedGaussianNaturalTerm q signedFourSelectedTilt (k + 9) := by
    rw [extendedGaussianPartition]
    linarith
  rw [hpart, selectedTilt_fourPartition_exact]
  have hinit := selectedTilt_initialMass_exact
  have htail := selectedTilt_naturalTail_le
  rw [hinit]
  norm_num at htail ⊢
  linarith

/-- The selected target is represented by the selected tilt, as required by
entropy transport. -/
theorem selectedTilt_mean_eq_target :
    ProfileEntropyS4.mean fourGaussianScore signedFourSelectedTilt =
      signedFourSelectedTarget := rfl

end

end Erdos625

