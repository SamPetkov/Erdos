import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Finite geometric first-moment tails

This module bounds the first-moment tail of a finite geometric sequence.  For
`0 ≤ rho < 1`, it proves the exact infinite-tail majorant

`sum_{d in [R,m)} d * rho^d ≤
  rho^R * (R / (1-rho) + rho / (1-rho)^2)`.

The result includes the empty-interval case `m ≤ R`.  It is a finite analytic
tool only: no asymptotic rate, optimizer bound, or partition-function limit is
asserted here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A finite first-moment geometric tail is bounded by the corresponding
infinite tail, evaluated in closed form. -/
theorem sum_Ico_cast_mul_pow_le_geometric_tail
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (R m : ℕ) :
    (∑ d ∈ Finset.Ico R m, (d : ℝ) * rho ^ d) ≤
      rho ^ R *
        ((R : ℝ) / (1 - rho) + rho / (1 - rho) ^ 2) := by
  have hrhoNorm : ‖rho‖ < 1 := by
    rwa [Real.norm_of_nonneg hrho0]
  have hgeometric : Summable (fun k : ℕ ↦ rho ^ k) :=
    summable_geometric_of_lt_one hrho0 hrho1
  have hfirstMoment : Summable (fun k : ℕ ↦ (k : ℝ) * rho ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrhoNorm).summable
  have hshift :
      (∑ d ∈ Finset.Ico R m, (d : ℝ) * rho ^ d) =
        ∑ k ∈ Finset.range (m - R),
          ((R : ℝ) + k) * rho ^ (R + k) := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [add_comm]
  have hfactor :
      (∑ k ∈ Finset.range (m - R),
          ((R : ℝ) + k) * rho ^ (R + k)) =
        rho ^ R *
          ((∑ k ∈ Finset.range (m - R), (R : ℝ) * rho ^ k) +
            ∑ k ∈ Finset.range (m - R), (k : ℝ) * rho ^ k) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    congr
    ext k
    rw [pow_add]
    ring
  calc
    (∑ d ∈ Finset.Ico R m, (d : ℝ) * rho ^ d) =
        ∑ k ∈ Finset.range (m - R),
          ((R : ℝ) + k) * rho ^ (R + k) := hshift
    _ = rho ^ R *
          ((∑ k ∈ Finset.range (m - R), (R : ℝ) * rho ^ k) +
            ∑ k ∈ Finset.range (m - R), (k : ℝ) * rho ^ k) := hfactor
    _ ≤ rho ^ R *
          ((∑' k : ℕ, (R : ℝ) * rho ^ k) +
            ∑' k : ℕ, (k : ℝ) * rho ^ k) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (Summable.sum_le_tsum
            (Finset.range (m - R))
            (fun _ _ ↦ by positivity)
            (hgeometric.mul_left _))
          (Summable.sum_le_tsum
            (Finset.range (m - R))
            (fun _ _ ↦ by positivity)
            hfirstMoment))
        (pow_nonneg hrho0 R)
    _ = rho ^ R *
          ((R : ℝ) / (1 - rho) + rho / (1 - rho) ^ 2) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hrho0 hrho1,
        tsum_coe_mul_geometric_of_norm_lt_one hrhoNorm]
      ring

end

end Erdos625
