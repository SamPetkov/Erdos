import Erdos625.GeometricMomentTools

/-!
# Finite geometric second-moment tails

This module evaluates the second moment of a geometric series and uses it to
bound a finite tail.  For `0 ≤ rho < 1`, the resulting majorant is

`rho ^ R * (R ^ 2 / (1 - rho) + 2 * R * rho / (1 - rho) ^ 2
  + rho * (1 + rho) / (1 - rho) ^ 3)`.

The proof is independent of any optimizer or random-graph argument.  It also
covers the empty interval `m ≤ R`.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Closed form for the second moment of a geometric series. -/
theorem tsum_cast_sq_mul_pow
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    (∑' k : ℕ, ((k : ℝ) ^ 2) * rho ^ k) =
      rho * (1 + rho) / (1 - rho) ^ 3 := by
  have hrhoNorm : ‖rho‖ < 1 := by
    rwa [Real.norm_of_nonneg hrho0]
  have htwo := hasSum_choose_mul_geometric_of_norm_lt_one 2 hrhoNorm
  have hone := hasSum_choose_mul_geometric_of_norm_lt_one 1 hrhoNorm
  have hzero := hasSum_choose_mul_geometric_of_norm_lt_one 0 hrhoNorm
  have hcombined :
      HasSum
        (fun k : ℕ ↦
          (2 : ℝ) * ((Nat.choose (k + 2) 2 : ℝ) * rho ^ k) -
            3 * ((Nat.choose (k + 1) 1 : ℝ) * rho ^ k) +
            (Nat.choose (k + 0) 0 : ℝ) * rho ^ k)
        ((2 : ℝ) * (1 / (1 - rho) ^ (2 + 1)) -
          3 * (1 / (1 - rho) ^ (1 + 1)) +
          1 / (1 - rho) ^ (0 + 1)) :=
    ((htwo.mul_left (2 : ℝ)).sub (hone.mul_left (3 : ℝ))).add hzero
  have hfunction :
      (fun k : ℕ ↦ ((k : ℝ) ^ 2) * rho ^ k) =
        fun k : ℕ ↦
          (2 : ℝ) * ((Nat.choose (k + 2) 2 : ℝ) * rho ^ k) -
            3 * ((Nat.choose (k + 1) 1 : ℝ) * rho ^ k) +
            (Nat.choose (k + 0) 0 : ℝ) * rho ^ k := by
    funext k
    rw [Nat.cast_choose_two]
    norm_num
    ring
  have hsquare :
      HasSum
        (fun k : ℕ ↦ ((k : ℝ) ^ 2) * rho ^ k)
        (2 * (1 / (1 - rho) ^ 3) -
          3 * (1 / (1 - rho) ^ 2) +
          1 / (1 - rho)) := by
    rw [hfunction]
    norm_num at hcombined ⊢
    exact hcombined
  rw [hsquare.tsum_eq]
  field_simp [ne_of_gt (sub_pos.mpr hrho1)]
  ring

/-- A finite second-moment geometric tail is bounded by the corresponding
infinite tail, evaluated in closed form. -/
theorem sum_Ico_cast_sq_mul_pow_le_geometric_tail
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) (R m : ℕ) :
    (∑ d ∈ Finset.Ico R m, ((d : ℝ) ^ 2) * rho ^ d) ≤
      rho ^ R *
        (((R : ℝ) ^ 2) / (1 - rho) +
          (2 * (R : ℝ) * rho) / (1 - rho) ^ 2 +
          rho * (1 + rho) / (1 - rho) ^ 3) := by
  have hrhoNorm : ‖rho‖ < 1 := by
    rwa [Real.norm_of_nonneg hrho0]
  have hgeometric : Summable (fun k : ℕ ↦ rho ^ k) :=
    summable_geometric_of_lt_one hrho0 hrho1
  have hfirstMoment : Summable (fun k : ℕ ↦ (k : ℝ) * rho ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrhoNorm).summable
  have hsecondMoment : Summable (fun k : ℕ ↦ ((k : ℝ) ^ 2) * rho ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hrhoNorm
  have hshift :
      (∑ d ∈ Finset.Ico R m, ((d : ℝ) ^ 2) * rho ^ d) =
        rho ^ R *
          ∑ k ∈ Finset.range (m - R),
            (((R : ℝ) + k) ^ 2) * rho ^ k := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    congr
    ext k
    rw [pow_add]
    push_cast
    ring
  have hfiniteExpansion :
      (∑ k ∈ Finset.range (m - R),
          (((R : ℝ) + k) ^ 2) * rho ^ k) =
        (∑ k ∈ Finset.range (m - R), (R : ℝ) ^ 2 * rho ^ k) +
        (∑ k ∈ Finset.range (m - R),
          (2 * (R : ℝ)) * ((k : ℝ) * rho ^ k)) +
        ∑ k ∈ Finset.range (m - R), ((k : ℝ) ^ 2) * rho ^ k := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (∑ d ∈ Finset.Ico R m, ((d : ℝ) ^ 2) * rho ^ d) =
        rho ^ R *
          ∑ k ∈ Finset.range (m - R),
            (((R : ℝ) + k) ^ 2) * rho ^ k := hshift
    _ = rho ^ R *
        ((∑ k ∈ Finset.range (m - R), (R : ℝ) ^ 2 * rho ^ k) +
          (∑ k ∈ Finset.range (m - R),
            (2 * (R : ℝ)) * ((k : ℝ) * rho ^ k)) +
          ∑ k ∈ Finset.range (m - R), ((k : ℝ) ^ 2) * rho ^ k) := by
      rw [hfiniteExpansion]
    _ ≤ rho ^ R *
        ((∑' k : ℕ, (R : ℝ) ^ 2 * rho ^ k) +
          (∑' k : ℕ, (2 * (R : ℝ)) * ((k : ℝ) * rho ^ k)) +
          ∑' k : ℕ, ((k : ℝ) ^ 2) * rho ^ k) := by
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hrho0 R)
      exact add_le_add
        (add_le_add
          (Summable.sum_le_tsum
            (Finset.range (m - R))
            (fun _ _ ↦ by positivity)
            (hgeometric.mul_left _))
          (Summable.sum_le_tsum
            (Finset.range (m - R))
            (fun _ _ ↦ by positivity)
            (hfirstMoment.mul_left _)))
        (Summable.sum_le_tsum
          (Finset.range (m - R))
          (fun _ _ ↦ by positivity)
          hsecondMoment)
    _ = rho ^ R *
        (((R : ℝ) ^ 2) / (1 - rho) +
          (2 * (R : ℝ) * rho) / (1 - rho) ^ 2 +
          rho * (1 + rho) / (1 - rho) ^ 3) := by
      rw [tsum_mul_left, tsum_mul_left,
        tsum_geometric_of_lt_one hrho0 hrho1,
        tsum_coe_mul_geometric_of_norm_lt_one hrhoNorm,
        tsum_cast_sq_mul_pow hrho0 hrho1]
      ring

end

end Erdos625
