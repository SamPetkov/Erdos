import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Erdos625.ColoringProfileDualBound

/-!
# Differentiation of the finite coloring-profile dual

This module develops the local calculus of the finite Gibbs dual on support
sizes `1, …, b`.  A positive support size is stated explicitly whenever the
partition must be nonzero.  Strict positivity of the variance uses the sharp
nondegeneracy hypothesis `2 ≤ b`.

No endpoint limit, optimizing tilt, root, or asymptotic assertion is made
here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-! ## First and second moments -/

/-- Unnormalized first size moment of the finite Gibbs family. -/
def profileDualFirstNumerator (b : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin b, profileClassSize i * profileDualUnnormalized t i

/-- Unnormalized second size moment of the finite Gibbs family. -/
def profileDualSecondNumerator (b : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin b, profileClassSize i ^ 2 * profileDualUnnormalized t i

/-- Mean support size.  The quotient is total at `b = 0`; probabilistic
normalization is used only under `0 < b`. -/
def profileDualMean (b : ℕ) (t : ℝ) : ℝ :=
  profileDualFirstNumerator b t / profileDualPartition b t

/-- Weighted centered second moment of the support size. -/
def profileDualVariance (b : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin b,
    profileDualWeight t i * (profileClassSize i - profileDualMean b t) ^ 2

/-- The mean is the normalized weighted support sum.  This algebraic identity
also holds in the totalized empty case. -/
theorem profileDualMean_eq_sum_weight_size (b : ℕ) (t : ℝ) :
    profileDualMean b t =
      ∑ i : Fin b, profileDualWeight t i * profileClassSize i := by
  rw [profileDualMean, profileDualFirstNumerator]
  simp only [profileDualWeight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Weighted second moment in numerator-over-partition form. -/
theorem sum_profileDualWeight_size_sq (b : ℕ) (t : ℝ) :
    (∑ i : Fin b, profileDualWeight t i * profileClassSize i ^ 2) =
      profileDualSecondNumerator b t / profileDualPartition b t := by
  rw [profileDualSecondNumerator]
  simp only [profileDualWeight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## Derivatives of the log-partition and the dual upper bound -/

theorem hasDerivAt_profileDualUnnormalized {b : ℕ}
    (t : ℝ) (i : Fin b) :
    HasDerivAt (fun u ↦ profileDualUnnormalized u i)
      (profileClassSize i * profileDualUnnormalized t i) t := by
  simpa only [profileDualUnnormalized, Function.const_apply, Pi.add_apply,
    id_eq, zero_add, one_mul, mul_one, mul_comm] using
    ((hasDerivAt_const t (profileDualScore i)).add
      ((hasDerivAt_id t).mul_const (profileClassSize i))).exp

theorem hasDerivAt_profileDualPartition (b : ℕ) (t : ℝ) :
    HasDerivAt (profileDualPartition b) (profileDualFirstNumerator b t) t := by
  change HasDerivAt
    (fun u ↦ ∑ i : Fin b, profileDualUnnormalized u i)
    (∑ i : Fin b, profileClassSize i * profileDualUnnormalized t i) t
  exact HasDerivAt.fun_sum fun i _ ↦
    hasDerivAt_profileDualUnnormalized t i

theorem hasDerivAt_profileDualFirstNumerator (b : ℕ) (t : ℝ) :
    HasDerivAt (profileDualFirstNumerator b)
      (profileDualSecondNumerator b t) t := by
  change HasDerivAt
    (fun u ↦ ∑ i : Fin b,
      profileClassSize i * profileDualUnnormalized u i)
    (∑ i : Fin b,
      profileClassSize i ^ 2 * profileDualUnnormalized t i) t
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [pow_two, mul_assoc] using
    (hasDerivAt_profileDualUnnormalized t i).const_mul (profileClassSize i)

/-- The derivative of the log-partition is the mean support size. -/
theorem hasDerivAt_log_profileDualPartition {b : ℕ} (hb : 0 < b)
    (t : ℝ) :
    HasDerivAt (fun u ↦ Real.log (profileDualPartition b u))
      (profileDualMean b t) t := by
  simpa only [profileDualMean] using
    (hasDerivAt_profileDualPartition b t).log
      (profileDualPartition_pos hb t).ne'

theorem deriv_log_profileDualPartition {b : ℕ} (hb : 0 < b)
    (t : ℝ) :
    deriv (fun u ↦ Real.log (profileDualPartition b u)) t =
      profileDualMean b t :=
  (hasDerivAt_log_profileDualPartition hb t).deriv

/-- The derivative of the dual upper expression is `parts * mean - n`. -/
theorem hasDerivAt_profileDualUpper {b : ℕ} (hb : 0 < b)
    (n parts t : ℝ) :
    HasDerivAt (profileDualUpper b n parts)
      (parts * profileDualMean b t - n) t := by
  unfold profileDualUpper
  apply HasDerivAt.sub
  · have h :=
      (hasDerivAt_const t
        (n * Real.log n - n + parts - parts * Real.log parts)).add
        ((hasDerivAt_log_profileDualPartition hb t).const_mul parts)
    exact (h.congr_deriv (zero_add _)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  · have h := (hasDerivAt_id t).mul_const n
    exact (h.congr_deriv (one_mul n)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ ↦ rfl)

theorem deriv_profileDualUpper {b : ℕ} (hb : 0 < b)
    (n parts t : ℝ) :
    deriv (profileDualUpper b n parts) t =
      parts * profileDualMean b t - n :=
  (hasDerivAt_profileDualUpper hb n parts t).deriv

/-! ## Variance and strict monotonicity -/

/-- Variance as second moment minus the square of the mean. -/
theorem profileDualVariance_eq_raw {b : ℕ} (hb : 0 < b) (t : ℝ) :
    profileDualVariance b t =
      profileDualSecondNumerator b t / profileDualPartition b t -
        profileDualMean b t ^ 2 := by
  calc
    profileDualVariance b t = ∑ i : Fin b,
        (profileDualWeight t i * profileClassSize i ^ 2 -
          2 * profileDualMean b t *
            (profileDualWeight t i * profileClassSize i) +
          profileDualMean b t ^ 2 * profileDualWeight t i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i : Fin b,
          profileDualWeight t i * profileClassSize i ^ 2) -
        2 * profileDualMean b t *
          (∑ i : Fin b, profileDualWeight t i * profileClassSize i) +
        profileDualMean b t ^ 2 *
          (∑ i : Fin b, profileDualWeight t i) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
    _ = profileDualSecondNumerator b t / profileDualPartition b t -
        profileDualMean b t ^ 2 := by
      rw [sum_profileDualWeight_size_sq,
        ← profileDualMean_eq_sum_weight_size,
        sum_profileDualWeight hb]
      ring

/-- Differentiating the mean gives the variance. -/
theorem hasDerivAt_profileDualMean {b : ℕ} (hb : 0 < b) (t : ℝ) :
    HasDerivAt (profileDualMean b) (profileDualVariance b t) t := by
  have hQuotient :=
    (hasDerivAt_profileDualFirstNumerator b t).div
      (hasDerivAt_profileDualPartition b t)
      (profileDualPartition_pos hb t).ne'
  have hAlgebra :
      profileDualVariance b t =
        (profileDualSecondNumerator b t * profileDualPartition b t -
          profileDualFirstNumerator b t * profileDualFirstNumerator b t) /
            profileDualPartition b t ^ 2 := by
    rw [profileDualVariance_eq_raw hb, profileDualMean]
    field_simp [(profileDualPartition_pos hb t).ne']
  rw [hAlgebra]
  exact hQuotient

theorem deriv_profileDualMean {b : ℕ} (hb : 0 < b) (t : ℝ) :
    deriv (profileDualMean b) t = profileDualVariance b t :=
  (hasDerivAt_profileDualMean hb t).deriv

/-- With at least two distinct support sizes, the Gibbs variance is strictly
positive at every finite tilt. -/
theorem profileDualVariance_pos {b : ℕ} (hb : 2 ≤ b) (t : ℝ) :
    0 < profileDualVariance b t := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hOneLt : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
  let i0 : Fin b := ⟨0, hbPos⟩
  let i1 : Fin b := ⟨1, hOneLt⟩
  have hSize0 : profileClassSize i0 = 1 := by
    norm_num [profileClassSize, i0]
  have hSize1 : profileClassSize i1 = 2 := by
    norm_num [profileClassSize, i1]
  have hSizeNe : profileClassSize i0 ≠ profileClassSize i1 := by
    rw [hSize0, hSize1]
    norm_num
  rw [profileDualVariance]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (profileDualWeight_pos hbPos t i).le (sq_nonneg _)
  · by_cases h0 : profileClassSize i0 = profileDualMean b t
    · have h1 : profileClassSize i1 ≠ profileDualMean b t := by
        intro h1
        exact hSizeNe (h0.trans h1.symm)
      refine ⟨i1, Finset.mem_univ i1,
        mul_pos (profileDualWeight_pos hbPos t i1) ?_⟩
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr h1)
    · refine ⟨i0, Finset.mem_univ i0,
        mul_pos (profileDualWeight_pos hbPos t i0) ?_⟩
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr h0)

/-- The explicit derivative formula has derivative `parts * variance`. -/
theorem hasDerivAt_profileDualDerivative {b : ℕ} (hb : 0 < b)
    (n parts t : ℝ) :
    HasDerivAt (fun u ↦ parts * profileDualMean b u - n)
      (parts * profileDualVariance b t) t :=
  ((hasDerivAt_profileDualMean hb t).const_mul parts).sub_const n

theorem deriv_profileDualDerivative {b : ℕ} (hb : 0 < b)
    (n parts t : ℝ) :
    deriv (fun u ↦ parts * profileDualMean b u - n) t =
      parts * profileDualVariance b t :=
  (hasDerivAt_profileDualDerivative hb n parts t).deriv

/-- For positive part count and at least two support sizes, the derivative
formula of the dual upper expression is strictly increasing. -/
theorem strictMono_profileDualDerivative {b : ℕ} (hb : 2 ≤ b)
    (n parts : ℝ) (hparts : 0 < parts) :
    StrictMono (fun t ↦ parts * profileDualMean b t - n) := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  apply strictMono_of_deriv_pos
  intro t
  rw [deriv_profileDualDerivative hbPos]
  exact mul_pos hparts (profileDualVariance_pos hb t)

/-- Equivalently, the actual derivative of the dual upper expression is
strictly increasing. -/
theorem strictMono_deriv_profileDualUpper {b : ℕ} (hb : 2 ≤ b)
    (n parts : ℝ) (hparts : 0 < parts) :
    StrictMono (fun t ↦ deriv (profileDualUpper b n parts) t) := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  simpa only [deriv_profileDualUpper hbPos] using
    strictMono_profileDualDerivative hb n parts hparts

end

end Erdos625
