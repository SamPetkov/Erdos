import Erdos625.ColoringProfileDeficitScoreBounds
import Erdos625.GaussianTailTools
import Erdos625.GaussianMomentTailTools
import Erdos625.GaussianSecondMomentTailTools

/-!
# Finite partition bounds in deficit coordinates

This module begins the passage from pointwise deficit-score control to uniform
partition and moment estimates.  Whenever `alpha > 0`, the support contains the
deficit-zero coordinate with unnormalized mass exactly one, so every centered
partition function is bounded below by one.  Reversing the finite support then
isolates the exceptional deficit `-1` atom and identifies all remaining
coordinates with the natural deficits `0, …, alpha - 1`.  On any fixed bounded
tilt interval, the pointwise Gaussian score estimate therefore gives an
explicit partition upper bound, as well as first- and second-moment bounds,
independent of the growing support size.

The module assumes a supplied tilt bound.  It does not prove boundedness of the
optimizer tilt, convergence of normalized means, a phase root, or any final
asymptotic statement.
-/

namespace Erdos625

noncomputable section

/-- The support coordinate of class size exactly `alpha`, hence deficit zero. -/
def profileDeficitZeroIndex (alpha : ℕ) (halpha : 0 < alpha) :
    Fin (alpha + 1) :=
  ⟨alpha - 1, by omega⟩

@[simp]
theorem profileDeficitZeroIndex_val_add_one
    (alpha : ℕ) (halpha : 0 < alpha) :
    (profileDeficitZeroIndex alpha halpha).1 + 1 = alpha := by
  simp [profileDeficitZeroIndex, Nat.sub_add_cancel halpha]

@[simp]
theorem profileDeficit_zeroIndex
    (alpha : ℕ) (halpha : 0 < alpha) :
    profileDeficit alpha (profileDeficitZeroIndex alpha halpha) = 0 := by
  rw [profileDeficit_eq_cast_sub]
  · simp
  · simp

@[simp]
theorem profileDeficitResidualScore_zeroIndex
    (alpha : ℕ) (halpha : 0 < alpha) :
    profileDeficitResidualScore alpha
        (profileDeficitZeroIndex alpha halpha) = 0 := by
  rw [profileDeficitResidualScore_eq_descFactorial]
  · simp
  · simp

@[simp]
theorem profileDeficitUnnormalized_zeroIndex
    (alpha : ℕ) (halpha : 0 < alpha) (lambda : ℝ) :
    profileDeficitUnnormalized alpha lambda
        (profileDeficitZeroIndex alpha halpha) = 1 := by
  simp [profileDeficitUnnormalized]

/-- The deficit-zero atom supplies a phase- and tilt-uniform positive lower
bound for the centered partition function. -/
theorem one_le_profileDeficitPartition
    (alpha : ℕ) (halpha : 0 < alpha) (lambda : ℝ) :
    1 ≤ profileDeficitPartition alpha lambda := by
  rw [profileDeficitPartition]
  calc
    1 = profileDeficitUnnormalized alpha lambda
        (profileDeficitZeroIndex alpha halpha) := by simp
    _ ≤ ∑ i : Fin (alpha + 1),
          profileDeficitUnnormalized alpha lambda i := by
      exact Finset.single_le_sum
        (fun i _ ↦ (profileDeficitUnnormalized_pos alpha lambda i).le)
        (Finset.mem_univ (profileDeficitZeroIndex alpha halpha))

/-- Unnormalized first deficit moment. -/
def profileDeficitFirstNumerator (alpha : ℕ) (lambda : ℝ) : ℝ :=
  ∑ i : Fin (alpha + 1),
    profileDeficitUnnormalized alpha lambda i * profileDeficit alpha i

/-- Unnormalized raw second deficit moment. -/
def profileDeficitSecondNumerator (alpha : ℕ) (lambda : ℝ) : ℝ :=
  ∑ i : Fin (alpha + 1),
    profileDeficitUnnormalized alpha lambda i *
      profileDeficit alpha i ^ 2

/-- Normalized raw second deficit moment. -/
def profileDeficitSecondMoment (alpha : ℕ) (lambda : ℝ) : ℝ :=
  ∑ i : Fin (alpha + 1),
    profileDeficitWeight alpha lambda i * profileDeficit alpha i ^ 2

/-- The normalized deficit mean is exactly the first numerator divided by the
partition function. -/
theorem profileDeficitMean_eq_firstNumerator_div
    (alpha : ℕ) (lambda : ℝ) :
    profileDeficitMean alpha lambda =
      profileDeficitFirstNumerator alpha lambda /
        profileDeficitPartition alpha lambda := by
  rw [profileDeficitMean, profileDeficitFirstNumerator]
  simp_rw [profileDeficitWeight, div_mul_eq_mul_div]
  rw [Finset.sum_div]

/-- The normalized raw second deficit moment is its unnormalized numerator
divided by the partition function. -/
theorem profileDeficitSecondMoment_eq_secondNumerator_div
    (alpha : ℕ) (lambda : ℝ) :
    profileDeficitSecondMoment alpha lambda =
      profileDeficitSecondNumerator alpha lambda /
        profileDeficitPartition alpha lambda := by
  rw [profileDeficitSecondMoment, profileDeficitSecondNumerator]
  simp_rw [profileDeficitWeight, div_mul_eq_mul_div]
  rw [Finset.sum_div]

/-- The unnormalized raw second deficit moment is nonnegative. -/
theorem profileDeficitSecondNumerator_nonneg
    (alpha : ℕ) (lambda : ℝ) :
    0 ≤ profileDeficitSecondNumerator alpha lambda := by
  rw [profileDeficitSecondNumerator]
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (profileDeficitUnnormalized_pos alpha lambda i).le
      (sq_nonneg (profileDeficit alpha i))

/-- The normalized raw second deficit moment is nonnegative. -/
theorem profileDeficitSecondMoment_nonneg
    (alpha : ℕ) (lambda : ℝ) :
    0 ≤ profileDeficitSecondMoment alpha lambda := by
  rw [profileDeficitSecondMoment_eq_secondNumerator_div]
  exact div_nonneg (profileDeficitSecondNumerator_nonneg alpha lambda)
    (profileDeficitPartition_pos alpha lambda).le

/-! ## Reversing the finite support -/

/-- Reversal splits an arbitrary sum on `Fin (alpha + 1)` into the last
coordinate and the reverse enumeration of the preceding coordinates. -/
theorem sum_comp_rev_eq_last_add
    (alpha : ℕ) (f : Fin (alpha + 1) → ℝ) :
    (∑ i : Fin (alpha + 1), f i) =
      f (Fin.last alpha) + ∑ d : Fin alpha, f (Fin.rev d.succ) := by
  calc
    (∑ i : Fin (alpha + 1), f i) =
        ∑ i : Fin (alpha + 1),
          f ((Fin.revPerm : Equiv.Perm (Fin (alpha + 1))) i) :=
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (alpha + 1))) f).symm
    _ = f (Fin.last alpha) + ∑ d : Fin alpha, f (Fin.rev d.succ) := by
      rw [Fin.sum_univ_succ]
      simp

/-- Reversing the support sends its first coordinate to the exceptional
deficit `-1` atom. -/
@[simp]
theorem profileDeficit_rev_zero (alpha : ℕ) :
    profileDeficit alpha (Fin.rev (0 : Fin (alpha + 1))) = -1 := by
  rw [Fin.rev_zero]
  exact profileDeficit_last alpha

/-- After the exceptional atom is removed, reversing the support identifies
the remaining coordinates exactly with the natural deficits `0, …, alpha-1`. -/
@[simp]
theorem profileDeficit_rev_succ (alpha : ℕ) (d : Fin alpha) :
    profileDeficit alpha (Fin.rev d.succ) = (d : ℝ) := by
  change
    (alpha : ℝ) - ((((Fin.rev d.succ).1 + 1 : ℕ)) : ℝ) = (d.1 : ℝ)
  rw [Fin.val_rev, Fin.val_succ]
  have hdle : d.1 ≤ alpha := Nat.le_of_lt d.2
  have hnat : alpha + 1 - (d.1 + 1 + 1) + 1 = alpha - d.1 := by
    omega
  rw [hnat, Nat.cast_sub hdle]
  ring

/-- Exact support reindexing: every sum over deficit coordinates consists of
the exceptional value at `-1` plus the sum over natural deficits below
`alpha`. -/
theorem sum_comp_profileDeficit_eq
    (alpha : ℕ) (f : ℝ → ℝ) :
    (∑ i : Fin (alpha + 1), f (profileDeficit alpha i)) =
      f (-1) + ∑ d : Fin alpha, f (d : ℝ) := by
  calc
    (∑ i : Fin (alpha + 1), f (profileDeficit alpha i)) =
        ∑ i : Fin (alpha + 1),
          f (profileDeficit alpha ((Fin.revPerm : Equiv.Perm (Fin (alpha + 1))) i)) :=
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (alpha + 1)))
        (fun i ↦ f (profileDeficit alpha i))).symm
    _ = f (-1) + ∑ d : Fin alpha, f (d : ℝ) := by
      rw [Fin.sum_univ_succ]
      simp [profileDeficit_last]

/-! ## Uniform partition control on a bounded tilt interval -/

/-- On every natural-deficit coordinate, the exact centered weight is bounded
by the corresponding tilted Gaussian term. -/
theorem profileDeficitUnnormalized_rev_succ_le_tiltedGaussian
    (alpha : ℕ) (halpha : 0 < alpha) (lambda : ℝ) (d : Fin alpha) :
    profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) ≤
      Real.exp
        (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2) := by
  rw [profileDeficitUnnormalized, profileDeficit_rev_succ]
  apply Real.exp_le_exp.mpr
  have hscore := profileDeficitResidualScore_le_gaussian
    alpha halpha (Fin.rev d.succ)
  rw [profileDeficit_rev_succ] at hscore
  linarith

/-- The exceptional deficit `-1` atom is at most `exp M` whenever the tilt is
bounded in absolute value by `M`. -/
theorem profileDeficitUnnormalized_last_le_exp
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    profileDeficitUnnormalized alpha lambda (Fin.last alpha) ≤
      Real.exp M := by
  rw [profileDeficitUnnormalized, profileDeficit_last]
  apply Real.exp_le_exp.mpr
  have hscore := profileDeficitResidualScore_le_gaussian
    alpha halpha (Fin.last alpha)
  rw [profileDeficit_last] at hscore
  have hq : 0 < q := by
    unfold q
    positivity
  have hlower := (abs_le.mp hlambda).1
  nlinarith

/-- A bounded deficit tilt gives an explicit partition bound independent of
the growing support size `alpha`.  The first term covers the unique deficit
`-1` atom; the second is the full natural-deficit Gaussian envelope. -/
theorem profileDeficitPartition_le_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    profileDeficitPartition alpha lambda ≤
      Real.exp M +
        Real.exp (M ^ 2 / q) *
          (1 / (1 - Real.exp (-q / 4))) := by
  have hq : 0 < q := by
    unfold q
    positivity
  rw [profileDeficitPartition, sum_comp_rev_eq_last_add]
  apply add_le_add
  · exact profileDeficitUnnormalized_last_le_exp alpha halpha hlambda
  · calc
      (∑ d : Fin alpha,
          profileDeficitUnnormalized alpha lambda (Fin.rev d.succ)) ≤
          ∑ d : Fin alpha,
            Real.exp
              (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2) :=
        Finset.sum_le_sum fun d _ ↦
          profileDeficitUnnormalized_rev_succ_le_tiltedGaussian
            alpha halpha lambda d
      _ = ∑ d ∈ Finset.Ico 0 alpha,
            Real.exp
              (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2) := by
        simpa only [Nat.Ico_zero_eq_range] using
          (Fin.sum_univ_eq_sum_range
            (fun d : ℕ ↦
              Real.exp
                (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2)) alpha)
      _ ≤ Real.exp (M ^ 2 / q) *
            (1 / (1 - Real.exp (-q / 4))) := by
        simpa using finiteTiltedGaussianTail_le hq hlambda 0 alpha

/-- On a bounded tilt interval, the absolute unnormalized first deficit moment
has an explicit bound independent of the growing support size. -/
theorem abs_profileDeficitFirstNumerator_le_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    |profileDeficitFirstNumerator alpha lambda| ≤
      Real.exp M +
        Real.exp (M ^ 2 / q) *
          (Real.exp (-q / 4) /
            (1 - Real.exp (-q / 4)) ^ 2) := by
  have hq : 0 < q := by
    unfold q
    positivity
  rw [profileDeficitFirstNumerator]
  calc
    |∑ i : Fin (alpha + 1),
        profileDeficitUnnormalized alpha lambda i *
          profileDeficit alpha i| ≤
        ∑ i : Fin (alpha + 1),
          |profileDeficitUnnormalized alpha lambda i *
            profileDeficit alpha i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = |profileDeficitUnnormalized alpha lambda (Fin.last alpha) *
            profileDeficit alpha (Fin.last alpha)| +
          ∑ d : Fin alpha,
            |profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) *
              profileDeficit alpha (Fin.rev d.succ)| :=
      sum_comp_rev_eq_last_add alpha
        (fun i ↦
          |profileDeficitUnnormalized alpha lambda i *
            profileDeficit alpha i|)
    _ = profileDeficitUnnormalized alpha lambda (Fin.last alpha) +
          ∑ d : Fin alpha,
            (d : ℝ) *
              profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) := by
      congr 1
      · rw [profileDeficit_last]
        simp [(profileDeficitUnnormalized_pos alpha lambda
          (Fin.last alpha)).le]
      · apply Finset.sum_congr rfl
        intro d _
        rw [profileDeficit_rev_succ]
        have hnonneg :
            0 ≤ profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) *
              (d : ℝ) := by
          exact mul_nonneg
            (profileDeficitUnnormalized_pos alpha lambda
              (Fin.rev d.succ)).le
            (by positivity)
        rw [abs_of_nonneg hnonneg]
        ring
    _ ≤ Real.exp M +
          ∑ d : Fin alpha,
            (d : ℝ) *
              Real.exp
                (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2) := by
      apply add_le_add
      · exact profileDeficitUnnormalized_last_le_exp alpha halpha hlambda
      · exact Finset.sum_le_sum fun d _ ↦
          mul_le_mul_of_nonneg_left
            (profileDeficitUnnormalized_rev_succ_le_tiltedGaussian
              alpha halpha lambda d)
            (by positivity)
    _ = Real.exp M +
          ∑ d ∈ Finset.Ico 0 alpha,
            (d : ℝ) *
              Real.exp
                (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2) := by
      congr 1
      simpa only [Nat.Ico_zero_eq_range] using
        (Fin.sum_univ_eq_sum_range
          (fun d : ℕ ↦
            (d : ℝ) *
              Real.exp
                (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2)) alpha)
    _ ≤ Real.exp M +
          Real.exp (M ^ 2 / q) *
            (Real.exp (-q / 4) /
              (1 - Real.exp (-q / 4)) ^ 2) := by
      gcongr
      simpa using
        finiteTiltedGaussianFirstMomentTail_le hq hlambda 0 alpha

/-- On a bounded tilt interval, the unnormalized raw second deficit moment has
an explicit bound independent of the growing support size. -/
theorem profileDeficitSecondNumerator_le_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    profileDeficitSecondNumerator alpha lambda ≤
      Real.exp M +
        Real.exp (M ^ 2 / q) *
          (Real.exp (-q / 4) * (1 + Real.exp (-q / 4)) /
            (1 - Real.exp (-q / 4)) ^ 3) := by
  have hq : 0 < q := by
    unfold q
    positivity
  rw [profileDeficitSecondNumerator, sum_comp_rev_eq_last_add]
  calc
    profileDeficitUnnormalized alpha lambda (Fin.last alpha) *
          profileDeficit alpha (Fin.last alpha) ^ 2 +
        ∑ d : Fin alpha,
          profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) *
            profileDeficit alpha (Fin.rev d.succ) ^ 2 =
        profileDeficitUnnormalized alpha lambda (Fin.last alpha) +
          ∑ d : Fin alpha,
            (d : ℝ) ^ 2 *
              profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) := by
      congr 1
      · rw [profileDeficit_last]
        ring
      · apply Finset.sum_congr rfl
        intro d _
        rw [profileDeficit_rev_succ]
        ring
    _ ≤ Real.exp M +
          ∑ d : Fin alpha,
            (d : ℝ) ^ 2 *
              Real.exp
                (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2) := by
      apply add_le_add
      · exact profileDeficitUnnormalized_last_le_exp alpha halpha hlambda
      · exact Finset.sum_le_sum fun d _ ↦
          mul_le_mul_of_nonneg_left
            (profileDeficitUnnormalized_rev_succ_le_tiltedGaussian
              alpha halpha lambda d)
            (sq_nonneg (d : ℝ))
    _ = Real.exp M +
          ∑ d ∈ Finset.Ico 0 alpha,
            (d : ℝ) ^ 2 *
              Real.exp
                (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2) := by
      congr 1
      simpa only [Nat.Ico_zero_eq_range] using
        (Fin.sum_univ_eq_sum_range
          (fun d : ℕ ↦
            (d : ℝ) ^ 2 *
              Real.exp
                (lambda * (d : ℝ) - q / 2 * (d : ℝ) ^ 2)) alpha)
    _ ≤ Real.exp M +
          Real.exp (M ^ 2 / q) *
            (Real.exp (-q / 4) * (1 + Real.exp (-q / 4)) /
              (1 - Real.exp (-q / 4)) ^ 3) := by
      gcongr
      simpa using
        finiteTiltedGaussianSecondMomentTail_le hq hlambda 0 alpha

/-- The same explicit envelope bounds the absolute value of the unnormalized
raw second deficit moment. -/
theorem abs_profileDeficitSecondNumerator_le_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    |profileDeficitSecondNumerator alpha lambda| ≤
      Real.exp M +
        Real.exp (M ^ 2 / q) *
          (Real.exp (-q / 4) * (1 + Real.exp (-q / 4)) /
            (1 - Real.exp (-q / 4)) ^ 3) := by
  rw [abs_of_nonneg (profileDeficitSecondNumerator_nonneg alpha lambda)]
  exact profileDeficitSecondNumerator_le_gaussianEnvelope
    alpha halpha hlambda

/-- Division by the partition function cannot enlarge the nonnegative raw
second moment, because the deficit-zero atom gives partition mass at least
one. -/
theorem profileDeficitSecondMoment_le_secondNumerator
    (alpha : ℕ) (halpha : 0 < alpha) (lambda : ℝ) :
    profileDeficitSecondMoment alpha lambda ≤
      profileDeficitSecondNumerator alpha lambda := by
  rw [profileDeficitSecondMoment_eq_secondNumerator_div,
    div_le_iff₀ (profileDeficitPartition_pos alpha lambda)]
  have hmul := mul_le_mul_of_nonneg_left
    (one_le_profileDeficitPartition alpha halpha lambda)
    (profileDeficitSecondNumerator_nonneg alpha lambda)
  simpa [mul_comm] using hmul

/-- On a bounded tilt interval, the normalized raw second deficit moment obeys
the same support-uniform envelope as its unnormalized numerator. -/
theorem profileDeficitSecondMoment_le_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    profileDeficitSecondMoment alpha lambda ≤
      Real.exp M +
        Real.exp (M ^ 2 / q) *
          (Real.exp (-q / 4) * (1 + Real.exp (-q / 4)) /
            (1 - Real.exp (-q / 4)) ^ 3) :=
  (profileDeficitSecondMoment_le_secondNumerator alpha halpha lambda).trans
    (profileDeficitSecondNumerator_le_gaussianEnvelope
      alpha halpha hlambda)

/-- Equivalently, the absolute normalized raw second deficit moment obeys the
same support-uniform envelope. -/
theorem abs_profileDeficitSecondMoment_le_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    |profileDeficitSecondMoment alpha lambda| ≤
      Real.exp M +
        Real.exp (M ^ 2 / q) *
          (Real.exp (-q / 4) * (1 + Real.exp (-q / 4)) /
            (1 - Real.exp (-q / 4)) ^ 3) := by
  rw [abs_of_nonneg (profileDeficitSecondMoment_nonneg alpha lambda)]
  exact profileDeficitSecondMoment_le_gaussianEnvelope
    alpha halpha hlambda

/-- The same envelope bounds the normalized deficit mean, since the
deficit-zero atom makes the partition function at least one. -/
theorem abs_profileDeficitMean_le_gaussianEnvelope
    (alpha : ℕ) (halpha : 0 < alpha) {lambda M : ℝ}
    (hlambda : |lambda| ≤ M) :
    |profileDeficitMean alpha lambda| ≤
      Real.exp M +
        Real.exp (M ^ 2 / q) *
          (Real.exp (-q / 4) /
            (1 - Real.exp (-q / 4)) ^ 2) := by
  rw [profileDeficitMean_eq_firstNumerator_div, abs_div,
    abs_of_pos (profileDeficitPartition_pos alpha lambda)]
  apply le_trans ?_
    (abs_profileDeficitFirstNumerator_le_gaussianEnvelope
      alpha halpha hlambda)
  rw [div_le_iff₀ (profileDeficitPartition_pos alpha lambda)]
  have hmul := mul_le_mul_of_nonneg_left
    (one_le_profileDeficitPartition alpha halpha lambda)
    (abs_nonneg (profileDeficitFirstNumerator alpha lambda))
  simpa using hmul

end

end Erdos625
