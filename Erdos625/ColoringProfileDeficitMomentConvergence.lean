import Erdos625.ColoringProfileDeficitPointwiseConvergence
import Erdos625.SeriesConvergenceTools

/-!
# Convergence of the finite deficit moments

This module rewrites the finite centered deficit partition and its first two
unnormalized moments as an exceptional `-1` atom together with totalized
natural-index series.  A dominated-convergence argument then proves, for each
fixed tilt, convergence to the corresponding extended Gaussian quantities at
quadratic coefficient `Real.log 2`.

The identities and bounds include `alpha = 0`; no small-support value is
silently discarded.  The limiting normalized mean is obtained only after the
strictly positive limiting denominator has been established.  Nothing here
asserts that a selected finite optimizer has bounded tilt.
-/

namespace Erdos625

open Filter Set
open scoped BigOperators Topology

noncomputable section

/-! ## Exact finite-series identities -/

/-- The totalized natural-deficit series is exactly the finite interior mass.
This also covers `alpha = 0`, when both sides are zero. -/
theorem tsum_profileDeficitNaturalTerm_eq_sum_fin
    (alpha : ℕ) (lambda : ℝ) :
    (∑' d : ℕ, profileDeficitNaturalTerm alpha lambda d) =
      ∑ d : Fin alpha,
        profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) := by
  rw [tsum_eq_sum_range_of_eq_zero
    (fun d : ℕ ↦ profileDeficitNaturalTerm alpha lambda d) alpha]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    simp [profileDeficitNaturalTerm, d.isLt]
  · intro d hd
    simp [profileDeficitNaturalTerm, Nat.not_lt.mpr hd]

/-- Exact partition identity: the unique exceptional atom plus the totalized
natural-deficit series. -/
theorem profileDeficitPartition_eq_exceptional_add_tsum
    (alpha : ℕ) (lambda : ℝ) :
    profileDeficitPartition alpha lambda =
      profileDeficitExceptionalTerm alpha lambda +
        ∑' d : ℕ, profileDeficitNaturalTerm alpha lambda d := by
  rw [profileDeficitPartition, sum_comp_rev_eq_last_add,
    profileDeficitExceptionalTerm,
    tsum_profileDeficitNaturalTerm_eq_sum_fin]

/-- The totalized natural first-moment series is exactly the finite interior
first moment. -/
theorem tsum_profileDeficitNaturalFirstMomentTerm_eq_sum_fin
    (alpha : ℕ) (lambda : ℝ) :
    (∑' d : ℕ,
        (d : ℝ) * profileDeficitNaturalTerm alpha lambda d) =
      ∑ d : Fin alpha,
        profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) *
          profileDeficit alpha (Fin.rev d.succ) := by
  rw [tsum_eq_sum_range_of_eq_zero
    (fun d : ℕ ↦
      (d : ℝ) * profileDeficitNaturalTerm alpha lambda d) alpha]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [profileDeficitNaturalTerm, dif_pos d.isLt]
    rw [profileDeficit_rev_succ]
    ring
  · intro d hd
    simp [profileDeficitNaturalTerm, Nat.not_lt.mpr hd]

/-- Exact first-numerator identity.  The exceptional coordinate is `-1`, so
its contribution has a minus sign. -/
theorem profileDeficitFirstNumerator_eq_neg_exceptional_add_tsum
    (alpha : ℕ) (lambda : ℝ) :
    profileDeficitFirstNumerator alpha lambda =
      -profileDeficitExceptionalTerm alpha lambda +
        ∑' d : ℕ,
          (d : ℝ) * profileDeficitNaturalTerm alpha lambda d := by
  rw [profileDeficitFirstNumerator, sum_comp_rev_eq_last_add,
    profileDeficit_last, profileDeficitExceptionalTerm,
    tsum_profileDeficitNaturalFirstMomentTerm_eq_sum_fin]
  ring

/-- The totalized natural second-moment series is exactly the finite interior
second moment. -/
theorem tsum_profileDeficitNaturalSecondMomentTerm_eq_sum_fin
    (alpha : ℕ) (lambda : ℝ) :
    (∑' d : ℕ,
        (d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d) =
      ∑ d : Fin alpha,
        profileDeficitUnnormalized alpha lambda (Fin.rev d.succ) *
          profileDeficit alpha (Fin.rev d.succ) ^ 2 := by
  rw [tsum_eq_sum_range_of_eq_zero
    (fun d : ℕ ↦
      (d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d) alpha]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [profileDeficitNaturalTerm, dif_pos d.isLt]
    rw [profileDeficit_rev_succ]
    ring
  · intro d hd
    simp [profileDeficitNaturalTerm, Nat.not_lt.mpr hd]

/-- Exact second-numerator identity.  The exceptional coordinate has square
`(-1)^2 = 1`, so its contribution has a plus sign. -/
theorem profileDeficitSecondNumerator_eq_exceptional_add_tsum
    (alpha : ℕ) (lambda : ℝ) :
    profileDeficitSecondNumerator alpha lambda =
      profileDeficitExceptionalTerm alpha lambda +
        ∑' d : ℕ,
          (d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d := by
  rw [profileDeficitSecondNumerator, sum_comp_rev_eq_last_add,
    profileDeficit_last, profileDeficitExceptionalTerm,
    tsum_profileDeficitNaturalSecondMomentTerm_eq_sum_fin]
  ring

/-! ## A summable fixed-tilt domination -/

/-- Every totalized finite natural-deficit term is dominated by its limiting
tilted-Gaussian term.  When `d ≥ alpha`, the finite term is exactly zero. -/
theorem norm_profileDeficitNaturalTerm_le_extendedGaussianNaturalTerm
    (alpha : ℕ) (lambda : ℝ) (d : ℕ) :
    ‖profileDeficitNaturalTerm alpha lambda d‖ ≤
      extendedGaussianNaturalTerm (Real.log 2) lambda d := by
  by_cases hd : d < alpha
  · have halpha : 0 < alpha := lt_of_le_of_lt (Nat.zero_le d) hd
    rw [profileDeficitNaturalTerm, dif_pos hd,
      Real.norm_eq_abs,
      abs_of_pos (profileDeficitUnnormalized_pos alpha lambda _)]
    simpa [extendedGaussianNaturalTerm, q] using
      profileDeficitUnnormalized_rev_succ_le_tiltedGaussian
        alpha halpha lambda (⟨d, hd⟩ : Fin alpha)
  · rw [profileDeficitNaturalTerm, dif_neg hd, norm_zero]
    exact (extendedGaussianNaturalTerm_pos (Real.log 2) lambda d).le

/-- Domination persists after multiplication by the first-moment
coordinate. -/
theorem norm_profileDeficitNaturalFirstMomentTerm_le
    (alpha : ℕ) (lambda : ℝ) (d : ℕ) :
    ‖(d : ℝ) * profileDeficitNaturalTerm alpha lambda d‖ ≤
      (d : ℝ) * extendedGaussianNaturalTerm (Real.log 2) lambda d := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg d)]
  exact mul_le_mul_of_nonneg_left
    (norm_profileDeficitNaturalTerm_le_extendedGaussianNaturalTerm
      alpha lambda d)
    (Nat.cast_nonneg d)

/-- Domination persists after multiplication by the raw second-moment
coordinate. -/
theorem norm_profileDeficitNaturalSecondMomentTerm_le
    (alpha : ℕ) (lambda : ℝ) (d : ℕ) :
    ‖(d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d‖ ≤
      (d : ℝ) ^ 2 *
        extendedGaussianNaturalTerm (Real.log 2) lambda d := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (d : ℝ))]
  exact mul_le_mul_of_nonneg_left
    (norm_profileDeficitNaturalTerm_le_extendedGaussianNaturalTerm
      alpha lambda d)
    (sq_nonneg (d : ℝ))

/-! ## Fixed-tilt convergence -/

/-- The natural part of the finite partition converges to the limiting
natural-index Gaussian series at every fixed tilt. -/
theorem tendsto_tsum_profileDeficitNaturalTerm (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦
        ∑' d : ℕ, profileDeficitNaturalTerm alpha lambda d)
      atTop
      (𝓝 (∑' d : ℕ,
        extendedGaussianNaturalTerm (Real.log 2) lambda d)) := by
  exact tendsto_tsum_of_norm_le_summable
    (summable_extendedGaussianNaturalTerm
      (show 0 < Real.log 2 by positivity))
    (fun alpha d ↦
      norm_profileDeficitNaturalTerm_le_extendedGaussianNaturalTerm
        alpha lambda d)
    (tendsto_profileDeficitNaturalTerm lambda)

/-- The natural part of the first numerator converges at every fixed tilt. -/
theorem tendsto_tsum_profileDeficitNaturalFirstMomentTerm (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦
        ∑' d : ℕ,
          (d : ℝ) * profileDeficitNaturalTerm alpha lambda d)
      atTop
      (𝓝 (∑' d : ℕ,
        (d : ℝ) *
          extendedGaussianNaturalTerm (Real.log 2) lambda d)) := by
  exact tendsto_tsum_of_norm_le_summable
    (summable_extendedGaussianFirstMoment
      (show 0 < Real.log 2 by positivity))
    (fun alpha d ↦
      norm_profileDeficitNaturalFirstMomentTerm_le alpha lambda d)
    (tendsto_profileDeficitNaturalFirstMomentTerm lambda)

/-- The natural part of the second numerator converges at every fixed tilt. -/
theorem tendsto_tsum_profileDeficitNaturalSecondMomentTerm (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦
        ∑' d : ℕ,
          (d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d)
      atTop
      (𝓝 (∑' d : ℕ,
        (d : ℝ) ^ 2 *
          extendedGaussianNaturalTerm (Real.log 2) lambda d)) := by
  exact tendsto_tsum_of_norm_le_summable
    (summable_extendedGaussianSecondMoment
      (show 0 < Real.log 2 by positivity))
    (fun alpha d ↦
      norm_profileDeficitNaturalSecondMomentTerm_le alpha lambda d)
    (tendsto_profileDeficitNaturalSecondMomentTerm lambda)

/-- The exact finite deficit partition converges to the extended Gaussian
partition at every fixed tilt. -/
theorem tendsto_profileDeficitPartition (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦ profileDeficitPartition alpha lambda)
      atTop
      (𝓝 (extendedGaussianPartition (Real.log 2) lambda)) := by
  have h := (tendsto_profileDeficitExceptionalTerm lambda).add
    (tendsto_tsum_profileDeficitNaturalTerm lambda)
  simpa only [profileDeficitPartition_eq_exceptional_add_tsum,
    extendedGaussianPartition] using h

/-- The exact finite first deficit numerator converges to the extended
Gaussian first numerator at every fixed tilt. -/
theorem tendsto_profileDeficitFirstNumerator (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦ profileDeficitFirstNumerator alpha lambda)
      atTop
      (𝓝 (extendedGaussianFirstNumerator (Real.log 2) lambda)) := by
  have h := (tendsto_profileDeficitExceptionalTerm lambda).neg.add
    (tendsto_tsum_profileDeficitNaturalFirstMomentTerm lambda)
  simpa only [profileDeficitFirstNumerator_eq_neg_exceptional_add_tsum,
    extendedGaussianFirstNumerator] using h

/-- The exact finite second deficit numerator converges to the extended
Gaussian second numerator at every fixed tilt. -/
theorem tendsto_profileDeficitSecondNumerator (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦ profileDeficitSecondNumerator alpha lambda)
      atTop
      (𝓝 (extendedGaussianSecondNumerator (Real.log 2) lambda)) := by
  have h := (tendsto_profileDeficitExceptionalTerm lambda).add
    (tendsto_tsum_profileDeficitNaturalSecondMomentTerm lambda)
  simpa only [profileDeficitSecondNumerator_eq_exceptional_add_tsum,
    extendedGaussianSecondNumerator] using h

/-- The normalized finite deficit mean converges at every fixed tilt.  The
division is justified by the strict positivity of the limiting partition. -/
theorem tendsto_profileDeficitMean (lambda : ℝ) :
    Tendsto
      (fun alpha : ℕ ↦ profileDeficitMean alpha lambda)
      atTop
      (𝓝 (extendedGaussianMean (Real.log 2) lambda)) := by
  rw [show (fun alpha : ℕ ↦ profileDeficitMean alpha lambda) =
      fun alpha : ℕ ↦
        profileDeficitFirstNumerator alpha lambda /
          profileDeficitPartition alpha lambda by
    funext alpha
    exact profileDeficitMean_eq_firstNumerator_div alpha lambda]
  exact (tendsto_profileDeficitFirstNumerator lambda).div
    (tendsto_profileDeficitPartition lambda)
    (extendedGaussianPartition_ne_zero
      (show 0 < Real.log 2 by positivity))

end

end Erdos625
