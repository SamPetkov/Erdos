import Erdos625.TiltedGaussianSummability

/-!
# The extended tilted-Gaussian deficit profile

This module defines the limiting weight profile on the deficit coordinates
`{-1, 0, 1, ...}`.  The exceptional deficit `-1` has weight

`exp (-lambda - a / 2)`,

while a natural deficit `d` has weight

`exp (lambda * d - a / 2 * d ^ 2)`.

The partition function and its first two unnormalized moments are represented
as an exceptional atom plus a `tsum` over the natural deficits.  Only
foundational analytic and algebraic properties are established here.  In
particular, this module makes no differentiability, endpoint, optimizer, or
strict-variance claim.
-/

namespace Erdos625

noncomputable section

/-- The unnormalized limiting weight at a natural deficit `d >= 0`. -/
def extendedGaussianNaturalTerm (a lambda : ℝ) (d : ℕ) : ℝ :=
  Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)

/-- The exceptional limiting weight at deficit `-1`. -/
def extendedGaussianExceptionalAtom (a lambda : ℝ) : ℝ :=
  Real.exp (-lambda - a / 2)

/-- The total mass of the extended tilted-Gaussian profile on
`{-1, 0, 1, ...}`. -/
def extendedGaussianPartition (a lambda : ℝ) : ℝ :=
  extendedGaussianExceptionalAtom a lambda +
    ∑' d : ℕ, extendedGaussianNaturalTerm a lambda d

/-- The unnormalized first moment of the extended profile.  The exceptional
atom contributes its coordinate `-1`. -/
def extendedGaussianFirstNumerator (a lambda : ℝ) : ℝ :=
  -extendedGaussianExceptionalAtom a lambda +
    ∑' d : ℕ, (d : ℝ) * extendedGaussianNaturalTerm a lambda d

/-- The unnormalized second moment of the extended profile.  The exceptional
atom contributes `(-1)^2 = 1`. -/
def extendedGaussianSecondNumerator (a lambda : ℝ) : ℝ :=
  extendedGaussianExceptionalAtom a lambda +
    ∑' d : ℕ, ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d

/-- The normalized mean deficit of the extended profile. -/
def extendedGaussianMean (a lambda : ℝ) : ℝ :=
  extendedGaussianFirstNumerator a lambda /
    extendedGaussianPartition a lambda

/-- The raw variance obtained from the normalized first and second moments. -/
def extendedGaussianRawVariance (a lambda : ℝ) : ℝ :=
  extendedGaussianSecondNumerator a lambda /
      extendedGaussianPartition a lambda -
    (extendedGaussianMean a lambda) ^ 2

@[simp]
theorem extendedGaussianNaturalTerm_zero (a lambda : ℝ) :
    extendedGaussianNaturalTerm a lambda 0 = 1 := by
  simp [extendedGaussianNaturalTerm]

theorem extendedGaussianNaturalTerm_pos (a lambda : ℝ) (d : ℕ) :
    0 < extendedGaussianNaturalTerm a lambda d := by
  exact Real.exp_pos _

theorem extendedGaussianExceptionalAtom_pos (a lambda : ℝ) :
    0 < extendedGaussianExceptionalAtom a lambda := by
  exact Real.exp_pos _

/-- The natural-index mass is summable whenever the quadratic coefficient is
positive. -/
theorem summable_extendedGaussianNaturalTerm
    {a lambda : ℝ} (ha : 0 < a) :
    Summable (extendedGaussianNaturalTerm a lambda) := by
  change Summable
    (fun d : ℕ ↦
      Real.exp (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2))
  exact (summable_tiltedGaussian_moments
    (a := a) (lambda := lambda) ha).1

/-- The natural-index first-moment series is summable. -/
theorem summable_extendedGaussianFirstMoment
    {a lambda : ℝ} (ha : 0 < a) :
    Summable
      (fun d : ℕ ↦
        (d : ℝ) * extendedGaussianNaturalTerm a lambda d) := by
  simpa [extendedGaussianNaturalTerm] using
    (summable_tiltedGaussian_moments (a := a) (lambda := lambda) ha).2.1

/-- The natural-index second-moment series is summable. -/
theorem summable_extendedGaussianSecondMoment
    {a lambda : ℝ} (ha : 0 < a) :
    Summable
      (fun d : ℕ ↦
        ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d) := by
  simpa [extendedGaussianNaturalTerm] using
    (summable_tiltedGaussian_moments (a := a) (lambda := lambda) ha).2.2

/-- The natural-index `tsum` is at least its deficit-zero atom. -/
theorem one_le_tsum_extendedGaussianNaturalTerm
    {a lambda : ℝ} (ha : 0 < a) :
    1 ≤ ∑' d : ℕ, extendedGaussianNaturalTerm a lambda d := by
  calc
    1 = ∑ d ∈ ({0} : Finset ℕ),
        extendedGaussianNaturalTerm a lambda d := by simp
    _ ≤ ∑' d : ℕ, extendedGaussianNaturalTerm a lambda d :=
      (summable_extendedGaussianNaturalTerm ha).sum_le_tsum
        ({0} : Finset ℕ)
        (fun d _ ↦ (extendedGaussianNaturalTerm_pos a lambda d).le)

/-- The deficit-zero atom gives the lower bound `1`, in addition to the
strictly positive exceptional atom. -/
theorem exceptionalAtom_add_one_le_extendedGaussianPartition
    {a lambda : ℝ} (ha : 0 < a) :
    extendedGaussianExceptionalAtom a lambda + 1 ≤
      extendedGaussianPartition a lambda := by
  rw [extendedGaussianPartition]
  simpa [add_comm] using
    add_le_add_left (one_le_tsum_extendedGaussianNaturalTerm ha)
      (extendedGaussianExceptionalAtom a lambda)

theorem one_lt_extendedGaussianPartition
    {a lambda : ℝ} (ha : 0 < a) :
    1 < extendedGaussianPartition a lambda := by
  have hatom := extendedGaussianExceptionalAtom_pos a lambda
  have hlower :=
    exceptionalAtom_add_one_le_extendedGaussianPartition
      (a := a) (lambda := lambda) ha
  linarith

theorem one_le_extendedGaussianPartition
    {a lambda : ℝ} (ha : 0 < a) :
    1 ≤ extendedGaussianPartition a lambda :=
  (one_lt_extendedGaussianPartition ha).le

theorem extendedGaussianPartition_pos
    {a lambda : ℝ} (ha : 0 < a) :
    0 < extendedGaussianPartition a lambda :=
  lt_trans zero_lt_one (one_lt_extendedGaussianPartition ha)

theorem extendedGaussianPartition_ne_zero
    {a lambda : ℝ} (ha : 0 < a) :
    extendedGaussianPartition a lambda ≠ 0 :=
  ne_of_gt (extendedGaussianPartition_pos ha)

/-! ## Exact algebraic identities -/

theorem extendedGaussianPartition_sub_exceptionalAtom
    (a lambda : ℝ) :
    extendedGaussianPartition a lambda -
        extendedGaussianExceptionalAtom a lambda =
      ∑' d : ℕ, extendedGaussianNaturalTerm a lambda d := by
  simp [extendedGaussianPartition]

theorem extendedGaussianFirstNumerator_add_exceptionalAtom
    (a lambda : ℝ) :
    extendedGaussianFirstNumerator a lambda +
        extendedGaussianExceptionalAtom a lambda =
      ∑' d : ℕ,
        (d : ℝ) * extendedGaussianNaturalTerm a lambda d := by
  simp [extendedGaussianFirstNumerator]

theorem extendedGaussianSecondNumerator_sub_exceptionalAtom
    (a lambda : ℝ) :
    extendedGaussianSecondNumerator a lambda -
        extendedGaussianExceptionalAtom a lambda =
      ∑' d : ℕ,
        ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm a lambda d := by
  simp [extendedGaussianSecondNumerator]

theorem extendedGaussianMean_mul_partition
    {a lambda : ℝ} (ha : 0 < a) :
    extendedGaussianMean a lambda * extendedGaussianPartition a lambda =
      extendedGaussianFirstNumerator a lambda := by
  exact div_mul_cancel₀ _ (extendedGaussianPartition_ne_zero ha)

theorem extendedGaussianRawVariance_add_mean_sq
    (a lambda : ℝ) :
    extendedGaussianRawVariance a lambda +
        (extendedGaussianMean a lambda) ^ 2 =
      extendedGaussianSecondNumerator a lambda /
        extendedGaussianPartition a lambda := by
  simp [extendedGaussianRawVariance]

theorem extendedGaussianRawVariance_add_mean_sq_mul_partition
    {a lambda : ℝ} (ha : 0 < a) :
    (extendedGaussianRawVariance a lambda +
        (extendedGaussianMean a lambda) ^ 2) *
        extendedGaussianPartition a lambda =
      extendedGaussianSecondNumerator a lambda := by
  rw [extendedGaussianRawVariance_add_mean_sq]
  exact div_mul_cancel₀ _ (extendedGaussianPartition_ne_zero ha)

theorem extendedGaussianRawVariance_eq_moment_quotients
    (a lambda : ℝ) :
    extendedGaussianRawVariance a lambda =
      extendedGaussianSecondNumerator a lambda /
          extendedGaussianPartition a lambda -
        (extendedGaussianFirstNumerator a lambda /
          extendedGaussianPartition a lambda) ^ 2 := by
  rfl

end

end Erdos625
