import Erdos625.ColoringProfileDualOptimizer
import Erdos625.Phase

/-!
# Exact deficit-coordinate form of the coloring-profile dual

For support sizes `1, …, α + 1`, the manuscript uses the deficit
`i = α - size`, whose range is `{-1, 0, …, α - 1}`.  This module performs
that reindexing without changing the finite index type.  It separates the
large affine part of the class score from a centered residual score and
proves the exact relation

`λ_deficit = B_α - t_size`.

No asymptotic estimate for the residual score, boundedness of `λ`, root
location, or rounding decrement is asserted here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Deficit `α - size` on the size support `1, …, α + 1`.  The largest class
has deficit `-1`. -/
def profileDeficit (alpha : ℕ) (i : Fin (alpha + 1)) : ℝ :=
  (alpha : ℝ) - profileClassSize i

/-- Constant affine score in the manuscript decomposition. -/
def profileDeficitAffineA (alpha : ℕ) : ℝ :=
  -coloringClassLogCost alpha

/-- Linear affine score in the manuscript decomposition. -/
def profileDeficitAffineB (alpha : ℕ) : ℝ :=
  q * (alpha : ℝ) - q / 2 + Real.log (alpha : ℝ)

/-- The exact score remaining after subtracting `A_α + B_α i`. -/
def profileDeficitResidualScore (alpha : ℕ)
    (i : Fin (alpha + 1)) : ℝ :=
  profileDualScore i - profileDeficitAffineA alpha -
    profileDeficitAffineB alpha * profileDeficit alpha i

theorem profileClassSize_add_profileDeficit (alpha : ℕ)
    (i : Fin (alpha + 1)) :
    profileClassSize i + profileDeficit alpha i = (alpha : ℝ) := by
  simp [profileDeficit]

theorem profileDualScore_eq_deficitAffine_add_residual (alpha : ℕ)
    (i : Fin (alpha + 1)) :
    profileDualScore i =
      profileDeficitAffineA alpha +
        profileDeficitAffineB alpha * profileDeficit alpha i +
          profileDeficitResidualScore alpha i := by
  unfold profileDeficitResidualScore
  ring

/-- Centered unnormalized mass in deficit coordinates. -/
def profileDeficitUnnormalized (alpha : ℕ) (lambda : ℝ)
    (i : Fin (alpha + 1)) : ℝ :=
  Real.exp
    (profileDeficitResidualScore alpha i +
      lambda * profileDeficit alpha i)

/-- Centered deficit partition function. -/
def profileDeficitPartition (alpha : ℕ) (lambda : ℝ) : ℝ :=
  ∑ i : Fin (alpha + 1), profileDeficitUnnormalized alpha lambda i

theorem profileDeficitUnnormalized_pos (alpha : ℕ) (lambda : ℝ)
    (i : Fin (alpha + 1)) :
    0 < profileDeficitUnnormalized alpha lambda i :=
  Real.exp_pos _

theorem profileDeficitPartition_pos (alpha : ℕ) (lambda : ℝ) :
    0 < profileDeficitPartition alpha lambda := by
  let i0 : Fin (alpha + 1) := ⟨0, Nat.succ_pos alpha⟩
  exact Finset.sum_pos'
    (fun i _ ↦ (profileDeficitUnnormalized_pos alpha lambda i).le)
    ⟨i0, Finset.mem_univ i0,
      profileDeficitUnnormalized_pos alpha lambda i0⟩

/-- Normalized centered deficit weight. -/
def profileDeficitWeight (alpha : ℕ) (lambda : ℝ)
    (i : Fin (alpha + 1)) : ℝ :=
  profileDeficitUnnormalized alpha lambda i /
    profileDeficitPartition alpha lambda

theorem profileDeficitWeight_pos (alpha : ℕ) (lambda : ℝ)
    (i : Fin (alpha + 1)) :
    0 < profileDeficitWeight alpha lambda i :=
  div_pos (profileDeficitUnnormalized_pos alpha lambda i)
    (profileDeficitPartition_pos alpha lambda)

theorem sum_profileDeficitWeight (alpha : ℕ) (lambda : ℝ) :
    ∑ i : Fin (alpha + 1), profileDeficitWeight alpha lambda i = 1 := by
  simp only [profileDeficitWeight]
  rw [← Finset.sum_div, profileDeficitPartition]
  exact div_self (profileDeficitPartition_pos alpha lambda).ne'

/-- Mean deficit under the centered family. -/
def profileDeficitMean (alpha : ℕ) (lambda : ℝ) : ℝ :=
  ∑ i : Fin (alpha + 1),
    profileDeficitWeight alpha lambda i * profileDeficit alpha i

/-- Exact factorization of each size-coordinate mass. -/
theorem profileDualUnnormalized_eq_deficitScaled
    (alpha : ℕ) (lambda : ℝ) (i : Fin (alpha + 1)) :
    profileDualUnnormalized
        (profileDeficitAffineB alpha - lambda) i =
      Real.exp
          (profileDeficitAffineA alpha +
            (profileDeficitAffineB alpha - lambda) * (alpha : ℝ)) *
        profileDeficitUnnormalized alpha lambda i := by
  rw [profileDualUnnormalized, profileDeficitUnnormalized, ← Real.exp_add]
  rw [profileDualScore_eq_deficitAffine_add_residual]
  congr 1
  unfold profileDeficit profileClassSize
  ring

/-- Exact partition-function factorization. -/
theorem profileDualPartition_eq_deficitScaled
    (alpha : ℕ) (lambda : ℝ) :
    profileDualPartition (alpha + 1)
        (profileDeficitAffineB alpha - lambda) =
      Real.exp
          (profileDeficitAffineA alpha +
            (profileDeficitAffineB alpha - lambda) * (alpha : ℝ)) *
        profileDeficitPartition alpha lambda := by
  rw [profileDualPartition, profileDeficitPartition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact profileDualUnnormalized_eq_deficitScaled alpha lambda i

/-- Logarithmic form of the exact partition factorization. -/
theorem log_profileDualPartition_eq_deficitCentered
    (alpha : ℕ) (lambda : ℝ) :
    Real.log
        (profileDualPartition (alpha + 1)
          (profileDeficitAffineB alpha - lambda)) =
      profileDeficitAffineA alpha +
        (profileDeficitAffineB alpha - lambda) * (alpha : ℝ) +
          Real.log (profileDeficitPartition alpha lambda) := by
  rw [profileDualPartition_eq_deficitScaled,
    Real.log_mul (Real.exp_ne_zero _)
      (profileDeficitPartition_pos alpha lambda).ne',
    Real.log_exp]

/-- Centering does not change normalized weights. -/
theorem profileDualWeight_eq_profileDeficitWeight
    (alpha : ℕ) (lambda : ℝ) (i : Fin (alpha + 1)) :
    profileDualWeight (profileDeficitAffineB alpha - lambda) i =
      profileDeficitWeight alpha lambda i := by
  rw [profileDualWeight, profileDeficitWeight,
    profileDualUnnormalized_eq_deficitScaled,
    profileDualPartition_eq_deficitScaled]
  field_simp [Real.exp_ne_zero _,
    (profileDeficitPartition_pos alpha lambda).ne']

/-- The size mean is `α` minus the deficit mean. -/
theorem profileDualMean_eq_alpha_sub_profileDeficitMean
    (alpha : ℕ) (lambda : ℝ) :
    profileDualMean (alpha + 1)
        (profileDeficitAffineB alpha - lambda) =
      (alpha : ℝ) - profileDeficitMean alpha lambda := by
  rw [profileDualMean_eq_sum_weight_size]
  calc
    (∑ i : Fin (alpha + 1),
        profileDualWeight (profileDeficitAffineB alpha - lambda) i *
          profileClassSize i) =
        ∑ i : Fin (alpha + 1),
          profileDeficitWeight alpha lambda i *
            ((alpha : ℝ) - profileDeficit alpha i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [profileDualWeight_eq_profileDeficitWeight]
      have hSize := profileClassSize_add_profileDeficit alpha i
      congr 1
      linarith
    _ = (alpha : ℝ) *
          (∑ i : Fin (alpha + 1),
            profileDeficitWeight alpha lambda i) -
        ∑ i : Fin (alpha + 1),
          profileDeficitWeight alpha lambda i *
            profileDeficit alpha i := by
      calc
        _ = ∑ i : Fin (alpha + 1),
              ((alpha : ℝ) * profileDeficitWeight alpha lambda i -
                profileDeficitWeight alpha lambda i *
                  profileDeficit alpha i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = (∑ i : Fin (alpha + 1),
                (alpha : ℝ) * profileDeficitWeight alpha lambda i) -
              ∑ i : Fin (alpha + 1),
                profileDeficitWeight alpha lambda i *
                  profileDeficit alpha i := by
            rw [Finset.sum_sub_distrib]
        _ = _ := by rw [Finset.mul_sum]
    _ = (alpha : ℝ) - profileDeficitMean alpha lambda := by
      rw [sum_profileDeficitWeight]
      unfold profileDeficitMean
      ring

/-- Deficit target corresponding to a prescribed size mean `n / parts`. -/
def profileDeficitTarget (alpha : ℕ) (n parts : ℝ) : ℝ :=
  (alpha : ℝ) - n / parts

theorem profileDualMean_eq_iff_profileDeficitMean_eq
    (alpha : ℕ) {n parts lambda : ℝ} :
    profileDualMean (alpha + 1)
        (profileDeficitAffineB alpha - lambda) = n / parts ↔
      profileDeficitMean alpha lambda =
        profileDeficitTarget alpha n parts := by
  rw [profileDualMean_eq_alpha_sub_profileDeficitMean]
  unfold profileDeficitTarget
  constructor <;> intro h <;> linarith

/-- Exact centered form of the finite dual objective.  This is the algebraic
bridge to the manuscript's deficit-coordinate entropy functional. -/
theorem profileDualUpper_eq_deficitCentered
    (alpha : ℕ) {n parts : ℝ} (hparts : parts ≠ 0) (lambda : ℝ) :
    profileDualUpper (alpha + 1) n parts
        (profileDeficitAffineB alpha - lambda) =
      n * Real.log n - n + parts - parts * Real.log parts +
        parts *
          (profileDeficitAffineA alpha +
            profileDeficitAffineB alpha *
              profileDeficitTarget alpha n parts +
            Real.log (profileDeficitPartition alpha lambda) -
            lambda * profileDeficitTarget alpha n parts) := by
  unfold profileDualUpper profileDeficitTarget
  rw [log_profileDualPartition_eq_deficitCentered]
  field_simp [hparts]
  ring

end

end Erdos625
