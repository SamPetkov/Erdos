import Erdos625.SPlusPrimalDirect
import Mathlib.Tactic

/-!
# Coordinate bounds for the direct `S₊` primal

These are finite, zero-safe coordinate identities and inequalities.  They do
not use the mass, moment, or entropy limits from `SPlusPrimalProfile`.
-/

namespace Erdos625

/-- Logarithm of one normalized natural-coordinate Gaussian weight. -/
theorem log_normalized_extendedGaussianNaturalTerm (tilt : ℝ) (d : ℕ) :
    Real.log
      (extendedGaussianNaturalTerm q tilt d /
        extendedGaussianPartition q tilt) =
    tilt * (d : ℝ) + extendedGaussianNaturalScore q d -
      Real.log (extendedGaussianPartition q tilt) := by
  have hNatural : extendedGaussianNaturalTerm q tilt d ≠ 0 :=
    (extendedGaussianNaturalTerm_pos q tilt d).ne'
  have hPartition : extendedGaussianPartition q tilt ≠ 0 :=
    extendedGaussianPartition_ne_zero q_pos
  rw [Real.log_div hNatural hPartition]
  simp only [extendedGaussianNaturalTerm, Real.log_exp,
    extendedGaussianNaturalScore]
  ring

/-- Logarithm of the normalized exceptional Gaussian atom. -/
theorem log_normalized_extendedGaussianExceptionalAtom (tilt : ℝ) :
    Real.log
      (extendedGaussianExceptionalAtom q tilt /
        extendedGaussianPartition q tilt) =
    -tilt + extendedGaussianExceptionalScore q -
      Real.log (extendedGaussianPartition q tilt) := by
  rw [Real.log_div (extendedGaussianExceptionalAtom_pos q tilt).ne'
    (extendedGaussianPartition_ne_zero q_pos)]
  rw [extendedGaussianExceptionalAtom, Real.log_exp]
  simp only [extendedGaussianExceptionalScore]
  ring

/-- Zero-safe Gibbs inequality at a natural deficit coordinate. -/
theorem extendedGaussianNaturalEntropyTerm_le_normalized
    (tilt : ℝ) (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    -x * Real.log x + x * extendedGaussianNaturalScore q d ≤
      extendedGaussianNaturalTerm q tilt d /
          extendedGaussianPartition q tilt - x +
        Real.log (extendedGaussianPartition q tilt) * x -
          tilt * ((d : ℝ) * x) := by
  have hPartition : 0 < extendedGaussianPartition q tilt :=
    extendedGaussianPartition_pos q_pos
  have hTerm : 0 < extendedGaussianNaturalTerm q tilt d :=
    extendedGaussianNaturalTerm_pos q tilt d
  have hNormalized :
      0 < extendedGaussianNaturalTerm q tilt d /
        extendedGaussianPartition q tilt :=
    div_pos hTerm hPartition
  have hLogNormalized :
      Real.log (extendedGaussianNaturalTerm q tilt d /
          extendedGaussianPartition q tilt) =
        tilt * (d : ℝ) + extendedGaussianNaturalScore q d -
          Real.log (extendedGaussianPartition q tilt) := by
    rw [Real.log_div hTerm.ne' hPartition.ne']
    simp only [extendedGaussianNaturalTerm, extendedGaussianNaturalScore,
      Real.log_exp]
    ring
  have hGibbs :=
    ProfileEntropyS4.neg_mul_log_add_mul_log_le_sub hx hNormalized
  rw [hLogNormalized] at hGibbs
  linarith

/-- Zero-safe Gibbs inequality at the exceptional deficit coordinate. -/
theorem extendedGaussianExceptionalEntropyTerm_le_normalized
    (tilt : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    -x * Real.log x + x * extendedGaussianExceptionalScore q ≤
      extendedGaussianExceptionalAtom q tilt /
          extendedGaussianPartition q tilt - x +
        Real.log (extendedGaussianPartition q tilt) * x + tilt * x := by
  have hpartition : 0 < extendedGaussianPartition q tilt :=
    extendedGaussianPartition_pos q_pos
  have hatom : 0 < extendedGaussianExceptionalAtom q tilt :=
    extendedGaussianExceptionalAtom_pos q tilt
  have hnormalized :
      Real.log (extendedGaussianExceptionalAtom q tilt /
          extendedGaussianPartition q tilt) =
        extendedGaussianExceptionalScore q - tilt -
          Real.log (extendedGaussianPartition q tilt) := by
    rw [Real.log_div hatom.ne' hpartition.ne']
    simp [extendedGaussianExceptionalAtom, extendedGaussianExceptionalScore]
    ring
  have hgibbs := ProfileEntropyS4.neg_mul_log_add_mul_log_le_sub hx
    (div_pos hatom hpartition)
  rw [hnormalized] at hgibbs
  linarith

end Erdos625
