import Erdos625.ColoringProfilePhaseObjectiveDeficitDecomposition
import Erdos625.SignedFourEntropyLossDecomposition
import Mathlib.Tactic

/-!
# Exact signed versus unrestricted phase-objective gap

The signed four-size root and the unrestricted profile root are defined by two
different finite objective functions.  This module identifies their exact
pointwise difference before taking any limit.

At a common real part count, the factorial, part-count, affine-deficit, and
logarithmic terms cancel.  The remaining normalized difference is precisely

`q - (finite unrestricted deficit entropy - finite four-size entropy)`.

The finite entropy loss is then decomposed into the manuscript limiting loss
plus two independently auditable errors:

* the finite four-score approximation error;
* the finite unrestricted-entropy approximation error.

No root existence, derivative bound, asymptotic estimate, first moment,
chromatic tail, partial diagonal, second moment, or final Erdős statement is
proved here.
-/

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The attained finite unrestricted deficit entropy at target mean `T`. -/
noncomputable def finiteUnrestrictedDeficitEntropy
    (alpha : ℕ) (T : ℝ) : ℝ :=
  Real.log
      (profileDeficitPartition alpha
        (profileDeficitTilt alpha T)) -
    profileDeficitTilt alpha T * T

/-- Exact finite entropy loss incurred by restricting the unrestricted deficit
support to the four deficits `{2,3,4,5}`. -/
noncomputable def finiteSignedFourEntropyLoss
    (alpha : ℕ) (T : ℝ) : ℝ :=
  finiteUnrestrictedDeficitEntropy alpha T -
    fourSizeFiniteEntropy alpha T

/-- Error from replacing the exact finite four-deficit scores by their
limiting Gaussian scores. -/
noncomputable def finiteFourScoreEntropyError
    (alpha : ℕ) (T : ℝ) : ℝ :=
  ProfileEntropyS4.optimizedValue fourGaussianScore T -
    ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T

/-- Error from replacing the exact finite unrestricted deficit entropy by the
extended-Gaussian entropy. -/
noncomputable def finiteUnrestrictedEntropyError
    (alpha : ℕ) (T : ℝ) : ℝ :=
  finiteUnrestrictedDeficitEntropy alpha T -
    extendedGaussianEntropyValue T

/-- Exact finite signed margin at deficit target `T`. -/
noncomputable def finiteSignedFourMargin
    (alpha : ℕ) (T : ℝ) : ℝ :=
  q - finiteSignedFourEntropyLoss alpha T

/-- The signed and unrestricted objectives use definitionally identical
deficit targets. -/
theorem fourSizeTarget_eq_profileDeficitTarget
    (n alpha : ℕ) (parts : ℝ) :
    fourSizeTarget n alpha parts =
      profileDeficitTarget alpha (n : ℝ) parts := by
  rfl

/-- Exact normalized pointwise difference between the signed four-size
objective and the unrestricted phase objective.  Every common finite term
cancels; no asymptotic approximation is used. -/
theorem
    phaseSignedFourSizeObjective_div_sub_unrestrictedPhaseObjective_div_eq_finiteMargin
    (n : ℕ) {parts : ℝ} (hparts : parts ≠ 0) :
    phaseSignedFourSizeObjective n parts / parts -
        unrestrictedPhaseObjective n parts / parts =
      finiteSignedFourMargin (phaseNat n)
        (fourSizeTarget n (phaseNat n) parts) := by
  rw [unrestrictedPhaseObjective_div_eq_deficitCentered n hparts]
  unfold phaseSignedFourSizeObjective signedFourSizeObjective
    signedFourSizeObjectiveAtTarget finiteSignedFourMargin
    finiteSignedFourEntropyLoss finiteUnrestrictedDeficitEntropy
    fourSizeTarget profileDeficitTarget
  field_simp [hparts]
  ring

/-- The exact finite entropy loss is the limiting four-size loss plus the two
separate finite approximation errors. -/
theorem finiteSignedFourEntropyLoss_eq_limiting_add_errors
    (alpha : ℕ) (T : ℝ) :
    finiteSignedFourEntropyLoss alpha T =
      fourEntropyLoss T +
        finiteFourScoreEntropyError alpha T +
          finiteUnrestrictedEntropyError alpha T := by
  calc
    finiteSignedFourEntropyLoss alpha T =
        finiteUnrestrictedEntropyError alpha T +
          (extendedGaussianEntropyValue T -
            fourSizeFiniteEntropy alpha T) := by
      unfold finiteSignedFourEntropyLoss finiteUnrestrictedEntropyError
      ring
    _ = finiteUnrestrictedEntropyError alpha T +
          (fourEntropyLoss T +
            finiteFourScoreEntropyError alpha T) := by
      rw [finite_four_entropy_loss_eq_limiting_add_error]
      rfl
    _ = fourEntropyLoss T +
          finiteFourScoreEntropyError alpha T +
            finiteUnrestrictedEntropyError alpha T := by
      ring

/-- Corresponding exact decomposition of the finite signed margin. -/
theorem finiteSignedFourMargin_eq_limiting_sub_errors
    (alpha : ℕ) (T : ℝ) :
    finiteSignedFourMargin alpha T =
      q - fourEntropyLoss T -
        finiteFourScoreEntropyError alpha T -
          finiteUnrestrictedEntropyError alpha T := by
  rw [finiteSignedFourMargin,
    finiteSignedFourEntropyLoss_eq_limiting_add_errors]
  ring

/-- At an unrestricted root, the signed objective is exactly the part count
multiplied by the finite signed entropy margin. -/
theorem
    phaseSignedFourSizeObjective_eq_parts_mul_finiteMargin_of_unrestrictedRoot
    (n : ℕ) {parts : ℝ} (hparts : parts ≠ 0)
    (hRoot : unrestrictedPhaseObjective n parts = 0) :
    phaseSignedFourSizeObjective n parts =
      parts * finiteSignedFourMargin (phaseNat n)
        (fourSizeTarget n (phaseNat n) parts) := by
  have h :=
    phaseSignedFourSizeObjective_div_sub_unrestrictedPhaseObjective_div_eq_finiteMargin
      n hparts
  rw [hRoot, zero_div, sub_zero] at h
  have hMul := (div_eq_iff hparts).mp h
  simpa only [mul_comm] using hMul

/-- Secant slope of the signed phase objective between candidate signed and
unrestricted roots. -/
noncomputable def phaseSignedFourRootSecantSlope
    (n : ℕ) (rCo rPlus : ℝ) : ℝ :=
  (phaseSignedFourSizeObjective n rPlus -
      phaseSignedFourSizeObjective n rCo) /
    (rPlus - rCo)

/-- Exact finite root-gap ledger.  Once `rCo` is a signed root and `rPlus` is
an unrestricted root, the signed secant increment equals the unrestricted
root count times the exact finite entropy margin.  This is the algebraic core
of the later root-gap asymptotic. -/
theorem phaseSignedFourRootSecantSlope_mul_gap_eq
    (n : ℕ) {rCo rPlus : ℝ}
    (hGap : rPlus - rCo ≠ 0)
    (hPlus : rPlus ≠ 0)
    (hCoRoot : phaseSignedFourSizeObjective n rCo = 0)
    (hPlusRoot : unrestrictedPhaseObjective n rPlus = 0) :
    phaseSignedFourRootSecantSlope n rCo rPlus *
        (rPlus - rCo) =
      rPlus * finiteSignedFourMargin (phaseNat n)
        (fourSizeTarget n (phaseNat n) rPlus) := by
  unfold phaseSignedFourRootSecantSlope
  rw [div_mul_cancel₀ _ hGap, hCoRoot, sub_zero]
  exact
    phaseSignedFourSizeObjective_eq_parts_mul_finiteMargin_of_unrestrictedRoot
      n hPlus hPlusRoot

#print axioms fourSizeTarget_eq_profileDeficitTarget
#print axioms phaseSignedFourSizeObjective_div_sub_unrestrictedPhaseObjective_div_eq_finiteMargin
#print axioms finiteSignedFourEntropyLoss_eq_limiting_add_errors
#print axioms finiteSignedFourMargin_eq_limiting_sub_errors
#print axioms phaseSignedFourSizeObjective_eq_parts_mul_finiteMargin_of_unrestrictedRoot
#print axioms phaseSignedFourRootSecantSlope_mul_gap_eq

end

end Erdos625