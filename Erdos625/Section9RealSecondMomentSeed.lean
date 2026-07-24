import Erdos625.Section9CanonicalTwoRegimeSeed
import Mathlib.Tactic

/-!
# Section IX: real-valued midpoint second-moment seed

This module states the Section X input in the requested real form.  The real
normalized second moment is the finite `toReal` image of the exact Section VI
`ENNReal` quotient; no replacement probability law or altered normalization
is introduced.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

/-- The exact normalized signed-profile second moment as a real number. -/
noncomputable def signedProfileNormalizedSecondMomentReal
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) : ℝ :=
  (signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2).toReal

/-- The requested finite real inequality with the explicit canonical exponent.
This is the literal `E[Z^2] / E[Z]^2` quotient formalized in Section VI and
transported through the attained canonical-demand law. -/
theorem signedProfileNormalizedSecondMomentReal_le_exp_canonicalMidpointLambda
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) (hU : 2 ≤ U)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) :
    signedProfileNormalizedSecondMomentReal n k ≤
      Real.exp (canonicalMidpointLambda row₀ U) := by
  unfold signedProfileNormalizedSecondMomentReal
  have h := normalizedSignedProfileSecondMoment_le_exp_canonicalMidpointLambda
    row₀ U hU hcap
  have htop : ENNReal.ofReal (Real.exp (canonicalMidpointLambda row₀ U)) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  calc
    (signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2).toReal ≤
        (ENNReal.ofReal (Real.exp (canonicalMidpointLambda row₀ U))).toReal :=
      ENNReal.toReal_mono htop h
    _ = Real.exp (canonicalMidpointLambda row₀ U) := by
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]

/-- Complete real-valued theorem-level seed from the two concrete residual
regime estimates.  It returns exactly the exponential second-moment bound,
nonnegativity, and the Little-o property needed by Section X. -/
theorem real_canonicalMidpoint_secondMoment_seed_of_twoRegime
    (b U m₀ : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hlarge : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m₀ n : ℝ) →
      canonicalPolymerReal (row₀ n) (U n) ≤
        Real.exp (C * Real.log (n : ℝ) ^ 8))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      (m₀ n : ℝ) < (n : ℝ) / Real.log (n : ℝ) ^ 6 →
      canonicalPolymerReal (row₀ n) (U n) ≤
        Real.exp (C * (n : ℝ) / Real.log (n : ℝ) ^ 5)) :
    (∀ n, signedProfileNormalizedSecondMomentReal n (k n) ≤
      Real.exp (canonicalMidpointLambda (row₀ n) (U n))) ∧
    (∀ n, 0 ≤ canonicalMidpointLambda (row₀ n) (U n)) ∧
    (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase := by
  obtain ⟨_hsecond, hnonneg, hsmallLambda⟩ :=
    canonicalMidpoint_secondMoment_seed_of_twoRegime
      b U m₀ k row₀ C hC hU hcap hlarge hsmall
  exact ⟨fun n =>
    signedProfileNormalizedSecondMomentReal_le_exp_canonicalMidpointLambda
      (row₀ n) (U n) (hU n) (hcap n), hnonneg, hsmallLambda⟩

#print axioms signedProfileNormalizedSecondMomentReal_le_exp_canonicalMidpointLambda
#print axioms real_canonicalMidpoint_secondMoment_seed_of_twoRegime

end

end Erdos625
