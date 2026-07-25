import Erdos625.Section9QOnlyTwoRegimeAssembly
import Erdos625.Section9MidpointSecondMomentSeed
import Mathlib.Tactic

/-!
# Section IX: q-only normalized-second-moment frontier

The repaired q-only route bounds the literal attained attachment sum by the
Section VIII bare-skeleton sum times a vanishing exponential factor.  This
module composes that theorem with the exact normalized-second-moment identity.

Consequently the only analytic premise left visible here is a vanishing-scale
bound on `canonicalBareSkeletonSum`.  No polymer surrogate, independent demand
law, or additional residual adapter is introduced.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

set_option autoImplicit false

/-- A Section VIII bare-skeleton estimate and the q-only literal attachment
bound give the requested normalized signed-profile second-moment estimate.
The resulting exponent coefficient is the sum of the two vanishing
coefficients. -/
theorem exists_normalizedSignedProfileSecondMoment_qOnly_error_of_bareSkeleton
    (b U : Nat → Nat)
    (k : (n : Nat) → ColoringProfile (b n))
    (row0 : (n : Nat) → OrderedProfilePartition n (k n))
    (epsilonSkeleton : Nat → Real)
    (hUmin : ∀ᶠ n : Nat in atTop, 2 ≤ U n)
    (hPhase : ∀ᶠ n : Nat in atTop, U n ≤ phaseNat n)
    (hcap : ∀ᶠ n : Nat in atTop,
      ∀ a : ProfileBlockIndex (k n), profileBlockMargin (k n) a ≤ U n)
    (hSkeletonTendsto : Tendsto epsilonSkeleton atTop (nhds 0))
    (hSkeletonNonneg : ∀ᶠ n : Nat in atTop, 0 ≤ epsilonSkeleton n)
    (hSkeleton : ∀ᶠ n : Nat in atTop,
      canonicalBareSkeletonSum (k n) (U n) ≤
        ENNReal.ofReal
          (Real.exp (epsilonSkeleton n * amplificationBase n))) :
    ∃ epsilon : Nat → Real,
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ᶠ n : Nat in atTop, 0 ≤ epsilon n) ∧
      ∀ᶠ n : Nat in atTop,
        signedProfileSecondMoment n (k n) /
            signedProfileExpectation n (k n) ^ 2 ≤
          ENNReal.ofReal
            (Real.exp (epsilon n * amplificationBase n)) := by
  obtain ⟨epsilonAttachment, hAttachmentTendsto,
      hAttachmentNonneg, hAttachment⟩ :=
    exists_midpointCanonicalAttachment_qOnly_twoRegime_error
      b U k row0 hPhase hcap
  let epsilon := fun n => epsilonSkeleton n + epsilonAttachment n
  refine ⟨epsilon, ?_, ?_, ?_⟩
  · simpa [epsilon] using hSkeletonTendsto.add hAttachmentTendsto
  · filter_upwards [hSkeletonNonneg, hAttachmentNonneg] with n hs ha
    exact add_nonneg hs ha
  · filter_upwards [hUmin, hSkeleton, hAttachment] with n hUn hs ha
    rw [normalizedSignedProfileSecondMoment_eq_midpointCanonicalAttachmentSum
      (row0 n) (U n) hUn]
    calc
      midpointCanonicalAttachmentSum (row0 n) (U n) ≤
          canonicalBareSkeletonSum (k n) (U n) *
            ENNReal.ofReal
              (Real.exp (epsilonAttachment n * amplificationBase n)) := ha
      _ ≤ ENNReal.ofReal
            (Real.exp (epsilonSkeleton n * amplificationBase n)) *
          ENNReal.ofReal
            (Real.exp (epsilonAttachment n * amplificationBase n)) := by
        exact mul_le_mul_left hs _
      _ = ENNReal.ofReal
          (Real.exp (epsilon n * amplificationBase n)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        simp only [epsilon, add_mul]

#print axioms
  exists_normalizedSignedProfileSecondMoment_qOnly_error_of_bareSkeleton

end

end Erdos625
