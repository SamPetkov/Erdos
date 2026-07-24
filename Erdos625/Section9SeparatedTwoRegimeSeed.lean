import Erdos625.Section9CanonicalPolymerAggregation
import Erdos625.Section9AttachmentAsymptotics
import Mathlib.Tactic

/-!
# Section IX: separated two-regime attachment assembly

This module applies the existing two-regime argument uniformly over the actual
dependent family of attained canonical demands.  It then combines that result
with a separate Section VIII skeleton estimate.  No common residual law is
introduced: the residual mass and polymer majorant are evaluated demand by
demand using the canonical reference witness.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

/-- Residual row-stub mass of an attained canonical demand. -/
def canonicalDemandResidualMass
    {b : ℕ} (k : ColoringProfile b) (U : ℕ)
    (demand : ProfileCanonicalHighSkeleton k U) : ℕ :=
  Finset.univ.sum
    (residualRowDegree
      (canonicalDemandReferenceWitness (profileBlockMargin k)
        (profileBlockMargin k) U demand))

/-- Finite real value of one attained demand's polymer majorant. -/
noncomputable def canonicalDemandPolymerReal
    {b : ℕ} (k : ColoringProfile b) (U : ℕ)
    (demand : ProfileCanonicalHighSkeleton k U) : ℝ :=
  (canonicalDemandPolymerMajorant
    (profileBlockMargin k) (profileBlockMargin k) U demand).toReal

/-- Exact recovery of one finite canonical polymer majorant from its real
value. -/
theorem ofReal_canonicalDemandPolymerReal
    {b : ℕ} (k : ColoringProfile b) (U : ℕ)
    (demand : ProfileCanonicalHighSkeleton k U) :
    ENNReal.ofReal (canonicalDemandPolymerReal k U demand) =
      canonicalDemandPolymerMajorant
        (profileBlockMargin k) (profileBlockMargin k) U demand := by
  exact ENNReal.ofReal_toReal
    (canonicalDemandPolymerMajorant_ne_top
      (profileBlockMargin k) (profileBlockMargin k) U demand)

/-- Uniform large- and small-residual bounds over the literal attained-demand
family produce one nonnegative vanishing attachment coefficient. -/
theorem exists_canonicalDemandAttachment_twoRegime_error
    (b U : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (C : ℝ) (hC : 0 ≤ C)
    (hlarge : ∀ᶠ n : ℕ in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤
            (canonicalDemandResidualMass (k n) (U n) demand : ℝ) →
        canonicalDemandPolymerReal (k n) (U n) demand ≤
          Real.exp (C * Real.log (n : ℝ) ^ 8))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (canonicalDemandResidualMass (k n) (U n) demand : ℝ) <
            (n : ℝ) / Real.log (n : ℝ) ^ 6 →
        canonicalDemandPolymerReal (k n) (U n) demand ≤
          Real.exp (C * (n : ℝ) / Real.log (n : ℝ) ^ 5)) :
    ∃ epsilonAttachment : ℕ → ℝ,
      Tendsto epsilonAttachment atTop (nhds 0) ∧
      (∀ᶠ n in atTop, 0 ≤ epsilonAttachment n) ∧
      ∀ᶠ n in atTop,
        ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
          canonicalDemandPolymerMajorant
            (profileBlockMargin (k n)) (profileBlockMargin (k n))
              (U n) demand ≤
            ENNReal.ofReal
              (Real.exp (epsilonAttachment n * amplificationBase n)) := by
  obtain ⟨epsilonAttachment, hepsilon, hevent⟩ :=
    exists_uniform_twoRegime_error
      (fun n => ProfileCanonicalHighSkeleton (k n) (U n))
      (fun n demand => canonicalDemandPolymerReal (k n) (U n) demand)
      (fun n demand => canonicalDemandResidualMass (k n) (U n) demand)
      C hC hlarge hsmall
  refine ⟨epsilonAttachment, hepsilon, hevent.mono fun n hn => hn.1, ?_⟩
  filter_upwards [hevent] with n hn
  intro demand
  rw [← ofReal_canonicalDemandPolymerReal (k n) (U n) demand]
  apply ENNReal.ofReal_le_ofReal
  simpa only [amplificationBase, mul_div_assoc] using hn.2 demand

/-- Complete real seed from a Section VIII skeleton estimate and the concrete
Section IX large- and small-residual estimates, all over the attained canonical
demand family. -/
theorem real_canonicalMidpoint_secondMoment_seed_of_skeleton_and_twoRegime
    (b U : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (epsilonSkeleton : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hSkeletonNonneg : ∀ᶠ n in atTop, 0 ≤ epsilonSkeleton n)
    (hSkeletonTendsto : Tendsto epsilonSkeleton atTop (nhds 0))
    (hSkeleton : ∀ᶠ n in atTop,
      canonicalBareSkeletonSum (k n) (U n) ≤
        ENNReal.ofReal
          (Real.exp (epsilonSkeleton n * amplificationBase n)))
    (hlarge : ∀ᶠ n : ℕ in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤
            (canonicalDemandResidualMass (k n) (U n) demand : ℝ) →
        canonicalDemandPolymerReal (k n) (U n) demand ≤
          Real.exp (C * Real.log (n : ℝ) ^ 8))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (canonicalDemandResidualMass (k n) (U n) demand : ℝ) <
            (n : ℝ) / Real.log (n : ℝ) ^ 6 →
        canonicalDemandPolymerReal (k n) (U n) demand ≤
          Real.exp (C * (n : ℝ) / Real.log (n : ℝ) ^ 5)) :
    (∀ n, signedProfileNormalizedSecondMomentReal n (k n) ≤
      Real.exp (canonicalMidpointLambda (row₀ n) (U n))) ∧
    (∀ n, 0 ≤ canonicalMidpointLambda (row₀ n) (U n)) ∧
    (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase := by
  obtain ⟨epsilonAttachment, hAttachmentTendsto,
      hAttachmentNonneg, hAttachment⟩ :=
    exists_canonicalDemandAttachment_twoRegime_error
      b U k C hC hlarge hsmall
  exact real_canonicalMidpoint_secondMoment_seed_of_separate_bounds
    b U k row₀ epsilonSkeleton epsilonAttachment hU hcap
    hSkeletonNonneg hAttachmentNonneg hSkeletonTendsto
    hAttachmentTendsto hSkeleton hAttachment

#print axioms exists_canonicalDemandAttachment_twoRegime_error
#print axioms real_canonicalMidpoint_secondMoment_seed_of_skeleton_and_twoRegime

end

end Erdos625
