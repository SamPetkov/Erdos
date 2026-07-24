import Erdos625.Section9RealSecondMomentSeed
import Mathlib.Tactic

/-!
# Section IX: separating skeleton mass from residual attachment

The canonical polymer sum contains two mathematically distinct estimates: the
Section VIII attained-skeleton mass and the Section IX residual polymer
majorant.  This module separates them without changing the canonical demand
law.  Consequently the remaining analytic cut can be stated pointwise for the
actual attained demands, rather than as a bound on an already-aggregated sum.
-/

namespace Erdos625

open Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Total bare mass of the attained canonical high skeletons.  Each demand is
weighted by its exact local reward and labelled-witness incidence. -/
noncomputable def canonicalBareSkeletonSum
    {b : ℕ} (k : ColoringProfile b) (U : ℕ) : ENNReal :=
  ∑ demand : ProfileCanonicalHighSkeleton k U,
    (canonicalDemandLocalReward demand : ENNReal) *
      labelledWitnessIncidence demand.1 (profileBlockMargin k)
        (profileBlockMargin k)

/-- A uniform pointwise attachment bound factors out of the literal canonical
demand mixture. -/
theorem midpointCanonicalPolymerSum_le_bare_mul
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) (K : ENNReal)
    (hK : ∀ demand : ProfileCanonicalHighSkeleton k U,
      canonicalDemandPolymerMajorant
        (profileBlockMargin k) (profileBlockMargin k) U demand ≤ K) :
    midpointCanonicalPolymerSum row₀ U ≤
      canonicalBareSkeletonSum k U * K := by
  unfold midpointCanonicalPolymerSum canonicalBareSkeletonSum
  calc
    (∑ demand : ProfileCanonicalHighSkeleton k U,
      (canonicalDemandLocalReward demand : ENNReal) *
        (labelledWitnessIncidence demand.1 (profileBlockMargin k)
          (profileBlockMargin k) *
          canonicalDemandPolymerMajorant
            (profileBlockMargin k) (profileBlockMargin k) U demand)) ≤
      ∑ demand : ProfileCanonicalHighSkeleton k U,
        ((canonicalDemandLocalReward demand : ENNReal) *
          labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k)) * K := by
      apply Finset.sum_le_sum
      intro demand _
      calc
        (canonicalDemandLocalReward demand : ENNReal) *
            (labelledWitnessIncidence demand.1 (profileBlockMargin k)
              (profileBlockMargin k) *
              canonicalDemandPolymerMajorant
                (profileBlockMargin k) (profileBlockMargin k) U demand) =
          ((canonicalDemandLocalReward demand : ENNReal) *
            labelledWitnessIncidence demand.1 (profileBlockMargin k)
              (profileBlockMargin k)) *
            canonicalDemandPolymerMajorant
              (profileBlockMargin k) (profileBlockMargin k) U demand := by
                rw [mul_assoc]
        _ ≤ ((canonicalDemandLocalReward demand : ENNReal) *
            labelledWitnessIncidence demand.1 (profileBlockMargin k)
              (profileBlockMargin k)) * K :=
          mul_le_mul_right (hK demand) _
    _ = (∑ demand : ProfileCanonicalHighSkeleton k U,
        (canonicalDemandLocalReward demand : ENNReal) *
          labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k)) * K := by rw [Finset.sum_mul]

/-- Separate exponential bounds for the attained skeleton mass and every
actual residual attachment combine into an exponential bound for the literal
canonical polymer sum. -/
theorem midpointCanonicalPolymerSum_le_exp_add
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) (skeletonError attachmentError : ℝ)
    (hSkeleton : canonicalBareSkeletonSum k U ≤
      ENNReal.ofReal (Real.exp skeletonError))
    (hAttachment : ∀ demand : ProfileCanonicalHighSkeleton k U,
      canonicalDemandPolymerMajorant
        (profileBlockMargin k) (profileBlockMargin k) U demand ≤
          ENNReal.ofReal (Real.exp attachmentError)) :
    midpointCanonicalPolymerSum row₀ U ≤
      ENNReal.ofReal (Real.exp (skeletonError + attachmentError)) := by
  calc
    midpointCanonicalPolymerSum row₀ U ≤
        canonicalBareSkeletonSum k U *
          ENNReal.ofReal (Real.exp attachmentError) :=
      midpointCanonicalPolymerSum_le_bare_mul row₀ U _ hAttachment
    _ ≤ ENNReal.ofReal (Real.exp skeletonError) *
          ENNReal.ofReal (Real.exp attachmentError) := by
      exact mul_le_mul_of_nonneg_right hSkeleton (by positivity)
    _ = ENNReal.ofReal (Real.exp (skeletonError + attachmentError)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

/-- Sequence form of the separated dependency cut.  Vanishing nonnegative
coefficients for the skeleton and attachment estimates give the direct
polymer bound consumed by `canonicalMidpoint_secondMoment_seed_of_polymer_bound`.
-/
theorem eventually_midpointCanonicalPolymerSum_le_exp_of_separate_bounds
    (b U : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (epsilonSkeleton epsilonAttachment : ℕ → ℝ)
    (hSkeleton : ∀ᶠ n in atTop,
      canonicalBareSkeletonSum (k n) (U n) ≤
        ENNReal.ofReal
          (Real.exp (epsilonSkeleton n * amplificationBase n)))
    (hAttachment : ∀ᶠ n in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        canonicalDemandPolymerMajorant
          (profileBlockMargin (k n)) (profileBlockMargin (k n)) (U n) demand ≤
            ENNReal.ofReal
              (Real.exp (epsilonAttachment n * amplificationBase n))) :
    ∀ᶠ n in atTop,
      midpointCanonicalPolymerSum (row₀ n) (U n) ≤
        ENNReal.ofReal (Real.exp
          ((epsilonSkeleton n + epsilonAttachment n) * amplificationBase n)) := by
  filter_upwards [hSkeleton, hAttachment] with n hs ha
  have h := midpointCanonicalPolymerSum_le_exp_add
    (row₀ n) (U n)
    (epsilonSkeleton n * amplificationBase n)
    (epsilonAttachment n * amplificationBase n) hs ha
  simpa only [add_mul] using h

/-- Complete real second-moment seed from separated Section VIII skeleton and
Section IX attachment estimates.  This theorem makes the exact remaining
analytic dependencies declaration-level and keeps every quantifier over the
attained canonical demand family. -/
theorem real_canonicalMidpoint_secondMoment_seed_of_separate_bounds
    (b U : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (epsilonSkeleton epsilonAttachment : ℕ → ℝ)
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hSkeletonNonneg : ∀ᶠ n in atTop, 0 ≤ epsilonSkeleton n)
    (hAttachmentNonneg : ∀ᶠ n in atTop, 0 ≤ epsilonAttachment n)
    (hSkeletonTendsto : Tendsto epsilonSkeleton atTop (nhds 0))
    (hAttachmentTendsto : Tendsto epsilonAttachment atTop (nhds 0))
    (hSkeleton : ∀ᶠ n in atTop,
      canonicalBareSkeletonSum (k n) (U n) ≤
        ENNReal.ofReal
          (Real.exp (epsilonSkeleton n * amplificationBase n)))
    (hAttachment : ∀ᶠ n in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        canonicalDemandPolymerMajorant
          (profileBlockMargin (k n)) (profileBlockMargin (k n)) (U n) demand ≤
            ENNReal.ofReal
              (Real.exp (epsilonAttachment n * amplificationBase n))) :
    (∀ n, signedProfileNormalizedSecondMomentReal n (k n) ≤
      Real.exp (canonicalMidpointLambda (row₀ n) (U n))) ∧
    (∀ n, 0 ≤ canonicalMidpointLambda (row₀ n) (U n)) ∧
    (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase := by
  let epsilon := fun n => epsilonSkeleton n + epsilonAttachment n
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ epsilon n := by
    filter_upwards [hSkeletonNonneg, hAttachmentNonneg] with n hs ha
    exact add_nonneg hs ha
  have htendsto : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using hSkeletonTendsto.add hAttachmentTendsto
  have hpolymer : ∀ᶠ n in atTop,
      midpointCanonicalPolymerSum (row₀ n) (U n) ≤
        ENNReal.ofReal (Real.exp (epsilon n * amplificationBase n)) := by
    simpa only [epsilon] using
      eventually_midpointCanonicalPolymerSum_le_exp_of_separate_bounds
        b U k row₀ epsilonSkeleton epsilonAttachment hSkeleton hAttachment
  have hseed := canonicalMidpoint_secondMoment_seed_of_polymer_bound
    b U k row₀ epsilon hU hcap hnonneg htendsto hpolymer
  exact ⟨fun n =>
    signedProfileNormalizedSecondMomentReal_le_exp_canonicalMidpointLambda
      (row₀ n) (U n) (hU n) (hcap n), hseed.2⟩

#print axioms midpointCanonicalPolymerSum_le_bare_mul
#print axioms midpointCanonicalPolymerSum_le_exp_add
#print axioms eventually_midpointCanonicalPolymerSum_le_exp_of_separate_bounds
#print axioms real_canonicalMidpoint_secondMoment_seed_of_separate_bounds

end

end Erdos625
