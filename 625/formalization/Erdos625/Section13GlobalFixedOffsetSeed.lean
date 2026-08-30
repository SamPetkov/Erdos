import Erdos625.OrderedProfileRealization
import Erdos625.Section8FourDeficitProfileCover
import Erdos625.Section9MidpointCanonicalAttachmentTwoRegime
import Erdos625.Section9ProfileAttachmentSmallResidualLogScale
import Erdos625.Section9ProfileAttachmentLargeResidualLogScale
import Erdos625.Section9MidpointSecondMomentSeed
import Erdos625.Section6SignedPaleyZygmundSeed
import Erdos625.Section12FixedOffsetCanonicalBareSkeletonAsymptotic
import Mathlib.Tactic

/-!
# Section IX: global fixed-offset seed

This module combines the small- and large-residual attachment
bounds at the concrete fixed-offset rounded profile.  A mass-correct fallback
makes the profile and its ordered realization total; eventual fixed-offset
admissibility then identifies them with the intended four-deficit profile.
The resulting attachment estimate combines with the canonical bare-skeleton
bound to give the real seed used by Sections X--XI.
-/

namespace Erdos625

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

noncomputable section

set_option autoImplicit false

/-- A total profile sequence.  Outside the eventual fixed-offset-admissible
regime, all vertices are placed in size-one classes solely to preserve the
exact vertex mass needed for an ordered realization. -/
private noncomputable def phaseFixedOffsetProfile (n : Nat) :
    ColoringProfile (phaseNat n + 1) := by
  classical
  exact
    if h : MidpointRoundingAdmissible n (phaseNat n)
        (phaseCochromaticFixedOffsetIndex n) then
      fourDeficitEmbedding (phaseNat n) h.1
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticFixedOffsetIndex n))
    else
      fun j => if j.val = 0 then n else 0

private theorem phaseFixedOffsetProfile_vertexMass (n : Nat) :
    ColoringProfile.vertexMass (phaseFixedOffsetProfile n) = n := by
  classical
  unfold phaseFixedOffsetProfile
  split_ifs with h
  · rw [(fourDeficitEmbedding_profile_invariants (phaseNat n) h.1
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticFixedOffsetIndex n))).2.1]
    exact midpointMultiplicity_vertexMass n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n) h
  · rw [ColoringProfile.vertexMass_eq_sum]
    simp

private theorem phaseFixedOffsetProfile_eq_of_admissible (n : Nat)
    (h : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n)) :
    phaseFixedOffsetProfile n =
      fourDeficitEmbedding (phaseNat n) h.1
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticFixedOffsetIndex n)) := by
  simp [phaseFixedOffsetProfile, h]

/-- A total cutoff sequence, equal to the exact four-endpoint cutoff whenever
the fixed-offset profile is admissible. -/
private noncomputable def phaseFixedOffsetCap (n : Nat) : Nat :=
  if h : 5 < phaseNat n then
    fourEndpointLargestSize (phaseNat n) h
  else
    2

private theorem phaseFixedOffsetCap_eq_of_admissible (n : Nat)
    (h : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n)) :
    phaseFixedOffsetCap n = fourEndpointLargestSize (phaseNat n) h.1 := by
  simp [phaseFixedOffsetCap, h.1]

private theorem fourEndpointLargestSize_eq_sub_two (alpha : Nat)
    (hAlpha : 5 < alpha) :
    fourEndpointLargestSize alpha hAlpha = alpha - 2 := by
  unfold fourEndpointLargestSize fourEndpointOverlapSize
  rw [min_self]
  unfold fourEndpointSize fourEndpointCoordinate
  simpa [fourDeficit] using
    (fourDeficitCoordinate_val_add_one_eq alpha hAlpha (0 : Fin 4))

private theorem phaseFixedOffsetCap_le_phaseNat_of_admissible (n : Nat)
    (h : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n)) :
    phaseFixedOffsetCap n ≤ phaseNat n := by
  rw [phaseFixedOffsetCap_eq_of_admissible n h]
  rw [fourEndpointLargestSize_eq_sub_two (phaseNat n) h.1]
  have hAlpha : 5 < phaseNat n := h.1
  omega

private theorem two_le_phaseFixedOffsetCap_of_admissible (n : Nat)
    (h : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n)) :
    2 ≤ phaseFixedOffsetCap n := by
  rw [phaseFixedOffsetCap_eq_of_admissible n h]
  rw [fourEndpointLargestSize_eq_sub_two (phaseNat n) h.1]
  have hAlpha : 5 < phaseNat n := h.1
  omega

private theorem phaseFixedOffsetProfile_cover_of_admissible (n : Nat)
    (h : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n)) :
    IsFourEndpointProfileCover (phaseNat n) h.1 (phaseFixedOffsetProfile n) := by
  rw [phaseFixedOffsetProfile_eq_of_admissible n h]
  exact fourDeficitEmbedding_isFourEndpointProfileCover
    (phaseNat n) h.1
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticFixedOffsetIndex n))

private theorem phaseFixedOffsetProfile_margin_le_cap_of_admissible (n : Nat)
    (h : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n))
    (a : ProfileBlockIndex (phaseFixedOffsetProfile n)) :
    profileBlockMargin (phaseFixedOffsetProfile n) a ≤ phaseFixedOffsetCap n := by
  rw [phaseFixedOffsetCap_eq_of_admissible n h]
  exact profileBlockMargin_le_fourEndpointLargest_of_cover
    (phaseNat n) h.1 (phaseFixedOffsetProfile n)
      (phaseFixedOffsetProfile_cover_of_admissible n h) a

private theorem phaseFixedOffsetProfile_partCount_of_admissible (n : Nat)
    (h : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n)) :
    ColoringProfile.partCount (phaseFixedOffsetProfile n) =
      phaseCochromaticFixedOffsetIndex n := by
  rw [phaseFixedOffsetProfile_eq_of_admissible n h]
  rw [(fourDeficitEmbedding_profile_invariants (phaseNat n) h.1
    (midpointMultiplicity n (phaseNat n)
      (phaseCochromaticFixedOffsetIndex n))).1]
  exact (midpointMultiplicity_count_deficit_intDisplacement n (phaseNat n)
    (phaseCochromaticFixedOffsetIndex n) h).1

private noncomputable def phaseFixedOffsetOrderedProfile (n : Nat) :
    OrderedProfilePartition n (phaseFixedOffsetProfile n) :=
  Classical.choice
    (nonempty_orderedProfilePartition_of_vertexMass
      (phaseFixedOffsetProfile n) (phaseFixedOffsetProfile_vertexMass n))

private theorem exists_phaseFixedOffsetCanonicalAttachment_error :
    ∃ epsilon : Nat → Real,
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ᶠ n : Nat in atTop, 0 ≤ epsilon n) ∧
      ∀ᶠ n : Nat in atTop,
        midpointCanonicalAttachmentSum
            (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n) ≤
          canonicalBareSkeletonSum
              (phaseFixedOffsetProfile n) (phaseFixedOffsetCap n) *
            ENNReal.ofReal
              (Real.exp (epsilon n * amplificationBase n)) := by
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    eventually_profileHighSkeletonAttachment_le_smallResidual_logScale
  obtain ⟨Clarge, hClarge, hlarge⟩ :=
    eventually_profileHighSkeletonAttachment_le_largeResidual_logScale
  let C : Real := max Csmall Clarge
  have hC : 0 ≤ C := hCsmall.trans (le_max_left Csmall Clarge)
  have hsmall' : ∀ᶠ n : Nat in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton
        (phaseFixedOffsetProfile n) (phaseFixedOffsetCap n),
        (canonicalDemandResidualTotal
          (profileBlockMargin (phaseFixedOffsetProfile n))
          (profileBlockMargin (phaseFixedOffsetProfile n))
          (phaseFixedOffsetCap n) demand : Real) <
            (n : Real) / Real.log (n : Real) ^ 6 →
        profileHighSkeletonAttachment
            (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n) demand ≤
          ENNReal.ofReal
            (Real.exp (C * (n : Real) / Real.log (n : Real) ^ 5)) := by
    filter_upwards [hsmall,
      eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible,
      eventually_gt_atTop (1 : Nat)] with n hn hadm hnLarge
    intro demand hres
    have hbound := hn (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n)
      (phaseFixedOffsetCap_le_phaseNat_of_admissible n hadm)
      (phaseFixedOffsetProfile_margin_le_cap_of_admissible n hadm) demand hres
    apply hbound.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hscale : 0 ≤ (n : Real) / Real.log (n : Real) ^ 5 := by
      positivity
    simpa only [mul_div_assoc] using
      (mul_le_mul_of_nonneg_right (le_max_left Csmall Clarge) hscale)
  have hlarge' : ∀ᶠ n : Nat in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton
        (phaseFixedOffsetProfile n) (phaseFixedOffsetCap n),
        (n : Real) / Real.log (n : Real) ^ 6 ≤
          (canonicalDemandResidualTotal
            (profileBlockMargin (phaseFixedOffsetProfile n))
            (profileBlockMargin (phaseFixedOffsetProfile n))
            (phaseFixedOffsetCap n) demand : Real) →
        profileHighSkeletonAttachment
            (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n) demand ≤
          ENNReal.ofReal
            (Real.exp (C * Real.log (n : Real) ^ 8)) := by
    filter_upwards [hlarge,
      eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible] with
      n hn hadm
    intro demand hres
    have hbound := hn (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n)
      (phaseFixedOffsetCap_le_phaseNat_of_admissible n hadm)
      (phaseFixedOffsetProfile_margin_le_cap_of_admissible n hadm) demand hres
    apply hbound.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_max_right Csmall Clarge)
      (by positivity)
  exact exists_midpointCanonicalAttachment_twoRegime_error
    (fun n => phaseNat n + 1) phaseFixedOffsetCap phaseFixedOffsetProfile
      phaseFixedOffsetOrderedProfile C hC hlarge' hsmall'

/-- The exact fixed-offset rounded profile has a real cocolourability seed with
an eventually nonnegative exponent negligible relative to the amplification
scale. -/
theorem exists_phaseCochromaticFixedOffset_real_seed :
    ∃ Lambda : Nat → Real,
      (∀ᶠ n : Nat in atTop, 0 ≤ Lambda n) ∧
      Lambda =o[atTop] amplificationBase ∧
      ∀ᶠ n : Nat in atTop,
        Real.exp (-Lambda n) ≤
          (randomGraphMeasure n).real
            {G | CoColorable G (phaseCochromaticFixedOffsetIndex n)} := by
  obtain ⟨epsilonSkeleton, hSkeletonTendsto, hSkeletonNonneg, hSkeleton⟩ :=
    exists_phaseFixedOffsetCanonicalBareSkeleton_error
  obtain ⟨epsilonAttachment, hAttachmentTendsto, hAttachmentNonneg,
      hAttachment⟩ := exists_phaseFixedOffsetCanonicalAttachment_error
  let Lambda : Nat → Real := fun n =>
    (epsilonSkeleton n + epsilonAttachment n) * amplificationBase n
  refine ⟨Lambda, ?_, ?_, ?_⟩
  · filter_upwards [hSkeletonNonneg, hAttachmentNonneg,
      eventually_gt_atTop (1 : Nat)] with n hs ha hn
    have hbase : 0 ≤ amplificationBase n := by
      unfold amplificationBase
      positivity
    exact mul_nonneg (add_nonneg hs ha) hbase
  · apply Asymptotics.isLittleO_iff_exists_eq_mul.mpr
    refine ⟨fun n => epsilonSkeleton n + epsilonAttachment n,
      (by simpa using hSkeletonTendsto.add hAttachmentTendsto), ?_⟩
    exact Filter.Eventually.of_forall fun n => rfl
  · filter_upwards [hSkeleton, hAttachment,
      eventually_phaseCochromaticFixedOffsetIndex_rounding_admissible] with
      n hs ha hadm
    have hs' : canonicalBareSkeletonSum
          (phaseFixedOffsetProfile n) (phaseFixedOffsetCap n) ≤
        ENNReal.ofReal
          (Real.exp (epsilonSkeleton n * amplificationBase n)) := by
      rw [phaseFixedOffsetProfile_eq_of_admissible n hadm,
        phaseFixedOffsetCap_eq_of_admissible n hadm]
      exact hs hadm.1
    have hsum : midpointCanonicalAttachmentSum
          (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n) ≤
        ENNReal.ofReal (Real.exp (Lambda n)) := by
      calc
        midpointCanonicalAttachmentSum
            (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n) ≤
          canonicalBareSkeletonSum
              (phaseFixedOffsetProfile n) (phaseFixedOffsetCap n) *
            ENNReal.ofReal
              (Real.exp (epsilonAttachment n * amplificationBase n)) := ha
        _ ≤ ENNReal.ofReal
              (Real.exp (epsilonSkeleton n * amplificationBase n)) *
            ENNReal.ofReal
              (Real.exp (epsilonAttachment n * amplificationBase n)) := by
          exact mul_le_mul_of_nonneg_right hs' (by positivity)
        _ = ENNReal.ofReal (Real.exp (Lambda n)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          congr 2
          simp only [Lambda]
          ring
    have hTable : signedProfileSecondMomentTableSumENNReal
          (phaseFixedOffsetOrderedProfile n) ≤
        ENNReal.ofReal (Real.exp (Lambda n)) := by
      rw [← normalizedSignedProfileSecondMoment_eq_tableSum
        (phaseFixedOffsetOrderedProfile n)]
      rw [normalizedSignedProfileSecondMoment_eq_midpointCanonicalAttachmentSum
        (phaseFixedOffsetOrderedProfile n) (phaseFixedOffsetCap n)
        (two_le_phaseFixedOffsetCap_of_admissible n hadm)]
      exact hsum
    have hseed := signedProfile_real_seed_of_tableSum_bound
      (phaseFixedOffsetOrderedProfile n) (Lambda n) hTable
    rw [phaseFixedOffsetProfile_partCount_of_admissible n hadm] at hseed
    exact hseed

#print axioms exists_phaseCochromaticFixedOffset_real_seed

end

end Erdos625
