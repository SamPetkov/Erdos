import Erdos625.NormalizedRootGapAssembly
import Erdos625.ProfileOptimizerContinuityS4
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-!
# Transporting the limiting four-size margin along moving targets

The normalized root-gap assembly isolates one remaining target term:

`(q - fourEntropyLoss T₊(n)) - signedFourPhaseMargin n`.

Since `signedFourPhaseMargin n = q - fourEntropyLoss (signedFourPhaseTarget n)`,
this is entirely a continuity problem for the limiting entropy loss.  The
phase target need not converge, so pointwise continuity is not enough.  This
module proves continuity of the limiting selected tilts and entropy values,
upgrades the loss to uniform continuity on every compact subinterval of
`(2,5)`, and transports any pair of asymptotically equal moving targets.

No root existence, target-location estimate, derivative corridor, root-gap
asymptotic, first moment, chromatic lower tail, partial diagonal, skeleton,
second moment, or final Erdős statement is proved here.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Interior targets converging to an interior target have convergent selected
extended-Gaussian tilts.  The proof uses strict monotonicity of the limiting
mean and does not assume a priori boundedness of the moving tilts. -/
theorem tendsto_extendedGaussianTilt_of_target
    {A : Type*} {l : Filter A}
    (target : A → ℝ) {target₀ : ℝ}
    (htarget : Tendsto target l (𝓝 target₀))
    (htarget₀ : -1 < target₀) :
    Tendsto (fun a ↦ extendedGaussianTilt q (target a)) l
      (𝓝 (extendedGaussianTilt q target₀)) := by
  rw [tendsto_order]
  constructor
  · intro lower hlower
    have hMeanLower : extendedGaussianMean q lower < target₀ := by
      calc
        extendedGaussianMean q lower <
            extendedGaussianMean q (extendedGaussianTilt q target₀) :=
          strictMono_extendedGaussianMean q q_pos hlower
        _ = target₀ :=
          extendedGaussianMean_extendedGaussianTilt q_pos htarget₀
    have hCompare : ∀ᶠ a in l,
        extendedGaussianMean q lower < target a :=
      (tendsto_const_nhds.eventually_lt htarget) hMeanLower
    have hInterior : ∀ᶠ a in l, -1 < target a :=
      htarget (Ioi_mem_nhds htarget₀)
    filter_upwards [hCompare, hInterior] with a ha hTa
    rw [← extendedGaussianMean_extendedGaussianTilt q_pos hTa] at ha
    exact (strictMono_extendedGaussianMean q q_pos).lt_iff_lt.mp ha
  · intro upper hupper
    have hMeanUpper : target₀ < extendedGaussianMean q upper := by
      calc
        target₀ =
            extendedGaussianMean q (extendedGaussianTilt q target₀) :=
          (extendedGaussianMean_extendedGaussianTilt q_pos htarget₀).symm
        _ < extendedGaussianMean q upper :=
          strictMono_extendedGaussianMean q q_pos hupper
    have hCompare : ∀ᶠ a in l,
        target a < extendedGaussianMean q upper :=
      (htarget.eventually_lt tendsto_const_nhds) hMeanUpper
    have hInterior : ∀ᶠ a in l, -1 < target a :=
      htarget (Ioi_mem_nhds htarget₀)
    filter_upwards [hCompare, hInterior] with a ha hTa
    rw [← extendedGaussianMean_extendedGaussianTilt q_pos hTa] at ha
    exact (strictMono_extendedGaussianMean q q_pos).lt_iff_lt.mp ha

/-- The selected extended-Gaussian tilt is continuous at every target above
its lower support endpoint. -/
theorem continuousAt_extendedGaussianTilt
    {target : ℝ} (htarget : -1 < target) :
    ContinuousAt (extendedGaussianTilt q) target :=
  tendsto_extendedGaussianTilt_of_target id tendsto_id htarget

/-- The selected extended-Gaussian entropy value is continuous under moving
interior targets. -/
theorem tendsto_extendedGaussianEntropyValue_of_target
    {A : Type*} {l : Filter A}
    (target : A → ℝ) {target₀ : ℝ}
    (htarget : Tendsto target l (𝓝 target₀))
    (htarget₀ : target₀ ∈ Ioo (2 : ℝ) 5) :
    Tendsto (fun a ↦ extendedGaussianEntropyValue (target a)) l
      (𝓝 (extendedGaussianEntropyValue target₀)) := by
  rw [extendedGaussianEntropyValue_eq_log_partition_sub_tilt_mul htarget₀]
  have htargetLower : -1 < target₀ := by linarith [htarget₀.1]
  have hTilt :=
    tendsto_extendedGaussianTilt_of_target target htarget htargetLower
  have hPartition : Tendsto
      (fun a ↦ extendedGaussianPartition q
        (extendedGaussianTilt q (target a))) l
      (𝓝 (extendedGaussianPartition q
        (extendedGaussianTilt q target₀))) :=
    (hasDerivAt_extendedGaussianPartition q
      (extendedGaussianTilt q target₀) q_pos).continuousAt.tendsto.comp hTilt
  have hLog : Tendsto
      (fun a ↦ Real.log (extendedGaussianPartition q
        (extendedGaussianTilt q (target a)))) l
      (𝓝 (Real.log (extendedGaussianPartition q
        (extendedGaussianTilt q target₀)))) :=
    (Real.continuousAt_log
      (extendedGaussianPartition_ne_zero q_pos)).tendsto.comp hPartition
  have hExpression := hLog.sub (hTilt.mul htarget)
  refine hExpression.congr' ?_
  have hInterior : ∀ᶠ a in l, target a ∈ Ioo (2 : ℝ) 5 :=
    htarget (isOpen_Ioo.mem_nhds htarget₀)
  filter_upwards [hInterior] with a ha
  exact (extendedGaussianEntropyValue_eq_log_partition_sub_tilt_mul ha).symm

/-- The limiting four-Gaussian entropy optimum is continuous under moving
interior targets. -/
theorem tendsto_fourGaussianOptimizedValue_of_target
    {A : Type*} {l : Filter A}
    (target : A → ℝ) {target₀ : ℝ}
    (htarget : Tendsto target l (𝓝 target₀))
    (htarget₀ : target₀ ∈ Ioo (2 : ℝ) 5) :
    Tendsto
      (fun a ↦ ProfileEntropyS4.optimizedValue
        fourGaussianScore (target a)) l
      (𝓝 (ProfileEntropyS4.optimizedValue
        fourGaussianScore target₀)) := by
  have hScores : ∀ i : Fin 4,
      Tendsto (fun _a : A ↦ fourGaussianScore i) l
        (𝓝 (fourGaussianScore i)) :=
    fun _i ↦ tendsto_const_nhds
  have hTilt :=
    ProfileEntropyS4.tendsto_tilt_of_scores_and_target
      (fun _a : A ↦ fourGaussianScore) fourGaussianScore
      target hScores htarget htarget₀
  have hPartition :=
    ProfileEntropyS4.tendsto_partition_of_scores_and_parameter
      (fun _a : A ↦ fourGaussianScore) fourGaussianScore
      (fun a ↦ ProfileEntropyS4.tilt fourGaussianScore (target a))
      (ProfileEntropyS4.tilt fourGaussianScore target₀)
      hScores hTilt
  have hLog : Tendsto
      (fun a ↦ Real.log
        (ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore (target a)))) l
      (𝓝 (Real.log
        (ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore target₀)))) :=
    (Real.continuousAt_log
      (ne_of_gt (ProfileEntropyS4.partition_pos fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore target₀)))).tendsto.comp
      hPartition
  have hExpression := hLog.sub (hTilt.mul htarget)
  simpa only [ProfileEntropyS4.optimizedValue] using hExpression

/-- The manuscript limiting four-size entropy loss is continuous under moving
interior targets. -/
theorem tendsto_fourEntropyLoss_of_target
    {A : Type*} {l : Filter A}
    (target : A → ℝ) {target₀ : ℝ}
    (htarget : Tendsto target l (𝓝 target₀))
    (htarget₀ : target₀ ∈ Ioo (2 : ℝ) 5) :
    Tendsto (fun a ↦ fourEntropyLoss (target a)) l
      (𝓝 (fourEntropyLoss target₀)) := by
  have hExtended :=
    tendsto_extendedGaussianEntropyValue_of_target
      target htarget htarget₀
  have hFour :=
    tendsto_fourGaussianOptimizedValue_of_target
      target htarget htarget₀
  simpa only [fourEntropyLoss] using hExtended.sub hFour

/-- Pointwise continuity of the limiting entropy loss on its manuscript
interior target domain. -/
theorem continuousAt_fourEntropyLoss
    {target : ℝ} (htarget : target ∈ Ioo (2 : ℝ) 5) :
    ContinuousAt fourEntropyLoss target :=
  tendsto_fourEntropyLoss_of_target id tendsto_id htarget

/-- Continuity of the limiting entropy loss on every compact subinterval of
`(2,5)`. -/
theorem continuousOn_fourEntropyLoss_Icc
    {A B : ℝ} (hA : 2 < A) (hB : B < 5) :
    ContinuousOn fourEntropyLoss (Icc A B) := by
  intro target htarget
  exact (continuousAt_fourEntropyLoss
    ⟨hA.trans_le htarget.1, htarget.2.trans_lt hB⟩).continuousWithinAt

/-- Uniform continuity of the limiting entropy loss on every compact target
corridor. -/
theorem uniformContinuousOn_fourEntropyLoss_Icc
    {A B : ℝ} (hA : 2 < A) (hB : B < 5) :
    UniformContinuousOn fourEntropyLoss (Icc A B) :=
  isCompact_Icc.uniformContinuousOn_of_continuous
    (continuousOn_fourEntropyLoss_Icc hA hB)

/-- Two moving targets that remain in one compact interior corridor and become
asymptotically equal have asymptotically equal limiting entropy losses.  No
limit of either target sequence is required. -/
theorem tendsto_fourEntropyLoss_sub_of_compact_targets
    {A B : ℝ} (hA : 2 < A) (hB : B < 5)
    (left right : ℕ → ℝ)
    (hLeft : ∀ᶠ n : ℕ in atTop, left n ∈ Icc A B)
    (hRight : ∀ᶠ n : ℕ in atTop, right n ∈ Icc A B)
    (hTargets : Tendsto (fun n : ℕ ↦ left n - right n)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        fourEntropyLoss (left n) - fourEntropyLoss (right n))
      atTop (𝓝 0) := by
  have hUniform := uniformContinuousOn_fourEntropyLoss_Icc hA hB
  rw [Metric.uniformContinuousOn_iff] at hUniform
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hControl⟩ := hUniform epsilon hepsilon
  rw [eventually_atTop] at hLeft hRight
  obtain ⟨NLeft, hNLeft⟩ := hLeft
  obtain ⟨NRight, hNRight⟩ := hRight
  rw [Metric.tendsto_atTop] at hTargets
  obtain ⟨NTarget, hNTarget⟩ := hTargets delta hdelta
  refine ⟨max NLeft (max NRight NTarget), ?_⟩
  intro n hn
  have hnLeftIndex : NLeft ≤ n := by omega
  have hnRightIndex : NRight ≤ n := by omega
  have hnTargetIndex : NTarget ≤ n := by omega
  have hnLeft := hNLeft n hnLeftIndex
  have hnRight := hNRight n hnRightIndex
  have hnTarget := hNTarget n hnTargetIndex
  have hnClose : dist (left n) (right n) < delta := by
    rw [Real.dist_eq, sub_zero] at hnTarget
    simpa only [Real.dist_eq] using hnTarget
  have hout := hControl (left n) hnLeft (right n) hnRight hnClose
  rw [Real.dist_eq] at hout
  rw [Real.dist_eq, sub_zero]
  exact hout

/-- Target transport in the exact form consumed by the normalized root-gap
assembly. -/
theorem tendsto_limitingMargin_sub_phaseMargin_of_target
    {A B : ℝ} (hA : 2 < A) (hB : B < 5)
    (target : ℕ → ℝ)
    (hTarget : ∀ᶠ n : ℕ in atTop, target n ∈ Icc A B)
    (hPhaseTarget : ∀ᶠ n : ℕ in atTop,
      signedFourPhaseTarget n ∈ Icc A B)
    (hTargets : Tendsto
      (fun n : ℕ ↦ target n - signedFourPhaseTarget n)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        (q - fourEntropyLoss (target n)) -
          signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  have hLoss :=
    tendsto_fourEntropyLoss_sub_of_compact_targets
      hA hB target signedFourPhaseTarget
      hTarget hPhaseTarget hTargets
  have hNeg : Tendsto
      (fun n : ℕ ↦
        -(fourEntropyLoss (target n) -
          fourEntropyLoss (signedFourPhaseTarget n)))
      atTop (𝓝 0) := by
    simpa only [neg_zero] using hLoss.neg
  refine hNeg.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  unfold signedFourPhaseMargin
  ring

/-- Root-gap wrapper in which the limiting-target transport is derived from
asymptotic equality of the unrestricted-root target and the manuscript phase
target. -/
theorem
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_target_and_secant
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5)
    (rCo rPlus : ℕ → ℝ)
    (hPhase : Tendsto phaseNat atTop atTop)
    (hTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (rPlus n) ∈ Icc A B)
    (hPhaseTarget : ∀ᶠ n : ℕ in atTop,
      signedFourPhaseTarget n ∈ Icc A B)
    (hTargetTransport : Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (rPlus n) -
          signedFourPhaseTarget n)
      atTop (𝓝 0))
    (hGap : ∀ᶠ n : ℕ in atTop, rPlus n - rCo n ≠ 0)
    (hPlus : ∀ᶠ n : ℕ in atTop, rPlus n ≠ 0)
    (hCoRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hPlusRoot : ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (rPlus n) = 0)
    (hRightParts : Tendsto
      (signedFourNormalizedRightRootPartCount rPlus)
      atTop (𝓝 (q / 2)))
    (hSecant : Tendsto
      (signedFourNormalizedRootSecantSlope rCo rPlus)
      atTop (𝓝 (2 / q))) :
    Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  have hLimitingTarget :=
    tendsto_limitingMargin_sub_phaseMargin_of_target
      hA hB
      (fun n ↦ fourSizeTarget n (phaseNat n) (rPlus n))
      hTarget hPhaseTarget hTargetTransport
  exact
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_compactTarget_and_secant
      hA hAB hB rCo rPlus hPhase hTarget hLimitingTarget
      hGap hPlus hCoRoot hPlusRoot hRightParts hSecant

#print axioms tendsto_extendedGaussianTilt_of_target
#print axioms continuousAt_extendedGaussianTilt
#print axioms tendsto_extendedGaussianEntropyValue_of_target
#print axioms tendsto_fourGaussianOptimizedValue_of_target
#print axioms tendsto_fourEntropyLoss_of_target
#print axioms continuousAt_fourEntropyLoss
#print axioms continuousOn_fourEntropyLoss_Icc
#print axioms uniformContinuousOn_fourEntropyLoss_Icc
#print axioms tendsto_fourEntropyLoss_sub_of_compact_targets
#print axioms tendsto_limitingMargin_sub_phaseMargin_of_target
#print axioms tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_target_and_secant

end

end Erdos625