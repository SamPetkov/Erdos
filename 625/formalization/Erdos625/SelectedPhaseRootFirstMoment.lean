import Erdos625.SignedPhaseRootConstruction
import Erdos625.FirstMomentFromCenterAndDerivativeCorridor
import Erdos625.SignedFourDerivativeCorridor
import Mathlib.Tactic

/-!
# Selected phase-root ordering and concrete E625-10 first moment

The preceding modules construct the signed and unrestricted roots separately
inside one common broad corridor.  This module compares those selected roots.
At the unrestricted root, the signed objective is the positive part count
multiplied by the exact finite signed margin.  The signed objective is
strictly increasing on the common corridor, so its selected zero lies to the
left of the unrestricted root.

The resulting order and common-corridor feasibility discharge the last root
hypotheses of the concrete E625-10 first-moment theorem.  This module does not
prove the chromatic lower tail, partial-diagonal estimates, skeleton bounds,
second moments, amplification, or the final Erdős statement.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- At the selected unrestricted-root target, the exact finite signed margin
converges to the manuscript phase-varying margin. -/
theorem
    tendsto_finiteSignedFourMargin_at_unrestrictedPhaseRoot_sub_phaseMargin :
    Tendsto
      (fun n : ℕ ↦
        finiteSignedFourMargin (phaseNat n)
            (fourSizeTarget n (phaseNat n) (unrestrictedPhaseRoot n)) -
          signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  have hTargetNamed :=
    eventually_unrestrictedRootTarget_mem_admissibilityCorridor
      unrestrictedPhaseRoot unrestrictedPhaseRoot_centerLocalization
  have hTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (unrestrictedPhaseRoot n) ∈
        Icc (5 / 2 : ℝ) (9 / 2 : ℝ) := by
    simpa only [signedFourAdmissibilityTargetCorridor] using hTargetNamed
  have hPhaseTarget : ∀ᶠ n : ℕ in atTop,
      signedFourPhaseTarget n ∈ Icc (5 / 2 : ℝ) (9 / 2 : ℝ) :=
    Filter.Eventually.of_forall fun n ↦ by
      simpa only [signedFourAdmissibilityTargetCorridor] using
        signedFourPhaseTarget_mem_admissibilityTargetCorridor n
  have hTargetTransport :=
    tendsto_unrestrictedRootTarget_sub_phaseTarget_of_centerLocalization
      unrestrictedPhaseRoot unrestrictedPhaseRoot_centerLocalization
  have hLimitingTarget :=
    tendsto_limitingMargin_sub_phaseMargin_of_target
      (by norm_num : (2 : ℝ) < 5 / 2)
      (by norm_num : (9 / 2 : ℝ) < 5)
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (unrestrictedPhaseRoot n))
      hTarget hPhaseTarget hTargetTransport
  exact
    tendsto_finiteSignedFourMargin_sub_phaseMargin_of_compactTarget
      (by norm_num : (2 : ℝ) < 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 9 / 2)
      (by norm_num : (9 / 2 : ℝ) < 5)
      phaseNat
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (unrestrictedPhaseRoot n))
      tendsto_phaseNat_atTop_nat hTarget hLimitingTarget

/-- The exact finite signed margin at the selected unrestricted root is
strictly positive eventually. -/
theorem eventually_finiteSignedFourMargin_at_unrestrictedPhaseRoot_pos :
    ∀ᶠ n : ℕ in atTop,
      0 < finiteSignedFourMargin (phaseNat n)
        (fourSizeTarget n (phaseNat n) (unrestrictedPhaseRoot n)) := by
  have hFloorPos :
      0 < Real.log ((200 : ℝ) / 153) :=
    log_200_div_153_pos
  have hHalfPos :
      0 < Real.log ((200 : ℝ) / 153) / 2 :=
    div_pos hFloorPos (by norm_num)
  have hClose : ∀ᶠ n : ℕ in atTop,
      -Real.log ((200 : ℝ) / 153) / 2 <
        finiteSignedFourMargin (phaseNat n)
            (fourSizeTarget n (phaseNat n) (unrestrictedPhaseRoot n)) -
          signedFourPhaseMargin n :=
    tendsto_finiteSignedFourMargin_at_unrestrictedPhaseRoot_sub_phaseMargin.eventually
      (Ioi_mem_nhds (by linarith [hHalfPos]))
  filter_upwards [hClose] with n hn
  have hPhaseLower := log_200_div_153_lt_signedFourPhaseMargin n
  nlinarith [hFloorPos]

/-- The signed objective is strictly positive at the selected unrestricted
root eventually. -/
theorem
    eventually_phaseSignedFourSizeObjective_unrestrictedPhaseRoot_pos :
    ∀ᶠ n : ℕ in atTop,
      0 < phaseSignedFourSizeObjective n (unrestrictedPhaseRoot n) := by
  filter_upwards [eventually_unrestrictedPhaseRootData,
    eventually_finiteSignedFourMargin_at_unrestrictedPhaseRoot_pos] with
    n hnRoot hnMargin
  rw [phaseSignedFourSizeObjective_eq_parts_mul_finiteMargin_of_unrestrictedRoot
    n hnRoot.2.1.ne' hnRoot.2.2.2]
  exact mul_pos hnRoot.2.1 hnMargin

/-- The selected signed root lies strictly to the left of the selected
unrestricted root eventually. -/
theorem eventually_signedPhaseRoot_lt_unrestrictedPhaseRoot :
    ∀ᶠ n : ℕ in atTop,
      signedPhaseRoot n < unrestrictedPhaseRoot n := by
  obtain ⟨C, _hC, hDerivative, hSlopeLower, _hSlopeUpper⟩ :=
    exists_signedFourDerivativeCorridor
  have hSlopePos :=
    eventually_signedFourSlope_pos_of_normalized_tendsto
      (signedFourDerivativeSlopeLower C) hSlopeLower
  filter_upwards [eventually_signedPhaseRootData,
    eventually_unrestrictedPhaseRootData,
    eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible,
    hDerivative, hSlopePos,
    eventually_phaseSignedFourSizeObjective_unrestrictedPhaseRoot_pos] with
    n hnCo hnPlus hnConstruction hnDerivative hnSlopePos hnValuePos
  by_contra hNot
  have hPlusLeCo : unrestrictedPhaseRoot n ≤ signedPhaseRoot n :=
    le_of_not_gt hNot
  have hSegmentData :
      ∀ s ∈ Icc (unrestrictedPhaseRoot n) (signedPhaseRoot n),
        0 < s ∧
          fourSizeTarget n (phaseNat n) s ∈
            signedFourAdmissibilityTargetCorridor := by
    intro s hs
    have hsBroad : s ∈ Icc
        (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
        (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n) := by
      exact ⟨hnPlus.1.1.le.trans hs.1, hs.2.trans hnCo.1.2.le⟩
    have hsConstruction := hnConstruction.2 s hsBroad
    exact ⟨hsConstruction.1, by
      simpa only [fourSizeTarget_eq_profileDeficitTarget] using
        hsConstruction.2⟩
  have hCont : ContinuousOn (phaseSignedFourSizeObjective n)
      (Icc (unrestrictedPhaseRoot n) (signedPhaseRoot n)) := by
    intro s hs
    have hsData := hSegmentData s hs
    exact
      (hasDerivAt_phaseSignedFourSizeObjective n hsData.1
        (signedFourAdmissibilityTargetCorridor_subset_Ioo hsData.2)).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ (phaseSignedFourSizeObjective n)
      (Ioo (unrestrictedPhaseRoot n) (signedPhaseRoot n)) := by
    intro s hs
    have hsData := hSegmentData s (Ioo_subset_Icc_self hs)
    exact
      (hasDerivAt_phaseSignedFourSizeObjective n hsData.1
        (signedFourAdmissibilityTargetCorridor_subset_Ioo hsData.2)).differentiableAt.differentiableWithinAt
  have hDerivLower :
      ∀ s ∈ Ioo (unrestrictedPhaseRoot n) (signedPhaseRoot n),
        signedFourDerivativeSlopeLower C n ≤
          deriv (phaseSignedFourSizeObjective n) s := by
    intro s hs
    have hsData := hSegmentData s (Ioo_subset_Icc_self hs)
    have hHasDeriv :=
      hasDerivAt_phaseSignedFourSizeObjective n hsData.1
        (signedFourAdmissibilityTargetCorridor_subset_Ioo hsData.2)
    rw [hHasDeriv.deriv]
    exact (hnDerivative s hsData.1 hsData.2).1
  have hIncrement :=
    derivative_lower_bound_mul_sub_le_sub
      hPlusLeCo hCont hDiff hDerivLower
  rw [hnCo.2.2.2] at hIncrement
  have hProductNonneg :
      0 ≤ signedFourDerivativeSlopeLower C n *
        (signedPhaseRoot n - unrestrictedPhaseRoot n) :=
    mul_nonneg hnSlopePos.le (sub_nonneg.mpr hPlusLeCo)
  linarith

/-- Every point between the two selected roots remains positive and in the
fixed manuscript target corridor eventually. -/
theorem eventually_selectedPhaseRootCorridor_feasible :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (signedPhaseRoot n) (unrestrictedPhaseRoot n),
        0 < s ∧
          fourSizeTarget n (phaseNat n) s ∈
            signedFourAdmissibilityTargetCorridor := by
  filter_upwards [eventually_signedPhaseRootData,
    eventually_unrestrictedPhaseRootData,
    eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible] with
    n hnCo hnPlus hnConstruction
  intro s hs
  have hsBroad : s ∈ Icc
      (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
      (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n) := by
    exact ⟨hnCo.1.1.le.trans hs.1, hs.2.trans hnPlus.1.2.le⟩
  have hsConstruction := hnConstruction.2 s hsBroad
  exact ⟨hsConstruction.1, by
    simpa only [fourSizeTarget_eq_profileDeficitTarget] using
      hsConstruction.2⟩

/-- The selected roots satisfy the manuscript phase-varying normalized gap
expansion. -/
theorem tendsto_selectedPhaseRootGap_sub_phaseMargin :
    Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap signedPhaseRoot unrestrictedPhaseRoot n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  obtain ⟨C, _hC, hDerivative, hSlopeLower, hSlopeUpper⟩ :=
    exists_signedFourDerivativeCorridor
  have hGap : ∀ᶠ n : ℕ in atTop,
      0 < unrestrictedPhaseRoot n - signedPhaseRoot n :=
    eventually_signedPhaseRoot_lt_unrestrictedPhaseRoot.mono fun _ hn ↦
      sub_pos.mpr hn
  have hFeasibleIoo : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (signedPhaseRoot n) (unrestrictedPhaseRoot n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5 := by
    filter_upwards [eventually_selectedPhaseRootCorridor_feasible] with n hn
    intro s hs
    exact ⟨(hn s hs).1,
      signedFourAdmissibilityTargetCorridor_subset_Ioo (hn s hs).2⟩
  have hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (signedPhaseRoot n) (unrestrictedPhaseRoot n),
        signedFourDerivativeSlopeLower C n ≤
          signedFourSizeObjectiveDerivative n (phaseNat n) s := by
    filter_upwards [eventually_selectedPhaseRootCorridor_feasible,
      hDerivative] with n hnFeasible hnDerivative
    intro s hs
    have hsClosed : s ∈ Icc
        (signedPhaseRoot n) (unrestrictedPhaseRoot n) :=
      Ioo_subset_Icc_self hs
    exact (hnDerivative s (hnFeasible s hsClosed).1
      (hnFeasible s hsClosed).2).1
  have hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (signedPhaseRoot n) (unrestrictedPhaseRoot n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤
          signedFourDerivativeSlopeUpper C n := by
    filter_upwards [eventually_selectedPhaseRootCorridor_feasible,
      hDerivative] with n hnFeasible hnDerivative
    intro s hs
    have hsClosed : s ∈ Icc
        (signedPhaseRoot n) (unrestrictedPhaseRoot n) :=
      Ioo_subset_Icc_self hs
    exact (hnDerivative s (hnFeasible s hsClosed).1
      (hnFeasible s hsClosed).2).2
  exact
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_centerLocalization_and_derivativeCorridor
      signedPhaseRoot unrestrictedPhaseRoot
      (signedFourDerivativeSlopeLower C)
      (signedFourDerivativeSlopeUpper C)
      unrestrictedPhaseRoot_centerLocalization hGap
      eventually_signedPhaseRoot_equation
      eventually_unrestrictedPhaseRoot_equation
      hFeasibleIoo hDerivLower hDerivUpper hSlopeLower hSlopeUpper

/-- Fully concrete E625-10 signed first-moment lower bound for the selected
signed and unrestricted roots. -/
theorem eventually_selectedPhaseRoot_firstMoment_lowerBound :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount
              signedPhaseRoot unrestrictedPhaseRoot n : ℝ)) <
        signedFourRootMidpointFirstMoment
          signedPhaseRoot unrestrictedPhaseRoot n := by
  have hGap : ∀ᶠ n : ℕ in atTop,
      0 < unrestrictedPhaseRoot n - signedPhaseRoot n :=
    eventually_signedPhaseRoot_lt_unrestrictedPhaseRoot.mono fun _ hn ↦
      sub_pos.mpr hn
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_positiveGap_rootEquations_centerLocalization_and_compactFeasibility
      signedPhaseRoot unrestrictedPhaseRoot
      unrestrictedPhaseRoot_centerLocalization hGap
      eventually_selectedPhaseRootCorridor_feasible
      eventually_signedPhaseRoot_equation
      eventually_unrestrictedPhaseRoot_equation

#print axioms tendsto_finiteSignedFourMargin_at_unrestrictedPhaseRoot_sub_phaseMargin
#print axioms eventually_finiteSignedFourMargin_at_unrestrictedPhaseRoot_pos
#print axioms eventually_phaseSignedFourSizeObjective_unrestrictedPhaseRoot_pos
#print axioms eventually_signedPhaseRoot_lt_unrestrictedPhaseRoot
#print axioms eventually_selectedPhaseRootCorridor_feasible
#print axioms tendsto_selectedPhaseRootGap_sub_phaseMargin
#print axioms eventually_selectedPhaseRoot_firstMoment_lowerBound

end

end Erdos625
