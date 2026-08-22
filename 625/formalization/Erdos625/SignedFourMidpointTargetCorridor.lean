import Erdos625.SignedFourMidpointAdmissibility
import Mathlib.Tactic

/-!
# An explicit compact corridor for the root-midpoint target

The phase-varying limiting target is

`1 + 2/q - phaseDelta n`.

Using explicit rigorous bounds on `log 2`, this target lies for every `n` in

`[14/5, 4]`.

Hence any actual midpoint target converging to the phase target is eventually
contained in the fixed compact interval

`[5/2, 9/2] ⊂ (2,5)`.

This module supplies that conversion and then feeds it to the midpoint
admissibility assembly.  The abstract compact-set input from the preceding
module is thereby replaced by one concrete target asymptotic.

No root existence, derivative estimate, root-gap estimate, first-moment
estimate, chromatic lower tail, partial diagonal, second moment, or final
Erdős statement is assumed or proved here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Fixed compact interval safely containing every sufficiently accurate
phase target. -/
def signedFourAdmissibilityTargetCorridor : Set ℝ :=
  Icc (5 / 2 : ℝ) (9 / 2 : ℝ)

/-- The explicit target corridor is compact. -/
theorem signedFourAdmissibilityTargetCorridor_compact :
    IsCompact signedFourAdmissibilityTargetCorridor := by
  exact isCompact_Icc

/-- The explicit target corridor lies strictly inside the four-size support
interval. -/
theorem signedFourAdmissibilityTargetCorridor_subset_Ioo :
    signedFourAdmissibilityTargetCorridor ⊆ Ioo (2 : ℝ) 5 := by
  intro x hx
  simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hx
  exact ⟨by linarith, by linarith⟩

/-- Uniform pointwise bounds for the phase-varying limiting target. -/
theorem signedFourPhaseTarget_mem_explicit_Icc (n : ℕ) :
    signedFourPhaseTarget n ∈ Icc (14 / 5 : ℝ) 4 := by
  have hqUpper : q < (5 / 7 : ℝ) := by
    unfold q
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hqLower : (2 / 3 : ℝ) < q := by
    unfold q
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hTwoDivLower : (14 / 5 : ℝ) < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    nlinarith
  have hTwoDivUpper : 2 / q < (3 : ℝ) := by
    rw [div_lt_iff₀ q_pos]
    nlinarith
  have hDeltaLower := phaseDelta_nonneg n
  have hDeltaUpper := (phaseDelta_lt_one n).le
  unfold signedFourPhaseTarget
  constructor <;> linarith

/-- The phase target itself belongs to the fixed admissibility corridor. -/
theorem signedFourPhaseTarget_mem_admissibilityTargetCorridor (n : ℕ) :
    signedFourPhaseTarget n ∈ signedFourAdmissibilityTargetCorridor := by
  have h := signedFourPhaseTarget_mem_explicit_Icc n
  simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at h ⊢
  constructor <;> linarith

/-- Convergence of an actual deficit target to the phase target gives eventual
containment in the explicit compact corridor. -/
theorem eventually_fourSizeTarget_mem_admissibilityTargetCorridor_of_tendsto
    (K : ℕ → ℕ)
    (hTargetApprox : Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n) (K n : ℝ) -
          signedFourPhaseTarget n)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (K n : ℝ) ∈
        signedFourAdmissibilityTargetCorridor := by
  have hError : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (K n : ℝ) -
          signedFourPhaseTarget n ∈
        Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    hTargetApprox.eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hError] with n hn
  have hPhase := signedFourPhaseTarget_mem_explicit_Icc n
  simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hPhase ⊢
  constructor <;> linarith [hn.1, hn.2]

/-- The root-midpoint rounding profile is eventually admissible as soon as its
deficit target converges to the exact phase target and its part count has the
ordinary manuscript asymptotic. -/
theorem eventually_rootMidpointRoundingAdmissible_of_target_tendsto
    (rCo rPlus : ℕ → ℝ)
    (hTargetApprox : Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n)
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseTarget n)
      atTop (𝓝 0))
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (signedFourRootMidpointPartCount rCo rPlus n) := by
  have hTarget :=
    eventually_fourSizeTarget_mem_admissibilityTargetCorridor_of_tendsto
      (signedFourRootMidpointPartCount rCo rPlus) hTargetApprox
  exact eventually_rootMidpointRoundingAdmissible_of_compactTarget
    rCo rPlus signedFourAdmissibilityTargetCorridor
    signedFourAdmissibilityTargetCorridor_compact
    signedFourAdmissibilityTargetCorridor_subset_Ioo
    hTarget hParts

/-- Manuscript-facing exponential E625-10 endpoint with both the compact
target corridor and midpoint admissibility derived from target convergence. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_target_tendsto
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ)
    (hTargetApprox : Tendsto
      (fun n : ℕ ↦
        fourSizeTarget n (phaseNat n)
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ) -
          signedFourPhaseTarget n)
      atTop (𝓝 0))
    (hCo : ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n)
    (hGap : ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n)
    (hSlopeLowerNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeLower n)
    (hSlopeUpperNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeUpper n)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        slopeLower n ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper n)
    (hRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hSlopeLower : Tendsto (signedFourNormalizedSlope slopeLower)
      atTop (𝓝 (2 / q)))
    (hSlopeUpper : Tendsto (signedFourNormalizedSlope slopeUpper)
      atTop (𝓝 (2 / q)))
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0))
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) <
        signedFourRootMidpointFirstMoment rCo rPlus n := by
  have hCompactTarget :=
    eventually_fourSizeTarget_mem_admissibilityTargetCorridor_of_tendsto
      (signedFourRootMidpointPartCount rCo rPlus) hTargetApprox
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_compactTarget
      rCo rPlus slopeLower slopeUpper
      signedFourAdmissibilityTargetCorridor
      signedFourAdmissibilityTargetCorridor_compact
      signedFourAdmissibilityTargetCorridor_subset_Ioo
      hCompactTarget hCo hGap hSlopeLowerNonneg hSlopeUpperNonneg
      hFeasible hDerivLower hDerivUpper hRoot hSlopeLower hSlopeUpper
      hRootGap hParts

#print axioms signedFourAdmissibilityTargetCorridor_compact
#print axioms signedFourAdmissibilityTargetCorridor_subset_Ioo
#print axioms signedFourPhaseTarget_mem_explicit_Icc
#print axioms signedFourPhaseTarget_mem_admissibilityTargetCorridor
#print axioms eventually_fourSizeTarget_mem_admissibilityTargetCorridor_of_tendsto
#print axioms eventually_rootMidpointRoundingAdmissible_of_target_tendsto
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_target_tendsto

end

end Erdos625
