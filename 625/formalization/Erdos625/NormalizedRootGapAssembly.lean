import Erdos625.FiniteSignedMarginAlongMovingTarget
import Erdos625.SignedFourMidpointObjectiveAsymptotic
import Mathlib.Tactic

/-!
# Assembling the normalized signed/unrestricted root gap

The exact secant identity proves at finite `n` that

`secantSlope * (rPlus-rCo) = rPlus * finiteMargin`.

This module normalizes that identity by the manuscript scales and performs the
phase-varying asymptotic algebra.  It does not assume the normalized root-gap
coefficient.  Instead it derives it from:

* the exact signed and unrestricted root equations;
* the normalized right-root part-count limit;
* the normalized signed-objective secant-slope limit;
* convergence of the exact finite margin to the phase-varying limiting margin.

A second wrapper obtains the finite-margin input from compact-uniform entropy
convergence and an explicit limiting-target transport theorem.  The target
transport remains a separate honest analytic input; it is not replaced by the
desired root-gap estimate.

No root existence, derivative-corridor proof, target-transport proof, first
moment, chromatic lower tail, partial diagonal, skeleton, second moment, or
final Erdős statement is supplied here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The unrestricted root normalized by the natural part-count scale. -/
noncomputable def signedFourNormalizedRightRootPartCount
    (rPlus : ℕ → ℝ) (n : ℕ) : ℝ :=
  rPlus n / signedFourNaturalPartScale n

/-- The signed-objective secant slope between the signed and unrestricted
roots, normalized by `(log n)^2`. -/
noncomputable def signedFourNormalizedRootSecantSlope
    (rCo rPlus : ℕ → ℝ) (n : ℕ) : ℝ :=
  phaseSignedFourRootSecantSlope n (rCo n) (rPlus n) /
    (logOrder n) ^ 2

/-- Exact normalized form of the finite secant/root-gap identity. -/
theorem signedFourNormalizedSecant_mul_gap_eq_right_mul_finiteMargin
    (rCo rPlus : ℕ → ℝ) (n : ℕ)
    (hn : 1 < n)
    (hGap : rPlus n - rCo n ≠ 0)
    (hPlus : rPlus n ≠ 0)
    (hCoRoot : phaseSignedFourSizeObjective n (rCo n) = 0)
    (hPlusRoot : unrestrictedPhaseObjective n (rPlus n) = 0) :
    signedFourNormalizedRootSecantSlope rCo rPlus n *
        signedFourNormalizedRootGap rCo rPlus n =
      signedFourNormalizedRightRootPartCount rPlus n *
        finiteSignedFourMargin (phaseNat n)
          (fourSizeTarget n (phaseNat n) (rPlus n)) := by
  have hExact := phaseSignedFourRootSecantSlope_mul_gap_eq
    n hGap hPlus hCoRoot hPlusRoot
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedRootSecantSlope
    signedFourNormalizedRootGap
    signedFourNormalizedRightRootPartCount
    signedFourNaturalRootGapScale signedFourNaturalPartScale
  field_simp [hnReal, hlog]
  linear_combination (logOrder n) * hExact

/-- Exact finite margin convergence to the phase margin can be assembled from
compact-uniform finite-margin convergence and a separate limiting-target
transport. -/
theorem tendsto_finiteSignedFourMargin_sub_phaseMargin_of_compactTarget
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5)
    (alpha : ℕ → ℕ) (target : ℕ → ℝ)
    (hAlpha : Tendsto alpha atTop atTop)
    (hTarget : ∀ᶠ n : ℕ in atTop, target n ∈ Icc A B)
    (hLimitingTarget : Tendsto
      (fun n : ℕ ↦
        (q - fourEntropyLoss (target n)) -
          signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        finiteSignedFourMargin (alpha n) (target n) -
          signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  have hFinite :=
    tendsto_finiteSignedFourMargin_sub_limiting_along_compactTarget
      hA hAB hB alpha target hAlpha hTarget
  have h := hFinite.add hLimitingTarget
  simpa only [add_zero] using h.congr'
    (Filter.Eventually.of_forall fun n ↦ by ring)

/-- The exact secant identity and the three normalized asymptotic inputs imply
the manuscript phase-varying normalized root-gap expansion. -/
theorem tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_secant
    (rCo rPlus : ℕ → ℝ)
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
      atTop (𝓝 (2 / q)))
    (hMargin : Tendsto
      (fun n : ℕ ↦
        finiteSignedFourMargin (phaseNat n)
            (fourSizeTarget n (phaseNat n) (rPlus n)) -
          signedFourPhaseMargin n)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  let coeff : ℕ → ℝ := fun n ↦
    signedFourNormalizedRightRootPartCount rPlus n *
      (signedFourNormalizedRootSecantSlope rCo rPlus n)⁻¹
  have hSecantInv := hSecant.inv₀
    (div_ne_zero (by norm_num : (2 : ℝ) ≠ 0) q_ne_zero)
  have hCoeffRaw := hRightParts.mul hSecantInv
  have hCoeffLimit : (q / 2) * (2 / q)⁻¹ = q ^ 2 / 4 := by
    field_simp [q_ne_zero]
    ring
  have hCoeff : Tendsto coeff atTop (𝓝 (q ^ 2 / 4)) := by
    simpa only [coeff, hCoeffLimit] using hCoeffRaw
  have hCoeffConst : Tendsto (fun _n : ℕ ↦ (q ^ 2 / 4 : ℝ))
      atTop (𝓝 (q ^ 2 / 4)) := tendsto_const_nhds
  have hCoeffErr : Tendsto
      (fun n : ℕ ↦ coeff n - q ^ 2 / 4)
      atTop (𝓝 0) := by
    simpa using hCoeff.sub hCoeffConst
  have hMarginCoeffErr : Tendsto
      (fun n : ℕ ↦ signedFourPhaseMargin n *
        (coeff n - q ^ 2 / 4))
      atTop (𝓝 0) := by
    apply bdd_le_mul_tendsto_zero (b := 0) (B := q)
    · exact Filter.Eventually.of_forall fun n ↦
        (signedFourPhaseMargin_mem_Icc n).1
    · exact Filter.Eventually.of_forall fun n ↦
        (signedFourPhaseMargin_mem_Icc n).2
    · exact hCoeffErr
  have hCoeffMarginErr : Tendsto
      (fun n : ℕ ↦ coeff n *
        (finiteSignedFourMargin (phaseNat n)
            (fourSizeTarget n (phaseNat n) (rPlus n)) -
          signedFourPhaseMargin n))
      atTop (𝓝 0) := by
    simpa using hCoeff.mul hMargin
  have hProductErr : Tendsto
      (fun n : ℕ ↦
        coeff n *
            finiteSignedFourMargin (phaseNat n)
              (fourSizeTarget n (phaseNat n) (rPlus n)) -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0) := by
    have h := hCoeffMarginErr.add hMarginCoeffErr
    convert h using 1
    · funext n
      dsimp only [coeff]
      ring
    · ring
  have hSecantNe : ∀ᶠ n : ℕ in atTop,
      signedFourNormalizedRootSecantSlope rCo rPlus n ≠ 0 :=
    hSecant.eventually_ne
      (div_ne_zero (by norm_num : (2 : ℝ) ≠ 0) q_ne_zero)
  refine hProductErr.congr' ?_
  filter_upwards [hGap, hPlus, hCoRoot, hPlusRoot, hSecantNe,
    eventually_gt_atTop (1 : ℕ)] with
    n hnGap hnPlus hnCoRoot hnPlusRoot hnSecant hn
  have hExact :=
    signedFourNormalizedSecant_mul_gap_eq_right_mul_finiteMargin
      rCo rPlus n hn hnGap hnPlus hnCoRoot hnPlusRoot
  have hSolved :
      signedFourNormalizedRootGap rCo rPlus n =
        coeff n * finiteSignedFourMargin (phaseNat n)
          (fourSizeTarget n (phaseNat n) (rPlus n)) := by
    unfold coeff
    apply (eq_mul_inv_iff_mul_eq₀ hnSecant).2
    simpa only [mul_comm] using hExact.symm
  rw [hSolved]

/-- Manuscript-facing root-gap wrapper: compact finite-margin convergence is
inserted before the exact secant asymptotic assembly. -/
theorem tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_compactTarget_and_secant
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5)
    (rCo rPlus : ℕ → ℝ)
    (hPhase : Tendsto phaseNat atTop atTop)
    (hTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (rPlus n) ∈ Icc A B)
    (hLimitingTarget : Tendsto
      (fun n : ℕ ↦
        (q - fourEntropyLoss
            (fourSizeTarget n (phaseNat n) (rPlus n))) -
          signedFourPhaseMargin n)
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
  have hMargin :=
    tendsto_finiteSignedFourMargin_sub_phaseMargin_of_compactTarget
      hA hAB hB phaseNat
      (fun n ↦ fourSizeTarget n (phaseNat n) (rPlus n))
      hPhase hTarget hLimitingTarget
  exact
    tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_secant
      rCo rPlus hGap hPlus hCoRoot hPlusRoot
      hRightParts hSecant hMargin

#print axioms signedFourNormalizedSecant_mul_gap_eq_right_mul_finiteMargin
#print axioms tendsto_finiteSignedFourMargin_sub_phaseMargin_of_compactTarget
#print axioms tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_secant
#print axioms tendsto_signedFourNormalizedRootGap_sub_phaseMargin_of_compactTarget_and_secant

end

end Erdos625