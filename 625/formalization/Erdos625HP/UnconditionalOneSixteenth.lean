import Erdos625.Section13GlobalFixedOffsetSeed
import Erdos625.Section10_11UniformSeedRootFinal
import Erdos625.Section11ConcreteChromaticLowerTail
import Erdos625.Section8FixedOffsetPhaseInputs
import Erdos625HP.FourSizeSharpCertificate

/-!
# Unconditional full-sequence recertification: `1/16 = 0.0625` and phase-resolved `A₄(δ_n)`

Combining the self-contained four-deficit (`S₄ = {2, 3, 4, 5}`) second-moment seed
(`Erdos625.exists_phaseCochromaticFixedOffset_real_seed`), uniform amplification
(`Erdos625.exists_uniform_cochromatic_amplification_at_manuscript_scales`), and
chromatic lower tail
(`Erdos625.randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero`)
from the `Erdos625` library with the sharp certificate and Lipschitz regularity of
`Erdos625HP.FourSizeSharpCertificate` yields **completely unconditional, closed,
zero-hypothesis full-sequence theorems** for `G_n ~ G(n, 1/2)`:

* `erdos625_fourSize_phaseResolved` — there exists a deterministic sequence
  `eps : ℕ → ℝ` with `0 ≤ eps n` and `eps n → 0` such that
  `P(((log 2)² / 4 · A₄(δ_n) - eps n) · n / (log n)³ ≤ χ(G_n) - ζ(G_n)) → 1`.
* `erdos625_one_sixteenth` — unconditionally along all integers `n → ∞`,
  `P((1 / 16) · n / (log n)³ ≤ χ(G_n) - ζ(G_n)) → 1` (`1/16 = 0.0625`, nearly
  doubling the `0.03218` constant of `Erdos625.erdos625`).
* `erdos625_lt_min_fourSize` — for every constant
  `c < (log 2)² / 4 · inf_{δ ∈ [0,1]} A₄(δ)`,
  `P(c · n / (log n)³ ≤ χ(G_n) - ζ(G_n)) → 1`.
-/

namespace Erdos625HP

open Erdos625 FiveSizeEntropyGap Filter MeasureTheory Set Asymptotics
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

/-- Upper bound `A₄(δ) ≤ log 2` on `[0, 1]` from `S₄ ⊆ S₊`. -/
theorem phaseGain4_le_log_two (delta : ℝ) (hdelta : delta ∈ Icc (0 : ℝ) 1) :
    phaseGain4 delta ≤ Real.log 2 := by
  obtain ⟨hT25, -⟩ := phaseTarget_bounds delta hdelta
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  have hmono := dualValue_mono subset_rfl S4_subset_Splus hm
  unfold phaseGain4
  linarith

/-- Phase-resolved four-size margin lower bound uniformly across every fixed
log-log corridor around `phaseRootCenter n`. -/
theorem eventually_phaseSignedFourMargin_phaseGain4_sub
    (C : ℝ) (hC : 0 ≤ C) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
        phaseGain4 (phaseDelta n) - eta ≤
          finiteSignedFourMargin (phaseNat n) (fourSizeTarget n (phaseNat n) s) := by
  let KLip : ℝ := 16 * dualLipschitzSpan + 1
  have hKLipPos : 0 < KLip := by
    dsimp [KLip]
    linarith [dualLipschitzSpan_nonneg]
  let rho : ℝ := (eta / 2) / KLip
  have hrhoPos : 0 < rho := div_pos (half_pos heta) hKLipPos
  have htransport :=
    eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center
      C hC rho hrhoPos
  obtain ⟨Nscore, hNscore⟩ :=
    eventually_uniform_fourDeficitOptimizedValue (eta / 2) (half_pos heta)
  have hle : (logOrder : ℕ → ℝ) ≤ᶠ[atTop] fun n : ℕ ↦ (phaseNat n : ℝ) := by
    filter_upwards
      [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
    exact hn.1
  have hphaseNat : Tendsto phaseNat atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ)).mp
      (tendsto_atTop_mono' atTop hle tendsto_logOrder_atTop)
  filter_upwards
    [eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
      htransport, eventually_five_lt_phaseNat,
      hphaseNat.eventually (eventually_ge_atTop Nscore),
      eventually_phaseRoot_domain_pos_and_target_corridor] with
      n htarget hmove hphase hscore hdomain
  obtain ⟨hdom, _, _⟩ := hdomain
  intro s hs
  set T : ℝ := fourSizeTarget n (phaseNat n) s with hT
  have hTK : T ∈ Icc (9 / 4 : ℝ) (17 / 4 : ℝ) := htarget s hs
  have hTinterior : T ∈ Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
  have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
    ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have hCenterEq : phaseRootDeficitTarget n = phaseTarget (phaseDelta n) := by
    rw [phaseRootDeficitTarget_eq hdom]
    rfl
  have hCenterK : phaseTarget (phaseDelta n) ∈ Icc (9 / 4 : ℝ) (17 / 4 : ℝ) := by
    obtain ⟨hA, hB⟩ := FiveSizePhaseGainCertificate.two_div_log_two_bounds
    unfold phaseTarget
    exact ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩
  have hdist : |T - phaseTarget (phaseDelta n)| < rho := by
    rw [← hCenterEq]
    simpa [Real.dist_eq, hT] using hmove s hs
  have hLipSp := abs_dualValue_sub_le_of_mem_Icc S4_subset_Splus subset_rfl hTK hCenterK
  have hLipS4 := abs_dualValue_sub_le_of_mem_Icc subset_rfl S4_subset_Splus hTK hCenterK
  have hDiffStep :
      (dualValue Splus T - dualValue S4 T) -
        (dualValue Splus (phaseTarget (phaseDelta n)) -
          dualValue S4 (phaseTarget (phaseDelta n))) ≤
        16 * dualLipschitzSpan * |T - phaseTarget (phaseDelta n)| := by
    have h1 := (abs_le.mp hLipSp).2
    have h2 := (abs_le.mp hLipS4).1
    linarith
  have hStepLt : 16 * dualLipschitzSpan * |T - phaseTarget (phaseDelta n)| < eta / 2 := by
    have h1 : 16 * dualLipschitzSpan * |T - phaseTarget (phaseDelta n)| ≤
        KLip * |T - phaseTarget (phaseDelta n)| := by
      dsimp [KLip]
      linarith [abs_nonneg (T - phaseTarget (phaseDelta n))]
    have h2 : KLip * |T - phaseTarget (phaseDelta n)| < KLip * rho :=
      mul_lt_mul_of_pos_left hdist hKLipPos
    have h3 : KLip * rho = eta / 2 := by
      dsimp [rho]
      exact mul_div_cancel₀ _ hKLipPos.ne'
    linarith
  have hLossLe : fourEntropyLoss T ≤ (q - phaseGain4 (phaseDelta n)) + eta / 2 := by
    have hbridge := fourEntropyLoss_le_dualValue_diff hTinterior
    unfold phaseGain4 q
    linarith
  have hscoreAbs := hNscore (phaseNat n) hscore T hTinterior
  have hscoreLt : finiteFourScoreEntropyError (phaseNat n) T < eta / 2 := by
    unfold finiteFourScoreEntropyError
    rw [abs_sub_comm] at hscoreAbs
    exact (abs_lt.mp hscoreAbs).2
  have hunrestrictedLe : finiteUnrestrictedEntropyError (phaseNat n) T ≤ 0 := by
    unfold finiteUnrestrictedEntropyError finiteUnrestrictedDeficitEntropy
    have h := finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
      (phaseNat n) hphase hTinterior
    linarith
  rw [hT, finiteSignedFourMargin_eq_limiting_sub_errors]
  linarith

/-- Scalar coefficient perturbation inequality used for both four-size and
five-size lower root separations (`0 ≤ A ≤ log 2`). -/
theorem lowerCoeff_quotient_le {A theta : ℝ} (hA0 : 0 ≤ A) (hAq : A ≤ q)
    (htheta : 0 < theta) :
    (Real.log 2) ^ 2 / 4 * A - theta ≤
      q ^ 3 / 8 * (A - min (1 / 4) (theta / (q ^ 2 + 1))) /
        (q / 2 + q * theta / 4) := by
  set eta : ℝ := min (1 / 4) (theta / (q ^ 2 + 1))
  set epsilon : ℝ := q * theta / 4
  have hepsilonPos : 0 < epsilon := div_pos (mul_pos q_pos htheta) (by norm_num)
  have hDenomPos : 0 < q / 2 + epsilon := by linarith [q_pos]
  rw [le_div_iff₀ hDenomPos]
  have hqeq : Real.log 2 = q := rfl
  rw [hqeq]
  have hq1 : q < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hq2le1 : q ^ 2 ≤ 1 := pow_le_one₀ q_pos.le hq1.le
  have hq3le1 : q ^ 3 ≤ 1 := pow_le_one₀ q_pos.le hq1.le
  have hq2p : 0 < q ^ 2 + 1 := by positivity
  -- Term 1: `q ^ 3 / 8 * eta ≤ theta * q / 8`
  have hetaBound : q ^ 3 / 8 * eta ≤ theta * q / 8 := by
    have heta2 : eta ≤ theta / (q ^ 2 + 1) := min_le_right _ _
    have h1 : q ^ 2 * eta ≤ q ^ 2 * (theta / (q ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_left heta2 (sq_nonneg q)
    have h2 : q ^ 2 * (theta / (q ^ 2 + 1)) ≤ (q ^ 2 + 1) * (theta / (q ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg htheta.le hq2p.le)
    have h3 : (q ^ 2 + 1) * (theta / (q ^ 2 + 1)) = theta := mul_div_cancel₀ _ hq2p.ne'
    have hq2eta : q ^ 2 * eta ≤ theta := h1.trans (h2.trans_eq h3)
    have hm := mul_le_mul_of_nonneg_left hq2eta (div_nonneg q_pos.le (by norm_num : (0 : ℝ) ≤ 8))
    linarith [show q / 8 * (q ^ 2 * eta) = q ^ 3 / 8 * eta by ring,
              show q / 8 * theta = theta * q / 8 by ring]
  -- Term 2: `(q ^ 2 / 4 * A) * epsilon ≤ theta * q / 16`
  have hepsProd : (q ^ 2 / 4 * A) * epsilon ≤ theta * q / 16 := by
    have hq3A : q ^ 3 * A ≤ q := by
      calc q ^ 3 * A ≤ 1 * q := mul_le_mul hq3le1 hAq hA0 zero_le_one
        _ = q := one_mul q
    have hm := mul_le_mul_of_nonneg_right hq3A (div_nonneg htheta.le (by norm_num : (0 : ℝ) ≤ 16))
    dsimp [epsilon]
    linarith [show (q ^ 2 / 4 * A) * (q * theta / 4) = (q ^ 3 * A) * (theta / 16) by ring,
              show q * (theta / 16) = theta * q / 16 by ring]
  have hte : 0 ≤ theta * epsilon := mul_nonneg htheta.le hepsilonPos.le
  linarith [mul_pos htheta q_pos]

/-- **Phase-resolved root separation for `S₄`:** for every `θ > 0`, eventually
`((log 2)² / 4 · A₄(δ_n) - θ) · baseScale n ≤ r_+(n) - r_co(n)`. -/
theorem eventually_phaseSelectedRootSeparation_phaseGain4
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ n : ℕ in atTop,
      ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta) * baseScale n ≤
        unrestrictedPhaseRootSelected n - phaseSignedFourSizeRootSelected n := by
  let C : ℝ := phaseRootCommonCorridorCoefficient
  have hCPos : 0 < C := phaseRootCommonCorridorCoefficient_pos
  have hCNonneg : 0 ≤ C := hCPos.le
  let eta : ℝ := min (1 / 4) (theta / (q ^ 2 + 1))
  have hetaPos : 0 < eta := lt_min (by norm_num) (div_pos htheta (by positivity))
  let epsilon : ℝ := q * theta / 4
  have hepsilonPos : 0 < epsilon := div_pos (mul_pos q_pos htheta) (by norm_num)
  have hDenomPos : 0 < q / 2 + epsilon := by linarith [q_pos]
  have hLogLogPos : ∀ᶠ n : ℕ in atTop, 0 < logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_gt_atTop 0
  filter_upwards
    [eventually_phaseSignedFourSizeRootSelected_spec_unique,
      eventually_unrestrictedPhaseRootSelected_spec_unique,
      eventually_phaseSignedFourMargin_phaseGain4_sub C hCNonneg hetaPos,
      eventually_signedFourSizeObjectiveDerivative_logLogCorridor_lower C hCNonneg,
      eventually_signedFourSizeObjectiveDerivative_logLogCorridor_upper_sharp
        C hCNonneg epsilon hepsilonPos,
      eventually_phaseRootLogLogCorridor_fourSize_domain C hCNonneg,
      eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower C hCNonneg,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_five_lt_phaseNat,
      eventually_ge_atTop (2 : ℕ),
      hLogLogPos] with
      n hSigned hUnrestricted hMargin hDerivLower hDerivUpper hDomain
        hScale hCenter hPhaseLarge hn2 hLogLog
  let rCo : ℝ := phaseSignedFourSizeRootSelected n
  let rPlus : ℝ := unrestrictedPhaseRootSelected n
  let center : ℝ := phaseRootCenter n
  let radius : ℝ := phaseRootGapRadius n
  let width : ℝ := logLogOrder n * radius
  let lower : ℝ := center - C * width
  let upper : ℝ := center + C * width
  let F : ℝ → ℝ := phaseSignedFourSizeObjective n
  let a : ℝ := phaseNat n
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hCenter.1.1)
  have hCenterPos : 0 < center := div_pos hnPos hCenter.2.1
  have haNatPos : 0 < phaseNat n := lt_trans (by omega : 0 < 5) hPhaseLarge
  have haPos : 0 < a := Nat.cast_pos.mpr haNatPos
  have hRadiusPos : 0 < radius := div_pos hCenterPos (sq_pos_of_pos haPos)
  have hWidthNonneg : 0 ≤ width := mul_nonneg hLogLog.le hRadiusPos.le
  have hSignedWidthLe :
      phaseSignedFourSizeRootCorridorCoefficient * width ≤ C * width :=
    mul_le_mul_of_nonneg_right
      (by simp only [C, phaseRootCommonCorridorCoefficient]
          linarith [unrestrictedPhaseRootCorridorCoefficient_pos])
      hWidthNonneg
  have hUnrestrictedWidthLe :
      unrestrictedPhaseRootCorridorCoefficient * width ≤ C * width :=
    mul_le_mul_of_nonneg_right
      (by simp only [C, phaseRootCommonCorridorCoefficient]
          linarith [phaseSignedFourSizeRootCorridorCoefficient_pos])
      hWidthNonneg
  have hSignedCommon : rCo ∈ Icc lower upper := by
    have hOwn := hSigned.1.1
    rw [mem_Ioo] at hOwn; rw [mem_Icc]
    exact ⟨by dsimp [rCo, center, width, lower] at hOwn ⊢; linarith [hSignedWidthLe],
           by dsimp [rCo, center, width, upper] at hOwn ⊢; linarith [hSignedWidthLe]⟩
  have hUnrestrictedCommon : rPlus ∈ Icc lower upper := by
    have hOwn := hUnrestricted.1.1
    rw [mem_Ioo] at hOwn; rw [mem_Icc]
    exact ⟨by dsimp [rPlus, center, width, lower] at hOwn ⊢; linarith [hUnrestrictedWidthLe],
           by dsimp [rPlus, center, width, upper] at hOwn ⊢; linarith [hUnrestrictedWidthLe]⟩
  have hDomain' : ∀ x ∈ Icc lower upper,
      0 < x ∧ fourSizeTarget n (phaseNat n) x ∈ Ioo (2 : ℝ) 5 := by
    intro x hx
    exact hDomain x (by simpa [lower, upper, center, width, C, mul_assoc] using hx)
  have hHasDeriv : ∀ x ∈ Icc lower upper,
      HasDerivAt F (signedFourSizeObjectiveDerivative n (phaseNat n) x) x :=
    fun x hx ↦ hasDerivAt_phaseSignedFourSizeObjective n (hDomain' x hx).1 (hDomain' x hx).2
  have hContinuous : ContinuousOn F (Icc lower upper) :=
    fun x hx ↦ (hHasDeriv x hx).continuousAt.continuousWithinAt
  have hStrict : StrictMonoOn F (Icc lower upper) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc lower upper) hContinuous
    intro x hx
    rw [interior_Icc] at hx
    have hxClosed : x ∈ Icc lower upper := ⟨hx.1.le, hx.2.le⟩
    have hLower := hDerivLower x
      (by simpa [lower, upper, center, width, radius, C, mul_assoc] using hxClosed)
    rw [(hHasDeriv x hxClosed).deriv]
    have haSqPos : 0 < (phaseNat n : ℝ) ^ 2 := sq_pos_of_pos haPos
    have hq8pos : 0 < q / 8 * (phaseNat n : ℝ) ^ 2 :=
      mul_pos (div_pos q_pos (by norm_num)) haSqPos
    linarith
  have hRootCo : F rCo = 0 := hSigned.1.2.2.2
  have hRootPlus : unrestrictedPhaseObjective n rPlus = 0 := hUnrestricted.1.2
  have hRPlusPos : 0 < rPlus := (hDomain' rPlus hUnrestrictedCommon).1
  have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
    ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have hA4lo : (1 / 2 : ℝ) < phaseGain4 (phaseDelta n) := by
    have h := lt_of_le_of_lt log_4207_div_2500_ge (log_4207_div_2500_lt_phaseGain4 _ hdelta)
    linarith
  have hetaLeQuarter : eta ≤ 1 / 4 := min_le_left _ _
  have hAdvPos : 0 < phaseGain4 (phaseDelta n) - eta := by linarith
  have hMarginPlus :
      phaseGain4 (phaseDelta n) - eta ≤
        finiteSignedFourMargin (phaseNat n) (fourSizeTarget n (phaseNat n) rPlus) :=
    hMargin rPlus (by simpa [lower, upper, center, width, C, mul_assoc] using hUnrestrictedCommon)
  have hAdvantage : rPlus * (phaseGain4 (phaseDelta n) - eta) ≤ F rPlus := by
    dsimp [F]
    rw [phaseSignedFourSizeObjective_eq_parts_mul_finiteMargin_of_unrestrictedRoot
      n hRPlusPos.ne' hRootPlus]
    exact mul_le_mul_of_nonneg_left hMarginPlus hRPlusPos.le
  have hOrder : rCo ≤ rPlus := by
    by_contra hNot
    have hMono := hStrict hUnrestrictedCommon hSignedCommon (lt_of_not_ge hNot)
    rw [hRootCo] at hMono
    linarith [mul_pos hRPlusPos hAdvPos]
  have hContinuousRoots : ContinuousOn F (Icc rCo rPlus) :=
    hContinuous.mono fun x hx ↦ ⟨hSignedCommon.1.trans hx.1, hx.2.trans hUnrestrictedCommon.2⟩
  have hDifferentiableRoots : DifferentiableOn ℝ F (Ioo rCo rPlus) := fun x hx ↦ by
    have hd := hHasDeriv x ⟨hSignedCommon.1.trans hx.1.le, hx.2.le.trans hUnrestrictedCommon.2⟩
    exact hd.differentiableAt.differentiableWithinAt
  have hSlopePos : 0 < (q / 2 + epsilon) * a ^ 2 := mul_pos hDenomPos (sq_pos_of_pos haPos)
  have hSlope : ∀ x ∈ Ioo rCo rPlus, deriv F x ≤ (q / 2 + epsilon) * a ^ 2 := by
    intro x hx
    have hxCommon : x ∈ Icc lower upper :=
      ⟨hSignedCommon.1.trans hx.1.le, hx.2.le.trans hUnrestrictedCommon.2⟩
    rw [(hHasDeriv x hxCommon).deriv]
    simpa [a] using hDerivUpper x
      (by simpa [lower, upper, center, width, C, mul_assoc] using hxCommon)
  have hRootGap := signed_root_separation_of_advantage_and_slope
    hOrder hContinuousRoots hDifferentiableRoots hSlopePos hSlope hRootCo hAdvantage
  have hScalePlus : q ^ 3 / 8 * baseScale n ≤ rPlus / a ^ 2 := by
    simpa [rPlus, a, lower, upper, center, width, C, mul_assoc] using
      hScale rPlus (by simpa [lower, upper, center, width, C, mul_assoc] using hUnrestrictedCommon)
  have hQuotNonneg : 0 ≤ (phaseGain4 (phaseDelta n) - eta) / (q / 2 + epsilon) :=
    div_nonneg hAdvPos.le hDenomPos.le
  have hBaseNonneg : 0 ≤ baseScale n := by
    rw [baseScale]
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    positivity
  have hCoeffLe :
      (Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta ≤
        q ^ 3 / 8 * (phaseGain4 (phaseDelta n) - eta) / (q / 2 + epsilon) :=
    lowerCoeff_quotient_le (by linarith [hA4lo]) (phaseGain4_le_log_two _ hdelta) htheta
  calc
    ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta) * baseScale n
        ≤ (q ^ 3 / 8 * (phaseGain4 (phaseDelta n) - eta) / (q / 2 + epsilon)) *
            baseScale n := mul_le_mul_of_nonneg_right hCoeffLe hBaseNonneg
    _ = (q ^ 3 / 8 * baseScale n) *
          ((phaseGain4 (phaseDelta n) - eta) / (q / 2 + epsilon)) := by ring
    _ ≤ (rPlus / a ^ 2) *
          ((phaseGain4 (phaseDelta n) - eta) / (q / 2 + epsilon)) :=
      mul_le_mul_of_nonneg_right hScalePlus hQuotNonneg
    _ = (rPlus * (phaseGain4 (phaseDelta n) - eta)) / ((q / 2 + epsilon) * a ^ 2) := by
      field_simp
    _ ≤ rPlus - rCo := hRootGap
    _ = unrestrictedPhaseRootSelected n - phaseSignedFourSizeRootSelected n := rfl

/-- Deterministic envelope conversion: if for every `θ > 0` eventually
`(coeff n - θ) * baseScale n ≤ val n`, then there exists `eps : ℕ → ℝ` with
`0 ≤ eps n`, `eps n → 0`, and eventually `(coeff n - eps n) * baseScale n ≤ val n`. -/
theorem exists_nonneg_tendsto_zero_envelope
    (coeff val : ℕ → ℝ)
    (h : ∀ {theta : ℝ}, 0 < theta →
      ∀ᶠ n : ℕ in atTop, (coeff n - theta) * baseScale n ≤ val n) :
    ∃ eps : ℕ → ℝ,
      (∀ n, 0 ≤ eps n) ∧
      Tendsto eps atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop, (coeff n - eps n) * baseScale n ≤ val n := by
  let eps : ℕ → ℝ := fun n ↦
    if 2 ≤ n then max 0 (coeff n - val n / baseScale n) else 0
  refine ⟨eps, ?_, ?_, ?_⟩
  · intro n
    dsimp [eps]
    split_ifs
    · exact le_max_left 0 _
    · exact le_rfl
  · rw [Metric.tendsto_atTop]
    intro delta hdelta
    have hev := h (half_pos hdelta)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop (2 : ℕ)))
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨hGapN, hn2⟩ := hN n hn
    have hBasePos : 0 < baseScale n := by
      rw [baseScale]
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hnpos : 0 < (n : ℝ) := by positivity
      positivity
    have hle : coeff n - val n / baseScale n ≤ delta / 2 := by
      have hdiv := (le_div_iff₀ hBasePos).mpr hGapN
      linarith
    have heps_eq : eps n = max 0 (coeff n - val n / baseScale n) := if_pos hn2
    have heps_nonneg : 0 ≤ eps n := by rw [heps_eq]; exact le_max_left 0 _
    have heps_le : eps n ≤ delta / 2 := by
      rw [heps_eq]
      exact max_le (half_pos hdelta).le hle
    rw [Real.dist_eq, sub_zero, abs_of_nonneg heps_nonneg]
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn2
    have hBasePos : 0 < baseScale n := by
      rw [baseScale]
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hnpos : 0 < (n : ℝ) := by positivity
      positivity
    have heps_ge : coeff n - val n / baseScale n ≤ eps n := by
      dsimp [eps]; rw [if_pos hn2]; exact le_max_right 0 _
    have h1 : coeff n - eps n ≤ val n / baseScale n := by linarith
    exact (le_div_iff₀ hBasePos).mp h1

/-- **Unconditional Phase-Resolved Four-Size Gap Theorem:** with zero external
assumptions, there exists a deterministic sequence `eps n ≥ 0` with `eps n → 0`
such that `((log 2)² / 4 · A₄(δ_n) - eps n) · n / (log n)³ ≤ χ(G_n) - ζ(G_n)`
holds with probability tending to `1` along all integers `n → ∞`. -/
theorem erdos625_fourSize_phaseResolved :
    ∃ eps : ℕ → ℝ,
      (∀ n, 0 ≤ eps n) ∧
      Tendsto eps atTop (nhds 0) ∧
      Tendsto (fun n ↦ randomGraphMeasure n
        {G : LabeledGraph n |
          ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - eps n) *
              ((n : ℝ) / (Real.log n) ^ 3) ≤
            (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)})
        atTop (nhds 1) := by
  obtain ⟨Lambda, hLambdaNonneg, hLambdaSmall, hSeed⟩ :=
    exists_phaseCochromaticFixedOffset_real_seed
  obtain ⟨C, _epsilon, _hC, _hEps, _hEpsNonneg, hUniform⟩ :=
    exists_uniform_cochromatic_amplification_at_manuscript_scales
  have hAmp := hUniform phaseCochromaticFixedOffsetIndex Lambda
    hLambdaNonneg hLambdaSmall hSeed
  let a : ℕ → ℝ := fun n ↦
    uniformAmplificationError C n (Lambda n) (amplificationRadius n)
  have haBase : a =o[atTop] baseScale := by
    change a =o[atTop] gapBase
    exact hAmp.1
  let val : ℕ → ℝ := fun n ↦
    ((phaseChromaticLowerIndex n + 1 : ℕ) : ℝ) -
      ((phaseCochromaticFixedOffsetIndex n : ℝ) + a n)
  have hAllTheta : ∀ {theta : ℝ}, 0 < theta →
      ∀ᶠ n : ℕ in atTop,
        ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta) * baseScale n ≤
          val n := by
    intro theta htheta
    let theta' : ℝ := min theta (1 / 32)
    have htheta'Pos : 0 < theta' := lt_min htheta (by norm_num)
    have htheta'Le : theta' ≤ theta := min_le_left _ _
    have htheta'Cap : theta' ≤ 1 / 32 := min_le_right _ _
    have hRoot := eventually_phaseSelectedRootSeparation_phaseGain4
      (htheta := div_pos htheta'Pos (by norm_num : (0 : ℝ) < 3))
    have hBudgetLt : ∀ᶠ n : ℕ in atTop, fixedOffsetRoundingBudget n < theta' / 3 :=
      fixedOffset_rounding_budget_spec.1.eventually
        (Iio_mem_nhds (div_pos htheta'Pos (by norm_num)))
    have haBound : ∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ (theta' / 3) * ‖baseScale n‖ :=
      haBase.bound (div_pos htheta'Pos (by norm_num))
    filter_upwards
      [hRoot, eventually_phaseSignedFourSizeRootSelected_spec_unique,
        fixedOffset_rounding_budget_spec.2, hBudgetLt, haBound,
        eventually_ge_atTop (2 : ℕ)] with
        n hGap hSigned hRounding hBud haN hn2
    set rCo : ℝ := phaseSignedFourSizeRootSelected n with hrCo
    set rPlus : ℝ := unrestrictedPhaseRootSelected n with hrPlus
    have hBasePos : 0 < baseScale n := by
      rw [baseScale]
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
      have hnpos : 0 < (n : ℝ) := by positivity
      positivity
    have hRCoPos : 0 < rCo := hSigned.1.2.1
    have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
      ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
    have hCoeffLo : (1 / 16 : ℝ) < (Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) :=
      one_sixteenth_lt_lowerPhaseCoeff4 _ hdelta
    have hRounding' : Real.log (n : ℝ) + 19 ≤
        fixedOffsetRoundingBudget n * baseScale n := by
      simpa [baseScale] using hRounding
    have hPosSurplus :
        fixedOffsetRoundingBudget n <
          (Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta' / 3 := by
      linarith
    have hBudgetMul :
        fixedOffsetRoundingBudget n * baseScale n ≤
          ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta' / 3) * baseScale n :=
      mul_le_mul_of_nonneg_right hPosSurplus.le hBasePos.le
    have hRPlusLarge : Real.log (n : ℝ) + 19 < rPlus := by linarith
    have hChromaticNonneg : 0 ≤ rootChromaticIndex rPlus (Real.log (n : ℝ)) := by
      unfold rootChromaticIndex
      rw [sub_nonneg]
      apply Int.le_floor.mpr
      have hCeil := Int.ceil_lt_add_one (Real.log (n : ℝ))
      exact (hCeil.trans (by linarith)).le
    have hCochromaticNonneg : 0 ≤ rootCochromaticFixedOffsetIndex rCo := by
      unfold rootCochromaticFixedOffsetIndex
      have := Int.ceil_nonneg hRCoPos.le
      omega
    have hRounded := root_fixedOffset_rounding_gap_toNat
      rPlus rCo (Real.log (n : ℝ))
      ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta' / 3)
      (baseScale n) (fixedOffsetRoundingBudget n) hGap hRounding
      hChromaticNonneg hCochromaticNonneg
    have hIdxGap :
        ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta' / 3 -
            fixedOffsetRoundingBudget n) * baseScale n ≤
          (phaseChromaticLowerIndex n : ℝ) - (phaseCochromaticFixedOffsetIndex n : ℝ) := by
      simpa [phaseChromaticLowerIndex, phaseCochromaticFixedOffsetIndex,
        hrPlus, hrCo] using hRounded
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hBasePos] at haN
    have haUpper : a n ≤ (theta' / 3) * baseScale n := (le_abs_self (a n)).trans haN
    have hBudMul' :
        ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - 2 * (theta' / 3)) * baseScale n ≤
          ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta' / 3 -
            fixedOffsetRoundingBudget n) * baseScale n :=
      mul_le_mul_of_nonneg_right (by linarith) hBasePos.le
    have hThetaCmp :
        ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta) * baseScale n ≤
          ((Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - theta') * baseScale n :=
      mul_le_mul_of_nonneg_right (by linarith) hBasePos.le
    dsimp [val]
    push_cast
    linarith
  obtain ⟨eps, hepsNonneg, hepsZero, hepsBound⟩ :=
    exists_nonneg_tendsto_zero_envelope
      (fun n ↦ (Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n)) val hAllTheta
  have hChromaticTail :=
    chromaticLowerEvent_probability_tendsto_one_of_atMost_tendsto_zero
      phaseChromaticLowerIndex
      randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero
  have hCochromaticTail : Tendsto
      (fun n ↦ randomGraphMeasure n
        (cochromaticUpperEvent n (phaseCochromaticFixedOffsetIndex n) (a n)))
      atTop (nhds 1) := by
    simpa only [a] using hAmp.2
  have hInter := tendsto_measure_inter_one randomGraphMeasure
    (fun n ↦ chromaticLowerEvent n (phaseChromaticLowerIndex n))
    (fun n ↦ cochromaticUpperEvent n (phaseCochromaticFixedOffsetIndex n) (a n))
    (fun n ↦ (Set.toFinite _).measurableSet)
    (fun n ↦ (Set.toFinite _).measurableSet)
    hChromaticTail hCochromaticTail
  refine ⟨eps, hepsNonneg, hepsZero, ?_⟩
  apply tendsto_measure_one_of_eventually_subset randomGraphMeasure _ _ hInter
  filter_upwards [hepsBound] with n hBound G ⟨hChi, hCo⟩
  have hChiNat : phaseChromaticLowerIndex n + 1 ≤ chromaticNumberNat G :=
    Nat.succ_le_iff.mpr hChi
  have hChiReal : ((phaseChromaticLowerIndex n + 1 : ℕ) : ℝ) ≤
      (chromaticNumberNat G : ℝ) := by exact_mod_cast hChiNat
  change (cochromaticNumber G : ℝ) ≤
    (phaseCochromaticFixedOffsetIndex n : ℝ) + a n at hCo
  have hBaseEq : baseScale n = (n : ℝ) / (Real.log n) ^ 3 := rfl
  rw [hBaseEq] at hBound
  dsimp [val] at hBound
  simp only [mem_setOf_eq]
  linarith

/-- **Unconditional `1/16 = 0.0625` Full-Sequence Gap Theorem:** with zero
external hypotheses, `P((1 / 16) · n / (log n)³ ≤ χ(G_n) - ζ(G_n)) → 1`
as `n → ∞` through all integers. -/
theorem erdos625_one_sixteenth :
    Tendsto (fun n ↦ randomGraphMeasure n
      {G : LabeledGraph n |
        (1 / 16 : ℝ) * ((n : ℝ) / (Real.log n) ^ 3) ≤
          (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)})
      atTop (nhds 1) := by
  obtain ⟨eps, _hepsNonneg, hepsZero, hPhase⟩ := erdos625_fourSize_phaseResolved
  have hepsSmall : ∀ᶠ n : ℕ in atTop, eps n < 1 / 100000 :=
    (tendsto_order.1 hepsZero).2 (1 / 100000) (by norm_num)
  apply tendsto_measure_one_of_eventually_subset randomGraphMeasure _ _ hPhase
  filter_upwards [eventually_ge_atTop (2 : ℕ), hepsSmall] with n hn2 heps G hG
  have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
    ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have hCoeff := coeff4_gt_6251_div_100000 (phaseDelta n) hdelta
  have h116 : (1 / 16 : ℝ) ≤ (Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - eps n := by
    linarith
  have hScaleNonneg : 0 ≤ (n : ℝ) / (Real.log n) ^ 3 := by
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hnpos : 0 < (n : ℝ) := by positivity
    positivity
  exact le_trans (mul_le_mul_of_nonneg_right h116 hScaleNonneg) hG

/-- **Unconditional optimal four-size constant theorem:** for every constant
`c < (log 2)² / 4 · inf_{δ ∈ [0,1]} A₄(δ)`,
`P(c · n / (log n)³ ≤ χ(G_n) - ζ(G_n)) → 1` unconditionally. -/
theorem erdos625_lt_min_fourSize (c : ℝ)
    (hc : c < (Real.log 2) ^ 2 / 4 * (⨅ x : Icc (0 : ℝ) 1, phaseGain4 x)) :
    Tendsto (fun n ↦ randomGraphMeasure n
      {G : LabeledGraph n |
        c * ((n : ℝ) / (Real.log n) ^ 3) ≤
          (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)})
      atTop (nhds 1) := by
  obtain ⟨eps, _hepsNonneg, hepsZero, hPhase⟩ := erdos625_fourSize_phaseResolved
  set c₄ : ℝ := (Real.log 2) ^ 2 / 4 * (⨅ x : Icc (0 : ℝ) 1, phaseGain4 x)
  have hmargin : 0 < c₄ - c := sub_pos.mpr hc
  have hepsSmall : ∀ᶠ n : ℕ in atTop, eps n < c₄ - c :=
    (tendsto_order.1 hepsZero).2 (c₄ - c) hmargin
  have hBdd : BddBelow (Set.range fun x : Icc (0 : ℝ) 1 ↦ phaseGain4 x) := by
    refine ⟨Real.log (4207 / 2500), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (log_4207_div_2500_lt_phaseGain4 x.1 x.2).le
  apply tendsto_measure_one_of_eventually_subset randomGraphMeasure _ _ hPhase
  filter_upwards [eventually_ge_atTop (2 : ℕ), hepsSmall] with n hn2 heps G hG
  have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
    ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have hInfLe : (⨅ x : Icc (0 : ℝ) 1, phaseGain4 x) ≤ phaseGain4 (phaseDelta n) :=
    ciInf_le hBdd ⟨phaseDelta n, hdelta⟩
  have hc4Le : c₄ ≤ (Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) :=
    mul_le_mul_of_nonneg_left hInfLe (by positivity)
  have hcLe : c ≤ (Real.log 2) ^ 2 / 4 * phaseGain4 (phaseDelta n) - eps n := by
    linarith
  have hScaleNonneg : 0 ≤ (n : ℝ) / (Real.log n) ^ 3 := by
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hnpos : 0 < (n : ℝ) := by positivity
    positivity
  exact le_trans (mul_le_mul_of_nonneg_right hcLe hScaleNonneg) hG

end

end Erdos625HP
