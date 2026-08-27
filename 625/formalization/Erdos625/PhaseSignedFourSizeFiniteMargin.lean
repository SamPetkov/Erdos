import Erdos625.PhaseSignedFourSizeTargetTransport
import Erdos625.UniformFiniteFourEntropyCertificate
import Erdos625.FiniteProfileDeficitEntropyComparison
import Erdos625.SignedUnrestrictedObjectiveGapIdentity
import Mathlib.Tactic

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

noncomputable def fourTargetRatioLog (T : ℝ) : ℝ :=
  Real.log
    (extendedGaussianPartition q
        (ProfileEntropyS4.tilt fourGaussianScore T) /
      ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore T))

theorem fourEntropyLoss_le_fourTargetRatioLog
    {T : ℝ} (hT : T ∈ Ioo (2 : ℝ) 5) :
    fourEntropyLoss T ≤ fourTargetRatioLog T := by
  set tilt := ProfileEntropyS4.tilt fourGaussianScore T with htilt
  have hMean : ProfileEntropyS4.mean fourGaussianScore tilt = T :=
    ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT
  have hDual := extendedGaussianEntropyValue_le_dual_interior
    (tilt := tilt) hT
  have h := entropy_loss_le_log_partition_ratio
    (tilt := tilt) hMean hDual
  simpa [fourEntropyLoss, fourTargetRatioLog, htilt] using h

theorem continuousOn_fourTargetRatioLog :
    ContinuousOn fourTargetRatioLog (Icc (9 / 4 : ℝ) (17 / 4 : ℝ)) := by
  let K : Set ℝ := Icc (9 / 4 : ℝ) (17 / 4 : ℝ)
  have hKinterior : K ⊆ Ioo (2 : ℝ) 5 := by
    intro T hT
    change T ∈ Icc (9 / 4 : ℝ) (17 / 4 : ℝ) at hT
    constructor <;> linarith [hT.1, hT.2]
  have htiltCont :
      ContinuousOn (fun T => ProfileEntropyS4.tilt fourGaussianScore T) K := by
    intro T hT
    apply ContinuousAt.continuousWithinAt
    exact ProfileEntropyS4.tendsto_tilt_of_scores_and_target
      (h := fun _ : ℝ => fourGaussianScore) fourGaussianScore
      (T' := id) (fun _ => tendsto_const_nhds) Filter.tendsto_id
      (hKinterior hT)
  have hExtCont : Continuous (extendedGaussianPartition q) := by
    rw [continuous_iff_continuousAt]
    exact fun lambda =>
      (hasDerivAt_extendedGaussianPartition q lambda q_pos).continuousAt
  have hFourCont :
      Continuous (ProfileEntropyS4.partition fourGaussianScore) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ProfileEntropyS4.tendsto_partition_of_scores_and_parameter
      (fun _ : ℝ => fourGaussianScore) fourGaussianScore id t
      (fun _ => tendsto_const_nhds) Filter.tendsto_id
  have hNum : ContinuousOn
      (fun T => extendedGaussianPartition q
        (ProfileEntropyS4.tilt fourGaussianScore T)) K :=
    hExtCont.comp_continuousOn htiltCont
  have hDen : ContinuousOn
      (fun T => ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore T)) K :=
    hFourCont.comp_continuousOn htiltCont
  have hDenNe : ∀ T ∈ K,
      ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore T) ≠ 0 :=
    fun T _ => (ProfileEntropyS4.partition_pos fourGaussianScore _).ne'
  have hRatio : ContinuousOn
      (fun T => extendedGaussianPartition q
          (ProfileEntropyS4.tilt fourGaussianScore T) /
        ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore T)) K :=
    hNum.div hDen hDenNe
  have hRatioNe : ∀ T ∈ K,
      extendedGaussianPartition q
          (ProfileEntropyS4.tilt fourGaussianScore T) /
        ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore T) ≠ 0 :=
    fun T _ => (div_pos (extendedGaussianPartition_pos q_pos)
      (ProfileEntropyS4.partition_pos fourGaussianScore _)).ne'
  change ContinuousOn fourTargetRatioLog K
  exact hRatio.log hRatioNe

private theorem phaseRootDeficitTarget_mem_targetCompact
    {n : ℕ} (hdom : PhaseDomain n) :
    phaseRootDeficitTarget n ∈ Icc (9 / 4 : ℝ) (17 / 4 : ℝ) := by
  have hqLower : (2 / 3 : ℝ) < q := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hqUpper : q < (4 / 5 : ℝ) := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hTwoDivQLower : (5 / 2 : ℝ) < 2 / q := by
    rw [lt_div_iff₀ q_pos]
    nlinarith
  have hTwoDivQUpper : 2 / q < (3 : ℝ) := by
    rw [div_lt_iff₀ q_pos]
    nlinarith
  rw [phaseRootDeficitTarget_eq hdom, mem_Icc]
  constructor <;> linarith [phaseDelta_nonneg n, phaseDelta_lt_one n]

theorem eventually_finiteSignedFourMargin_gt_log_200_div_153_on_logLogCorridor
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        Real.log (200 / 153 : ℝ) <
          finiteSignedFourMargin (phaseNat n)
            (fourSizeTarget n (phaseNat n) s) := by
  obtain ⟨delta0, hdelta0, hmax⟩ :=
    (isCompact_Icc).exists_isMaxOn
      (⟨0, by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty)
      continuousOn_fourRatioLog
  set M : ℝ := fourRatioLog delta0 with hM
  have hMlt : M < Real.log (153 / 100 : ℝ) := by
    rw [hM]
    exact fourRatioLog_lt_log_153_div_100 delta0 hdelta0
  set eta : ℝ := (Real.log (153 / 100 : ℝ) - M) / 4 with heta
  have hetaPos : 0 < eta := by rw [heta]; linarith
  have hUniformContinuous : UniformContinuousOn fourTargetRatioLog
      (Icc (9 / 4 : ℝ) (17 / 4 : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      continuousOn_fourTargetRatioLog
  obtain ⟨rho, hrho, hratioClose⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUniformContinuous) eta hetaPos
  have htransport :=
    eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center
      C hC rho hrho
  obtain ⟨Nscore, hNscore⟩ :=
    eventually_uniform_fourDeficitOptimizedValue eta hetaPos
  have hle : (logOrder : ℕ → ℝ) ≤ᶠ[atTop]
      fun n : ℕ => (phaseNat n : ℝ) := by
    filter_upwards
      [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
    exact hn.1
  have hphaseReal : Tendsto (fun n : ℕ => (phaseNat n : ℝ))
      atTop atTop := tendsto_atTop_mono' atTop hle tendsto_logOrder_atTop
  have hphaseNat : Tendsto phaseNat atTop atTop := by
    rwa [tendsto_natCast_atTop_iff] at hphaseReal
  filter_upwards
    [eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
      htransport, eventually_five_lt_phaseNat,
      hphaseNat.eventually (eventually_ge_atTop Nscore),
      eventually_phaseRoot_domain_pos_and_target_corridor] with
      n htarget hmove hphase hscore hdomain
  obtain ⟨hdom, _, _⟩ := hdomain
  intro s hs
  set T : ℝ := fourSizeTarget n (phaseNat n) s with hT
  have hTK : T ∈ Icc (9 / 4 : ℝ) (17 / 4 : ℝ) := by
    simpa [hT] using htarget s hs
  have hTinterior : T ∈ Ioo (2 : ℝ) 5 := by
    constructor <;> linarith [hTK.1, hTK.2]
  have hcenterK : phaseRootDeficitTarget n ∈
      Icc (9 / 4 : ℝ) (17 / 4 : ℝ) :=
    phaseRootDeficitTarget_mem_targetCompact hdom
  have hratioDist : dist (fourTargetRatioLog T)
      (fourTargetRatioLog (phaseRootDeficitTarget n)) < eta := by
    apply hratioClose T hTK (phaseRootDeficitTarget n) hcenterK
    simpa [Real.dist_eq, hT] using hmove s hs
  have hdelta : phaseDelta n ∈ Icc (0 : ℝ) 1 :=
    ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have hcenterRatio : fourTargetRatioLog (phaseRootDeficitTarget n) =
      fourRatioLog (phaseDelta n) := by
    rw [phaseRootDeficitTarget_eq hdom]
    rfl
  have hratioCenterLe :
      fourTargetRatioLog (phaseRootDeficitTarget n) ≤ M := by
    rw [hcenterRatio, hM]
    exact hmax hdelta
  have hratioTlt : fourTargetRatioLog T < M + eta := by
    rw [Real.dist_eq] at hratioDist
    have := (abs_lt.mp hratioDist).2
    linarith
  have hlossLe : fourEntropyLoss T ≤ fourTargetRatioLog T :=
    fourEntropyLoss_le_fourTargetRatioLog hTinterior
  have hscoreAbs := hNscore (phaseNat n) hscore T hTinterior
  have hscoreLt : finiteFourScoreEntropyError (phaseNat n) T < eta := by
    unfold finiteFourScoreEntropyError
    rw [abs_sub_comm] at hscoreAbs
    exact (abs_lt.mp hscoreAbs).2
  have hunrestrictedLe :
      finiteUnrestrictedEntropyError (phaseNat n) T ≤ 0 := by
    unfold finiteUnrestrictedEntropyError finiteUnrestrictedDeficitEntropy
    have h := finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
      (phaseNat n) hphase hTinterior
    linarith
  have htotal :
      fourEntropyLoss T + finiteFourScoreEntropyError (phaseNat n) T +
          finiteUnrestrictedEntropyError (phaseNat n) T <
        Real.log (153 / 100 : ℝ) := by
    rw [heta] at hratioTlt hscoreLt
    linarith
  rw [hT, finiteSignedFourMargin,
    finiteSignedFourEntropyLoss_eq_limiting_add_errors]
  exact signed_margin_gt_log_200_div_153_of_entropy_loss_lt htotal

#print axioms fourEntropyLoss_le_fourTargetRatioLog
#print axioms continuousOn_fourTargetRatioLog
#print axioms eventually_finiteSignedFourMargin_gt_log_200_div_153_on_logLogCorridor

end

end Erdos625
