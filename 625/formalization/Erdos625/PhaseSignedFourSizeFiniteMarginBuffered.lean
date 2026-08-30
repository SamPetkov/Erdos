import Erdos625.PhaseSignedFourSizeFiniteMargin
import Mathlib.Tactic

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section
set_option autoImplicit false

/-- A fixed positive phase-uniform buffer above the manuscript margin. -/
theorem exists_pos_uniform_finiteSignedFourMargin_buffer_on_logLogCorridor
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ s ∈ Icc
            (phaseRootCenter n -
              C * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              C * logLogOrder n * phaseRootGapRadius n),
          Real.log (200 / 153 : ℝ) + eta ≤
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
  refine ⟨eta, hetaPos, ?_⟩
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
      Icc (9 / 4 : ℝ) (17 / 4 : ℝ) := by
    have hqLower : (2 / 3 : ℝ) < q :=
      (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    have hqUpper : q < (4 / 5 : ℝ) :=
      Real.log_two_lt_d9.trans (by norm_num)
    have hTwoDivQLower : (5 / 2 : ℝ) < 2 / q := by
      rw [lt_div_iff₀ q_pos]
      nlinarith
    have hTwoDivQUpper : 2 / q < (3 : ℝ) := by
      rw [div_lt_iff₀ q_pos]
      nlinarith
    rw [phaseRootDeficitTarget_eq hdom, mem_Icc]
    constructor <;> linarith [phaseDelta_nonneg n, phaseDelta_lt_one n]
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
  -- Two of the four quarters of the slack `log (153 / 100) - M` are spent on
  -- the target transport and the finite-score error; the remaining two
  -- quarters survive as the uniform buffer.
  have htotal :
      fourEntropyLoss T + finiteFourScoreEntropyError (phaseNat n) T +
          finiteUnrestrictedEntropyError (phaseNat n) T ≤
        Real.log (153 / 100 : ℝ) - eta := by
    rw [heta] at hratioTlt hscoreLt ⊢
    linarith
  have hidentity : q - Real.log (153 / 100 : ℝ) = Real.log (200 / 153 : ℝ) :=
    q_sub_log_153_div_100_eq_log_200_div_153
  rw [hT, finiteSignedFourMargin,
    finiteSignedFourEntropyLoss_eq_limiting_add_errors]
  linarith

#print axioms exists_pos_uniform_finiteSignedFourMargin_buffer_on_logLogCorridor

end
end Erdos625
