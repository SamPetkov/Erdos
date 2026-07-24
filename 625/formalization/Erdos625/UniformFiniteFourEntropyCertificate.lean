import Erdos625.UniformLimitingEntropyCertificate
import Erdos625.FourDeficitScoreConvergence
import Erdos625.SignedFourEntropyLossDecomposition
import Erdos625.SignedFourSizeObjective
import Erdos625.SignedFourEntropyCertificate
import Erdos625.ProfileOptimizerContinuityS4
import Erdos625.ProfileOptimizerUniformS4
import Erdos625.ExtendedGaussianCalculus
import Mathlib.Tactic

namespace Erdos625

noncomputable section

set_option autoImplicit false

open scoped Topology

theorem two_div_q_bounds : 2 < 2 / q ∧ 2 / q < 4 := by
  have hq_lt_one : q < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num [q] at h ⊢
    exact h
  have hq_gt_half : (1 / 2 : ℝ) < q := by
    have h := Real.log_two_gt_d9
    unfold q
    norm_num at h ⊢
    linarith
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ q_pos]; linarith
  · rw [div_lt_iff₀ q_pos]; linarith

theorem fourTarget_mem_Ioo (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    (1 + 2 / q - delta) ∈ Set.Ioo (2 : ℝ) 5 := by
  rcases hdelta with ⟨h0, h1⟩
  obtain ⟨hlo, hhi⟩ := two_div_q_bounds
  constructor <;> [linarith; linarith]

noncomputable def fourRatioLog (delta : ℝ) : ℝ :=
  Real.log
    (extendedGaussianPartition q
        (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)) /
      ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)))

theorem fourEntropyLoss_le_fourRatioLog (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    fourEntropyLoss (1 + 2 / q - delta) ≤ fourRatioLog delta := by
  have hT : (1 + 2 / q - delta) ∈ Set.Ioo (2 : ℝ) 5 :=
    fourTarget_mem_Ioo delta hdelta
  set tilt := ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta) with htilt
  have hMean : ProfileEntropyS4.mean fourGaussianScore tilt = 1 + 2 / q - delta :=
    ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT
  have hDual := extendedGaussianEntropyValue_le_dual_interior (tilt := tilt) hT
  have h := entropy_loss_le_log_partition_ratio (tilt := tilt) hMean hDual
  simpa [fourEntropyLoss, fourRatioLog, htilt] using h

theorem fourRatioLog_lt_log_153_div_100 (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    fourRatioLog delta < Real.log (153 / 100 : ℝ) := by
  rcases hdelta with ⟨h0, h1⟩
  set tilt := ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta) with htilt
  have hT : (1 + 2 / q - delta) ∈ Set.Ioo (2 : ℝ) 5 :=
    fourTarget_mem_Ioo delta ⟨h0, h1⟩
  have hMean : ProfileEntropyS4.mean fourGaussianScore tilt = 1 + 2 / q - delta :=
    ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT
  have hRatio := uniform_four_size_partition_ratio_for_delta delta tilt h0 h1 hMean
  have hpos : 0 < extendedGaussianPartition q tilt /
      ProfileEntropyS4.partition fourGaussianScore tilt :=
    div_pos (extendedGaussianPartition_pos q_pos)
      (ProfileEntropyS4.partition_pos fourGaussianScore tilt)
  have := Real.strictMonoOn_log hpos (by norm_num) hRatio
  simpa [fourRatioLog, htilt] using this

theorem continuousOn_fourRatioLog :
    ContinuousOn fourRatioLog (Set.Icc (0 : ℝ) 1) := by
  have htiltCont :
      ContinuousOn
        (fun delta => ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta))
        (Set.Icc (0 : ℝ) 1) := by
    intro delta hdelta
    apply ContinuousAt.continuousWithinAt
    have hT : (1 + 2 / q - delta) ∈ Set.Ioo (2 : ℝ) 5 :=
      fourTarget_mem_Ioo delta hdelta
    exact ProfileEntropyS4.tendsto_tilt_of_scores_and_target
      (h := fun _ : ℝ => fourGaussianScore) fourGaussianScore
      (T' := fun d => 1 + 2 / q - d)
      (fun _ => tendsto_const_nhds)
      ((continuous_const.sub continuous_id).tendsto delta) hT
  have hExtCont : Continuous (extendedGaussianPartition q) := by
    rw [continuous_iff_continuousAt]
    exact fun lambda => (hasDerivAt_extendedGaussianPartition q lambda q_pos).continuousAt
  have hFourCont : Continuous (ProfileEntropyS4.partition fourGaussianScore) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ProfileEntropyS4.tendsto_partition_of_scores_and_parameter
      (fun _ : ℝ => fourGaussianScore) fourGaussianScore id t
      (fun _ => tendsto_const_nhds) Filter.tendsto_id
  have hNum : ContinuousOn
      (fun delta => extendedGaussianPartition q
        (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)))
      (Set.Icc (0 : ℝ) 1) := hExtCont.comp_continuousOn htiltCont
  have hDen : ContinuousOn
      (fun delta => ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)))
      (Set.Icc (0 : ℝ) 1) := hFourCont.comp_continuousOn htiltCont
  have hDenNe : ∀ delta ∈ Set.Icc (0 : ℝ) 1,
      ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)) ≠ 0 :=
    fun delta _ => (ProfileEntropyS4.partition_pos fourGaussianScore _).ne'
  have hRatio : ContinuousOn
      (fun delta => extendedGaussianPartition q
          (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)) /
        ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)))
      (Set.Icc (0 : ℝ) 1) := hNum.div hDen hDenNe
  have hRatioPos : ∀ delta ∈ Set.Icc (0 : ℝ) 1,
      extendedGaussianPartition q
          (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)) /
        ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore (1 + 2 / q - delta)) ≠ 0 :=
    fun delta _ => (div_pos (extendedGaussianPartition_pos q_pos)
      (ProfileEntropyS4.partition_pos fourGaussianScore _)).ne'
  exact hRatio.log hRatioPos

theorem uniform_fourEntropyLoss_bound :
    ∃ M : ℝ, M < Real.log (153 / 100 : ℝ) ∧
      ∀ delta ∈ Set.Icc (0 : ℝ) 1,
        fourEntropyLoss (1 + 2 / q - delta) ≤ M := by
  obtain ⟨delta0, hdelta0, hmax⟩ :=
    (isCompact_Icc).exists_isMaxOn (⟨0, by norm_num⟩ : (Set.Icc (0 : ℝ) 1).Nonempty)
      continuousOn_fourRatioLog
  refine ⟨fourRatioLog delta0, fourRatioLog_lt_log_153_div_100 delta0 hdelta0, ?_⟩
  intro delta hdelta
  exact (fourEntropyLoss_le_fourRatioLog delta hdelta).trans (hmax hdelta)

/-- Transfer the limiting uniform entropy gap to the exact finite
four-deficit scores with one threshold valid for every phase displacement. -/
theorem eventually_uniform_finite_four_entropy_certificate :
    ∃ N : ℕ, ∀ alpha ≥ N, ∀ delta ∈ Set.Icc (0 : ℝ) 1,
      extendedGaussianEntropyValue (1 + 2 / q - delta) -
          fourSizeFiniteEntropy alpha (1 + 2 / q - delta) <
        Real.log (153 / 100 : ℝ) := by
  obtain ⟨M, hM_lt, hM_bound⟩ := uniform_fourEntropyLoss_bound
  set m := Real.log (153 / 100 : ℝ) - M with hm
  have hm_pos : 0 < m := by simp only [hm]; linarith
  obtain ⟨N, hN⟩ := eventually_uniform_fourDeficitOptimizedValue m hm_pos
  refine ⟨N, fun alpha halpha delta hdelta => ?_⟩
  have hT : (1 + 2 / q - delta) ∈ Set.Ioo (2 : ℝ) 5 :=
    fourTarget_mem_Ioo delta hdelta
  have hdecomp :=
    finite_four_entropy_loss_eq_limiting_add_error alpha (1 + 2 / q - delta)
  have herr := hN alpha halpha (1 + 2 / q - delta) hT
  have hloss := hM_bound delta hdelta
  rw [hdecomp]
  simp only [hm] at hm_pos
  have : |ProfileEntropyS4.optimizedValue fourGaussianScore (1 + 2 / q - delta) -
      ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) (1 + 2 / q - delta)| < m := by
    rw [abs_sub_comm]; exact herr
  have h2 := abs_lt.mp this
  linarith [h2.2, hloss]

end

end Erdos625
