import Erdos625.UniformFiniteFourEntropyCertificate
import Erdos625.ProfileOptimizerContinuityS4
import Erdos625.ProfileOptimizerUniformS4
import Mathlib.Tactic

namespace Erdos625

noncomputable section

set_option autoImplicit false

open Filter
open scoped Topology

/-! ## Neighborhood extension of the finite four-entropy certificate

The helper declarations below are the ones genuinely needed to prove
`exists_uniform_finite_four_entropy_neighborhood`.  They are kept local to this
file (and `private`) so that no dependency file has to be modified. -/

/-- Target-parameterized version of `fourRatioLog`: the log of the extended
Gaussian partition ratio at the exact four-size tilt representing `target`. -/
private noncomputable def fourRatioLogTarget (target : ℝ) : ℝ :=
  Real.log
    (extendedGaussianPartition q
        (ProfileEntropyS4.tilt fourGaussianScore target) /
      ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore target))

private theorem fourEntropyLoss_le_fourRatioLogTarget (target : ℝ)
    (hT : target ∈ Set.Ioo (2 : ℝ) 5) :
    fourEntropyLoss target ≤ fourRatioLogTarget target := by
  set tilt := ProfileEntropyS4.tilt fourGaussianScore target with htilt
  have hMean : ProfileEntropyS4.mean fourGaussianScore tilt = target :=
    ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT
  have hDual := extendedGaussianEntropyValue_le_dual_interior (tilt := tilt) hT
  have h := entropy_loss_le_log_partition_ratio (tilt := tilt) hMean hDual
  simpa [fourEntropyLoss, fourRatioLogTarget, htilt] using h

private theorem fourRatioLogTarget_lt_log_153_div_100 (target : ℝ)
    (hlo : 2 / q ≤ target) (hhi : target ≤ 1 + 2 / q) :
    fourRatioLogTarget target < Real.log (153 / 100 : ℝ) := by
  have hT : target ∈ Set.Ioo (2 : ℝ) 5 := by
    obtain ⟨h2, h4⟩ := two_div_q_bounds
    exact ⟨by linarith, by linarith⟩
  set tilt := ProfileEntropyS4.tilt fourGaussianScore target with htilt
  have hMean : ProfileEntropyS4.mean fourGaussianScore tilt = target :=
    ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT
  have hRatio := uniform_four_size_partition_ratio target tilt hlo hhi hMean
  have hpos : 0 < extendedGaussianPartition q tilt /
      ProfileEntropyS4.partition fourGaussianScore tilt :=
    div_pos (extendedGaussianPartition_pos q_pos)
      (ProfileEntropyS4.partition_pos fourGaussianScore tilt)
  have := Real.strictMonoOn_log hpos (by norm_num) hRatio
  simpa [fourRatioLogTarget, htilt] using this

private theorem continuousOn_fourRatioLogTarget :
    ContinuousOn fourRatioLogTarget (Set.Ioo (2 : ℝ) 5) := by
  have htiltCont :
      ContinuousOn
        (fun target => ProfileEntropyS4.tilt fourGaussianScore target)
        (Set.Ioo (2 : ℝ) 5) := by
    intro target hT
    apply ContinuousAt.continuousWithinAt
    exact ProfileEntropyS4.tendsto_tilt_of_scores_and_target
      (h := fun _ : ℝ => fourGaussianScore) fourGaussianScore
      (T' := id)
      (fun _ => tendsto_const_nhds)
      (continuous_id.tendsto target) hT
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
      (fun target => extendedGaussianPartition q
        (ProfileEntropyS4.tilt fourGaussianScore target))
      (Set.Ioo (2 : ℝ) 5) := hExtCont.comp_continuousOn htiltCont
  have hDen : ContinuousOn
      (fun target => ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore target))
      (Set.Ioo (2 : ℝ) 5) := hFourCont.comp_continuousOn htiltCont
  have hDenNe : ∀ target ∈ Set.Ioo (2 : ℝ) 5,
      ProfileEntropyS4.partition fourGaussianScore
        (ProfileEntropyS4.tilt fourGaussianScore target) ≠ 0 :=
    fun target _ => (ProfileEntropyS4.partition_pos fourGaussianScore _).ne'
  have hRatio : ContinuousOn
      (fun target => extendedGaussianPartition q
          (ProfileEntropyS4.tilt fourGaussianScore target) /
        ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore target))
      (Set.Ioo (2 : ℝ) 5) := hNum.div hDen hDenNe
  have hRatioPos : ∀ target ∈ Set.Ioo (2 : ℝ) 5,
      extendedGaussianPartition q
          (ProfileEntropyS4.tilt fourGaussianScore target) /
        ProfileEntropyS4.partition fourGaussianScore
          (ProfileEntropyS4.tilt fourGaussianScore target) ≠ 0 :=
    fun target _ => (div_pos (extendedGaussianPartition_pos q_pos)
      (ProfileEntropyS4.partition_pos fourGaussianScore _)).ne'
  exact hRatio.log hRatioPos

/-- The finite four-entropy loss is bounded by a single constant strictly below
`log(153/100)` on a genuine closed neighborhood of the limiting phase interval
`[2/q, 1+2/q]`.  The neighborhood radius `eta` is a single positive constant. -/
private theorem exists_neighborhood_fourEntropyLoss_bound :
    ∃ eta : ℝ, 0 < eta ∧ (2 : ℝ) < 2 / q - eta ∧ 1 + 2 / q + eta < 5 ∧
      ∃ M : ℝ, M < Real.log (153 / 100 : ℝ) ∧
        ∀ target ∈ Set.Icc (2 / q - eta) (1 + 2 / q + eta),
          fourEntropyLoss target ≤ M := by
  obtain ⟨hq2, hq4⟩ := two_div_q_bounds
  set a : ℝ := 2 / q with ha
  set b : ℝ := 1 + 2 / q with hb
  have hab : a < b := by simp only [ha, hb]; linarith
  have hKsub : Set.Icc a b ⊆ Set.Ioo (2 : ℝ) 5 := by
    intro t ht
    exact ⟨by simp only [ha] at ht ⊢; linarith [ht.1],
      by simp only [hb] at ht ⊢; linarith [ht.2]⟩
  -- the open set on which the ratio log is strictly below the target constant
  set c : ℝ := Real.log (153 / 100 : ℝ) with hc
  set U : Set ℝ := Set.Ioo (2 : ℝ) 5 ∩ (fourRatioLogTarget ⁻¹' Set.Iio c) with hU
  have hUopen : IsOpen U := by
    rw [hU]
    exact continuousOn_fourRatioLogTarget.isOpen_inter_preimage isOpen_Ioo isOpen_Iio
  have hKU : Set.Icc a b ⊆ U := by
    intro t ht
    refine ⟨hKsub ht, ?_⟩
    simp only [Set.mem_preimage, Set.mem_Iio, hc]
    exact fourRatioLogTarget_lt_log_153_div_100 t (by simp only [ha] at ht; exact ht.1)
      (by simp only [hb] at ht; exact ht.2)
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_Icc).exists_cthickening_subset_open hUopen hKU
  set eta : ℝ := min δ (min ((a - 2) / 2) ((5 - b) / 2)) with heta
  have hetapos : 0 < eta := by
    simp only [heta, lt_min_iff]
    refine ⟨hδpos, ?_, ?_⟩
    · simp only [ha]; linarith
    · simp only [hb]; linarith
  have heta_le_δ : eta ≤ δ := min_le_left _ _
  have heta_lo : (2 : ℝ) < a - eta := by
    have : eta ≤ (a - 2) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    simp only [ha] at this ⊢; linarith
  have heta_hi : b + eta < 5 := by
    have : eta ≤ (5 - b) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    simp only [hb] at this ⊢; linarith
  -- the closed neighborhood interval sits inside the cthickening, hence inside U
  have hIntervalU : Set.Icc (a - eta) (b + eta) ⊆ U := by
    intro t ht
    apply hδsub
    rcases ht with ⟨htlo, hthi⟩
    rcases le_or_gt t a with hta | hta
    · refine Metric.mem_cthickening_of_dist_le t a δ _ ⟨le_refl a, hab.le⟩ ?_
      rw [Real.dist_eq]
      rw [abs_of_nonpos (by linarith)]
      linarith
    · rcases le_or_gt t b with htb | htb
      · refine Metric.mem_cthickening_of_dist_le t t δ _ ⟨hta.le, htb⟩ ?_
        simp [hδpos.le]
      · refine Metric.mem_cthickening_of_dist_le t b δ _ ⟨hab.le, le_refl b⟩ ?_
        rw [Real.dist_eq]
        rw [abs_of_pos (by linarith)]
        linarith
  have hIntervalIoo : Set.Icc (a - eta) (b + eta) ⊆ Set.Ioo (2 : ℝ) 5 :=
    fun t ht => (hIntervalU ht).1
  have hIntervalRatio : ∀ t ∈ Set.Icc (a - eta) (b + eta),
      fourRatioLogTarget t < c := fun t ht => (hIntervalU ht).2
  -- maximum of the ratio log over the compact neighborhood interval
  have hContOnInterval : ContinuousOn fourRatioLogTarget
      (Set.Icc (a - eta) (b + eta)) :=
    continuousOn_fourRatioLogTarget.mono hIntervalIoo
  have hNe : (Set.Icc (a - eta) (b + eta)).Nonempty :=
    Set.nonempty_Icc.2 (by linarith)
  obtain ⟨tmax, htmax_mem, htmax⟩ :=
    (isCompact_Icc).exists_isMaxOn hNe hContOnInterval
  refine ⟨eta, hetapos, ?_, ?_, fourRatioLogTarget tmax, ?_, ?_⟩
  · simpa [ha] using heta_lo
  · simpa [hb] using heta_hi
  · exact hIntervalRatio tmax htmax_mem
  · intro target htarget
    have hTioo : target ∈ Set.Ioo (2 : ℝ) 5 := hIntervalIoo htarget
    exact (fourEntropyLoss_le_fourRatioLogTarget target hTioo).trans (htmax htarget)

/-- The strict finite four-entropy certificate extends uniformly to one fixed
neighborhood of the full limiting phase interval. -/
theorem exists_uniform_finite_four_entropy_neighborhood :
    ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, ∀ alpha ≥ N,
      ∀ target ∈ Set.Icc (2 / q - eta) (1 + 2 / q + eta),
        extendedGaussianEntropyValue target -
            fourSizeFiniteEntropy alpha target <
          Real.log (153 / 100 : ℝ) := by
  obtain ⟨eta, heta, hlo, hhi, M, hM_lt, hM_bound⟩ :=
    exists_neighborhood_fourEntropyLoss_bound
  refine ⟨eta, heta, ?_⟩
  set m : ℝ := Real.log (153 / 100 : ℝ) - M with hm
  have hm_pos : 0 < m := by simp only [hm]; linarith
  obtain ⟨N, hN⟩ := eventually_uniform_fourDeficitOptimizedValue m hm_pos
  refine ⟨N, fun alpha halpha target htarget => ?_⟩
  have hTioo : target ∈ Set.Ioo (2 : ℝ) 5 := by
    rcases htarget with ⟨htlo, hthi⟩
    exact ⟨by linarith, by linarith⟩
  have hdecomp :=
    finite_four_entropy_loss_eq_limiting_add_error alpha target
  have herr := hN alpha halpha target hTioo
  have hloss := hM_bound target htarget
  rw [hdecomp]
  have h2 := abs_lt.mp herr
  linarith [h2.1, h2.2, hloss]

/-- Specialization of `exists_uniform_finite_four_entropy_neighborhood` to the
phase size `phaseNat n`: since `phaseNat` eventually exceeds every fixed natural
threshold, the uniform neighborhood bound holds eventually along `phaseNat n`. -/
theorem exists_eventually_uniform_phaseNat_four_entropy_neighborhood :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ target ∈ Set.Icc (2 / q - eta) (1 + 2 / q + eta),
          extendedGaussianEntropyValue target -
              fourSizeFiniteEntropy (phaseNat n) target <
            Real.log (153 / 100 : ℝ) := by
  obtain ⟨eta, heta, N, hN⟩ := exists_uniform_finite_four_entropy_neighborhood
  refine ⟨eta, heta, ?_⟩
  filter_upwards
    [tendsto_logOrder_atTop.eventually_ge_atTop (N : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
  have hge : N ≤ phaseNat n := by exact_mod_cast hn.trans hphase.1
  exact hN (phaseNat n) hge

end

end Erdos625
