import Erdos625.FourDeficitScoreConvergence
import Erdos625.ProfileOptimizerUniformS4
import Erdos625.SignedFourSizeObjective
import Mathlib.Tactic

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The exact four-deficit tilt is uniformly bounded on the compact target
interval used by the manuscript-scale phase-root corridor. -/
theorem exists_eventually_uniform_fourDeficitTilt_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ alpha ≥ N,
      ∀ target ∈ Set.Icc (5 / 2 : ℝ) (9 / 2 : ℝ),
        |ProfileEntropyS4.tilt (fourDeficitScore alpha) target| ≤ M := by
  set K : Set ℝ := Set.Icc (5 / 2 : ℝ) (9 / 2 : ℝ) with hK
  have hKcompact : IsCompact K := isCompact_Icc
  have hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5 := by
    intro T hT
    rw [hK, Set.mem_Icc] at hT
    rw [Set.mem_Ioo]
    constructor <;> [linarith [hT.1]; linarith [hT.2]]
  have hKne : K.Nonempty :=
    ⟨(5 / 2 : ℝ), by rw [hK, Set.mem_Icc]; norm_num⟩
  have hContOn : ContinuousOn
      (fun T : ℝ ↦ |ProfileEntropyS4.tilt fourGaussianScore T|) K := by
    apply Continuous.comp_continuousOn continuous_abs
    intro T hTK
    have hjoint : ContinuousAt
        (fun y : (Fin 4 → ℝ) × ℝ ↦ ProfileEntropyS4.tilt y.1 y.2)
        (fourGaussianScore, T) :=
      ProfileEntropyS4.continuousAt_tilt_joint (fourGaussianScore, T)
        (hKinterior hTK)
    have hmap : ContinuousAt (fun T' : ℝ ↦ (fourGaussianScore, T')) T :=
      (continuousAt_const.prodMk continuousAt_id)
    exact (hjoint.comp hmap).continuousWithinAt
  obtain ⟨T0, hT0K, hT0max⟩ :=
    hKcompact.exists_isMaxOn hKne hContOn
  set M0 : ℝ := |ProfileEntropyS4.tilt fourGaussianScore T0| with hM0
  have hM0nonneg : 0 ≤ M0 := abs_nonneg _
  obtain ⟨N, hN⟩ :=
    ProfileEntropyS4.eventually_uniformOn_tilt_of_uniform_scores
      fourDeficitScore fourGaussianScore K hKcompact hKinterior
      eventually_uniform_fourDeficitScore 1 (by norm_num)
  refine ⟨M0 + 1, by linarith, N, fun alpha halpha target htarget ↦ ?_⟩
  have htargetK : target ∈ K := htarget
  have hclose := hN alpha halpha target htargetK
  have hgbound : |ProfileEntropyS4.tilt fourGaussianScore target| ≤ M0 :=
    hT0max htargetK
  have hdiff := abs_sub_abs_le_abs_sub
    (ProfileEntropyS4.tilt (fourDeficitScore alpha) target)
    (ProfileEntropyS4.tilt fourGaussianScore target)
  have hlt : |ProfileEntropyS4.tilt (fourDeficitScore alpha) target| -
      |ProfileEntropyS4.tilt fourGaussianScore target| < 1 :=
    lt_of_le_of_lt hdiff hclose
  linarith

/-- Uniform bound on the exact four-deficit scores for all large `alpha`. -/
theorem exists_eventually_uniform_fourDeficitScore_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ alpha ≥ N, ∀ i : Fin 4,
      |fourDeficitScore alpha i| ≤ C := by
  obtain ⟨N, hN⟩ := eventually_uniform_fourDeficitScore 1 (by norm_num)
  refine ⟨1 + ∑ j : Fin 4, |fourGaussianScore j|, by positivity, N, ?_⟩
  intro alpha halpha i
  have h := hN alpha halpha i
  have htri := abs_sub_abs_le_abs_sub
    (fourDeficitScore alpha i) (fourGaussianScore i)
  have hsum : |fourGaussianScore i| ≤ ∑ j : Fin 4, |fourGaussianScore j| :=
    Finset.single_le_sum (f := fun j => |fourGaussianScore j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

/-- Elementary two-sided bound on the log-partition of the four-point family in
terms of uniform bounds `C` on the score and `M` on the tilt.  Each
unnormalized mass `exp (h i + t * support i)` has exponent in `[-(C+5M), C+5M]`
because `support i ∈ [2,5]`, so the four-term partition lies between
`exp (-(C+5M))` and `4 * exp (C+5M)`. -/
theorem abs_log_partition_le (h : Fin 4 → ℝ) (t C M : ℝ)
    (hM : 0 ≤ M) (hh : ∀ i, |h i| ≤ C) (ht : |t| ≤ M) :
    |Real.log (ProfileEntropyS4.partition h t)| ≤ Real.log 4 + C + 5 * M := by
  set P := ProfileEntropyS4.partition h t with hP
  have hPpos : 0 < P := ProfileEntropyS4.partition_pos h t
  -- Each support value lies in `[2,5]`, so `|support i| ≤ 5`.
  have hsupp : ∀ i : Fin 4, |ProfileEntropyS4.support i| ≤ 5 := by
    intro i; fin_cases i <;> norm_num [ProfileEntropyS4.support]
  -- Two-sided bound on the tilt contribution `t * support i`.
  have htsupp : ∀ i : Fin 4, |t * ProfileEntropyS4.support i| ≤ 5 * M := by
    intro i
    calc |t * ProfileEntropyS4.support i|
        = |t| * |ProfileEntropyS4.support i| := abs_mul _ _
      _ ≤ M * 5 := mul_le_mul ht (hsupp i) (abs_nonneg _) hM
      _ = 5 * M := by ring
  -- Hence each exponent lies in `[-(C+5M), C+5M]`.
  have hexp_le : ∀ i : Fin 4,
      h i + t * ProfileEntropyS4.support i ≤ C + 5 * M := by
    intro i
    have h1 : h i ≤ C := (abs_le.mp (hh i)).2
    have h2 : t * ProfileEntropyS4.support i ≤ 5 * M :=
      le_trans (le_abs_self _) (htsupp i)
    linarith
  have hexp_ge : ∀ i : Fin 4,
      -(C + 5 * M) ≤ h i + t * ProfileEntropyS4.support i := by
    intro i
    have h1 : -C ≤ h i := (abs_le.mp (hh i)).1
    have h2 : -(5 * M) ≤ t * ProfileEntropyS4.support i :=
      neg_le_of_neg_le (le_trans (neg_le_abs _) (htsupp i))
    linarith
  -- Term-wise bounds on the unnormalized masses.
  have hterm_le : ∀ i : Fin 4,
      ProfileEntropyS4.unnormalized h t i ≤ Real.exp (C + 5 * M) := by
    intro i; exact Real.exp_le_exp.mpr (hexp_le i)
  have hterm_ge : ∀ i : Fin 4,
      Real.exp (-(C + 5 * M)) ≤ ProfileEntropyS4.unnormalized h t i := by
    intro i; exact Real.exp_le_exp.mpr (hexp_ge i)
  have hu0 := ProfileEntropyS4.unnormalized_pos h t 0
  have hu1 := ProfileEntropyS4.unnormalized_pos h t 1
  have hu2 := ProfileEntropyS4.unnormalized_pos h t 2
  have hu3 := ProfileEntropyS4.unnormalized_pos h t 3
  -- Upper and lower bounds on the partition function.
  have hP_le : P ≤ 4 * Real.exp (C + 5 * M) := by
    rw [hP, ProfileEntropyS4.partition, Fin.sum_univ_four]
    have := hterm_le 0; have := hterm_le 1
    have := hterm_le 2; have := hterm_le 3
    linarith [hterm_le 0, hterm_le 1, hterm_le 2, hterm_le 3]
  have hP_ge : Real.exp (-(C + 5 * M)) ≤ P := by
    rw [hP, ProfileEntropyS4.partition, Fin.sum_univ_four]
    linarith [hterm_ge 0, hu1, hu2, hu3]
  -- Translate to the logarithm.
  have hlog_le : Real.log P ≤ Real.log 4 + (C + 5 * M) := by
    have hle := Real.log_le_log hPpos hP_le
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hle
  have hlog_ge : -(C + 5 * M) ≤ Real.log P := by
    have hle := Real.log_le_log (Real.exp_pos _) hP_ge
    rwa [Real.log_exp] at hle
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The exact four-deficit log-partition, evaluated at the mean-`target` tilt, is
uniformly bounded on the compact target corridor `[5/2, 9/2]` for large `alpha`.
This is the companion of `exists_eventually_uniform_fourDeficitTilt_bound` used
by the derivative assembly. -/
theorem exists_eventually_uniform_fourDeficit_logPartition_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ alpha ≥ N,
      ∀ target ∈ Set.Icc (5 / 2 : ℝ) (9 / 2 : ℝ),
        |Real.log (ProfileEntropyS4.partition (fourDeficitScore alpha)
          (ProfileEntropyS4.tilt (fourDeficitScore alpha) target))| ≤ M := by
  obtain ⟨C, hC, Nc, hCbound⟩ := exists_eventually_uniform_fourDeficitScore_bound
  obtain ⟨Mt, hMt, Nt, hTbound⟩ := exists_eventually_uniform_fourDeficitTilt_bound
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.log 4 + C + 5 * Mt, by linarith, max Nc Nt, ?_⟩
  intro alpha halpha target htarget
  have h1 : alpha ≥ Nc := le_trans (le_max_left _ _) halpha
  have h2 : alpha ≥ Nt := le_trans (le_max_right _ _) halpha
  exact abs_log_partition_le _ _ C Mt hMt (hCbound alpha h1)
    (hTbound alpha h2 target htarget)

end

end Erdos625
