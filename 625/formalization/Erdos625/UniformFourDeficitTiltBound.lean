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

end

end Erdos625
