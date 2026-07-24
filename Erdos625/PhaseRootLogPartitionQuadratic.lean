import Erdos625.PhaseRootFiniteCommon
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/-- The derivative's selected log-partition term is eventually quadratically negligible. -/
theorem eventually_abs_phaseRootLogPartition_le_quadratic :
    ∀ᶠ n : ℕ in atTop,
      |Real.log
        (profileDeficitPartition (phaseNat n)
          (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n)))| ≤
        q / 32 * (phaseNat n : ℝ) ^ 2 := by
  have hA : (-1 : ℝ) < 2 / q := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hAB : (2 / q : ℝ) ≤ 1 + 2 / q := by linarith
  obtain ⟨M, _, huniform⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hA hAB
  set C : ℝ :=
    Real.exp M + Real.exp (M ^ 2 / q) * (1 / (1 - Real.exp (-q / 4))) with hC
  obtain ⟨N, hN⟩ := (eventually_atTop.1 huniform)
  have hphaseLarge : ∀ᶠ n : ℕ in atTop, N ≤ phaseNat n := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop (N : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact_mod_cast hn.trans hphase.1
  -- The log-partition term is eventually bounded by the constant `C` coming from
  -- the uniform selected-tilt bound and the Gaussian envelope for the partition.
  have hlogBound : ∀ᶠ n : ℕ in atTop,
      |Real.log
        (profileDeficitPartition (phaseNat n)
          (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n)))| ≤ C := by
    filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
        hphaseLarge, eventually_two_le_phaseNat] with n hn hlarge hphasePos
    have htilt := (hN (phaseNat n) hlarge
      (phaseRootDeficitTarget n) (by
        simpa [phaseRootDeficitTarget] using hn.2.2)).2
    have hpartLower := one_le_profileDeficitPartition
      (phaseNat n) (by omega)
      (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))
    have hpartUpper := profileDeficitPartition_le_gaussianEnvelope
      (phaseNat n) (by omega) htilt
    rw [abs_of_nonneg (Real.log_nonneg hpartLower)]
    exact (Real.log_le_sub_one_of_pos (profileDeficitPartition_pos _ _)).trans
      (by rw [hC]; linarith)
  -- `phaseNat` grows without bound, so the `q / 32` quadratic eventually dominates `C`.
  have hquad : ∀ᶠ n : ℕ in atTop, C ≤ q / 32 * (phaseNat n : ℝ) ^ 2 := by
    have hpt : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ)) atTop atTop := by
      apply tendsto_atTop_mono' atTop _ tendsto_logOrder_atTop
      filter_upwards
        [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
      exact hn.1
    have hsq : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (two_ne_zero)).comp hpt
    have htend : Tendsto (fun n : ℕ ↦ q / 32 * (phaseNat n : ℝ) ^ 2) atTop atTop :=
      hsq.const_mul_atTop (div_pos q_pos (by norm_num))
    exact htend.eventually_ge_atTop C
  filter_upwards [hlogBound, hquad] with n h1 h2
  exact h1.trans h2

end

end Erdos625

