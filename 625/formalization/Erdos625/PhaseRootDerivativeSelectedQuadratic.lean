Exit code: 0
Wall time: 0.3 seconds
Output:
Exit code: 0
Wall time: 0.2 seconds
Output:
import Erdos625.PhaseRootFiniteCommon
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/--
The complete selected term occurring in the derivative is eventually
quadratically negligible.
-/
theorem eventually_abs_phaseRootDerivativeSelectedTerm_le_quadratic :
    ∀ᶠ n : ℕ in atTop,
      |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))) -
        profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
          (phaseNat n : ℝ)| ≤
        q / 16 * (phaseNat n : ℝ) ^ 2 := by
  have hA : (-1 : ℝ) < 2 / q := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hAB : (2 / q : ℝ) ≤ 1 + 2 / q := by linarith
  obtain ⟨M, _, huniform⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hA hAB
  obtain ⟨N, hN⟩ := eventually_atTop.1 huniform
  -- The constant logarithmic-partition envelope coming from the Gaussian bound.
  set CL : ℝ :=
    Real.exp M +
      Real.exp (M ^ 2 / q) * (1 / (1 - Real.exp (-q / 4))) with hCLdef
  -- The linear-growth threshold ensuring quadratic domination.
  set K : ℝ := 16 / q * (CL + M) with hKdef
  -- `phaseNat` eventually exceeds the natural index `N` from the uniform bound.
  have hphaseN : ∀ᶠ n : ℕ in atTop, N ≤ phaseNat n := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop (N : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact_mod_cast hn.trans hphase.1
  -- `phaseNat` eventually exceeds the real threshold `K`.
  have hphaseK : ∀ᶠ n : ℕ in atTop, K ≤ (phaseNat n : ℝ) := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop K,
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact hn.trans hphase.1
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
      hphaseN, hphaseK, eventually_two_le_phaseNat] with n hn hlarge hKle hphasePos
  -- The deficit target lands in the uniform selected-tilt corridor.
  have hcorr :
      phaseRootDeficitTarget n ∈ Set.Icc (2 / q) (1 + 2 / q) := by
    simpa [phaseRootDeficitTarget] using hn.2.2
  have htiltbound :=
    (hN (phaseNat n) hlarge (phaseRootDeficitTarget n) hcorr).2
  -- Partition corridor: lower bound `1` and Gaussian-envelope upper bound `CL`.
  have hpartLower :=
    one_le_profileDeficitPartition (phaseNat n) (by omega)
      (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))
  have hpartUpper :=
    profileDeficitPartition_le_gaussianEnvelope (phaseNat n) (by omega) htiltbound
  rw [← hCLdef] at hpartUpper
  have hCLnn : (0 : ℝ) ≤ CL := by linarith
  -- Uniform bound on the logarithmic-partition piece.
  have hlogPart :
      |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n)))| ≤ CL := by
    rw [abs_of_nonneg (Real.log_nonneg hpartLower)]
    exact (Real.log_le_sub_one_of_pos (profileDeficitPartition_pos _ _)).trans
      (by linarith)
  -- Bound on the tilt-linear piece.
  have hPnn : (0 : ℝ) ≤ (phaseNat n : ℝ) := by positivity
  have htiltP :
      |profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
          (phaseNat n : ℝ)| ≤ M * (phaseNat n : ℝ) := by
    rw [abs_mul, abs_of_nonneg hPnn]
    exact mul_le_mul_of_nonneg_right htiltbound hPnn
  -- Linear-in-`phaseNat` domination from the growth threshold.
  have hqDivNn : (0 : ℝ) ≤ q / 16 := div_nonneg q_pos.le (by norm_num)
  have hstep : CL + M ≤ q / 16 * (phaseNat n : ℝ) := by
    have hK : q / 16 * K = CL + M := by
      have hqne : q ≠ 0 := q_pos.ne'
      rw [hKdef]
      field_simp
    calc
      CL + M = q / 16 * K := hK.symm
      _ ≤ q / 16 * (phaseNat n : ℝ) := mul_le_mul_of_nonneg_left hKle hqDivNn
  have hP1 : (1 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (by omega : 1 ≤ phaseNat n)
  have hfinal :
      CL + M * (phaseNat n : ℝ) ≤ q / 16 * (phaseNat n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hstep hPnn,
      mul_nonneg hCLnn (by linarith : (0 : ℝ) ≤ (phaseNat n : ℝ) - 1)]
  calc
    |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))) -
        profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
          (phaseNat n : ℝ)| ≤
        |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n)))| +
        |profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
          (phaseNat n : ℝ)| := abs_sub _ _
    _ ≤ CL + M * (phaseNat n : ℝ) := by linarith
    _ ≤ q / 16 * (phaseNat n : ℝ) ^ 2 := hfinal

end

end Erdos625


