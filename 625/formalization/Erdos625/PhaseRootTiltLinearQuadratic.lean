import Erdos625.PhaseRootFiniteCommon
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/-- The derivative's tilt-linear term is eventually quadratically negligible. -/
theorem eventually_abs_phaseRootTilt_mul_phaseNat_le_quadratic :
    ∀ᶠ n : ℕ in atTop,
      |profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
          (phaseNat n : ℝ)| ≤
        q / 32 * (phaseNat n : ℝ) ^ 2 := by
  have hA : (-1 : ℝ) < 2 / q := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hAB : (2 / q : ℝ) ≤ 1 + 2 / q := by linarith
  obtain ⟨M, _hM, huniform⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hA hAB
  obtain ⟨N, hN⟩ := (eventually_atTop.1 huniform)
  have hphaseLargeN : ∀ᶠ n : ℕ in atTop, N ≤ phaseNat n := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop (N : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact_mod_cast hn.trans hphase.1
  have hphaseThresh : ∀ᶠ n : ℕ in atTop, (32 * M / q : ℝ) ≤ (phaseNat n : ℝ) := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop (32 * M / q : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact hn.trans hphase.1
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
      hphaseLargeN, hphaseThresh] with n hn hlarge hthresh
  have htilt := (hN (phaseNat n) hlarge
    (phaseRootDeficitTarget n) (by
      simpa [phaseRootDeficitTarget] using hn.2.2)).2
  have hphaseNonneg : (0 : ℝ) ≤ (phaseNat n : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hphaseNonneg]
  have h1 : 32 * M ≤ (phaseNat n : ℝ) * q := by
    rw [div_le_iff₀ q_pos] at hthresh
    exact hthresh
  calc |profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n)| * (phaseNat n : ℝ)
      ≤ M * (phaseNat n : ℝ) := by gcongr
    _ ≤ q / 32 * (phaseNat n : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right h1 hphaseNonneg, hphaseNonneg, q_pos]

end

end Erdos625

